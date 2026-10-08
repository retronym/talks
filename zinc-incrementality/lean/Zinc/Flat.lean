import Zinc.NonLocalAns
import Zinc.Hier

/-!
# Flattened Merkle composition over a stored, possibly stale linearization

The Zinc PoC (decision 1) composes the per-name hash of class `C` without recursion:

    H_C(n) = hash(own_C(n), [(P as seen from C, own_P(n)) | P ∈ lin(C), n ∈ decls(P)])

where `lin(C)` is the linearization *stored at `C`'s last compile*. It goes stale when an
ancestor's parents change; the argument for soundness is that such a header change recompiles
every transitive descendant, which refreshes the stored `lin`.

The model: the language of `Hier.lean` (one type parameter, parents with a type argument) with
Scala's linearization. A class's compilation computes its linearization by asking every ancestor
for its `parents` and stores it in its interface. A client selects `c.n` with one `member` query
whose answer is the lookup along `c`'s *stored* linearization, which is a function of the
flattened hash by construction. Keys:

* `(c, name n)`, hashed by the flattened composition and `c`'s kind (a trait receiver is
  `invokeinterface`), for a selection `c.n` (`client`, or `uses`
  when a class selects its own member: Zinc drops those self-references);
* `(p, parents)`, hashed by `p`'s parents, for every `parents` query a class asks while
  linearizing (`header`). Since a class asks this of *every* ancestor, the keys say "recompile
  every transitive descendant when a parents list changes": the header rule.

A class's compilation also runs a refchecks prelude against its ancestors (PoC decision 3, talk
§10a), each check a query recorded like a client's:

* override conformance of each own member: `(p, own n)`, Zinc's decls-only name hash (`overrides`);
* inherited-member reconciliation: which ancestors declare `n` (`(p, has n)`), and for pairs
  through different parents their members (`(p, own n)`) (`conflicts`);
* abstract members of a concrete class: which ancestors declare `n` and whether deferred
  (`(p, dfr n)`) (`abstract`).

and a codegen epilogue, since a class's bytecode also derives from ancestors its source never names:

* mixin forwarders: a class (or object) asks each trait it mixes in for its declarations
  (`(t, decls)`), and the ancestors ahead of the trait whether they declare the name
  (`(q, has n)`) (`trait`);
* static forwarders: an object asks every ancestor for its declarations, for its mirror
  class (`(q, decls)`) (`mirror`);
* `final` parents and which ancestors are traits are part of the header (`(p, parents)`).

So the rule table of decision 3 is the key abstraction of the descendant's refchecks and codegen
trace, and T2″ covers the filtered inheritance edge.

`Fl_obligations` proves the full key set meets `NCompiler.Obligations`, so decision 1 is sound
(T2″, T3a″) with `Δ` over `R` and the classes whose stored linearization meets `R`. The scenarios
check the PoC's literal `Δ` domain (`R ∪ inheritance.reverse*(R)`) and the header rule as a
policy instead of keys, and show what breaks without it or with a non-transitive one.
-/

namespace Zinc.Flat

open Zinc.Hier (Cls Name Ty allCls)
open Zinc.Hier.Cls Zinc.Hier.Name

instance : Fintype Cls := ⟨allCls, by intro x; cases x <;> decide⟩

structure Mem where
  ty : Ty
  deferred : Bool := false
  deriving DecidableEq, Repr

/-- What a definition is. Traits get no forwarders; a class or object gets mixin forwarders for
the traits it mixes in, and a top-level object (no companion) gets a mirror class of static
forwarders. -/
inductive CKind | cls | trt | obj
  deriving DecidableEq, Repr

structure Decl where
  parents : List (Cls × Ty) := []
  decls : List (Name × Mem) := []
  /-- An abstract class or trait need not implement its deferred members. -/
  abstract : Bool := false
  kind : CKind := .cls
  final : Bool := false
  deriving DecidableEq, Repr

/-- Proper ancestors, most derived first, with type arguments as seen from the class. -/
abbrev Lin := List (Cls × Ty)

structure Src where
  decl : Decl
  body : List (Cls × Name) := []
  deriving DecidableEq, Repr

/-- The interface stores the declaration and the linearization computed when it was compiled. -/
@[ext] structure Iface where
  decl : Decl
  lin : Lin := []
  deriving DecidableEq, Repr

/-- A refchecks verdict. Errors stand in for everything a descendant's own compilation derives
from its ancestors (also bridges and forwarders in a legal program). -/
inductive Err
  | override (n : Name)
  | conflict (n : Name)
  | abstract (n : Name)
  /-- A parent is `final`. -/
  | final (p : Cls)
  deriving DecidableEq, Repr

structure Out where
  iface : Iface
  errs : List Err
  /-- The resolved type of each selection, and the receiver's kind: `invokeinterface` for a
  trait, `invokevirtual` for a class. -/
  descs : List (CKind × Option Ty)
  /-- Mixin forwarders: a concrete trait member that the class's linearization resolves to, for
  a trait it mixes in (one not already in its superclass's linearization), as seen from it. -/
  fwds : List (Name × Ty) := []
  /-- Static forwarders of an object's mirror class: every member, resolved, as seen from it. -/
  statics : List (Name × Ty) := []
  deriving DecidableEq, Repr

def own (i : Iface) (n : Name) : Option Mem := i.decl.decls.lookup n

/-- The flattened composition: `own_C(n)`, then each ancestor of the stored linearization that
declares `n`, with its type argument as seen from `c`. -/
def flatOf (I : Cls → Iface) (c : Cls) (n : Name) : List (Cls × Ty × Mem) :=
  ((c, Ty.param) :: (I c).lin).filterMap fun e => (own (I e.1) n).map fun m => (e.1, e.2, m)

/-- Lookup along the stored linearization: the first declaration, as seen from `c`. -/
def lookupFlat (l : List (Cls × Ty × Mem)) : Option Ty :=
  l.head?.map fun e => Ty.subst e.2.1 e.2.2.ty

/-! ## Queries -/

inductive Q
  | parents
  /-- Select member `n` of the addressed class: a lookup along its stored linearization. -/
  | member (n : Name)
  /-- Refchecks, override conformance: the addressed ancestor's own member `n`. -/
  | ovr (n : Name)
  /-- Refchecks, conflicts: does the addressed ancestor declare `n`? -/
  | has (n : Name)
  /-- Refchecks, conflicts: the own member `n` of an ancestor in a cross-parent pair. -/
  | cfl (n : Name)
  /-- Refchecks, abstract members: is the addressed ancestor's `n` deferred, if declared? -/
  | dfr (n : Name)
  /-- The rest of the header: kind and finality (final parents, which ancestors are traits). -/
  | hdr
  /-- Mixin forwarders: the declarations of a trait the class mixes in. -/
  | fwd
  /-- Mixin forwarders: does an ancestor ahead of the trait declare `n` (and so win)? -/
  | fhas (n : Name)
  /-- Static forwarders: the declarations of an ancestor of an object. -/
  | mirror
  deriving DecidableEq, Repr

inductive AnsV
  | ps (l : List (Cls × Ty))
  | ty (t : Option Ty)
  | sel (k : CKind) (t : Option Ty)
  | mem (m : Option Mem)
  | b (x : Bool)
  | ob (x : Option Bool)
  | hd (k : CKind) (f : Bool)
  | ds (l : List (Name × Mem))
  deriving DecidableEq, Repr

def answer (I : Cls → Iface) : Cls × Q → AnsV
  | (c, .parents) => .ps (I c).decl.parents
  | (c, .member n) => .sel (I c).decl.kind (lookupFlat (flatOf I c n))
  | (c, .ovr n) => .mem (own (I c) n)
  | (c, .cfl n) => .mem (own (I c) n)
  | (c, .has n) => .b (own (I c) n).isSome
  | (c, .dfr n) => .ob ((own (I c) n).map (·.deferred))
  | (c, .hdr) => .hd (I c).decl.kind (I c).decl.final
  | (c, .fwd) => .ds (I c).decl.decls
  | (c, .fhas n) => .b (own (I c) n).isSome
  | (c, .mirror) => .ds (I c).decl.decls

abbrev T := Task (Cls × Q) (fun _ => AnsV)

def askQ (c : Cls) (q : Q) : T AnsV := Task.ask (c, q) Task.pure

@[simp] theorem run_askQ (c : Cls) (q : Q) (e : Task.Env (Cls × Q) (fun _ => AnsV)) :
    (askQ c q).run e = e (c, q) := rfl
@[simp] theorem trace_askQ (c : Cls) (q : Q) (e : Task.Env (Cls × Q) (fun _ => AnsV)) :
    (askQ c q).trace e = [(c, q)] := rfl

/-! ## Linearization -/

/-- Scala's rule: `L(C) = C, L(Pₙ) ⃗+ … ⃗+ L(P₁)`, where elements of the right operand win. -/
def merge (ls : List Lin) : Lin :=
  ls.foldl (fun acc l => l.filter (fun e => !acc.any (·.1 == e.1)) ++ acc) []

/-- The linearization of each parent, the parent included, as seen from the child. -/
def parentLins (r : Cls → T Lin) : List (Cls × Ty) → T (List Lin)
  | [] => pure []
  | (p, a) :: rest => do
    let l ← r p
    let ls ← parentLins r rest
    pure (((p, a) :: l.map fun e => (e.1, Ty.subst a e.2)) :: ls)

/-- Proper ancestors of `c` in linearization order, asking each for its parents. -/
def ancestors : ℕ → Cls → T Lin
  | 0, _ => pure []
  | fuel + 1, c => do
    match ← askQ c .parents with
    | .ps ps => do
      let ls ← parentLins (ancestors fuel) ps
      pure (merge ls)
    | _ => pure []

def depth : ℕ := 6

/-! ## Per-unit task -/

def selects : List (Cls × Name) → T (List (CKind × Option Ty))
  | [] => pure []
  | (c, n) :: rest => do
    let r ← askQ c (.member n)
    let ts ← selects rest
    pure ((match r with | .sel k t => (k, t) | _ => (.cls, none)) :: ts)

/-! ## Refchecks

A class's own compilation reads its ancestors (talk §10a, "When a descendant must recompile
anyway"). Each check is a query to the ancestor, recorded like a client's. -/

def names : List Name := [m, g]

/-- Override conformance: each own member against every ancestor's member of that name. -/
def checkOverrides (ds : List (Name × Mem)) (L : Lin) : T (List Err) := do
  let mut errs := []
  for (n, mm) in ds do
    for (p, a) in L do
      match ← askQ p (.ovr n) with
      | .mem (some m') => if Ty.subst a m'.ty != mm.ty then errs := errs ++ [Err.override n]
      | _ => pure ()
  pure errs

/-- Both in the linearization of one parent: the pair was checked when that parent compiled
(scalac's `OverridingPairs` skips it). -/
def sameSide (pls : List Lin) (q₁ q₂ : Cls) : Bool :=
  pls.any fun l => l.any (·.1 == q₁) && l.any (·.1 == q₂)

/-- Inherited-member reconciliation: for a name the class does not declare, find the ancestors
declaring it; for pairs coming through different parents, two concrete members conflict, and
the types (as seen from the class) must agree. -/
def checkConflicts (d : Decl) (pls : List Lin) (L : Lin) : T (List Err) := do
  let mut errs := []
  for n in names do
    if (d.decls.lookup n).isNone then
      let mut decl : Lin := []
      for (q, a) in L do
        if (← askQ q (.has n)) == .b true then decl := decl ++ [(q, a)]
      let cross := decl.filter fun e₁ => decl.any fun e₂ => e₁.1 != e₂.1 && !sameSide pls e₁.1 e₂.1
      let mut ms : List (Cls × Ty × Bool) := []
      for (q, a) in cross do
        match ← askQ q (.cfl n) with
        | .mem (some mm) => ms := ms ++ [(q, Ty.subst a mm.ty, mm.deferred)]
        | _ => pure ()
      let bad := ms.any fun e₁ => ms.any fun e₂ =>
        e₁.1 != e₂.1 && !sameSide pls e₁.1 e₂.1 && ((!e₁.2.2 && !e₂.2.2) || e₁.2.1 != e₂.2.1)
      if bad then errs := errs ++ [Err.conflict n]
  pure errs

/-- A concrete class must not be left with only deferred members of a name. A deferred
declaration in `q` overrides a concrete one in an ancestor of `q` (scalac: in
`abstract class A extends M { def m: Int }`, `A.m` hides `M.m`), while a concrete member through
another path implements it. So `n` is implemented iff some concrete declaration is not an
ancestor of a deferred one. -/
def checkAbstract (d : Decl) (L : Lin) : T (List Err) := do
  if d.abstract then return []
  let mut errs := []
  for n in names do
    match d.decls.lookup n with
    | some mm => if mm.deferred then errs := errs ++ [Err.abstract n]
    | none =>
      let mut conc : List Cls := []
      let mut dfrd : List Cls := []
      for (q, _) in L do
        match ← askQ q (.dfr n) with
        | .ob (some true) => dfrd := dfrd ++ [q]
        | .ob (some false) => conc := conc ++ [q]
        | _ => pure ()
      if !dfrd.isEmpty then
        let mut hidden : List Cls := []
        for q in dfrd do
          let lq ← ancestors depth q
          hidden := hidden ++ lq.map (·.1)
        if conc.all hidden.contains then errs := errs ++ [Err.abstract n]
  pure errs

/-! ## Code generation

A class's bytecode also derives from its ancestors without naming them in its source: mixin
forwarders (scalac's `mixin` phase) and an object's mirror class (`genBCode`). Each is a query
to the ancestor, recorded like a client's. -/

/-- The kind and finality of each class of the linearization. -/
def headers : Lin → T (List (Cls × CKind × Bool))
  | [] => pure []
  | (c, _) :: rest => do
    let h ← askQ c .hdr
    let hs ← headers rest
    pure (match h with | .hd k f => (c, k, f) :: hs | _ => hs)

def isTrait (hs : List (Cls × CKind × Bool)) (c : Cls) : Bool := hs.any fun e => e.1 == c && e.2.1 == .trt

/-- A parent may not be `final`. -/
def checkFinal (d : Decl) (hs : List (Cls × CKind × Bool)) : List Err :=
  d.parents.filterMap fun (p, _) => if hs.any (fun e => e.1 == p && e.2.2) then some (Err.final p) else none

/-- The first ancestor that declares `n`. -/
def firstDecl (n : Name) : Lin → T (Option Cls)
  | [] => pure none
  | (q, _) :: rest => do
    if (← askQ q (.fhas n)) == .b true then pure (some q) else firstDecl n rest

/-- The traits mixed in here: those not in the superclass's linearization. The superclass is
the first parent, unless that is a trait. -/
def mixins (d : Decl) (pls : List Lin) (L : Lin) (hs : List (Cls × CKind × Bool)) : Lin :=
  let sup : List Cls := match d.parents, pls with
    | (p, _) :: _, l :: _ => if isTrait hs p then [] else l.map (·.1)
    | _, _ => []
  L.filter fun e => isTrait hs e.1 && !sup.contains e.1

def mixinFwds (d : Decl) (pls : List Lin) (L : Lin) (hs : List (Cls × CKind × Bool)) :
    T (List (Name × Ty)) := do
  if d.kind == .trt then return []
  let mut fs := []
  for (t, a) in mixins d pls L hs do
    match ← askQ t .fwd with
    | .ds ds =>
      for (n, mm) in ds do
        if !mm.deferred && (d.decls.lookup n).isNone then
          if (← firstDecl n L) == some t then fs := fs ++ [(n, Ty.subst a mm.ty)]
    | _ => pure ()
  pure fs

def staticFwds (d : Decl) (L : Lin) : T (List (Name × Ty)) := do
  if d.kind != .obj then return []
  let mut seen : List (Cls × Ty × List (Name × Mem)) := []
  for (q, a) in L do
    match ← askQ q .mirror with
    | .ds ds => seen := seen ++ [(q, a, ds)]
    | _ => pure ()
  pure <| names.filterMap fun n =>
    match d.decls.lookup n with
    | some mm => some (n, mm.ty)
    | none => (seen.findSome? fun (_, a, ds) => (ds.lookup n).map fun mm => (n, Ty.subst a mm.ty))

def unitF (s : Src) : T Out := do
  let pls ← parentLins (ancestors depth) s.decl.parents
  let L := merge pls
  let hs ← headers L
  let e₁ ← checkOverrides s.decl.decls L
  let e₂ ← checkConflicts s.decl pls L
  let e₃ ← checkAbstract s.decl L
  let ts ← selects s.body
  let fs ← mixinFwds s.decl pls L hs
  let ss ← staticFwds s.decl L
  pure ⟨⟨s.decl, L⟩, checkFinal s.decl hs ++ e₁ ++ e₂ ++ e₃, ts, fs, ss⟩

/-! ## Keys and hashes -/

inductive K
  | name (n : Name)
  /-- The header: parents, kind, finality. -/
  | parents
  /-- The ancestor's own member `n`: Zinc's decls-only name hash. -/
  | own (n : Name)
  /-- Whether the ancestor declares `n`. -/
  | has (n : Name)
  /-- Whether the ancestor declares `n`, and if so whether deferred. -/
  | dfr (n : Name)
  /-- The ancestor's declarations: a trait's for forwarders, any ancestor's for a mirror. -/
  | decls
  deriving DecidableEq, Repr

inductive H
  | flat (k : CKind) (l : List (Cls × Ty × Mem))
  | ps (k : CKind) (f : Bool) (l : List (Cls × Ty))
  | ds (l : List (Name × Mem))
  | own (m : Option Mem)
  | has (b : Bool)
  | dfr (o : Option Bool)
  deriving DecidableEq, Repr

def π (I : Cls → Iface) (c : Cls) : K → H
  | .name n => .flat (I c).decl.kind (flatOf I c n)
  | .parents => .ps (I c).decl.kind (I c).decl.final (I c).decl.parents
  | .decls => .ds (I c).decl.decls
  | .own n => .own (own (I c) n)
  | .has n => .has (own (I c) n).isSome
  | .dfr n => .dfr ((own (I c) n).map (·.deferred))

/-- The key covering a query. -/
def keyOf : Q → K
  | .parents => .parents
  | .member n => .name n
  | .ovr n => .own n
  | .cfl n => .own n
  | .has n => .has n
  | .dfr n => .dfr n
  | .hdr => .parents
  | .fwd => .decls
  | .fhas n => .has n
  | .mirror => .decls

/-- Which rule of the PoC's table a recorded key stands for. -/
inductive Kind | client | uses | header | overrides | conflicts | abstract | «trait» | mirror
  deriving DecidableEq, Repr

def kindOf (d : Cls) : Cls × Q → Kind
  | (_, .parents) => .header
  | (c, .member _) => if c = d then .uses else .client
  | (_, .ovr _) => .overrides
  | (_, .has _) => .conflicts
  | (_, .cfl _) => .conflicts
  | (_, .dfr _) => .abstract
  | (_, .hdr) => .header
  | (_, .fwd) => .trait
  | (_, .fhas _) => .trait
  | (_, .mirror) => .mirror

/-- The extractor, recording the keys of the enabled kinds only. -/
def keys (E : Kind → Bool) (d : Cls) (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.filterMap fun q => if E (kindOf d q) then some (q.1, keyOf q.2) else none).toFinset

def hashDeps (I : Cls → Iface) (c : Cls) : Finset Cls :=
  insert c ((I c).lin.map (·.1)).toFinset

/-! ## Joint compilation -/

/-- The interfaces of a group: linearizations need only the group's source declarations. -/
def matIface (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface) (u : Cls) : Iface :=
  ⟨(src u).decl, merge ((parentLins (ancestors depth) (src u).decl.parents).run
    (answer fun v => if v ∈ G then ⟨(src v).decl, []⟩ else I v))⟩

def group (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface) (u : Cls) : Out :=
  (unitF (src u)).run (answer fun v => if v ∈ G then matIface G src I v else I v)

def Fl (E : Kind → Bool) : NCompiler Cls Src Out Iface K H Q (fun _ => AnsV) where
  unit := unitF
  group := group
  iface := Out.iface
  answer := answer
  π := π
  hashDeps := hashDeps
  keys := keys E
  covers := fun _ q k => k = (q.1, keyOf q.2)

def full : Kind → Bool := fun _ => true

/-! ## Obligations -/

theorem trace_parentLins (r : Cls → T Lin) (e : Task.Env (Cls × Q) (fun _ => AnsV))
    (hr : ∀ p q, q ∈ (r p).trace e → q.2 = .parents) :
    ∀ ps q, q ∈ (parentLins r ps).trace e → q.2 = .parents := by
  intro ps
  induction ps with
  | nil => intro q hq; simp [parentLins] at hq
  | cons p rest ih =>
    intro q hq
    obtain ⟨c, a⟩ := p
    simp only [parentLins, Task.bind_eq, Task.pure_eq, Task.trace_bind, Task.trace_pure,
      List.append_nil, List.mem_append] at hq
    rcases hq with hq | hq
    · exact hr c q hq
    · exact ih q hq

theorem trace_ancestors (e : Task.Env (Cls × Q) (fun _ => AnsV)) :
    ∀ fuel c q, q ∈ (ancestors fuel c).trace e → q.2 = .parents := by
  intro fuel
  induction fuel with
  | zero => intro c q hq; simp [ancestors] at hq
  | succ fuel ih =>
    intro c q hq
    simp only [ancestors, Task.bind_eq, Task.trace_bind, trace_askQ, List.singleton_append,
      List.mem_cons] at hq
    rcases hq with rfl | hq
    · rfl
    · split at hq
      · simp only [Task.pure_eq, Task.trace_bind, Task.trace_pure,
          List.append_nil] at hq
        exact trace_parentLins _ e (fun p q hq => ih p q hq) _ q hq
      · simp at hq

/-- Two interface maps with the same parents lists give the same linearizations. -/
theorem parentLins_congr (I I' : Cls → Iface) (h : ∀ c, (I c).decl.parents = (I' c).decl.parents)
    (ps : List (Cls × Ty)) :
    (parentLins (ancestors depth) ps).run (answer I) =
      (parentLins (ancestors depth) ps).run (answer I') := by
  apply Task.run_congr
  intro q hq
  have := trace_parentLins _ _ (fun p q hq => trace_ancestors _ _ p q hq) ps q hq
  obtain ⟨c, q⟩ := q
  simp only at this
  subst this
  simp [answer, h c]

theorem iface_unitF (s : Src) (e : Task.Env (Cls × Q) (fun _ => AnsV)) :
    ((unitF s).run e).iface = ⟨s.decl, merge ((parentLins (ancestors depth) s.decl.parents).run e)⟩ := by
  simp [unitF]

theorem group_iface (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface) (u : Cls) :
    (group G src I u).iface = matIface G src I u := by
  simp only [group, iface_unitF, matIface]
  congr 2
  apply parentLins_congr
  intro c
  by_cases hc : c ∈ G <;> simp [hc]

theorem Fl_comp (E : Kind → Bool) : ∀ (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface), ∀ d ∈ G,
    (Fl E).group G src I d = ((Fl E).unit (src d)).run
      ((Fl E).answer (NCompiler.override I G ((Fl E).iface ∘ (Fl E).group G src I))) := by
  intro G src I d _
  show group G src I d = (unitF (src d)).run (answer (NCompiler.override I G (Out.iface ∘ group G src I)))
  conv_lhs => unfold group
  congr 2
  funext v
  simp only [NCompiler.override, Function.comp]
  split
  · rw [group_iface]
  · rfl

theorem flatOf_congr (I I' : Cls → Iface) (c : Cls) (n : Name)
    (h : ∀ d ∈ hashDeps I c, I d = I' d) : flatOf I c n = flatOf I' c n := by
  have hc : I c = I' c := h c (Finset.mem_insert_self _ _)
  unfold flatOf
  rw [← hc]
  apply List.filterMap_congr
  intro e he
  rw [h e.1]
  simp only [hashDeps, Finset.mem_insert, List.mem_toFinset, List.mem_map]
  rcases List.mem_cons.1 he with rfl | he
  · exact Or.inl rfl
  · exact Or.inr ⟨e, he, rfl⟩

theorem Fl_obligations : (Fl full).Obligations where
  comp := Fl_comp full
  coverage := by
    intro I d s q hq
    refine ⟨(q.1, keyOf q.2), ?_, rfl⟩
    show _ ∈ keys full d _
    simp only [keys, full, ite_true, List.mem_toFinset, List.mem_filterMap, Option.some.injEq]
    exact ⟨q, hq, rfl⟩
  abstraction := by
    intro I I' k h q hc
    refine ⟨?_, hc⟩
    change k = (q.1, keyOf q.2) at hc
    subst hc
    obtain ⟨c, q⟩ := q
    change π I c (keyOf q) = π I' c (keyOf q) at h
    cases q with
    | parents =>
      simp only [keyOf, π, H.ps.injEq] at h
      simp [Fl, answer, h]
    | member n =>
      simp only [keyOf, π, H.flat.injEq] at h
      simp [Fl, answer, h]
    | ovr n =>
      simp only [keyOf, π, H.own.injEq] at h
      simp [Fl, answer, h]
    | cfl n =>
      simp only [keyOf, π, H.own.injEq] at h
      simp [Fl, answer, h]
    | has n =>
      simp only [keyOf, π, H.has.injEq] at h
      simp [Fl, answer, h]
    | dfr n =>
      simp only [keyOf, π, H.dfr.injEq] at h
      simp [Fl, answer, h]
    | hdr =>
      simp only [keyOf, π, H.ps.injEq] at h
      simp [Fl, answer, h]
    | fwd =>
      simp only [keyOf, π, H.ds.injEq] at h
      simp [Fl, answer, h]
    | fhas n =>
      simp only [keyOf, π, H.has.injEq] at h
      simp [Fl, answer, h]
    | mirror =>
      simp only [keyOf, π, H.ds.injEq] at h
      simp [Fl, answer, h]
  locality := by
    intro I I' c h k
    have hc : I c = I' c := h c (Finset.mem_insert_self _ _)
    cases k with
    | name n => simp only [Fl, π, flatOf_congr I I' c n h, hc]
    | parents => simp only [Fl, π, hc]
    | own n => simp only [Fl, π, hc]
    | has n => simp only [Fl, π, hc]
    | dfr n => simp only [Fl, π, hc]
    | decls => simp only [Fl, π, hc]

/-- **Decision 1 is sound**: with every key kind recorded, any sound policy, and `Δ` over the
classes whose stored linearization meets the recompiled set, a terminating run leaves no class
dirty. -/
theorem flat_sound (S : Finset Cls) (src : Cls → Src) (P : Compiler.Policy Cls Out K)
    (hP : P.Sound S) (fuel n : ℕ) (R : Finset Cls) (s : Compiler.State Cls Out K)
    (D : Finset Cls) (hD : D ⊆ R) (hInv : (Fl full).Inv S src s D) (s' : Compiler.State Cls Out K)
    (h : (Fl full).zinc S src P fuel n R s = some s') : (Fl full).Inv S src s' ∅ :=
  (Fl full).zinc_sound Fl_obligations S src P hP fuel n R s D hD hInv s' h

/-! ## Runs -/

section runs
open Compiler (State Policy)

abbrev St := State Cls Out K

/-- Direct parents, as Zinc's `inheritance` relation records them. -/
def directParents (s : St) (d : Cls) : List Cls := (s.out d).iface.decl.parents.map (·.1)

/-- `R` and its direct children. -/
def children (s : St) (R : Finset Cls) : Finset Cls :=
  R ∪ Finset.univ.filter fun d => ∃ p ∈ directParents s d, p ∈ R

/-- `R` and its transitive descendants: `inheritance.reverse*`. -/
def descendants (s : St) (R : Finset Cls) : Finset Cls :=
  (List.range 7).foldl (fun D _ => children s D) R

/-- Where `Δ` is taken: the read sets of the proof, the PoC's `R ∪ inheritance.reverse*(R)` in the
new state (decision 2), or `R` alone. -/
inductive Dom | proof | zinc | stale

def domain (E : Kind → Bool) : Dom → Finset Cls → St → St → Finset Cls
  | .proof, R, s, _ => (Fl E).affected R s
  | .zinc, R, _, s' => descendants s' R
  | .stale, R, _, _ => R

structure Run where
  state : St
  rounds : ℕ
  compiled : Finset Cls

/-- The loop, with the policy applied *before* the stop test, as Zinc does with its inheritance
invalidation (`NCompiler.zinc` applies it after; for a sound policy this only stops later). -/
def all : List Cls := [A, B, M, C, X, Y, Z]

/-- Tabulate a state, so later rounds do not recompute it through the closures of earlier ones.
Extensionally the identity. -/
def memo (s : St) : St :=
  let o := all.map fun c => (c, s.out c)
  let u := all.map fun c => (c, s.U c)
  { out := fun c => match o.lookup c with | some x => x | none => s.out c
    U := fun c => match u.lookup c with | some x => x | none => s.U c }

def runF (E : Kind → Bool) (dom : Dom) (src : Cls → Src) (P : Policy Cls Out K) :
    ℕ → ℕ → Finset Cls → Finset Cls → St → Option Run
  | 0, _, _, _, _ => none
  | fuel + 1, n, acc, R, s =>
    let s' := memo ((Fl E).round src R s)
    let I := P n R s s' ((Fl E).invalidated Finset.univ (domain E dom R s s') s s')
    if I ⊆ R then some ⟨s', n + 1, acc ∪ R⟩
    else runF E dom src P fuel (n + 1) (acc ∪ R) I s'

def headerChanged (s s' : St) (p : Cls) : Bool :=
  let d := (s.out p).iface.decl
  let d' := (s'.out p).iface.decl
  d.parents != d'.parents || d.kind != d'.kind || d.final != d'.final

/-- The header rule as a policy: when a recompiled class's parents changed, recompile its
descendants, transitively or only the direct children. -/
def headerPolicy (transitive : Bool) : Policy Cls Out K := fun _ R s s' I =>
  let Hd := R.filter (headerChanged s s' · = true)
  I ∪ if transitive then descendants s' Hd else children s' Hd

def dummy : St := { out := fun _ => ⟨⟨{}, []⟩, [], [], [], []⟩, U := fun _ => ∅ }

def init (E : Kind → Bool) (src : Cls → Src) : St := memo ((Fl E).round src Finset.univ dummy)

def clean (src : Cls → Src) : Cls → Out := group Finset.univ src fun _ => ⟨{}, []⟩

structure Report where
  recompiled : List Cls
  rounds : ℕ
  clean : Bool
  deriving Repr, DecidableEq

def report (E : Kind → Bool) (dom : Dom) (P : Policy Cls Out K) (src₀ src₁ : Cls → Src)
    (R₀ : Finset Cls) : Option Report :=
  (runF E dom src₁ P 9 0 ∅ R₀ (init E src₀)).map fun r =>
    { recompiled := all.filter fun c => c ∈ r.compiled ∧ c ∉ R₀
      rounds := r.rounds
      clean := let cl := memo { out := clean src₁, U := fun _ => ∅ }
        all.all fun c => r.state.out c == cl.out c }

end runs

/-! ## Scenarios -/

def int : Mem := { ty := .int }
def str : Mem := { ty := .string }
def par : Mem := { ty := .param }
def intD : Mem := { ty := .int, deferred := true }

/-- §10a: `A[T] { m: Int; g: Int }`, `B extends A[Int]`, `C extends B with M`; clients
`X (B.m)`, `Y (C.m)`, `Z (B.g)`. -/
def base : Cls → Src
  | A => { decl := { decls := [(m, int), (g, int)], abstract := true } }
  | B => { decl := { parents := [(A, .int)] } }
  | M => { decl := { abstract := true, kind := .trt } }
  | C => { decl := { parents := [(B, .int), (M, .int)] } }
  | X => { decl := { kind := .obj }, body := [(B, m)] }
  | Y => { decl := { kind := .obj }, body := [(C, m)] }
  | Z => { decl := { kind := .obj }, body := [(B, g)] }

/-- Edit 1: `A.m: Int → String`. -/
def edit1 : Cls → Src
  | A => { decl := { decls := [(m, str), (g, int)], abstract := true } }
  | c => base c

/-- Edit 2 base: `A.m: T`. -/
def base2 : Cls → Src
  | A => { decl := { decls := [(m, par), (g, int)], abstract := true } }
  | c => base c

/-- Edit 2: `B extends A[Int]` → `A[String]`, a header change. -/
def edit2 : Cls → Src
  | B => { decl := { parents := [(A, .string)] } }
  | c => base2 c

/-- Edit 3: the mixin `M` gains `m`. -/
def edit3 : Cls → Src
  | M => { decl := { decls := [(m, str)], abstract := true, kind := .trt } }
  | c => base c

/-- Edit 4 base: a header change two levels up. `M[T] { g: T }`, `A extends M[Int]`,
`B extends A[Int]`, `C extends B`; clients `X (B.g)`, `Y (C.g)`, `Z (B.m)`. -/
def base4 : Cls → Src
  | M => { decl := { decls := [(g, par)], abstract := true, kind := .trt } }
  | A => { decl := { parents := [(M, .int)], decls := [(m, int)], abstract := true } }
  | B => { decl := { parents := [(A, .int)] } }
  | C => { decl := { parents := [(B, .int)] } }
  | X => { decl := { kind := .obj }, body := [(B, g)] }
  | Y => { decl := { kind := .obj }, body := [(C, g)] }
  | Z => { decl := { kind := .obj }, body := [(B, m)] }

/-- Edit 4: `A extends M[Int]` → `M[String]`. `B`'s and `C`'s stored linearizations now say
`M[Int]`. -/
def edit4 : Cls → Src
  | A => { decl := { parents := [(M, .string)], decls := [(m, int)], abstract := true } }
  | c => base4 c

def noHeader : Kind → Bool
  | .header => false
  | _ => true

def plain : Compiler.Policy Cls Out K := Compiler.Policy.plain

/-! ### Decision 1, with header keys

Edit 1 is as for the recursive Merkle design (`Hier.Mk`); Edit 3 also recompiles `C`, whose
conflict check sees the new `M.m` (below). A header change (Edits 2
and 4) costs a round more: in the round that recompiles `B` (or `A`), `Δ` recomputes the
descendants' hashes over their *stale* linearizations, so their clients only move once the
header keys have recompiled the descendants. The PoC's `Δ` domain gives the same runs as the
proof's. -/

example : report full .proof plain base edit1 {A} = some ⟨[X, Y], 2, true⟩ := by native_decide
example : report full .zinc plain base edit1 {A} = some ⟨[X, Y], 2, true⟩ := by native_decide
example : report full .proof plain base2 edit2 {B} = some ⟨[C, X, Y, Z], 3, true⟩ := by native_decide
example : report full .zinc plain base2 edit2 {B} = some ⟨[C, X, Y, Z], 3, true⟩ := by native_decide
example : report full .proof plain base edit3 {M} = some ⟨[C, Y], 2, true⟩ := by native_decide
example : report full .zinc plain base edit3 {M} = some ⟨[C, Y], 2, true⟩ := by native_decide
example : report full .proof plain base4 edit4 {A} = some ⟨[B, C, X, Y], 3, true⟩ := by native_decide
example : report full .zinc plain base4 edit4 {A} = some ⟨[B, C, X, Y], 3, true⟩ := by native_decide

/-- Decision 2 still matters: `Δ` over the recompiled set alone undercompiles (T2-stale). -/
example : report full .stale plain base edit1 {A} = some ⟨[], 1, false⟩ := by native_decide

/-! ### The header rule as a policy

Drop the header keys and enforce the rule as a policy instead. Transitive (all of
`inheritance.reverse*`) gives the same runs as the keys. Without it, or with direct children
only, the stored linearization of a grandchild stays stale: in Edit 4, `C` still says `M[Int]`
and so does its client `Y`. -/

example : report noHeader .zinc plain base4 edit4 {A} = some ⟨[], 1, false⟩ := by native_decide
example : report noHeader .zinc (headerPolicy true) base4 edit4 {A} =
    some ⟨[B, C, X, Y], 3, true⟩ := by native_decide
example : report noHeader .zinc (headerPolicy false) base4 edit4 {A} =
    some ⟨[B, X], 3, false⟩ := by native_decide
example : report noHeader .zinc plain base2 edit2 {B} = some ⟨[X, Z], 2, false⟩ := by native_decide
example : report noHeader .zinc (headerPolicy true) base2 edit2 {B} =
    some ⟨[C, X, Y, Z], 3, true⟩ := by native_decide

/-! ### Descendants' own checks (talk §10a, "When a descendant must recompile anyway")

The refchecks keys make the inheritance edge name-filtered, and T2″ covers it. Edit 1 recompiles
no descendant (above). Each check's edit recompiles the descendant that runs it, and no other: -/

/-- `B` overrides `m`. -/
def baseO : Cls → Src
  | B => { decl := { parents := [(A, .int)], decls := [(m, int)] } }
  | c => base c

/-- Override: `A.m: Int → String`; `B.m: Int` no longer conforms. `C` inherits `m` from `B` and
`A`, through one parent, so it does not recheck the pair. -/
def editO : Cls → Src
  | A => (edit1 A)
  | c => baseO c

example : report full .zinc plain baseO editO {A} = some ⟨[B, X, Y], 2, true⟩ := by native_decide

/-- `trait M { def m: Int }`; `A.m` implements it in `C`. -/
def baseC : Cls → Src
  | M => { decl := { decls := [(m, intD)], abstract := true, kind := .trt } }
  | c => base c

/-- Conflict through two parents: `A.m: Int → String` no longer matches `M.m: Int` in `C`. `B`
sees only `A.m`. -/
def editC : Cls → Src
  | A => edit1 A
  | c => baseC c

example : report full .zinc plain baseC editC {A} = some ⟨[C, X, Y], 2, true⟩ := by native_decide

/-- Abstract: `A.m` becomes deferred; the concrete `B` and `C` must implement it. -/
def editA : Cls → Src
  | A => { decl := { decls := [(m, intD), (g, int)], abstract := true } }
  | c => base c

example : report full .zinc plain base editA {A} = some ⟨[B, C, X, Y], 2, true⟩ := by native_decide

/-- `B` selects its own inherited `m` (`this.m`). -/
def baseU : Cls → Src
  | B => { decl := { parents := [(A, .int)] }, body := [(B, m)] }
  | c => base c

def editU : Cls → Src
  | A => edit1 A
  | c => baseU c

example : report full .zinc plain baseU editU {A} = some ⟨[B, X, Y], 2, true⟩ := by native_decide

/-! ### Ablation: every key kind is needed

Dropping one kind of key leaves a scenario unclean. (Dropping `client` keys is T2-stale's
cousin: nothing reaches `X` and `Y`.) -/

def without (k : Kind) : Kind → Bool := fun k' => k' != k

example : report (without .client) .zinc plain base edit1 {A} = some ⟨[], 1, false⟩ := by native_decide
example : report (without .uses) .zinc plain baseU editU {A} = some ⟨[X, Y], 2, false⟩ := by
  native_decide
example : report (without .header) .zinc plain base4 edit4 {A} = some ⟨[], 1, false⟩ := by
  native_decide
example : report (without .overrides) .zinc plain baseO editO {A} = some ⟨[X, Y], 2, false⟩ := by
  native_decide
/-- Edit 3's new `M.m` is also seen by the concrete `C`'s abstract check, which asks every
ancestor whether it declares `m`; the conflict keys are needed for a type mismatch. -/
example : report (without .conflicts) .zinc plain base edit3 {M} = some ⟨[C, Y], 2, true⟩ := by
  native_decide
example : report (without .conflicts) .zinc plain baseC editC {A} = some ⟨[X, Y], 2, false⟩ := by
  native_decide
example : report (without .abstract) .zinc plain base editA {A} = some ⟨[X, Y], 2, false⟩ := by
  native_decide

/-! ### Codegen: forwarders and `final`

`trait M[T] { def g: Int = … }` is mixed into `C`, which gets a forwarder for `g`; the object
`X extends C[Int]` gets a static forwarder for it in its mirror class. Nobody selects `g`. -/

def baseF : Cls → Src
  | A => { decl := { decls := [(m, int)], abstract := true } }
  | B => { decl := { parents := [(A, .int)] } }
  | M => { decl := { decls := [(g, int)], abstract := true, kind := .trt } }
  | C => { decl := { parents := [(B, .int), (M, .int)] } }
  | X => { decl := { kind := .obj, parents := [(C, .int)] } }
  | Y => { decl := { kind := .obj }, body := [(C, m)] }
  | Z => { decl := { kind := .obj } }

/-- `M.g: Int → String`: both forwarders change, and no presence or client key sees it. -/
def editF : Cls → Src
  | M => { decl := { decls := [(g, str)], abstract := true, kind := .trt } }
  | c => baseF c

/-- `B` becomes `final`: `C` must fail. -/
def editFinal : Cls → Src
  | B => { decl := { parents := [(A, .int)], final := true } }
  | c => baseF c

example : report full .zinc plain baseF editF {M} = some ⟨[C, X], 2, true⟩ := by native_decide
example : report (without .trait) .zinc plain baseF editF {M} = some ⟨[X], 2, false⟩ := by
  native_decide
example : report (without .mirror) .zinc plain baseF editF {M} = some ⟨[C], 2, false⟩ := by
  native_decide
example : report full .zinc plain baseF editFinal {B} = some ⟨[C, X], 2, true⟩ := by native_decide
example : report (without .header) .zinc plain baseF editFinal {B} = some ⟨[], 1, false⟩ := by
  native_decide

end Zinc.Flat
