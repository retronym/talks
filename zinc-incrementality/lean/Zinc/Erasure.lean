import Zinc.NonLocalAns
import Zinc.Termination

/-!
# Erasure through inheritance: as seen from, as declared, and an erasure witness

How should `ExtractAPI` render an inherited member? The Scala 2 bridge renders it *as seen from*
the inheriting class (`memberInfo`); Scala 3 renders it *as declared* in its owner (`sym.info`)
and keeps the type arguments only in `parents` (talk §7). This file compares the two, and a third
rendering that adds an *erasure witness* (the owner-side erased descriptor) to the declared one,
on a language where a descendant's bytecode depends on the erasure of its ancestors' members:

* **bridges**: a member `d` declares that overrides an ancestor's member gets a bridge for each
  overridden member whose erased descriptor differs from its own;
* **forwarders**: a class with `fwd` set (a mixin forwarder for a trait parent, or a static
  forwarder in a mirror class) emits one for each inherited member, with that member's erasure;
* **value classes** referenced by name: `vc` erases to the erasure of `V`'s underlying type.

Erasure is a function of the member's signature *as declared in its owner*: `M[T].m: T` erases to
`Object` whatever `T` is instantiated to in a subclass.

Interfaces are source-determined (`Iface := Decl`); the materialised rendering of a class is a
non-local hash over its ancestor chain, recomputed over `affected` (T2″). That stands for "the
class's API was refreshed when its ancestors changed" without modelling the hierarchy recompiles
(`Hier.lean` shows the two are interchangeable).

Keys, as Zinc records them:

* a descendant `d` with direct parent `p` records one inheritance key `(p, inh)` for everything its
  own compilation reads from its ancestors (the external `inheritance` edge on the direct parent:
  across subprojects there is nothing else);
* a client selecting `c.n` records `(c, name n)` and `(c, cls)`, the class-name key, whose hash
  covers `c`'s parents (use-site expansion: the client computes the type as seen from `c`);
* a macro observing `c.n` (its type as seen from `c`) records `(c, name n)`, and `(c, cls)` only
  if the macro's reads are recorded faithfully (`safe`);
* erasing an own member of type `vc` records `(V, und)`, the name `V` whose hash covers the
  underlying type (talk §15b);
* erasing an *inherited* member of type `vc` is folded into the inheritance key on the parent, as
  Zinc does today, or, with `vEdge`, recorded as `(V, und)` too (`Ext`).

Three renderings, i.e. three hash functions over the same keys (`Rend`):

* `asf`: `(c, name n)` is the type of `n` as seen from `c`; `(c, inh)` is `c`'s linearization with
  type arguments and every member as seen from `c` (Scala 2);
* `decl`: `(c, name n)` lists the declarations of `n` along `c`'s chain, as declared, with no
  dedup; `(c, inh)` is the parents and declarations of every class on the chain (Scala 3);
* `wit`: `decl` plus, in `(c, inh)`, the erasure of `V` when some declaration on the chain
  mentions `vc` (the erasure witness).

Results (checked below; counts from `lake exe exhaustive erasure`, see the end of the file):

1. `asf` undercompiles the missing bridge of `erasure-bridge-upstream-grandparent`; `decl` and `wit`
   do not. With Zinc's transitive inheritance invalidation (one subproject) `asf` is clean too.
2. `asf` hashes are functions of `decl` hashes (`asf_of_decl`): `decl` is a sound
   over-approximation, and the converse fails on the precision case (`M[T,U].m: T → m: U`).
3. The class-name key: `decl` per-name hashes do not move on a type-argument change, `(c, cls)`
   does, and that suffices for clients that record it. A macro that observes a member as seen from
   `c` without recording `(c, cls)` escapes.
4. Value classes by name: `asf` and `decl` miss a forwarder's descriptor change, `wit` does not,
   and neither does either rendering with `vEdge`. Generic erasure is a function of the owner's
   declaration, so it needs only the as-declared rendering; value-class erasure is a function of
   another class's contents, so it needs a dependency on that class. The dependency suffices: no
   member hash has to change.
5. `Er_obligations`: as declared with faithful macro keys meets `NCompiler.Obligations` if value
   classes reach descendants through the witness or through `vEdge` (`wit_obligations`,
   `vEdge_obligations`), so both are sound by T3a″.

`Flat.lean` reaches the value-class result independently, inside the Merkle PoC's model: its
`erasure` keys (codegen's reads of `V`, kind `.erasure`) are the `vEdge` here, and dropping them
leaves the same forwarder cases unclean. This file asks the question one level up: which
*rendering* of an inherited member is sound for descendants, and whether erasure needs a hash
change at all.
-/

namespace Zinc.Erasure

inductive Cls | V | M | A | B | X | Y
  deriving DecidableEq, Repr

def allCls : List Cls := [.V, .M, .A, .B, .X, .Y]

instance : Fintype Cls := ⟨allCls.toFinset, by intro x; cases x <;> decide⟩

inductive Name | m | g
  deriving DecidableEq, Repr

def names : List Name := [.m, .g]

/-- Types: two type parameters, three base types, and the value class `V` by name. -/
inductive Ty | int | long | str | p0 | p1 | vc
  deriving DecidableEq, Repr

/-- `asSeenFrom`: instantiate the enclosing class's parameters. -/
def Ty.subst (args : List Ty) : Ty → Ty
  | .p0 => args.getD 0 .p0
  | .p1 => args.getD 1 .p1
  | t => t

def ids : List Ty := [.p0, .p1]

/-- JVM descriptors. -/
inductive JTy | I | J | Str | Obj
  deriving DecidableEq, Repr

def eraseBase : Ty → JTy
  | .int => .I
  | .long => .J
  | .str => .Str
  | _ => .Obj

/-- The erasure of `V`: its underlying type's. -/
def eraseV (und : Option Ty) : JTy := (und.map eraseBase).getD .Obj

structure Decl where
  parent : Option (Cls × List Ty) := none
  decls : List (Name × Ty) := []
  /-- A value class's underlying type. -/
  und : Option Ty := none
  /-- Emits a forwarder for every inherited member (mixin forwarders, or a mirror class). -/
  fwd : Bool := false
  deriving DecidableEq, Repr

abbrev Iface := Decl

structure Src where
  decl : Decl
  /-- Member selections `c.n`. -/
  sel : List (Cls × Name) := []
  /-- Macro observations of `c.n`'s type as seen from `c`. -/
  obs : List (Cls × Name) := []
  deriving DecidableEq, Repr

structure Out where
  iface : Iface
  /-- Erasures of own members. -/
  own : List JTy
  /-- Override conformance errors. -/
  errs : List Name
  /-- Bridge descriptors per own member. -/
  bridges : List (Name × List JTy)
  /-- Forwarder descriptors per inherited member. -/
  fwds : List (Name × JTy)
  /-- Types of selections, as seen from the receiver. -/
  descs : List (Option Ty)
  /-- What each macro observation saw. -/
  seen : List (Option Ty)
  deriving DecidableEq, Repr

/-! ## Queries

A query names the class it reads and *why*: the context says which tree the compiler was
typing. The extractor maps each query to a key by its context, which is how the bridge knows
whether a read belongs to a client's selection or to a descendant's own checks. -/

inductive Ctx
  /-- A descendant reading its ancestors through its direct parent `p`. -/
  | inh (p : Cls)
  /-- A client selecting through `c`. -/
  | sel (c : Cls)
  /-- A macro observing `c.n`. -/
  | obs (c : Cls) (n : Name)
  /-- Erasing an own member. -/
  | own
  deriving DecidableEq, Repr

inductive Q
  | parent (x : Ctx)
  | decl (x : Ctx) (n : Name)
  /-- The erasure of the value class (addressed to `V`). -/
  | und (x : Ctx)
  deriving DecidableEq, Repr

inductive AnsV
  | par (p : Option (Cls × List Ty))
  | ty (t : Option Ty)
  | j (x : JTy)
  deriving DecidableEq, Repr

/-- Every answer reads the interface of the class it is addressed to. -/
def answer (I : Cls → Iface) : Cls × Q → AnsV
  | (c, .parent _) => .par (I c).parent
  | (c, .decl _ n) => .ty ((I c).decls.lookup n)
  | (c, .und _) => .j (eraseV (I c).und)

abbrev T := Task (Cls × Q) (fun _ => AnsV)

def askQ (c : Cls) (q : Q) : T AnsV := Task.ask (c, q) Task.pure

@[simp] theorem run_askQ (c : Cls) (q : Q) (e : Task.Env (Cls × Q) (fun _ => AnsV)) :
    (askQ c q).run e = e (c, q) := rfl
@[simp] theorem trace_askQ (c : Cls) (q : Q) (e : Task.Env (Cls × Q) (fun _ => AnsV)) :
    (askQ c q).trace e = [(c, q)] := rfl

/-! ## The compiler -/

def depth : ℕ := 4

/-- `c` and its ancestors, each with its type arguments as seen from the start (`a` for `c`). -/
def linT (x : Ctx) : ℕ → Cls → List Ty → T (List (Cls × List Ty))
  | 0, _, _ => pure []
  | f + 1, c, a => do
    match ← askQ c (.parent x) with
    | .par (some (q, qa)) => do
      let l ← linT x f q (qa.map (Ty.subst a))
      pure ((c, a) :: l)
    | _ => pure [(c, a)]

/-- The declarations of `n` along a linearization. -/
def entriesT (x : Ctx) (n : Name) : List (Cls × List Ty) → T (List (List Ty × Option Ty))
  | [] => pure []
  | (c, a) :: rest => do
    let r ← askQ c (.decl x n)
    let l ← entriesT x n rest
    pure ((a, match r with | .ty t => t | _ => none) :: l)

/-- The first declaration, as seen from the start of the linearization. -/
def render (es : List (List Ty × Option Ty)) : Option Ty :=
  (es.filterMap fun e => e.2.map (Ty.subst e.1)).head?

/-- Erase declared types; erasing `vc` asks `V`. -/
def erasT (x : Ctx) : List Ty → T (List JTy)
  | [] => pure []
  | t :: rest => do
    let j ← if t = .vc then do
        match ← askQ .V (.und x) with
        | .j y => pure y
        | _ => pure .Obj
      else pure (eraseBase t)
    let l ← erasT x rest
    pure (j :: l)

structure PerName where
  err : Bool
  bridges : List JTy
  fwd : Option JTy

/-- A descendant's own checks and codegen for one name, against its parent `p`'s chain `L`. -/
def nameT (d : Decl) (p : Cls) (L : List (Cls × List Ty)) (ownJ : List (Name × JTy)) (n : Name) :
    T PerName := do
  let es ← entriesT (.inh p) n L
  let js ← erasT (.inh p) (es.filterMap (·.2))
  let inh := render es
  match d.decls.lookup n with
  | some t =>
    let jo := (ownJ.lookup n).getD .Obj
    pure ⟨inh.isSome && inh != some t, (js.filter (· != jo)).dedup, none⟩
  | none => pure ⟨false, [], if d.fwd then js.head? else none⟩

def namesT (d : Decl) (p : Cls) (L : List (Cls × List Ty)) (ownJ : List (Name × JTy)) :
    List Name → T (List (Name × PerName))
  | [] => pure []
  | n :: rest => do
    let r ← nameT d p L ownJ n
    let l ← namesT d p L ownJ rest
    pure ((n, r) :: l)

def descT (d : Decl) (ownJ : List (Name × JTy)) : T (List (Name × PerName)) :=
  match d.parent with
  | none => pure []
  | some (p, a) => do
    let L ← linT (.inh p) depth p a
    namesT d p L ownJ names

/-- Selections (`obs := false`) or macro observations (`obs := true`). -/
def selsT (obs : Bool) : List (Cls × Name) → T (List (Option Ty))
  | [] => pure []
  | (c, n) :: rest => do
    let x := if obs then Ctx.obs c n else Ctx.sel c
    let L ← linT x depth c ids
    let es ← entriesT x n L
    let l ← selsT obs rest
    pure (render es :: l)

def unitF (s : Src) : T Out := do
  let ownJ ← erasT .own (s.decl.decls.map (·.2))
  let r ← descT s.decl (s.decl.decls.map (·.1) |>.zip ownJ)
  let descs ← selsT false s.sel
  let seen ← selsT true s.obs
  pure ⟨s.decl, ownJ, r.filterMap (fun e => if e.2.err then some e.1 else none),
    r.filterMap (fun e => if e.2.bridges.isEmpty then none else some (e.1, e.2.bridges)),
    r.filterMap (fun e => e.2.fwd.map (e.1, ·)), descs, seen⟩

/-! ## Pure views of an interface map (what the hashes read) -/

def linP (I : Cls → Iface) : ℕ → Cls → List Ty → List (Cls × List Ty)
  | 0, _, _ => []
  | f + 1, c, a =>
    match (I c).parent with
    | some (q, qa) => (c, a) :: linP I f q (qa.map (Ty.subst a))
    | none => [(c, a)]

def chainP (I : Cls → Iface) (c : Cls) : List Cls := (linP I depth c ids).map (·.1)

def entriesP (I : Cls → Iface) (n : Name) (L : List (Cls × List Ty)) : List (List Ty × Option Ty) :=
  L.map fun e => (e.2, (I e.1).decls.lookup n)

/-- The type of `c.n` as seen from `c`. -/
def asfP (I : Cls → Iface) (c : Cls) (n : Name) : Option Ty :=
  render (entriesP I n (linP I depth c ids))

/-! ## Keys and the three renderings -/

inductive K
  | name (n : Name)
  /-- The class-name key: its hash covers the class's parents. -/
  | cls
  /-- The inheritance edge: the class's whole API. -/
  | inh
  /-- The name `V`: its hash covers the underlying type. -/
  | und
  deriving DecidableEq, Repr

inductive Rend | asf | decl | wit
  deriving DecidableEq, Repr

inductive H
  | ty (t : Option Ty)
  | ents (l : List (Cls × Option Ty))
  | chain (l : List (Cls × Option (Cls × List Ty)))
  | asfInh (lin : List (Cls × List Ty)) (ts : List (Option Ty))
  | inh (l : List (Cls × Option (Cls × List Ty) × List (Name × Ty))) (w : Option JTy)
  | j (x : JTy)
  deriving DecidableEq, Repr

/-- Parents and declarations along the chain: the as-declared API. -/
def declsP (I : Cls → Iface) (c : Cls) : List (Cls × Option (Cls × List Ty) × List (Name × Ty)) :=
  (chainP I c).map fun e => (e, (I e).parent, (I e).decls)

def mentionsVC (l : List (Cls × Option (Cls × List Ty) × List (Name × Ty))) : Bool :=
  l.any fun e => e.2.2.any (·.2 == .vc)

def π (r : Rend) (I : Cls → Iface) (c : Cls) : K → H
  | .name n => match r with
    | .asf => .ty (asfP I c n)
    | _ => .ents ((chainP I c).map fun e => (e, (I e).decls.lookup n))
  | .cls => .chain ((chainP I c).map fun e => (e, (I e).parent))
  | .inh => match r with
    | .asf => .asfInh (linP I depth c ids) (names.map (asfP I c))
    | .decl => .inh (declsP I c) none
    | .wit => .inh (declsP I c) (if mentionsVC (declsP I c) then some (eraseV (I .V).und) else none)
  | .und => .j (eraseV (I c).und)

/-- Extractor options. -/
structure Ext where
  /-- A macro's reads are recorded as a client's (its reads of parents under the class-name key). -/
  safe : Bool := false
  /-- A descendant that erases an inherited member of type `V` records a dependency on the name
  `V` (whose hash covers the underlying type), instead of folding the read into the inheritance
  key on its parent. -/
  vEdge : Bool := false
  deriving DecidableEq, Repr

/-- The key a query is recorded under. -/
def keyOf (x : Ext) : Cls × Q → Cls × K
  | (_, .parent (.inh p)) => (p, .inh)
  | (_, .decl (.inh p) _) => (p, .inh)
  | (c, .und (.inh p)) => if x.vEdge then (c, .und) else (p, .inh)
  | (_, .parent (.sel c)) => (c, .cls)
  | (_, .decl (.sel c) n) => (c, .name n)
  | (_, .parent (.obs c n)) => if x.safe then (c, .cls) else (c, .name n)
  | (_, .decl (.obs c _) n) => (c, .name n)
  | (c, .und _) => (c, .und)
  | (c, _) => (c, .cls)

/-- Which queries a key stands for: the reads of its context, on the chain it hashes. -/
def scope (x : Ext) (I : Cls → Iface) : Cls × Q → Prop
  | (e, .parent (.inh p)) => e ∈ chainP I p
  | (e, .decl (.inh p) _) => e ∈ chainP I p
  | (e, .und (.inh p)) => e = .V ∧ (x.vEdge = true ∨ mentionsVC (declsP I p) = true)
  | (e, .parent (.sel c)) => e ∈ chainP I c
  | (e, .decl (.sel c) _) => e ∈ chainP I c
  | (e, .parent (.obs c _)) => e ∈ chainP I c
  | (e, .decl (.obs c _) _) => e ∈ chainP I c
  | (_, .und .own) => True
  | _ => False

def keys (x : Ext) (_ : Cls) (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.map (keyOf x)).toFinset

def group (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface) (u : Cls) : Out :=
  (unitF (src u)).run (answer fun v => if v ∈ G then (src v).decl else I v)

def Er (r : Rend) (x : Ext) : NCompiler Cls Src Out Iface K H Q (fun _ => AnsV) where
  unit := unitF
  group := group
  iface := Out.iface
  answer := answer
  π := π r
  hashDeps := fun I c => insert .V (chainP I c).toFinset
  keys := keys x
  covers := fun I q k => k = keyOf x q ∧ scope x I q

/-! ## As declared determines as seen from

The as-seen-from rendering is a function of the as-declared one plus the parents: `π .asf` is
determined by `π .decl`, key by key (the name key with the class-name key, and the inheritance
key on its own). So `decl` (and `wit`) can only invalidate *more*. The converse fails on the
precision case below. -/

theorem mem_of_map_pair {α β : Type} {l l' : List α} {f g : α → β}
    (h : l.map (fun e => (e, f e)) = l'.map (fun e => (e, g e))) {e : α} (he : e ∈ l) :
    e ∈ l' ∧ f e = g e := by
  have : (e, f e) ∈ l'.map (fun e => (e, g e)) := h ▸ List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨e', he', hee⟩ := List.mem_map.1 this
  simp only [Prod.mk.injEq] at hee
  obtain ⟨rfl, hfg⟩ := hee
  exact ⟨he', hfg.symm⟩

theorem linP_congr (I I' : Cls → Iface) :
    ∀ f c a, (∀ e ∈ (linP I f c a).map (·.1), (I e).parent = (I' e).parent) →
      linP I f c a = linP I' f c a := by
  intro f
  induction f with
  | zero => intro c a _; rfl
  | succ f ih =>
    intro c a h
    have hc : (I c).parent = (I' c).parent := h c (by
      simp only [linP]; split <;> simp)
    simp only [linP, ← hc]
    split
    · rename_i q qa hq
      congr 1
      apply ih
      intro e he
      apply h
      simp only [linP, hq, List.map_cons, List.mem_cons]
      exact Or.inr he
    · rfl

theorem chain_fst (I : Cls → Iface) :
    ∀ f c a a', (linP I f c a).map (·.1) = (linP I f c a').map (·.1) := by
  intro f
  induction f with
  | zero => intro c a a'; rfl
  | succ f ih =>
    intro c a a'
    simp only [linP]
    split
    · simp only [List.map_cons]; rw [ih]
    · rfl

theorem mem_chainP_self (I : Cls → Iface) (c : Cls) : c ∈ chainP I c := by
  simp only [chainP, depth, linP]; split <;> simp

theorem entriesP_congr (I I' : Cls → Iface) (n : Name) (L : List (Cls × List Ty))
    (h : ∀ e ∈ L.map (·.1), (I e).decls.lookup n = (I' e).decls.lookup n) :
    entriesP I n L = entriesP I' n L := by
  unfold entriesP
  apply List.map_congr_left
  intro e he
  rw [h e.1 (List.mem_map.2 ⟨e, he, rfl⟩)]

/-- **Item 2.** The name key as seen from is determined by the as-declared name key and the
class-name key. -/
theorem asf_of_decl (I I' : Cls → Iface) (c : Cls) (n : Name)
    (hc : π .decl I c .cls = π .decl I' c .cls) (hn : π .decl I c (.name n) = π .decl I' c (.name n)) :
    π .asf I c (.name n) = π .asf I' c (.name n) := by
  simp only [π, H.chain.injEq, H.ents.injEq] at hc hn
  have hlin : linP I depth c ids = linP I' depth c ids :=
    linP_congr I I' _ _ _ fun e he => (mem_of_map_pair hc he).2
  simp only [π, asfP, H.ty.injEq]
  rw [← hlin]
  congr 1
  apply entriesP_congr
  intro e he
  exact (mem_of_map_pair hn he).2

/-- …and the inheritance key as seen from by the as-declared one. -/
theorem asfInh_of_declInh (I I' : Cls → Iface) (c : Cls)
    (h : π .decl I c .inh = π .decl I' c .inh) : π .asf I c .inh = π .asf I' c .inh := by
  simp only [π, H.inh.injEq, and_true, declsP] at h
  have hp : ∀ e ∈ chainP I c, (I e).parent = (I' e).parent ∧ (I e).decls = (I' e).decls := by
    intro e he
    have := (mem_of_map_pair (f := fun e => ((I e).parent, (I e).decls))
      (g := fun e => ((I' e).parent, (I' e).decls)) h he).2
    simpa using this
  have hlin : linP I depth c ids = linP I' depth c ids :=
    linP_congr I I' _ _ _ fun e he => (hp e he).1
  simp only [π, H.asfInh.injEq]
  refine ⟨hlin, ?_⟩
  apply List.map_congr_left
  intro n _
  unfold asfP
  rw [← hlin, entriesP_congr I I' n _ fun e he => by rw [(hp e he).2]]

/-! ## The witness rendering is sound

`wit` with faithfully recorded macro reads meets `NCompiler.Obligations`, so T2″ and T3a″ apply:
every terminating run leaves no class dirty. -/

section obligations

abbrev Env := Task.Env (Cls × Q) (fun _ => AnsV)

theorem run_linT (I : Cls → Iface) (x : Ctx) :
    ∀ f c a, (linT x f c a).run (answer I) = linP I f c a := by
  intro f
  induction f with
  | zero => intro c a; rfl
  | succ f ih =>
    intro c a
    simp only [linT, linP, Task.bind_eq, Task.run_bind, run_askQ, answer]
    rcases h : (I c).parent with _ | ⟨q, qa⟩
    · simp
    · simp [ih]

theorem trace_linT (I : Cls → Iface) (x : Ctx) :
    ∀ f c a q, q ∈ (linT x f c a).trace (answer I) →
      q.2 = .parent x ∧ q.1 ∈ (linP I f c a).map (·.1) := by
  intro f
  induction f with
  | zero => intro c a q hq; simp [linT] at hq
  | succ f ih =>
    intro c a q hq
    simp only [linT, Task.bind_eq, Task.trace_bind, trace_askQ, run_askQ, answer,
      List.singleton_append, List.mem_cons] at hq
    rcases hq with rfl | hq
    · refine ⟨rfl, ?_⟩
      simp only [linP]; split <;> simp
    · rcases h : (I c).parent with _ | ⟨p, pa⟩
      · simp [h] at hq
      · simp only [h, Task.trace_bind, Task.pure_eq, Task.trace_pure,
          List.append_nil] at hq
        obtain ⟨h1, h2⟩ := ih _ _ q hq
        refine ⟨h1, ?_⟩
        simp only [linP, h, List.map_cons, List.mem_cons]
        exact Or.inr h2

theorem run_entriesT (I : Cls → Iface) (x : Ctx) (n : Name) :
    ∀ L, (entriesT x n L).run (answer I) = entriesP I n L := by
  intro L
  induction L with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨c, a⟩ := e
    simp [entriesT, entriesP, answer, ih]

theorem trace_entriesT (I : Cls → Iface) (x : Ctx) (n : Name) :
    ∀ L q, q ∈ (entriesT x n L).trace (answer I) → q.2 = .decl x n ∧ q.1 ∈ L.map (·.1) := by
  intro L
  induction L with
  | nil => intro q hq; simp [entriesT] at hq
  | cons e rest ih =>
    intro q hq
    obtain ⟨c, a⟩ := e
    simp only [entriesT, Task.bind_eq, Task.trace_bind, trace_askQ, run_askQ, Task.pure_eq,
      Task.trace_pure, List.append_nil, List.singleton_append, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp
    · obtain ⟨h1, h2⟩ := ih q hq
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem trace_erasT (I : Cls → Iface) (x : Ctx) :
    ∀ ts q, q ∈ (erasT x ts).trace (answer I) → q = (.V, .und x) ∧ Ty.vc ∈ ts := by
  intro ts
  induction ts with
  | nil => intro q hq; simp [erasT] at hq
  | cons t rest ih =>
    intro q hq
    by_cases ht : t = .vc
    · subst ht
      simp [erasT, answer, askQ, Task.bind] at hq
      rcases hq with rfl | hq
      · simp
      · exact ⟨(ih q hq).1, List.mem_cons_of_mem _ (ih q hq).2⟩
    · simp [erasT, ht, Task.bind] at hq
      exact ⟨(ih q hq).1, List.mem_cons_of_mem _ (ih q hq).2⟩

theorem trace_nameT (I : Cls → Iface) (d : Decl) (p : Cls) (L : List (Cls × List Ty))
    (ownJ : List (Name × JTy)) (n : Name) (q : Cls × Q)
    (hq : q ∈ (nameT d p L ownJ n).trace (answer I)) :
    (q.2 = .decl (.inh p) n ∧ q.1 ∈ L.map (·.1)) ∨
      (q = (.V, .und (.inh p)) ∧ Ty.vc ∈ (entriesP I n L).filterMap (·.2)) := by
  simp only [nameT, Task.bind_eq, Task.trace_bind, List.mem_append] at hq
  rcases hq with hq | hq | hq
  · exact Or.inl (trace_entriesT I _ n L q hq)
  · rw [run_entriesT] at hq
    exact Or.inr (trace_erasT I _ _ q hq)
  · split at hq <;> simp at hq

theorem trace_namesT (I : Cls → Iface) (d : Decl) (p : Cls) (L : List (Cls × List Ty))
    (ownJ : List (Name × JTy)) :
    ∀ ns q, q ∈ (namesT d p L ownJ ns).trace (answer I) → ∃ n,
      (q.2 = .decl (.inh p) n ∧ q.1 ∈ L.map (·.1)) ∨
        (q = (.V, .und (.inh p)) ∧ Ty.vc ∈ (entriesP I n L).filterMap (·.2)) := by
  intro ns
  induction ns with
  | nil => intro q hq; simp [namesT] at hq
  | cons n rest ih =>
    intro q hq
    simp only [namesT, Task.bind_eq, Task.trace_bind, Task.pure_eq, Task.trace_pure,
      List.append_nil, List.mem_append] at hq
    rcases hq with hq | hq
    · exact ⟨n, trace_nameT I d p L ownJ n q hq⟩
    · exact ih q hq

theorem lookup_mem {n : Name} {t : Ty} : ∀ {l : List (Name × Ty)}, l.lookup n = some t → (n, t) ∈ l
  | [], h => by simp at h
  | (k, v) :: rest, h => by
    by_cases hk : n = k
    · subst hk
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      subst h
      simp
    · have : (n == k) = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem mentionsVC_of (I : Cls → Iface) (p : Cls) (n : Name) (a : List Ty)
    (h : Ty.vc ∈ (entriesP I n (linP I depth p a)).filterMap (·.2)) :
    mentionsVC (declsP I p) = true := by
  simp only [entriesP, List.mem_filterMap, List.mem_map] at h
  obtain ⟨_, ⟨e, he, rfl⟩, hlk⟩ := h
  have hmem := lookup_mem hlk
  have hc : e.1 ∈ chainP I p := by
    unfold chainP
    rw [chain_fst I depth p ids a]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  simp only [mentionsVC, declsP, List.any_map, List.any_eq_true, Function.comp]
  exact ⟨e.1, hc, (n, Ty.vc), hmem, by simp⟩

theorem trace_descT (I : Cls → Iface) (d : Decl) (ownJ : List (Name × JTy)) (q : Cls × Q)
    (hq : q ∈ (descT d ownJ).trace (answer I)) : ∃ p,
      ((q.2 = .parent (.inh p) ∨ ∃ n, q.2 = .decl (.inh p) n) ∧ q.1 ∈ chainP I p) ∨
        (q = (.V, .und (.inh p)) ∧ mentionsVC (declsP I p) = true) := by
  unfold descT at hq
  split at hq
  · simp at hq
  · rename_i p a _
    refine ⟨p, ?_⟩
    have hch : (linP I depth p a).map (·.1) = chainP I p := chain_fst I depth p a ids
    simp only [Task.bind_eq, Task.trace_bind, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨h1, h2⟩ := trace_linT I _ _ _ _ q hq
      exact Or.inl ⟨Or.inl h1, hch ▸ h2⟩
    · rw [run_linT] at hq
      obtain ⟨n, h | h⟩ := trace_namesT I d p _ ownJ names q hq
      · exact Or.inl ⟨Or.inr ⟨n, h.1⟩, hch ▸ h.2⟩
      · exact Or.inr ⟨h.1, mentionsVC_of I p n a h.2⟩

theorem trace_selsT (I : Cls → Iface) (obs : Bool) :
    ∀ body q, q ∈ (selsT obs body).trace (answer I) → ∃ c n,
      (q.2 = .parent (if obs then Ctx.obs c n else Ctx.sel c) ∨
        q.2 = .decl (if obs then Ctx.obs c n else Ctx.sel c) n) ∧ q.1 ∈ chainP I c := by
  intro body
  induction body with
  | nil => intro q hq; simp [selsT] at hq
  | cons e rest ih =>
    intro q hq
    obtain ⟨c, n⟩ := e
    simp only [selsT, Task.bind_eq, Task.trace_bind, Task.pure_eq, Task.trace_pure,
      List.append_nil, List.mem_append] at hq
    rcases hq with hq | hq | hq
    · obtain ⟨h1, h2⟩ := trace_linT I _ _ _ _ q hq
      exact ⟨c, n, Or.inl h1, h2⟩
    · rw [run_linT] at hq
      obtain ⟨h1, h2⟩ := trace_entriesT I _ n _ q hq
      exact ⟨c, n, Or.inr h1, h2⟩
    · exact ih q hq

theorem scope_unitF (x : Ext) (I : Cls → Iface) (s : Src) :
    ∀ q ∈ (unitF s).trace (answer I), scope x I q := by
  intro q hq
  simp only [unitF, Task.bind_eq, Task.trace_bind, Task.pure_eq, Task.trace_pure,
    List.append_nil, List.mem_append] at hq
  obtain ⟨e, q⟩ := q
  rcases hq with hq | hq | hq | hq
  · obtain ⟨h, _⟩ := trace_erasT I _ _ _ hq
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [scope]
  · obtain ⟨p, ⟨hq, he⟩ | ⟨h, hm⟩⟩ := trace_descT I _ _ _ hq
    · rcases hq with h | ⟨n, h⟩ <;> (cases h; exact he)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Or.inr hm⟩
  · obtain ⟨c, n, h, he⟩ := trace_selsT I false _ _ hq
    simp only [Bool.false_eq_true, ite_false] at h
    rcases h with h | h <;> (cases h; exact he)
  · obtain ⟨c, n, h, he⟩ := trace_selsT I true _ _ hq
    simp only [ite_true] at h
    rcases h with h | h <;> (cases h; exact he)

theorem iface_unitF (s : Src) (e : Env) : ((unitF s).run e).iface = s.decl := by
  simp [unitF]

theorem Er_comp (r : Rend) (x : Ext) :
    ∀ (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface), ∀ d ∈ G,
      (Er r x).group G src I d = ((Er r x).unit (src d)).run
        ((Er r x).answer (NCompiler.override I G ((Er r x).iface ∘ (Er r x).group G src I))) := by
  intro G src I d _
  show group G src I d = (unitF (src d)).run (answer (NCompiler.override I G (Out.iface ∘ group G src I)))
  unfold group
  congr 2
  funext v
  simp only [NCompiler.override, Function.comp, iface_unitF]

theorem linP_congr_all (I I' : Cls → Iface) (f : ℕ) (c : Cls) (a : List Ty)
    (h : ∀ e ∈ (linP I f c a).map (·.1), I e = I' e) : linP I f c a = linP I' f c a :=
  linP_congr I I' f c a fun e he => by rw [h e he]

theorem Er_locality (r : Rend) (x : Ext) (I I' : Cls → Iface) (c : Cls)
    (h : ∀ d ∈ (Er r x).hashDeps I c, I d = I' d) (k : K) :
    (Er r x).π I c k = (Er r x).π I' c k := by
  have hch : ∀ e ∈ chainP I c, I e = I' e := fun e he =>
    h e (Finset.mem_insert_of_mem (List.mem_toFinset.2 he))
  have hV : I .V = I' .V := h .V (Finset.mem_insert_self _ _)
  have hlin : linP I depth c ids = linP I' depth c ids := linP_congr_all I I' _ _ _ hch
  have hchain : chainP I c = chainP I' c := by unfold chainP; rw [hlin]
  have hmap : ∀ {β : Type} (f : (Cls → Iface) → Cls → β),
      (∀ e ∈ chainP I c, f I e = f I' e) → (chainP I c).map (f I) = (chainP I' c).map (f I') := by
    intro β f hf
    rw [← hchain]
    exact List.map_congr_left hf
  have hasf : ∀ n, asfP I c n = asfP I' c n := by
    intro n
    unfold asfP
    rw [← hlin, entriesP_congr I I' n _ fun e he => by rw [hch e he]]
  have hdecls : declsP I c = declsP I' c :=
    hmap (fun I e => (e, (I e).parent, (I e).decls)) fun e he => by rw [hch e he]
  show π r I c k = π r I' c k
  cases k with
  | name n =>
    cases r
    · simp only [π, hasf]
    all_goals
      simp only [π]
      rw [hmap (fun I e => (e, (I e).decls.lookup n)) fun e he => by rw [hch e he]]
  | cls =>
    simp only [π]
    rw [hmap (fun I e => (e, (I e).parent)) fun e he => by rw [hch e he]]
  | inh =>
    cases r
    · simp only [π, hlin, List.map_congr_left fun n _ => hasf n]
    · simp only [π, hdecls]
    · simp only [π, hdecls, hV]
  | und =>
    simp only [π, hch c (mem_chainP_self I c)]

/-- **Item 5.** As declared, with faithful macro keys, meets the bridge spec if the erasure of a
value class reaches descendants: either through the witness in the inheritance key, or through a
dependency on the value class's name (`vEdge`). As seen from does not: its inheritance key does
not determine the owner's declaration (`bridge₀`/`bridge₁` below). -/
theorem Er_obligations (r : Rend) (x : Ext) (hr : r ≠ .asf) (hsafe : x.safe = true)
    (hv : r = .wit ∨ x.vEdge = true) : (Er r x).Obligations where
  comp := Er_comp r x
  coverage := by
    intro I d s q hq
    exact ⟨keyOf x q, List.mem_toFinset.2 (List.mem_map.2 ⟨q, hq, rfl⟩), rfl,
      scope_unitF x I s q hq⟩
  abstraction := by
    intro I I' k hk q hc
    obtain ⟨rfl, hs⟩ := hc
    obtain ⟨e, q⟩ := q
    change π r I _ _ = π r I' _ _ at hk
    suffices answer I (e, q) = answer I' (e, q) ∧ scope x I' (e, q) from ⟨this.1, rfl, this.2⟩
    -- The as-declared inheritance key: parents and declarations along the chain.
    have hinh : ∀ p, π r I p .inh = π r I' p .inh → declsP I p = declsP I' p := by
      intro p h
      cases r with
      | asf => exact absurd rfl hr
      | decl => simpa only [π, H.inh.injEq, and_true] using h
      | wit => simp only [π, H.inh.injEq] at h; exact h.1
    have hname : ∀ c n, π r I c (.name n) = π r I' c (.name n) →
        (chainP I c).map (fun e => (e, (I e).decls.lookup n)) =
          (chainP I' c).map (fun e => (e, (I' e).decls.lookup n)) := by
      intro c n h
      cases r with
      | asf => exact absurd rfl hr
      | decl => simpa only [π, H.ents.injEq] using h
      | wit => simpa only [π, H.ents.injEq] using h
    have hdecl : ∀ p, π r I p .inh = π r I' p .inh → e ∈ chainP I p →
        e ∈ chainP I' p ∧ (I e).parent = (I' e).parent ∧ (I e).decls = (I' e).decls := by
      intro p h he
      have := mem_of_map_pair (f := fun e => ((I e).parent, (I e).decls))
        (g := fun e => ((I' e).parent, (I' e).decls)) (by simpa only [declsP] using hinh p h) he
      simpa only [Prod.mk.injEq] using this
    cases q with
    | parent y =>
      cases y with
      | inh p =>
        obtain ⟨h1, h2, _⟩ := hdecl p hk hs
        exact ⟨by simp only [answer, h2], h1⟩
      | sel c =>
        simp only [keyOf, π, H.chain.injEq] at hk
        have := mem_of_map_pair hk hs
        exact ⟨by simp only [answer, this.2], this.1⟩
      | obs c n =>
        simp only [keyOf, hsafe, ite_true, π, H.chain.injEq] at hk
        have := mem_of_map_pair hk hs
        exact ⟨by simp only [answer, this.2], this.1⟩
      | own => exact absurd hs (by simp [scope])
    | decl y n =>
      cases y with
      | inh p =>
        obtain ⟨h1, _, h3⟩ := hdecl p hk hs
        exact ⟨by simp only [answer, h3], h1⟩
      | sel c =>
        have := mem_of_map_pair (hname c n hk) hs
        exact ⟨by simp only [answer, this.2], this.1⟩
      | obs c n' =>
        have := mem_of_map_pair (hname c n hk) hs
        exact ⟨by simp only [answer, this.2], this.1⟩
      | own => exact absurd hs (by simp [scope])
    | und y =>
      cases y with
      | inh p =>
        obtain ⟨rfl, hm⟩ := hs
        by_cases hx : x.vEdge = true
        · simp only [keyOf, hx, ite_true] at hk
          have hj : eraseV (I .V).und = eraseV (I' .V).und := by
            simpa only [π, H.j.injEq] using hk
          exact ⟨by simp only [answer, hj], rfl, Or.inl hx⟩
        · have hw : r = .wit := hv.resolve_right hx
          subst hw
          simp only [keyOf, hx, Bool.false_eq_true, ite_false, π, H.inh.injEq] at hk
          obtain ⟨hd, hw⟩ := hk
          have hm : mentionsVC (declsP I p) = true := hm.resolve_left hx
          have hm' : mentionsVC (declsP I' p) = true := hd ▸ hm
          simp only [hm, hm', ite_true, Option.some.injEq] at hw
          exact ⟨by simp only [answer, hw], rfl, Or.inr hm'⟩
      | own =>
        simp only [keyOf, π, H.j.injEq] at hk
        exact ⟨by simp only [answer, hk], trivial⟩
      | sel c => exact absurd hs (by simp [scope])
      | obs c n => exact absurd hs (by simp [scope])
  locality := Er_locality r x

/-- The witness, with faithful macro keys. -/
theorem wit_obligations : (Er .wit { safe := true }).Obligations :=
  Er_obligations .wit _ (by decide) rfl (Or.inl rfl)

/-- As declared plus a dependency on the value class: no witness, no change to any hash. -/
theorem vEdge_obligations : (Er .decl { safe := true, vEdge := true }).Obligations :=
  Er_obligations .decl _ (by decide) rfl (Or.inr rfl)

/-- …so a terminating run leaves no class dirty (T3a″). -/
theorem vEdge_sound (S : Finset Cls) (src : Cls → Src) (P : Compiler.Policy Cls Out K)
    (hP : P.Sound S) (fuel n : ℕ) (R : Finset Cls) (s : Compiler.State Cls Out K) (D : Finset Cls)
    (hD : D ⊆ R) (hInv : (Er .decl { safe := true, vEdge := true }).Inv S src s D)
    (s' : Compiler.State Cls Out K)
    (h : (Er .decl { safe := true, vEdge := true }).zinc S src P fuel n R s = some s') :
    (Er .decl { safe := true, vEdge := true }).Inv S src s' ∅ :=
  (Er .decl _).zinc_sound vEdge_obligations S src P hP fuel n R s D hD hInv s' h

end obligations

/-! ## Runs -/

section runs
open Compiler (State Policy)

abbrev St := State Cls Out K

def memo (s : St) : St :=
  let o := allCls.map fun c => (c, s.out c)
  let u := allCls.map fun c => (c, s.U c)
  { out := fun c => match o.lookup c with | some x => x | none => s.out c
    U := fun c => match u.lookup c with | some x => x | none => s.U c }

structure Run where
  state : St
  rounds : ℕ
  compiled : Finset Cls

/-- Zinc's transitive inheritance invalidation within one subproject: every class whose chain
meets the recompiled set. -/
def inhPolicy : Policy Cls Out K := fun _ R _ s' I =>
  I ∪ Finset.univ.filter fun d => ∃ e ∈ chainP (fun c => (s'.out c).iface) d, e ∈ R

def plain : Policy Cls Out K := Compiler.Policy.plain

def runE (r : Rend) (x : Ext) (src : Cls → Src) (P : Policy Cls Out K) :
    ℕ → ℕ → Finset Cls → Finset Cls → St → Option Run
  | 0, _, _, _, _ => none
  | fuel + 1, n, acc, R, s =>
    let C := Er r x
    let s' := memo (C.round src R s)
    let I := P n R s s' (C.invalidated Finset.univ (C.affected R s) s s')
    if I ⊆ R then some ⟨s', n + 1, acc ∪ R⟩
    else runE r x src P fuel (n + 1) (acc ∪ R) I s'

def dummy : St := { out := fun _ => ⟨{}, [], [], [], [], [], []⟩, U := fun _ => ∅ }

def init (r : Rend) (x : Ext) (src : Cls → Src) : St :=
  memo ((Er r x).round src Finset.univ dummy)

def clean (src : Cls → Src) : Cls → Out := group Finset.univ src fun _ => {}

structure Report where
  recompiled : List Cls
  rounds : ℕ
  /-- Classes whose final output differs from a clean build. -/
  wrong : List Cls
  /-- Recompiled classes (other than the edited ones) whose output did not change. -/
  wasted : List Cls
  deriving Repr, DecidableEq

def report (r : Rend) (x : Ext) (P : Policy Cls Out K) (src₀ src₁ : Cls → Src)
    (R₀ : Finset Cls) : Option Report :=
  let s₀ := init r x src₀
  (runE r x src₁ P 8 0 ∅ R₀ s₀).map fun res =>
    let cl := clean src₁
    let rec_ := allCls.filter fun c => c ∈ res.compiled ∧ c ∉ R₀
    { recompiled := rec_
      rounds := res.rounds
      wrong := allCls.filter fun c => res.state.out c != cl c
      wasted := rec_.filter fun c => res.state.out c == s₀.out c }

end runs

/-! ## Scenarios -/

open Cls Name Ty

/-- `erasure-bridge-upstream-grandparent`: `trait M[T] { def m: Int }`, `A extends M[Int]`,
`B extends A { override def m: Int }`, client `X` of `B.m`. -/
def bridge₀ : Cls → Src
  | M => { decl := { decls := [(m, int)] } }
  | A => { decl := { parent := some (M, [int, int]) } }
  | B => { decl := { parent := some (A, [int, int]), decls := [(m, int)] } }
  | X => { decl := {}, sel := [(B, m)] }
  | _ => { decl := {} }

/-- `M.m: Int → T`: `M.m` now erases to `Object`, so `B` needs a bridge `m()Object`. As seen from
`A`, `m` is `Int` before and after. -/
def bridge₁ : Cls → Src
  | M => { decl := { decls := [(m, p0)] } }
  | c => bridge₀ c

/-- **As seen from is the wrong input for erasure.** `A` recompiles (its inheritance key on `M`
moved), but its own rendering of `m` is `Int` before and after, so across subprojects (only the
inheritance key on `A`) `B` keeps its old bridges. -/
example : report .asf {} plain bridge₀ bridge₁ {M} = some ⟨[A], 2, [B], [A]⟩ := by native_decide
/-- As declared (Scala 3), and with the witness, `B` recompiles. `X` too: the name `m` of `B` lists
`M.m` as declared. -/
example : report .decl {} plain bridge₀ bridge₁ {M} = some ⟨[A, B, X], 2, [], [A, X]⟩ := by
  native_decide
example : report .wit {} plain bridge₀ bridge₁ {M} = some ⟨[A, B, X], 2, [], [A, X]⟩ := by
  native_decide
/-- In one subproject, transitive inheritance invalidation hides the bug. -/
example : report .asf {} inhPolicy bridge₀ bridge₁ {M} = some ⟨[A, B], 2, [], [A]⟩ := by
  native_decide

/-- The precision case: `M[T, U].m: T → m: U`, `A extends M[Int, Int]`, `B` overrides `m`.
Neither the type as seen from `A` nor the erasure changes. -/
def prec₀ : Cls → Src
  | M => { decl := { decls := [(m, p0)] } }
  | A => { decl := { parent := some (M, [int, int]) } }
  | B => { decl := { parent := some (A, [int, int]), decls := [(m, int)] } }
  | X => { decl := {}, sel := [(B, m)] }
  | _ => { decl := {} }

def prec₁ : Cls → Src
  | M => { decl := { decls := [(m, p1)] } }
  | c => prec₀ c

/-- `asf` recompiles only `A`; `decl` also recompiles `B`, and `X` through the name `m` of `B`, for
nothing. The same mechanism as the bridge fix. (In Zinc, `X` recompiles under both bridges through
its `memberRef` on the owner `M`, which the model does not record.) -/
example : report .asf {} plain prec₀ prec₁ {M} = some ⟨[A], 2, [], [A]⟩ := by native_decide
example : report .decl {} plain prec₀ prec₁ {M} = some ⟨[A, B, X], 2, [], [A, B, X]⟩ := by
  native_decide

/-- The converse fails: on the precision case the as-seen-from hashes of `A` agree, the
as-declared ones do not. -/
example : π .asf (fun c => (prec₀ c).decl) .A .inh = π .asf (fun c => (prec₁ c).decl) .A .inh ∧
    π .decl (fun c => (prec₀ c).decl) .A .inh ≠ π .decl (fun c => (prec₁ c).decl) .A .inh := by
  native_decide

/-- The class-name key: `trait M[T] { def m: T }`, `A extends M[T]` (passing its parameter on),
`B extends A[Int] → A[Long]`; client `X` selects `B.m`, macro `Y` observes `B.m`. -/
def hdr₀ : Cls → Src
  | M => { decl := { decls := [(m, p0)] } }
  | A => { decl := { parent := some (M, [p0, p1]) } }
  | B => { decl := { parent := some (A, [int, int]) } }
  | X => { decl := {}, sel := [(B, m)] }
  | Y => { decl := {}, obs := [(B, m)] }
  | _ => { decl := {} }

def hdr₁ : Cls → Src
  | B => { decl := { parent := some (A, [long, int]) } }
  | c => hdr₀ c

/-- Scala 2 moves the name `m` of `B`; both clients recompile. -/
example : report .asf {} plain hdr₀ hdr₁ {B} = some ⟨[X, Y], 2, [], []⟩ := by native_decide
/-- Scala 3's name `m` of `B` does not move; `X` recompiles through the class-name key, the macro
`Y` (recording names only) does not and keeps the stale type. -/
example : report .decl {} plain hdr₀ hdr₁ {B} = some ⟨[X], 2, [Y], []⟩ := by native_decide
/-- Recorded faithfully, the macro's reads of `B`'s parents are covered by the class-name key. -/
example : report .decl { safe := true } plain hdr₀ hdr₁ {B} = some ⟨[X, Y], 2, [], []⟩ := by native_decide

/-- `value-class-mixin-forwarder`: `class V(val x: String) extends AnyVal`, `trait M { def g: V }`,
`A extends M` with a mixin forwarder for `g`. -/
def vc₀ : Cls → Src
  | V => { decl := { und := some str } }
  | M => { decl := { decls := [(g, vc)] } }
  | A => { decl := { parent := some (M, [int, int]), fwd := true } }
  | _ => { decl := {} }

/-- `V(String) → V(Long)`. -/
def vc₁ : Cls → Src
  | V => { decl := { und := some long } }
  | c => vc₀ c

/-- Neither rendering moves: `M.g: V` names `V`. `M` recompiles (it erases its own `g`), `A`'s
forwarder keeps `g()Ljava/lang/String;`. -/
example : report .asf {} plain vc₀ vc₁ {V} = some ⟨[M], 2, [A], []⟩ := by native_decide
example : report .decl {} plain vc₀ vc₁ {V} = some ⟨[M], 2, [A], []⟩ := by native_decide
/-- The witness moves `A`'s inheritance key. -/
example : report .wit {} plain vc₀ vc₁ {V} = some ⟨[M, A], 2, [], []⟩ := by native_decide
/-- So does a dependency on `V` recorded by `A` when it erases `M.g`, with no change to any hash,
under either rendering. -/
example : report .decl { vEdge := true } plain vc₀ vc₁ {V} = some ⟨[M, A], 2, [], []⟩ := by
  native_decide
example : report .asf { vEdge := true } plain vc₀ vc₁ {V} = some ⟨[M, A], 2, [], []⟩ := by
  native_decide

/-! ## Bounded exhaustive comparison of the three renderings

`trait M[T, U]` declares `m` (none, `Int`, `Long`, `T`, `U`, `V`) and `g` (none, `V`);
`A extends M[..]` (`[Int, Int]`, `[Int, Long]`, `[T, U]`) optionally declares `m` (`Int`, `T`)
and has forwarders or not; `B extends A[Int, Int]` or `A[Long, Int]` optionally declares `m`
(`Int`, `Long`, `V`) and has forwarders or not; `V` wraps `Int` or `Long`. Client `X` selects
`B.m` and `B.g`, macro `Y` observes `B.m`. An edit changes one of these choices.
`lake exe exhaustive erasure` runs every (base, edit) pair under each variant.

Results: 6,912 bases, 117,504 edits, of which 25,120 pairs have a base and an edit that both
compile (the model rejects every non-conforming override, so most pairs are illegal). Unclean
runs, and the classes left wrong:

| variant | unclean | wrong | recompiles | wasted (output unchanged) |
|---|---|---|---|---|
| as seen from, across subprojects | 1,716 | `A` 592, `B` 1,384 | 36,352 | `A` 4,128, `B` 7,392, `X` 5,440 |
| as seen from, one subproject (transitive inheritance) | 0 | | 43,696 | `A` 4,720, `B` 12,168, `X` 5,440 |
| as declared | 1,204 | `A` 592, `B` 520, `Y` 352 | 52,128 | `A` 4,128, `B` 9,472, `X` 12,032, `Y` 6,592 |
| as declared, macro reads recorded | 852 | `A` 592, `B` 520 | 57,920 | `A` 4,128, `B` 9,472, `X` 12,032, `Y` 12,032 |
| as seen from + `V` edge | 864 | `B` 864 | 38,576 | `A` 4,720, `B` 7,912, `X` 5,440 |
| as declared + `V` edge | 352 | `Y` 352 | 54,352 | `A` 4,720, `B` 9,992, `X` 12,032, `Y` 6,592 |
| as declared + `V` edge, macro reads recorded | **0** | | 60,144 | `A` 4,720, `B` 9,992, `X` 12,032, `Y` 12,032 |
| witness | 352 | `Y` 352 | 54,352 | `A` 4,720, `B` 9,992, `X` 12,032, `Y` 6,592 |
| witness, macro reads recorded | **0** | | 60,144 | `A` 4,720, `B` 9,992, `X` 12,032, `Y` 12,032 |

* Unclean runs by the class edited: as seen from, `V` 852, `M` 768, `A` 96; as declared, `V` 852
  and (macro) `A` 192, `B` 160; witness, (macro) `A` 192, `B` 160.
* As seen from: 864 runs miss a bridge or forwarder through a type-argument erasure change
  (smallest: `B` forwards `M.m`, `M.m: Int → T`), plus the 852 value-class runs.
* As declared: the 852 value-class runs (`A` or `B` forwards a member of type `V`, `V` edited)
  and, with names-only macro keys, the macro escaping the class-name key (352, all header edits;
  smallest: `B extends A[Int, Int] → A[Long, Int]` with `A.m: T`).
* The witness closes the value-class runs; with faithful macro keys nothing is left. The `V` edge
  gives identical counts without changing any hash. Under as seen from it closes the value-class
  runs and leaves exactly the 864 generic ones: the two problems are independent.
* Precision: as declared recompiles more *clients* as well as descendants (`X` 12,032 wasted vs
  5,440): a client's name `m` of `B` lists every declaration of `m` on the chain (no dedup), so a
  change to an overridden or invisibly re-instantiated declaration moves it. The witness's extra
  cost is descendants that mention `V` but emit no forwarder for it. -/

inductive OM | none | int | long | p0 | p1 | vc
  deriving DecidableEq, Repr

def OM.ty : OM → Option Ty
  | .none => Option.none | .int => some .int | .long => some .long | .p0 => some .p0 | .p1 => some .p1
  | .vc => some .vc

structure Cfg where
  mM : OM
  gM : Bool
  aArgs : Fin 3
  mA : Fin 3
  fA : Bool
  bArg : Bool
  mB : Fin 4
  fB : Bool
  vLong : Bool
  deriving DecidableEq, Repr

def tyOpt (o : Option Ty) (n : Name) : List (Name × Ty) := (o.map fun t => [(n, t)]).getD []

def Cfg.src (k : Cfg) : Cls → Src
  | V => { decl := { und := some (if k.vLong then long else int) } }
  | M => { decl := { decls := tyOpt k.mM.ty m ++ (if k.gM then [(g, vc)] else []) } }
  | A => { decl := { parent := some (M, [[int, int], [int, long], [p0, p1]].getD k.aArgs.val []),
                     decls := tyOpt ([Option.none, some Ty.int, some Ty.p0].getD k.mA.val Option.none) m, fwd := k.fA } }
  | B => { decl := { parent := some (A, if k.bArg then [long, int] else [int, int]),
                     decls := tyOpt ([Option.none, some Ty.int, some Ty.long, some Ty.vc].getD k.mB.val Option.none) m,
                     fwd := k.fB } }
  | X => { decl := {}, sel := [(B, m), (B, g)] }
  | Y => { decl := {}, obs := [(B, m)] }

def oms : List OM := [.none, .int, .long, .p0, .p1, .vc]

def cfgs : List Cfg := do
  let mM ← oms; let gM ← [false, true]
  let aArgs ← [0, 1, 2]; let mA ← [0, 1, 2]; let fA ← [false, true]
  let bArg ← [false, true]; let mB ← [0, 1, 2, 3]; let fB ← [false, true]
  let vLong ← [false, true]
  pure ⟨mM, gM, aArgs, mA, fA, bArg, mB, fB, vLong⟩

/-- Single-choice edits, with the class edited. -/
def edits (k : Cfg) : List (Cfg × Cls) :=
  (oms.filter (· != k.mM)).map (fun o => ({ k with mM := o }, M)) ++
  [({ k with gM := !k.gM }, M)] ++
  (([0, 1, 2] : List (Fin 3)).filter (· != k.aArgs)).map (fun o => ({ k with aArgs := o }, A)) ++
  (([0, 1, 2] : List (Fin 3)).filter (· != k.mA)).map (fun o => ({ k with mA := o }, A)) ++
  [({ k with fA := !k.fA }, A), ({ k with bArg := !k.bArg }, B)] ++
  (([0, 1, 2, 3] : List (Fin 4)).filter (· != k.mB)).map (fun o => ({ k with mB := o }, B)) ++
  [({ k with fB := !k.fB }, B), ({ k with vLong := !k.vLong }, V)]

def Cfg.size (k : Cfg) : ℕ :=
  (if k.mM != .none then 1 else 0) + (if k.gM then 1 else 0) + (if k.aArgs != 0 then 1 else 0) +
    (if k.mA != 0 then 1 else 0) + (if k.fA then 1 else 0) + (if k.bArg then 1 else 0) +
    (if k.mB != 0 then 1 else 0) + (if k.fB then 1 else 0) + (if k.vLong then 1 else 0)

/-- A variant: rendering, faithful macro keys, and the policy (`true`: Zinc's transitive
inheritance invalidation, as within one subproject). -/
structure Variant where
  name : String
  rend : Rend
  ext : Ext
  inh : Bool

def variants : List Variant :=
  [⟨"as seen from (Scala 2), across subprojects", .asf, {}, false⟩,
   ⟨"as seen from (Scala 2), one subproject", .asf, {}, true⟩,
   ⟨"as seen from + V edge", .asf, { vEdge := true }, false⟩,
   ⟨"as declared (Scala 3)", .decl, {}, false⟩,
   ⟨"as declared, macro reads recorded", .decl, { safe := true }, false⟩,
   ⟨"as declared + V edge", .decl, { vEdge := true }, false⟩,
   ⟨"as declared + V edge, macro reads recorded", .decl, { safe := true, vEdge := true }, false⟩,
   ⟨"as declared + erasure witness", .wit, {}, false⟩,
   ⟨"as declared + erasure witness, macro reads recorded", .wit, { safe := true }, false⟩]

/-- A clean build reports no errors. Incremental runs are compared only between legal programs. -/
def Cfg.legal (k : Cfg) : Bool := allCls.all fun c => (clean k.src c).errs.isEmpty

def runVariant (v : Variant) (k k' : Cfg) (e : Cls) : Option Report :=
  report v.rend v.ext (if v.inh then inhPolicy else plain) k.src k'.src {e}

end Zinc.Erasure
