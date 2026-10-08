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

* `(c, name n)`, hashed by the flattened composition, for a selection `c.n` (`client`, or `uses`
  when a class selects its own member: Zinc drops those self-references);
* `(p, parents)`, hashed by `p`'s parents, for every `parents` query a class asks while
  linearizing (`header`). Since a class asks this of *every* ancestor, the keys say "recompile
  every transitive descendant when a parents list changes": the header rule.

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
  deriving DecidableEq, Repr

structure Decl where
  parents : List (Cls × Ty) := []
  decls : List (Name × Mem) := []
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

structure Out where
  iface : Iface
  /-- The resolved type of each selection. -/
  descs : List (Option Ty)
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
  deriving DecidableEq, Repr

inductive AnsV
  | ps (l : List (Cls × Ty))
  | ty (t : Option Ty)
  deriving DecidableEq, Repr

def answer (I : Cls → Iface) : Cls × Q → AnsV
  | (c, .parents) => .ps (I c).decl.parents
  | (c, .member n) => .ty (lookupFlat (flatOf I c n))

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

def selects : List (Cls × Name) → T (List (Option Ty))
  | [] => pure []
  | (c, n) :: rest => do
    let r ← askQ c (.member n)
    let ts ← selects rest
    pure ((match r with | .ty t => t | _ => none) :: ts)

def unitF (s : Src) : T Out := do
  let ls ← parentLins (ancestors depth) s.decl.parents
  let ts ← selects s.body
  pure ⟨⟨s.decl, merge ls⟩, ts⟩

/-! ## Keys and hashes -/

inductive K
  | name (n : Name)
  | parents
  deriving DecidableEq, Repr

inductive H
  | flat (l : List (Cls × Ty × Mem))
  | ps (l : List (Cls × Ty))
  deriving DecidableEq, Repr

def π (I : Cls → Iface) (c : Cls) : K → H
  | .name n => .flat (flatOf I c n)
  | .parents => .ps (I c).decl.parents

/-- The key covering a query. -/
def keyOf : Q → K
  | .parents => .parents
  | .member n => .name n

/-- Which rule of the PoC's table a recorded key stands for. -/
inductive Kind | client | uses | header
  deriving DecidableEq, Repr

def kindOf (d : Cls) : Cls × Q → Kind
  | (_, .parents) => .header
  | (c, .member _) => if c = d then .uses else .client

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
  locality := by
    intro I I' c h k
    have hc : I c = I' c := h c (Finset.mem_insert_self _ _)
    cases k with
    | name n => simp only [Fl, π, flatOf_congr I I' c n h]
    | parents => simp only [Fl, π, hc]

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
def runF (E : Kind → Bool) (dom : Dom) (src : Cls → Src) (P : Policy Cls Out K) :
    ℕ → ℕ → Finset Cls → Finset Cls → St → Option Run
  | 0, _, _, _, _ => none
  | fuel + 1, n, acc, R, s =>
    let s' := (Fl E).round src R s
    let I := P n R s s' ((Fl E).invalidated Finset.univ (domain E dom R s s') s s')
    if I ⊆ R then some ⟨s', n + 1, acc ∪ R⟩
    else runF E dom src P fuel (n + 1) (acc ∪ R) I s'

def headerChanged (s s' : St) (p : Cls) : Bool :=
  (s.out p).iface.decl.parents != (s'.out p).iface.decl.parents

/-- The header rule as a policy: when a recompiled class's parents changed, recompile its
descendants, transitively or only the direct children. -/
def headerPolicy (transitive : Bool) : Policy Cls Out K := fun _ R s s' I =>
  let Hd := R.filter (headerChanged s s' · = true)
  I ∪ if transitive then descendants s' Hd else children s' Hd

def dummy : St := { out := fun _ => ⟨⟨{}, []⟩, []⟩, U := fun _ => ∅ }

def init (E : Kind → Bool) (src : Cls → Src) : St := (Fl E).round src Finset.univ dummy

def clean (src : Cls → Src) : Cls → Out := group Finset.univ src fun _ => ⟨{}, []⟩

def all : List Cls := [A, B, M, C, X, Y, Z]

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
      clean := all.all fun c => r.state.out c == clean src₁ c }

end runs

/-! ## Scenarios -/

def int : Mem := ⟨.int⟩
def str : Mem := ⟨.string⟩
def par : Mem := ⟨.param⟩

/-- §10a: `A[T] { m: Int; g: Int }`, `B extends A[Int]`, `C extends B with M`; clients
`X (B.m)`, `Y (C.m)`, `Z (B.g)`. -/
def base : Cls → Src
  | A => { decl := { decls := [(m, int), (g, int)] } }
  | B => { decl := { parents := [(A, .int)] } }
  | M => { decl := {} }
  | C => { decl := { parents := [(B, .int), (M, .int)] } }
  | X => { decl := {}, body := [(B, m)] }
  | Y => { decl := {}, body := [(C, m)] }
  | Z => { decl := {}, body := [(B, g)] }

/-- Edit 1: `A.m: Int → String`. -/
def edit1 : Cls → Src
  | A => { decl := { decls := [(m, str), (g, int)] } }
  | c => base c

/-- Edit 2 base: `A.m: T`. -/
def base2 : Cls → Src
  | A => { decl := { decls := [(m, par), (g, int)] } }
  | c => base c

/-- Edit 2: `B extends A[Int]` → `A[String]`, a header change. -/
def edit2 : Cls → Src
  | B => { decl := { parents := [(A, .string)] } }
  | c => base2 c

/-- Edit 3: the mixin `M` gains `m`. -/
def edit3 : Cls → Src
  | M => { decl := { decls := [(m, str)] } }
  | c => base c

/-- Edit 4 base: a header change two levels up. `M[T] { g: T }`, `A extends M[Int]`,
`B extends A[Int]`, `C extends B`; clients `X (B.g)`, `Y (C.g)`, `Z (B.m)`. -/
def base4 : Cls → Src
  | M => { decl := { decls := [(g, par)] } }
  | A => { decl := { parents := [(M, .int)], decls := [(m, int)] } }
  | B => { decl := { parents := [(A, .int)] } }
  | C => { decl := { parents := [(B, .int)] } }
  | X => { decl := {}, body := [(B, g)] }
  | Y => { decl := {}, body := [(C, g)] }
  | Z => { decl := {}, body := [(B, m)] }

/-- Edit 4: `A extends M[Int]` → `M[String]`. `B`'s and `C`'s stored linearizations now say
`M[Int]`. -/
def edit4 : Cls → Src
  | A => { decl := { parents := [(M, .string)], decls := [(m, int)] } }
  | c => base4 c

def noHeader : Kind → Bool
  | .header => false
  | _ => true

def plain : Compiler.Policy Cls Out K := Compiler.Policy.plain

/-! ### Decision 1, with header keys

Edit 1 and Edit 3 are as for the recursive Merkle design (`Hier.Mk`). A header change (Edits 2
and 4) costs a round more: in the round that recompiles `B` (or `A`), `Δ` recomputes the
descendants' hashes over their *stale* linearizations, so their clients only move once the
header keys have recompiled the descendants. The PoC's `Δ` domain gives the same runs as the
proof's. -/

example : report full .proof plain base edit1 {A} = some ⟨[X, Y], 2, true⟩ := by native_decide
example : report full .zinc plain base edit1 {A} = some ⟨[X, Y], 2, true⟩ := by native_decide
example : report full .proof plain base2 edit2 {B} = some ⟨[C, X, Y, Z], 3, true⟩ := by native_decide
example : report full .zinc plain base2 edit2 {B} = some ⟨[C, X, Y, Z], 3, true⟩ := by native_decide
example : report full .proof plain base edit3 {M} = some ⟨[Y], 2, true⟩ := by native_decide
example : report full .zinc plain base edit3 {M} = some ⟨[Y], 2, true⟩ := by native_decide
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

end Zinc.Flat
