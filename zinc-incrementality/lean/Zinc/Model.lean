import Zinc.Task

/-!
# The abstract model of a compiler and of Zinc's loop

* `Compiler` packages the per-unit task `F_d`, the black-box joint compiler, the interface
  projection, the query answerer, the bridge's key extractor and the per-key API hash `π`.
* `Obligations` are the hypotheses on the compiler: compositionality, coverage, abstraction.
  Purity needs no clause: the per-unit task is a function of the source, and its output a function
  of the answers (`Task.run`).
* `round` is one Zinc cycle; `invalidated` is `inv(ΔAPI)`; `zinc` is the fuelled loop with a
  pluggable invalidation `Policy`.

All queries and keys are addressed to a unit: `Query := CUnit × Q`, `Key := CUnit × K`.

This is the specification's first page. Instances that need more use one of its variants: keys read
from the output (`TCompiler`, `Tree.lean`), a hash that reads several units (`GCompiler`,
`NonLocal.lean`), answers that read several units and an upstream (`NCompiler`, `NonLocalAns.lean`,
`Classpath.lean`). Each lifts into the general form `XCompiler` (`General.lean`), where T2, T3a,
T5 and the monotone regimes of T4 are proved once; every variant's theorems are corollaries.
-/

namespace Zinc

/-- The compiler as seen by Zinc. `CUnit` is a compilation unit (a class, for Zinc ≥ 1.0). -/
structure Compiler (CUnit Src Out Iface K Hash Q : Type) (A : Q → Type) where
  /-- `F_d`: compile one unit against an oracle. -/
  unit   : Src → Task (CUnit × Q) (fun p => A p.2) Out
  /-- Joint compilation of a group against an oracle for everything else. -/
  group  : Finset CUnit → (CUnit → Src) → Task.Env (CUnit × Q) (fun p => A p.2) → (CUnit → Out)
  /-- The interface of an output (classfile / TASTy view). -/
  iface  : Out → Iface
  /-- Answer a query from an interface. -/
  answer : Iface → (q : Q) → A q
  /-- `π`: the bridge-side API hash per key (`ExtractAPI` + name hashing). -/
  π      : Iface → K → Hash
  /-- `U(d)`: the bridge's abstraction of a query trace into recorded keys (`ExtractUsedNames`). -/
  keys   : List (CUnit × Q) → Finset (CUnit × K)
  /-- `q ⊑ k`: key `k` covers query `q`. -/
  covers : Q → K → Prop

namespace Compiler

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : Compiler CUnit Src Out Iface K Hash Q A)

abbrev Env := Task.Env (CUnit × Q) (fun p => A p.2)

/-- The oracle induced by an interface per unit. -/
def envOf (I : CUnit → Iface) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  fun p => C.answer (I p.1) p.2

variable [DecidableEq CUnit]

/-- Override an oracle on the units of `G` with fresh interfaces. -/
def override (e : Env (CUnit := CUnit) (Q := Q) (A := A)) (G : Finset CUnit)
    (I : CUnit → Iface) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  fun p => if p.1 ∈ G then C.answer (I p.1) p.2 else e p

theorem override_envOf (I I' : CUnit → Iface) (G : Finset CUnit) :
    C.override (C.envOf I) G I' = C.envOf (fun u => if u ∈ G then I' u else I u) := by
  funext p
  simp only [override, envOf]
  split <;> rfl

/-- The bridge spec: what Zinc's soundness proof needs from the compiler. -/
structure Obligations : Prop where
  /-- Compositionality (§6): joint compilation of `G` is a fixed point of the per-unit tasks,
  with group-mates answered from their fresh interfaces. -/
  comp : ∀ (G : Finset CUnit) (src : CUnit → Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)),
    ∀ d ∈ G, C.group G src e d =
      (C.unit (src d)).run (C.override e G (C.iface ∘ C.group G src e))
  /-- Coverage: every traced query (misses and closure queries included) has a recorded key. -/
  coverage : ∀ (tr : List (CUnit × Q)), ∀ q ∈ tr, ∃ k ∈ C.keys tr, q.1 = k.1 ∧ C.covers q.2 k.2
  /-- Abstraction: equal hashes on a key give equal answers to every query it covers. -/
  abstraction : ∀ (i i' : Iface) (k : K), C.π i k = C.π i' k →
    ∀ q, C.covers q k → C.answer i q = C.answer i' q

/-- Zinc's persisted state: outputs and recorded keys per unit. -/
structure State (CUnit Out K : Type) where
  out : CUnit → Out
  U   : CUnit → Finset (CUnit × K)

/-- The oracle a state presents: every unit answered from the interface of its current output. -/
def env (s : State CUnit Out K) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  C.envOf (C.iface ∘ s.out)

/-- One Zinc cycle: compile `R` jointly against the current outputs, record the keys of each
recompiled unit's per-unit trace against the new outputs. -/
def round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) : State CUnit Out K :=
  let o := C.group R src (C.env s)
  let out' : CUnit → Out := fun u => if u ∈ R then o u else s.out u
  let e' := C.envOf (C.iface ∘ out')
  { out := out'
    U := fun d => if d ∈ R then C.keys ((C.unit (src d)).trace e') else s.U d }

/-- `(c, k)` changed in the round that took `s` to `s'`: `c` was recompiled and its hash on `k`
differs. -/
def changed (R : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) : Prop :=
  p.1 ∈ R ∧ C.π (C.iface (s.out p.1)) p.2 ≠ C.π (C.iface (s'.out p.1)) p.2

instance [DecidableEq Hash] (R : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) :
    Decidable (C.changed R s s' p) := by unfold changed; infer_instance

/-- `inv(ΔAPI)`: units of `S` holding a changed key. -/
def invalidated [DecidableEq K] [DecidableEq Hash] (S : Finset CUnit) (R : Finset CUnit)
    (s s' : State CUnit Out K) : Finset CUnit :=
  S.filter fun d => ∃ p ∈ s'.U d, C.changed R s s' p

/-- A policy chooses the next round from the round number, the round just compiled, the old and
new states and `inv(ΔAPI)`. Zinc's heuristics are policies, including its hierarchy walk. -/
abbrev Policy (CUnit Out K : Type) :=
  ℕ → Finset CUnit → State CUnit Out K → State CUnit Out K → Finset CUnit → Finset CUnit

/-- The one obligation on a policy that soundness needs: never drop an invalidated unit outside
the round just compiled. -/
def Policy.Sound (S : Finset CUnit) (P : Policy CUnit Out K) : Prop :=
  ∀ n R s s' I, I ⊆ S → I \ R ⊆ P n R s s' I

/-- Policies that stay inside the project. -/
def Policy.InS (S : Finset CUnit) (P : Policy CUnit Out K) : Prop :=
  ∀ n R s s' I, I ⊆ S → P n R s s' I ⊆ S

/-- A policy that, from round `k` on, keeps the round just compiled and the invalidations. -/
def Policy.MonotoneFrom (S : Finset CUnit) (k : ℕ) (P : Policy CUnit Out K) : Prop :=
  ∀ n R s s' I, k ≤ n → R ⊆ S → I ⊆ S → R ⊆ P n R s s' I ∧ I ⊆ P n R s s' I

/-- Zinc's loop, fuelled. Stops when every invalidated unit was in the round just compiled
(`IncrementalCommon.invalidateAfterInternalCompilation`: `newInvalidations.isEmpty`). -/
def zinc [DecidableEq K] [DecidableEq Hash] (S : Finset CUnit) (src : CUnit → Src)
    (P : Policy CUnit Out K) : ℕ → ℕ → Finset CUnit → State CUnit Out K → Option (State CUnit Out K)
  | 0, _, _, _ => none
  | fuel + 1, n, R, s =>
    let s' := C.round src R s
    let I := C.invalidated S R s s'
    if I ⊆ R then some s' else zinc S src P fuel (n + 1) (P n R s s' I) s'

/-- A clean build: everything compiled jointly against an external oracle. -/
def clean (S : Finset CUnit) (src : CUnit → Src) (ext : Env (CUnit := CUnit) (Q := Q) (A := A)) :
    CUnit → Out :=
  C.group S src ext

end Compiler
end Zinc
