import Zinc.Model
import Zinc.General

/-!
# T2 and T3a: the round invariant and the fixed point at termination

`UpToDate s u`: `u`'s output is its own per-unit compilation against the current oracle, and its
recorded keys cover that compilation's trace. `Inv s D`: every unit of `S` outside the dirty set
`D` is up to date.

* **T2** (`round_preserves`): a round compiling `R ⊇ D` leaves exactly `inv(ΔAPI) \ R` dirty.
* **T3a** (`zinc_sound`): whatever the policy (as long as it is `Policy.Sound`), if the loop stops,
  the final state has no dirty unit: it is a per-unit fixed point of separate compilation.

Both are proved once, for the general form `XCompiler` (`General.lean`), and hold here through the
lift `toX`, whose loop is this one round for round (`zinc_toX`).
-/

namespace Zinc.Compiler

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : Compiler CUnit Src Out Iface K Hash Q A)
variable [DecidableEq CUnit] [DecidableEq K] [DecidableEq Hash]

def UpToDate (src : CUnit → Src) (s : State CUnit Out K) (u : CUnit) : Prop :=
  s.out u = (C.unit (src u)).run (C.env s) ∧
  ∀ q ∈ (C.unit (src u)).trace (C.env s), ∃ k ∈ s.U u, q.1 = k.1 ∧ C.covers q.2 k.2

def Inv (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) (D : Finset CUnit) : Prop :=
  ∀ u ∈ S, u ∉ D → C.UpToDate src s u

omit [DecidableEq K] [DecidableEq Hash] in
theorem env_round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) :
    C.env (C.round src R s) =
      C.override (C.env s) R (C.iface ∘ C.group R src (C.env s)) := by
  simp only [env, round]
  rw [override_envOf]
  congr 1
  funext u
  simp only [Function.comp]
  split <;> rfl

/-- The lift into the general form: answers and hashes read one interface, keys come from the
trace. -/
def toX : XCompiler CUnit Src Out Iface K Hash Q A where
  unit := C.unit
  group G src I := C.group G src (C.envOf I)
  iface := C.iface
  answer I q := C.answer (I q.1) q.2
  π I c k := C.π (I c) k
  hashDeps _ c := {c}
  keys _ _ tr := C.keys tr
  covers _ q k := q.1 = k.1 ∧ C.covers q.2 k.2

omit [DecidableEq K] [DecidableEq Hash] in
theorem toX_obligations (ob : C.Obligations) : C.toX.Obligations where
  comp G src I d hd := by
    show C.group G src (C.envOf I) d = (C.unit (src d)).run _
    rw [ob.comp G src (C.envOf I) d hd, C.override_envOf]
    rfl
  coverage _ _ _ q hq := ob.coverage _ q hq
  abstraction I I' k h q hc := by
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, h1, h2⟩
    show C.answer (I q.1) q.2 = C.answer (I' q.1) q.2
    rw [h1]
    exact ob.abstraction _ _ k.2 h q.2 h2
  locality I I' c h k := by
    show C.π (I c) k = C.π (I' c) k
    rw [h c (Finset.mem_singleton_self c)]

theorem invalidated_toX (S R : Finset CUnit) (s s' : State CUnit Out K) :
    C.toX.invalidated S R s s' = C.invalidated S R s s' := by
  unfold XCompiler.invalidated invalidated
  apply Finset.filter_congr
  intro d _
  simp only [XCompiler.changed, changed, XCompiler.Affected, toX, Finset.mem_singleton,
    exists_eq_left, or_self]
  rfl

/-- The loop on the lift is this loop. -/
theorem zinc_toX (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) :
    ∀ fuel n R s, C.toX.zinc S src P fuel n R s = C.zinc S src P fuel n R s := by
  intro fuel
  induction fuel with
  | zero => intro n R s; rfl
  | succ fuel ih =>
    intro n R s
    simp only [XCompiler.zinc, zinc, ih, invalidated_toX]
    rfl

/-- **T2.** One round preserves the invariant, with the new dirty set `inv(ΔAPI) \ R`. -/
theorem round_preserves (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) (D R : Finset CUnit) (hD : D ⊆ R) (hInv : C.Inv S src s D) :
    C.Inv S src (C.round src R s) (C.invalidated S R s (C.round src R s) \ R) := by
  have := C.toX.round_preserves (C.toX_obligations ob) S src s D R hD hInv
  rwa [invalidated_toX] at this

/-- **T3a.** If the loop stops, the final state has no dirty unit. -/
theorem zinc_sound (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (P : Policy CUnit Out K) (hP : P.Sound S) :
    ∀ (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K) (D : Finset CUnit),
      D ⊆ R → C.Inv S src s D →
      ∀ s', C.zinc S src P fuel n R s = some s' → C.Inv S src s' ∅ := by
  intro fuel n R s D hD hInv s' h
  rw [← zinc_toX] at h
  exact C.toX.zinc_sound (C.toX_obligations ob) S src P hP fuel n R s D hD hInv s' h

end Zinc.Compiler

namespace Zinc.Compiler

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : Compiler CUnit Src Out Iface K Hash Q A)
/-- The starting point of an incremental build: the previous build was a fixed point for the old
sources, and `D` contains every unit whose source changed. -/
theorem inv_of_changed (S : Finset CUnit) (src₀ src : CUnit → Src) (s : State CUnit Out K)
    (D : Finset CUnit) (hD : ∀ u, src₀ u ≠ src u → u ∈ D) (h : C.Inv S src₀ s ∅) :
    C.Inv S src s D := by
  intro u hu huD
  have : src₀ u = src u := by
    by_contra hne; exact huD (hD u hne)
  have h' := h u hu (Finset.notMem_empty u)
  simpa [UpToDate, this] using h'

end Zinc.Compiler
