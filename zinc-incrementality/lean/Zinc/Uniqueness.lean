import Zinc.Soundness

/-!
# T3b: fixed points of separate compilation are unique (under a hypothesis), hence T3

T3a leaves Zinc's final state as a *per-unit fixed point*: every unit equals its own compilation
against the interfaces of the current outputs. The clean build is another such fixed point
(compositionality with `G = S`). They need not coincide: with mutually recursive units,
`A.x : typeof(B.y)`, `B.y : typeof(A.x)` has many solutions, and joint compilation picks one.
This is the sbt/zinc#1284 situation. Two sufficient conditions, each a Scala best practice:

* **acyclic** (`fixpoint_unique_of_wf`): traced dependencies respect a well-founded order on units;
* **explicit interfaces** (`fixpoint_unique_of_explicit`): the interface of a unit's output is a
  function of its source alone (explicit result types on public members).

`zinc_eq_clean_of_wf` / `zinc_eq_clean_of_explicit` are the resulting T3 statements.
-/

namespace Zinc.Compiler

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : Compiler CUnit Src Out Iface K Hash Q A)
variable [DecidableEq CUnit]

/-- `o` is a per-unit fixed point of separate compilation on `S`. -/
def Fixpoint (S : Finset CUnit) (src : CUnit → Src) (o : CUnit → Out) : Prop :=
  ∀ u ∈ S, o u = (C.unit (src u)).run (C.envOf (C.iface ∘ o))

omit [DecidableEq CUnit] in
theorem fixpoint_of_inv (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K)
    (h : C.Inv S src s ∅) : C.Fixpoint S src s.out :=
  fun u hu => (h u hu (Finset.notMem_empty u)).1

/-- A clean build of `S`, keeping the outputs of everything outside `S` (libraries) from `s`. -/
def cleanFrom (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) : CUnit → Out :=
  fun u => if u ∈ S then C.group S src (C.env s) u else s.out u

theorem cleanFrom_outside (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K)
    (u : CUnit) (hu : u ∉ S) : C.cleanFrom S src s u = s.out u := by
  simp [cleanFrom, hu]

/-- The clean build is a fixed point: compositionality with `G = S`. -/
theorem cleanFrom_fixpoint (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) : C.Fixpoint S src (C.cleanFrom S src s) := by
  intro u hu
  have h := ob.comp S src (C.env s) u hu
  have hout : C.cleanFrom S src s u = C.group S src (C.env s) u := by simp [cleanFrom, hu]
  rw [hout, h]
  congr 1
  simp only [env, override_envOf]
  congr 1
  funext v
  simp only [cleanFrom, Function.comp]
  split <;> rfl

/-- **Uniqueness under acyclicity.** -/
theorem fixpoint_unique_of_wf (S : Finset CUnit) (src : CUnit → Src)
    (r : CUnit → CUnit → Prop) (hwf : WellFounded r)
    (hdep : ∀ u ∈ S, ∀ e, ∀ q ∈ (C.unit (src u)).trace e, r q.1 u)
    (o₁ o₂ : CUnit → Out) (h₁ : C.Fixpoint S src o₁) (h₂ : C.Fixpoint S src o₂)
    (hext : ∀ u ∉ S, o₁ u = o₂ u) : o₁ = o₂ := by
  funext u
  induction u using hwf.induction with
  | _ u ih =>
    by_cases hu : u ∈ S
    · rw [h₁ u hu, h₂ u hu]
      apply Task.run_congr
      intro q hq
      simp only [envOf, Function.comp]
      rw [ih q.1 (hdep u hu _ q hq)]
    · exact hext u hu

/-- **Uniqueness under explicit interfaces.** -/
theorem fixpoint_unique_of_explicit (S : Finset CUnit) (src : CUnit → Src)
    (ifaceSrc : Src → Iface)
    (hex : ∀ (sr : Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)), C.iface ((C.unit sr).run e) = ifaceSrc sr)
    (o₁ o₂ : CUnit → Out) (h₁ : C.Fixpoint S src o₁) (h₂ : C.Fixpoint S src o₂)
    (hext : ∀ u ∉ S, o₁ u = o₂ u) : o₁ = o₂ := by
  have henv : C.envOf (C.iface ∘ o₁) = C.envOf (C.iface ∘ o₂) := by
    funext p
    simp only [envOf, Function.comp]
    by_cases hp : p.1 ∈ S
    · rw [h₁ _ hp, h₂ _ hp, hex, hex]
    · rw [hext _ hp]
  funext u
  by_cases hu : u ∈ S
  · rw [h₁ u hu, h₂ u hu, henv]
  · exact hext u hu

variable [DecidableEq K] [DecidableEq Hash]

/-- Policies that stay inside the project. -/
def Policy.InS (S : Finset CUnit) (P : Policy CUnit Out K) : Prop :=
  ∀ n R s I, P n R s I ⊆ S

omit [DecidableEq K] [DecidableEq Hash] in
theorem round_out_outside (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K)
    (u : CUnit) (hu : u ∉ R) : (C.round src R s).out u = s.out u := by
  simp [round, hu]

/-- The loop never touches units outside `S`. -/
theorem zinc_out_outside (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K)
    (hP : P.InS S) : ∀ (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K), R ⊆ S →
      ∀ s', C.zinc S src P fuel n R s = some s' → ∀ u ∉ S, s'.out u = s.out u := by
  intro fuel
  induction fuel with
  | zero => intro n R s _ s' h; simp [zinc] at h
  | succ fuel ih =>
    intro n R s hR s' h u hu
    simp only [zinc] at h
    have hnot : u ∉ R := fun h' => hu (hR h')
    split at h
    · cases h; exact C.round_out_outside src R s u hnot
    · rw [ih _ _ _ (hP _ _ _ _) s' h u hu, C.round_out_outside src R s u hnot]

/-- **T3 (acyclic).** The incremental result is the clean build. -/
theorem zinc_eq_clean_of_wf (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (P : Policy CUnit Out K) (hP : P.Sound S) (hPS : P.InS S)
    (r : CUnit → CUnit → Prop) (hwf : WellFounded r)
    (hdep : ∀ u ∈ S, ∀ e, ∀ q ∈ (C.unit (src u)).trace e, r q.1 u)
    (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K) (D : Finset CUnit)
    (hD : D ⊆ R) (hR : R ⊆ S) (hInv : C.Inv S src s D)
    (s' : State CUnit Out K) (h : C.zinc S src P fuel n R s = some s') :
    s'.out = C.cleanFrom S src s := by
  apply C.fixpoint_unique_of_wf S src r hwf hdep
  · exact C.fixpoint_of_inv S src s' (C.zinc_sound ob S src P hP fuel n R s D hD hInv s' h)
  · exact C.cleanFrom_fixpoint ob S src s
  · intro u hu
    rw [C.zinc_out_outside S src P hPS fuel n R s hR s' h u hu, C.cleanFrom_outside S src s u hu]

/-- **T3 (explicit interfaces).** -/
theorem zinc_eq_clean_of_explicit (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (P : Policy CUnit Out K) (hP : P.Sound S) (hPS : P.InS S)
    (ifaceSrc : Src → Iface)
    (hex : ∀ (sr : Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)), C.iface ((C.unit sr).run e) = ifaceSrc sr)
    (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K) (D : Finset CUnit)
    (hD : D ⊆ R) (hR : R ⊆ S) (hInv : C.Inv S src s D)
    (s' : State CUnit Out K) (h : C.zinc S src P fuel n R s = some s') :
    s'.out = C.cleanFrom S src s := by
  apply C.fixpoint_unique_of_explicit S src ifaceSrc hex
  · exact C.fixpoint_of_inv S src s' (C.zinc_sound ob S src P hP fuel n R s D hD hInv s' h)
  · exact C.cleanFrom_fixpoint ob S src s
  · intro u hu
    rw [C.zinc_out_outside S src P hPS fuel n R s hR s' h u hu, C.cleanFrom_outside S src s u hu]

end Zinc.Compiler
