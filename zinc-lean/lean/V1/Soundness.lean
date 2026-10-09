import V1.Model

-- Snapshot of `zinc-incrementality/lean/Zinc/Soundness.lean`, unchanged apart from the namespace.

/-!
# T2 and T3a: the round invariant and the fixed point at termination

`UpToDate s u`: `u`'s output is its own per-unit compilation against the current oracle, and its
recorded keys cover that compilation's trace. `Inv s D`: every unit of `S` outside the dirty set
`D` is up to date.

* **T2** (`round_preserves`): a round compiling `R ⊇ D` leaves exactly `inv(ΔAPI) \ R` dirty.
* **T3a** (`zinc_sound`): whatever the policy (as long as it is `Policy.Sound`), if the loop stops,
  the final state has no dirty unit: it is a per-unit fixed point of separate compilation.
-/

namespace V1.Compiler

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

/-- **T2.** One round preserves the invariant, with the new dirty set `inv(ΔAPI) \ R`. -/
theorem round_preserves (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) (D R : Finset CUnit) (hD : D ⊆ R)
    (hInv : C.Inv S src s D) :
    C.Inv S src (C.round src R s) (C.invalidated S R s (C.round src R s) \ R) := by
  intro u huS hu
  set s' := C.round src R s with hs'
  by_cases huR : u ∈ R
  · -- recompiled in this round: compositionality gives the fixed-point equation,
    -- coverage gives the recorded keys.
    refine ⟨?_, ?_⟩
    · have h1 := ob.comp R src (C.env s) u huR
      have h2 : s'.out u = C.group R src (C.env s) u := by
        simp only [hs', round, huR, ite_true]
      rw [h2, h1, ← env_round]
    · intro q hq
      have hU : s'.U u = C.keys ((C.unit (src u)).trace (C.env s')) := by
        simp only [hs', round, huR, ite_true]; rfl
      rw [hU]
      exact ob.coverage _ q hq
  · -- not recompiled: it was up to date, and every key it reads is either untouched or
    -- hash-unchanged, so by T1 its compilation is unaffected.
    have huI : u ∉ C.invalidated S R s s' := fun h => hu (Finset.mem_sdiff.2 ⟨h, huR⟩)
    have huD : u ∉ D := fun h => huR (hD h)
    obtain ⟨hout, hcov⟩ := hInv u huS huD
    have hU : s'.U u = s.U u := by simp only [hs', round, huR, ite_false]
    have hout' : s'.out u = s.out u := by simp only [hs', round, huR, ite_false]
    have hnochange : ∀ p ∈ s.U u, p.1 ∈ R →
        C.π (C.iface (s.out p.1)) p.2 = C.π (C.iface (s'.out p.1)) p.2 := by
      intro p hp hpR
      by_contra hne
      apply huI
      simp only [invalidated, Finset.mem_filter]
      exact ⟨huS, p, hU ▸ hp, hpR, hne⟩
    have hagree : ∀ q ∈ (C.unit (src u)).trace (C.env s), C.env s q = C.env s' q := by
      intro q hq
      obtain ⟨k, hk, hqk, hcovers⟩ := hcov q hq
      simp only [env, envOf, Function.comp]
      by_cases hqR : q.1 ∈ R
      · have := hnochange k hk (hqk ▸ hqR)
        rw [← hqk] at this
        exact ob.abstraction _ _ k.2 this q.2 hcovers
      · have : s'.out q.1 = s.out q.1 := by simp only [hs', round, hqR, ite_false]
        rw [this]
    obtain ⟨hrun, htrace⟩ := Task.run_eq_of_trace _ _ _ hagree
    refine ⟨?_, ?_⟩
    · rw [hout', hout, hrun]
    · rw [← htrace, hU]; exact hcov

/-- **T3a.** If the loop stops, the final state is a per-unit fixed point for the sources it was
run with: no unit is dirty. -/
theorem zinc_sound (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (P : Policy CUnit Out K) (hP : P.Sound S) :
    ∀ (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K) (D : Finset CUnit),
      D ⊆ R → C.Inv S src s D →
      ∀ s', C.zinc S src P fuel n R s = some s' → C.Inv S src s' ∅ := by
  intro fuel
  induction fuel with
  | zero => intro n R s D _ _ s' h; simp [zinc] at h
  | succ fuel ih =>
    intro n R s D hD hInv s' h
    simp only [zinc] at h
    have hstep := C.round_preserves ob S src s D R hD hInv
    split at h
    · rename_i hsub
      cases h
      have : C.invalidated S R s (C.round src R s) \ R = ∅ := Finset.sdiff_eq_empty_iff_subset.2 hsub
      rw [this] at hstep
      exact hstep
    · exact ih _ _ _ _ (hP _ _ _ _ _ (Finset.filter_subset _ _)) hstep s' h

end V1.Compiler

namespace V1.Compiler

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

end V1.Compiler
