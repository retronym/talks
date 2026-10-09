import V1.Uniqueness
import Mathlib.Data.Finset.Card

-- Snapshot of `zinc-incrementality/lean/Zinc/Termination.lean`, unchanged apart from the namespace.

/-!
# T4: termination

The fuelled loop returns `some` with enough fuel, under three regimes:

* **monotone policies** (`zinc_some_of_monotoneFrom`): from round `k` on the policy keeps the
  previous round and adds the invalidations (`transitiveStep`: brute-force transitive
  invalidation `∪ recompiledClasses`). `R` grows strictly while the loop continues, so at most
  `k + |S| + 1` rounds. No assumption on the dependency graph.
* **explicit interfaces** (`zinc_some_of_explicit`): two rounds (§4: "a signature change takes 2").
* **acyclic, plain policy** (`zinc_some_of_wf`): a unit of rank `r` is never invalidated after
  round `r`, so at most `height + 2` rounds.
-/

namespace V1.Compiler

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : Compiler CUnit Src Out Iface K Hash Q A)
variable [DecidableEq CUnit] [DecidableEq K] [DecidableEq Hash]

/-! ## Monotone policies -/

def Policy.MonotoneFrom (S : Finset CUnit) (k : ℕ) (P : Policy CUnit Out K) : Prop :=
  ∀ n R s s' I, k ≤ n → R ⊆ S → I ⊆ S → R ⊆ P n R s s' I ∧ I ⊆ P n R s s' I

theorem zinc_some_of_monotone (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K)
    (hPS : P.InS S) (k : ℕ) (hM : P.MonotoneFrom S k) :
    ∀ (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K), k ≤ n → R ⊆ S →
      S.card - R.card + 1 ≤ fuel → (C.zinc S src P fuel n R s).isSome := by
  intro fuel
  induction fuel with
  | zero => intro n R s _ _ h; omega
  | succ fuel ih =>
    intro n R s hk hR hfuel
    simp only [zinc]
    split
    · rfl
    · rename_i hsub
      obtain ⟨hR', hI'⟩ := hM n R s (C.round src R s) (C.invalidated S R s (C.round src R s)) hk hR (Finset.filter_subset _ _)
      have hssub : R ⊂ P n R s (C.round src R s) (C.invalidated S R s (C.round src R s)) := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨hR', ?_⟩
        intro heq
        exact hsub (hI'.trans (le_of_eq heq.symm))
      have hcard := Finset.card_lt_card hssub
      have hR'S : P n R s (C.round src R s) (C.invalidated S R s (C.round src R s)) ⊆ S :=
        hPS _ _ _ _ _ (Finset.filter_subset _ _)
      have hcardS := Finset.card_le_card hR'S
      exact ih (n + 1) _ _ (by omega) hR'S (by omega)

/-- Any policy that is monotone from round `k` on (e.g. `transitiveStep = k`) terminates within
`k + |S| + 1` rounds. -/
theorem zinc_some_of_monotoneFrom (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K)
    (hPS : P.InS S) (k : ℕ) (hM : P.MonotoneFrom S k) :
    ∀ (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K), R ⊆ S →
      (k - n) + S.card + 1 ≤ fuel → (C.zinc S src P fuel n R s).isSome := by
  intro fuel
  induction fuel with
  | zero => intro n R s _ h; omega
  | succ fuel ih =>
    intro n R s hR hfuel
    by_cases hk : k ≤ n
    · exact C.zinc_some_of_monotone S src P hPS k hM (fuel + 1) n R s hk hR
        (by have := Finset.card_le_card hR; omega)
    · simp only [zinc]
      split
      · rfl
      · exact ih (n + 1) _ _ (hPS _ _ _ _ _ (Finset.filter_subset _ _)) (by omega)

/-- Zinc's brute-force regime: the transitive dependents of the invalidations, plus the round just
compiled. `deps s c` are the units of `S` holding a key of `c`. -/
def dependents (S : Finset CUnit) (s : State CUnit Out K) (X : Finset CUnit) : Finset CUnit :=
  S.filter fun d => ∃ p ∈ s.U d, p.1 ∈ X

/-- `transitiveStep k`: plain invalidation before round `k`, brute force from `k` on. The closure
is approximated by one step of `dependents` here; soundness and termination only need
`I ∪ R ⊆ next`, which any closure satisfies. -/
def Policy.transitiveStep (S : Finset CUnit) (k : ℕ) : Policy CUnit Out K :=
  fun n R _ s I => if k ≤ n then (I ∪ dependents S s I ∪ R).filter (· ∈ S) else I.filter (· ∈ S)

omit [DecidableEq K] in
theorem transitiveStep_sound (S : Finset CUnit) (k : ℕ) :
    (Policy.transitiveStep (Out := Out) (K := K) S k).Sound S := by
  intro n R _ s I hI p hp
  have hpI : p ∈ I := (Finset.mem_sdiff.1 hp).1
  simp only [Policy.transitiveStep]
  split <;> simp [hpI, hI hpI]

omit [DecidableEq K] in
theorem transitiveStep_inS (S : Finset CUnit) (k : ℕ) : (Policy.transitiveStep (Out := Out) (K := K) S k).InS S := by
  intro n R _ s I _ p hp
  simp only [Policy.transitiveStep] at hp
  split at hp <;> exact (Finset.mem_filter.1 hp).2

omit [DecidableEq K] in
theorem transitiveStep_monotone (S : Finset CUnit) (k : ℕ) :
    (Policy.transitiveStep (Out := Out) (K := K) S k).MonotoneFrom S k := by
  intro n R _ s I hk hR hI
  simp only [Policy.transitiveStep, hk, ite_true]
  constructor
  · intro p hp; simp [hp, hR hp]
  · intro p hp; simp [hp, hI hp]

/-! ## Explicit interfaces: two rounds -/

omit [DecidableEq K] [DecidableEq Hash] in
theorem iface_round_mem (ob : C.Obligations) (src : CUnit → Src) (ifaceSrc : Src → Iface)
    (hex : ∀ (sr : Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)),
      C.iface ((C.unit sr).run e) = ifaceSrc sr)
    (R : Finset CUnit) (s : State CUnit Out K) (u : CUnit) (hu : u ∈ R) :
    C.iface ((C.round src R s).out u) = ifaceSrc (src u) := by
  have h2 : (C.round src R s).out u = C.group R src (C.env s) u := by
    simp only [round, hu, ite_true]
  rw [h2, ob.comp R src (C.env s) u hu, hex]

omit [DecidableEq CUnit] [DecidableEq K] [DecidableEq Hash] in
theorem iface_of_upToDate (src : CUnit → Src) (ifaceSrc : Src → Iface)
    (hex : ∀ (sr : Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)),
      C.iface ((C.unit sr).run e) = ifaceSrc sr)
    (s : State CUnit Out K) (u : CUnit) (h : C.UpToDate src s u) :
    C.iface (s.out u) = ifaceSrc (src u) := by
  rw [h.1, hex]

/-- With source-determined interfaces, the loop stops after at most two rounds. -/
theorem zinc_some_of_explicit (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (P : Policy CUnit Out K) (hPS : P.InS S) (ifaceSrc : Src → Iface)
    (hex : ∀ (sr : Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)),
      C.iface ((C.unit sr).run e) = ifaceSrc sr)
    (n : ℕ) (R : Finset CUnit) (s : State CUnit Out K) (D : Finset CUnit)
    (hD : D ⊆ R) (hInv : C.Inv S src s D) :
    (C.zinc S src P 2 n R s).isSome := by
  simp only [zinc]
  split
  · rfl
  · set s₁ := C.round src R s
    -- after round 0 every unit of `S` has its source interface
    have h₁ : ∀ u ∈ S, C.iface (s₁.out u) = ifaceSrc (src u) := by
      intro u hu
      by_cases huR : u ∈ R
      · exact C.iface_round_mem ob src ifaceSrc hex R s u huR
      · have : s₁.out u = s.out u := C.round_out_outside src R s u huR
        rw [this]
        exact C.iface_of_upToDate src ifaceSrc hex s u (hInv u hu fun h => huR (hD h))
    set R₁ := P n R s s₁ (C.invalidated S R s s₁)
    have hR₁ : R₁ ⊆ S := hPS _ _ _ _ _ (Finset.filter_subset _ _)
    -- round 1 changes no hash, so nothing is invalidated
    have hnone : C.invalidated S R₁ s₁ (C.round src R₁ s₁) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro d _ ⟨p, _, hpR, hne⟩
      apply hne
      rw [h₁ p.1 (hR₁ hpR), C.iface_round_mem ob src ifaceSrc hex R₁ s₁ p.1 hpR]
    split
    · rfl
    · rename_i h; exact absurd (hnone ▸ Finset.empty_subset R₁) h

/-! ## Acyclic dependencies, plain policy: height + 2 rounds -/

/-- Zinc's default policy: the next round is exactly `inv(ΔAPI)`. -/
def Policy.plain : Policy CUnit Out K := fun _ _ _ _ I => I

omit [DecidableEq K] in
theorem plain_sound (S : Finset CUnit) :
    (Policy.plain (CUnit := CUnit) (Out := Out) (K := K)).Sound S :=
  fun _ _ _ _ _ _ => Finset.sdiff_subset

omit [DecidableEq CUnit] [DecidableEq K] in
theorem plain_inS (S : Finset CUnit) :
    (Policy.plain (CUnit := CUnit) (Out := Out) (K := K)).InS S :=
  fun _ _ _ _ _ h => h

/-- The extractor only records keys owned by units it actually queried (no `⊤`-style
over-approximation across units). Needed for the round bound, not for soundness. -/
def KeysOwned : Prop :=
  ∀ (tr : List (CUnit × Q)), ∀ k ∈ C.keys tr, ∃ q ∈ tr, k.1 = q.1

/-- Every recorded key set is the extraction of some trace of the unit's task. -/
def Recorded (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) : Prop :=
  ∀ u ∈ S, ∃ e, s.U u = C.keys ((C.unit (src u)).trace e)

omit [DecidableEq K] [DecidableEq Hash] in
theorem recorded_round (S : Finset CUnit) (src : CUnit → Src) (R : Finset CUnit)
    (s : State CUnit Out K) (h : C.Recorded S src s) : C.Recorded S src (C.round src R s) := by
  intro u hu
  by_cases huR : u ∈ R
  · refine ⟨C.env (C.round src R s), ?_⟩
    simp only [round, huR, ite_true]
    rfl
  · obtain ⟨e, he⟩ := h u hu
    refine ⟨e, ?_⟩
    simp only [round, huR, ite_false]
    exact he

theorem rank_of_invalidated (S : Finset CUnit) (src : CUnit → Src)
    (rank : CUnit → ℕ)
    (hdep : ∀ u ∈ S, ∀ e, ∀ q ∈ (C.unit (src u)).trace e, rank q.1 < rank u)
    (hK : C.KeysOwned) (R : Finset CUnit) (s s' : State CUnit Out K)
    (hrec : C.Recorded S src s') (n : ℕ) (hR : ∀ u ∈ R, n ≤ rank u) :
    ∀ d ∈ C.invalidated S R s s', n + 1 ≤ rank d := by
  intro d hd
  obtain ⟨hdS, p, hp, hpR, _⟩ := Finset.mem_filter.1 hd
  obtain ⟨e, he⟩ := hrec d hdS
  rw [he] at hp
  obtain ⟨q, hq, hqp⟩ := hK _ p hp
  have h1 := hdep d hdS e q hq
  have h2 := hR p.1 hpR
  rw [← hqp] at h1
  omega

theorem zinc_some_of_wf (S : Finset CUnit) (src : CUnit → Src)
    (rank : CUnit → ℕ) (H : ℕ) (hH : ∀ u ∈ S, rank u ≤ H)
    (hdep : ∀ u ∈ S, ∀ e, ∀ q ∈ (C.unit (src u)).trace e, rank q.1 < rank u)
    (hK : C.KeysOwned) :
    ∀ (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K), R ⊆ S →
      (∀ u ∈ R, n ≤ rank u) → C.Recorded S src s → 1 ≤ fuel → H + 2 - n ≤ fuel →
      (C.zinc S src Policy.plain fuel n R s).isSome := by
  intro fuel
  induction fuel with
  | zero => intro n R s _ _ _ h; omega
  | succ fuel ih =>
    intro n R s hR hrank hrec _ hfuel
    simp only [zinc]
    split
    · rfl
    · rename_i hsub
      have hrec' := C.recorded_round S src R s hrec
      have hI := C.rank_of_invalidated S src rank hdep hK R s _ hrec' n hrank
      have hIS : C.invalidated S R s (C.round src R s) ⊆ S := Finset.filter_subset _ _
      have hle : n ≤ H := by
        by_contra hgt
        apply hsub
        intro d hd
        have := hI d hd
        have := hH d (hIS hd)
        omega
      exact ih (n + 1) _ _ hIS hI hrec' (by clear ih; omega) (by clear ih; omega)

end V1.Compiler
