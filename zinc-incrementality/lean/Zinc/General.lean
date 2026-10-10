import Zinc.Model
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

/-!
# The framework's general form

`XCompiler` is the general form every variant lifts into: answers and hashes that read several
interfaces (`NCompiler`'s), and an extractor that reads a unit's output as well as its trace
(`TCompiler`'s), so a key can name what the compilation resolved to (implicit search's chosen
scope) and not only what it asked. The local `Compiler` (`Model.lean`) is the specification's
first page; `XCompiler` is where its theorems are proved once.

**T2** (`round_preserves`): with `Δ` over `affected R s`, one round preserves the invariant.
**T3a** (`zinc_sound`): if the loop stops, every unit is up to date. The variants reach both
through their lifts (`Lifts.lean`), round for round.
-/

namespace Zinc

structure XCompiler (CUnit Src Out Iface K Hash Q : Type) (A : Q → Type) where
  unit   : Src → Task (CUnit × Q) (fun p => A p.2) Out
  /-- Joint compilation of a group against the interfaces of everything else. -/
  group  : Finset CUnit → (CUnit → Src) → (CUnit → Iface) → (CUnit → Out)
  iface  : Out → Iface
  /-- An answer may read the interfaces of several units. -/
  answer : (CUnit → Iface) → (q : CUnit × Q) → A q.2
  π      : (CUnit → Iface) → CUnit → K → Hash
  /-- The units `π I c _` reads, which may depend on `I`. -/
  hashDeps : (CUnit → Iface) → CUnit → Finset CUnit
  /-- `U(d)`: the extractor for unit `d`, reading its output (the typed tree) and its trace. -/
  keys   : CUnit → Out → List (CUnit × Q) → Finset (CUnit × K)
  covers : (CUnit → Iface) → (CUnit × Q) → (CUnit × K) → Prop

namespace XCompiler

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : XCompiler CUnit Src Out Iface K Hash Q A)
variable [DecidableEq CUnit]

/-- Replace the interfaces of `G`. -/
def override (I : CUnit → Iface) (G : Finset CUnit) (I' : CUnit → Iface) : CUnit → Iface :=
  fun u => if u ∈ G then I' u else I u

structure Obligations : Prop where
  comp : ∀ (G : Finset CUnit) (src : CUnit → Src) (I : CUnit → Iface), ∀ d ∈ G,
    C.group G src I d = (C.unit (src d)).run (C.answer (override I G (C.iface ∘ C.group G src I)))
  coverage : ∀ (I : CUnit → Iface) (d : CUnit) (s : Src), ∀ q ∈ (C.unit s).trace (C.answer I),
    ∃ k ∈ C.keys d ((C.unit s).run (C.answer I)) ((C.unit s).trace (C.answer I)), C.covers I q k
  abstraction : ∀ (I I' : CUnit → Iface) (k : CUnit × K), C.π I k.1 k.2 = C.π I' k.1 k.2 →
    ∀ q, C.covers I q k → C.answer I q = C.answer I' q ∧ C.covers I' q k
  locality : ∀ (I I' : CUnit → Iface) (c : CUnit), (∀ d ∈ C.hashDeps I c, I d = I' d) →
    ∀ k, C.π I c k = C.π I' c k

/-- The abstraction obligation alone: T5a (`inv_external`) needs nothing else (an observation of
the split-layout session's `External.lean`). -/
def Abstraction : Prop :=
  ∀ (I I' : CUnit → Iface) (k : CUnit × K), C.π I k.1 k.2 = C.π I' k.1 k.2 →
    ∀ q, C.covers I q k → C.answer I q = C.answer I' q ∧ C.covers I' q k

open Compiler (State Policy)

def ifaces (s : State CUnit Out K) : CUnit → Iface := C.iface ∘ s.out

def round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) : State CUnit Out K :=
  let o := C.group R src (C.ifaces s)
  let out' : CUnit → Out := fun u => if u ∈ R then o u else s.out u
  { out := out'
    U := fun d => if d ∈ R then
        C.keys d (out' d) ((C.unit (src d)).trace (C.answer (C.iface ∘ out'))) else s.U d }

/-- A unit whose hash may have changed after recompiling `R`, read sets taken in `s`: it is in `R`,
or its hash reads a unit in `R`. A predicate, so that no `Fintype` is needed. -/
def Affected (R : Finset CUnit) (s : State CUnit Out K) (c : CUnit) : Prop :=
  c ∈ R ∨ ∃ d ∈ C.hashDeps (C.ifaces s) c, d ∈ R

instance (R : Finset CUnit) (s : State CUnit Out K) (c : CUnit) : Decidable (C.Affected R s c) := by
  unfold Affected; infer_instance

def changed (R : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) : Prop :=
  C.Affected R s p.1 ∧ C.π (C.ifaces s) p.1 p.2 ≠ C.π (C.ifaces s') p.1 p.2

instance [DecidableEq Hash] (R : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) :
    Decidable (C.changed R s s' p) := by unfold changed; infer_instance

/-- `inv(ΔAPI)` after recompiling `R`: units of `S` holding a key whose hash moved, over the
affected units. -/
def invalidated [DecidableEq K] [DecidableEq Hash] (S R : Finset CUnit)
    (s s' : State CUnit Out K) : Finset CUnit :=
  S.filter fun d => ∃ p ∈ s'.U d, C.changed R s s' p

def UpToDate (src : CUnit → Src) (s : State CUnit Out K) (u : CUnit) : Prop :=
  s.out u = (C.unit (src u)).run (C.answer (C.ifaces s)) ∧
  ∀ q ∈ (C.unit (src u)).trace (C.answer (C.ifaces s)), ∃ k ∈ s.U u, C.covers (C.ifaces s) q k

def Inv (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) (D : Finset CUnit) : Prop :=
  ∀ u ∈ S, u ∉ D → C.UpToDate src s u

theorem ifaces_round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) :
    C.ifaces (C.round src R s) = override (C.ifaces s) R (C.iface ∘ C.group R src (C.ifaces s)) := by
  funext u
  simp only [ifaces, round, override, Function.comp]
  split <;> rfl

variable [DecidableEq K] [DecidableEq Hash]

/-- **T2.** With `Δ` over the affected units, one round preserves the invariant. -/
theorem round_preserves (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) (D R : Finset CUnit) (hD : D ⊆ R) (hInv : C.Inv S src s D) :
    C.Inv S src (C.round src R s) (C.invalidated S R s (C.round src R s) \ R) := by
  intro u huS hu
  set s' := C.round src R s with hs'
  by_cases huR : u ∈ R
  · have hout : s'.out u = (C.unit (src u)).run (C.answer (C.ifaces s')) := by
      have h1 := ob.comp R src (C.ifaces s) u huR
      have h2 : s'.out u = C.group R src (C.ifaces s) u := by
        simp only [hs', round, huR, ite_true]
      rw [h2, h1, ← ifaces_round]
    refine ⟨hout, ?_⟩
    intro q hq
    have hU : s'.U u = C.keys u (s'.out u) ((C.unit (src u)).trace (C.answer (C.ifaces s'))) := by
      simp only [hs', round, huR, ite_true]; rfl
    rw [hU, hout]
    exact ob.coverage _ u _ q hq
  · have huI : u ∉ C.invalidated S R s s' :=
      fun h => hu (Finset.mem_sdiff.2 ⟨h, huR⟩)
    have huD : u ∉ D := fun h => huR (hD h)
    obtain ⟨hout, hcov⟩ := hInv u huS huD
    have hU : s'.U u = s.U u := by simp only [hs', round, huR, ite_false]
    have hout' : s'.out u = s.out u := by simp only [hs', round, huR, ite_false]
    have hiface : ∀ d, d ∉ R → C.ifaces s d = C.ifaces s' d := by
      intro d hd
      simp only [hs', ifaces, round, hd, ite_false, Function.comp]
    have hhash : ∀ p ∈ s.U u, C.π (C.ifaces s) p.1 p.2 = C.π (C.ifaces s') p.1 p.2 := by
      intro p hp
      by_cases haff : C.Affected R s p.1
      · by_contra hne
        apply huI
        simp only [invalidated, Finset.mem_filter]
        exact ⟨huS, p, hU ▸ hp, haff, hne⟩
      · apply ob.locality
        intro d hd
        apply hiface
        intro hdR
        exact haff (Or.inr ⟨d, hd, hdR⟩)
    have hagree : ∀ q ∈ (C.unit (src u)).trace (C.answer (C.ifaces s)),
        C.answer (C.ifaces s) q = C.answer (C.ifaces s') q := by
      intro q hq
      obtain ⟨k, hk, hcovers⟩ := hcov q hq
      exact (ob.abstraction _ _ k (hhash k hk) q hcovers).1
    obtain ⟨hrun, htrace⟩ := Task.run_eq_of_trace _ _ _ hagree
    refine ⟨?_, ?_⟩
    · rw [hout', hout, hrun]
    · rw [← htrace, hU]
      intro q hq
      obtain ⟨k, hk, hcovers⟩ := hcov q hq
      exact ⟨k, hk, (ob.abstraction _ _ k (hhash k hk) q hcovers).2⟩

/-- Zinc's loop with `Δ` over the affected units. -/
def zinc (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) :
    ℕ → ℕ → Finset CUnit → State CUnit Out K → Option (State CUnit Out K)
  | 0, _, _, _ => none
  | fuel + 1, n, R, s =>
    let s' := C.round src R s
    let I := C.invalidated S R s s'
    if I ⊆ R then some s' else zinc S src P fuel (n + 1) (P n R s s' I) s'

/-- **T3a.** If the loop stops, no unit is dirty. -/
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
      have : C.invalidated S R s (C.round src R s) \ R = ∅ :=
        Finset.sdiff_eq_empty_iff_subset.2 hsub
      rw [this] at hstep
      exact hstep
    · exact ih _ _ _ _ (hP _ _ _ _ _ (Finset.filter_subset _ _)) hstep s' h

/-! ## Termination under monotone policies (T4) -/

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

/-- **T4, monotone policies.** A policy monotone from round `k` on terminates within
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

end XCompiler
end Zinc

/-! ## The classpath: upstream subprojects, stored snapshots (T5)

`Classpath.lean`'s definitions and theorems, once, for the general form; `Classpath.lean` states
them for `NCompiler` as corollaries. -/

namespace Zinc.XCompiler

open Compiler (State Policy)

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : XCompiler CUnit Src Out Iface K Hash Q A)
variable [DecidableEq CUnit]

/-- The interfaces the stored snapshot describes: upstream units from `snap`, the rest from `s`. -/
def snapView (Up : Finset CUnit) (s : State CUnit Out K) (snap : CUnit → Iface) : CUnit → Iface :=
  fun u => if u ∈ Up then snap u else C.ifaces s u

/-- Every key a downstream unit outside `D` recorded hashes the same over the snapshot as over the
interfaces of the state it was compiled against. -/
def Fresh (Up S : Finset CUnit) (s : State CUnit Out K) (snap : CUnit → Iface)
    (D : Finset CUnit) : Prop :=
  ∀ d ∈ S, d ∉ D → ∀ k ∈ s.U d, C.π (C.snapView Up s snap) k.1 k.2 = C.π (C.ifaces s) k.1 k.2

/-- A new classpath: the upstream units get new outputs. -/
def withUpstream (Up : Finset CUnit) (s : State CUnit Out K) (o : CUnit → Out) : State CUnit Out K :=
  { s with out := fun u => if u ∈ Up then o u else s.out u }

variable [DecidableEq K] [DecidableEq Hash]

/-- Zinc's initial external invalidation: downstream units holding a key whose hash over the
snapshot differs from its hash over the new classpath. -/
def extInvalidated (Up S : Finset CUnit) (s : State CUnit Out K) (snap : CUnit → Iface)
    (s₁ : State CUnit Out K) : Finset CUnit :=
  S.filter fun d => ∃ k ∈ s.U d, C.π (C.snapView Up s snap) k.1 k.2 ≠ C.π (C.ifaces s₁) k.1 k.2

omit [DecidableEq K] [DecidableEq Hash] in
theorem withUpstream_out_of_not_mem (Up : Finset CUnit) (s : State CUnit Out K) (o : CUnit → Out)
    (u : CUnit) (hu : u ∉ Up) : (withUpstream Up s o).out u = s.out u := by
  simp [withUpstream, hu]

omit [DecidableEq K] in
/-- **T5a.** From an up-to-date downstream with fresh snapshots, the new classpath leaves dirty
only the changed sources and the holders of keys whose hash moved. -/
theorem inv_external (hab : C.Abstraction) (Up S : Finset CUnit) (hdisj : Disjoint Up S)
    (src₀ src : CUnit → Src) (s : State CUnit Out K) (snap : CUnit → Iface) (o : CUnit → Out)
    (D : Finset CUnit) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : C.Inv S src₀ s ∅) (hFresh : C.Fresh Up S s snap ∅) :
    C.Inv S src (withUpstream Up s o)
      (D ∪ C.extInvalidated Up S s snap (withUpstream Up s o)) := by
  intro u huS hu
  set s₁ := withUpstream Up s o
  have huD : u ∉ D := fun h => hu (Finset.mem_union_left _ h)
  have huE : u ∉ C.extInvalidated Up S s snap s₁ := fun h => hu (Finset.mem_union_right _ h)
  have hsrc : src₀ u = src u := by by_contra h; exact huD (hD u h)
  obtain ⟨hout, hcov⟩ := hInv u huS (Finset.notMem_empty u)
  rw [hsrc] at hout hcov
  have hhash : ∀ k ∈ s.U u, C.π (C.ifaces s) k.1 k.2 = C.π (C.ifaces s₁) k.1 k.2 := by
    intro k hk
    rw [← hFresh u huS (Finset.notMem_empty u) k hk]
    by_contra hne
    exact huE (Finset.mem_filter.2 ⟨huS, k, hk, hne⟩)
  have hagree : ∀ q ∈ (C.unit (src u)).trace (C.answer (C.ifaces s)),
      C.answer (C.ifaces s) q = C.answer (C.ifaces s₁) q := by
    intro q hq
    obtain ⟨k, hk, hc⟩ := hcov q hq
    exact (hab _ _ k (hhash k hk) q hc).1
  obtain ⟨hrun, htrace⟩ := Task.run_eq_of_trace _ _ _ hagree
  have huUp : u ∉ Up := fun h => Finset.disjoint_left.1 hdisj h huS
  refine ⟨?_, ?_⟩
  · show s₁.out u = _
    rw [withUpstream_out_of_not_mem Up s o u huUp, hout, hrun]
  · rw [← htrace]
    intro q hq
    obtain ⟨k, hk, hc⟩ := hcov q hq
    exact ⟨k, hk, (hab _ _ k (hhash k hk) q hc).2⟩

/-- **T5.** If the downstream loop, started from the changed sources and the external
invalidations, stops, every downstream unit is up to date against the new classpath. -/
theorem downstream_sound (ob : C.Obligations) (Up S : Finset CUnit) (hdisj : Disjoint Up S)
    (src₀ src : CUnit → Src) (s : State CUnit Out K) (snap : CUnit → Iface) (o : CUnit → Out)
    (D : Finset CUnit) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : C.Inv S src₀ s ∅) (hFresh : C.Fresh Up S s snap ∅)
    (P : Policy CUnit Out K) (hP : P.Sound S) (fuel : ℕ) (R₀ : Finset CUnit)
    (hR₀ : D ∪ C.extInvalidated Up S s snap (withUpstream Up s o) ⊆ R₀)
    (s' : State CUnit Out K) (h : C.zinc S src P fuel 0 R₀ (withUpstream Up s o) = some s') :
    C.Inv S src s' ∅ :=
  C.zinc_sound ob S src P hP fuel 0 R₀ _ _ hR₀
    (C.inv_external ob.abstraction Up S hdisj src₀ src s snap o D hD hInv hFresh) s' h

/-! ## Refreshing the snapshot -/

/-- Refresh every upstream unit. -/
def refreshAll (Up : Finset CUnit) (s' : State CUnit Out K) (snap : CUnit → Iface) :
    CUnit → Iface :=
  fun u => if u ∈ Up then C.ifaces s' u else snap u

/-- Zinc's rule: refresh the upstream units referenced by a key of a recompiled unit. -/
def refreshRef (Up Rc : Finset CUnit) (s' : State CUnit Out K) (snap : CUnit → Iface) :
    CUnit → Iface :=
  fun u => if u ∈ Up ∧ ∃ d ∈ Rc, ∃ k ∈ s'.U d, k.1 = u then C.ifaces s' u else snap u

omit [DecidableEq K] [DecidableEq Hash] in
theorem fresh_refreshAll (Up S : Finset CUnit) (s' : State CUnit Out K) (snap : CUnit → Iface) :
    C.Fresh Up S s' (C.refreshAll Up s' snap) ∅ := by
  intro d _ _ k _
  have : C.snapView Up s' (C.refreshAll Up s' snap) = C.ifaces s' := by
    funext u; simp only [snapView, refreshAll]; split <;> rfl
  rw [this]

/-- The loop leaves units outside `S` alone. -/
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
    have hr : (C.round src R s).out u = s.out u := by simp [round, hnot]
    split at h
    · cases h; exact hr
    · rw [ih _ _ _ (hP _ _ _ _ _ (Finset.filter_subset _ _)) s' h u hu, hr]

omit [DecidableEq K] in
/-- **Zinc's refresh rule is enough for local hashes.** If every hash reads only its own unit,
refreshing the upstream units referenced by recompiled units keeps the snapshots fresh. `Rc` is
the set of units recompiled in the build: it contains the external invalidations, and every
other unit keeps its keys. The snapshot before the build need not have been fresh: a unit that was
not invalidated has, by definition, the same hash over the snapshot as over the new classpath. -/
theorem fresh_refreshRef_local (ob : C.Obligations) (hloc : ∀ I c, C.hashDeps I c = {c})
    (Up S : Finset CUnit) (s : State CUnit Out K) (snap : CUnit → Iface) (o : CUnit → Out)
    (s' : State CUnit Out K) (Rc : Finset CUnit)
    (hUp : ∀ u ∈ Up, s'.out u = (withUpstream Up s o).out u)
    (hext : C.extInvalidated Up S s snap (withUpstream Up s o) ⊆ Rc)
    (hRc : ∀ d ∈ S, d ∉ Rc → s'.U d = s.U d) :
    C.Fresh Up S s' (C.refreshRef Up Rc s' snap) ∅ := by
  intro d hd _ k hk
  -- a hash depends on its own unit's interface only
  have hpt : ∀ I I' : CUnit → Iface, I k.1 = I' k.1 → C.π I k.1 k.2 = C.π I' k.1 k.2 := by
    intro I I' h
    apply ob.locality I I' k.1 _ k.2
    intro e he
    rw [hloc, Finset.mem_singleton] at he
    rw [he]; exact h
  by_cases hkUp : k.1 ∈ Up
  · by_cases href : ∃ d' ∈ Rc, ∃ k' ∈ s'.U d', k'.1 = k.1
    · apply hpt
      simp only [snapView, refreshRef, hkUp, href, and_self, ite_true]
    · have hdRc : d ∉ Rc := fun h => href ⟨d, h, k, hk, rfl⟩
      have hkU : k ∈ s.U d := by rw [← hRc d hd hdRc]; exact hk
      have hnot : d ∉ C.extInvalidated Up S s snap (withUpstream Up s o) := fun h => hdRc (hext h)
      have h2 : C.π (C.snapView Up s snap) k.1 k.2 = C.π (C.ifaces (withUpstream Up s o)) k.1 k.2 := by
        by_contra hne; exact hnot (Finset.mem_filter.2 ⟨hd, k, hkU, hne⟩)
      calc C.π (C.snapView Up s' (C.refreshRef Up Rc s' snap)) k.1 k.2
          = C.π (C.snapView Up s snap) k.1 k.2 := by
            apply hpt
            simp only [snapView, refreshRef, hkUp, href, and_false, ite_false, ite_true]
        _ = C.π (C.ifaces (withUpstream Up s o)) k.1 k.2 := h2
        _ = C.π (C.ifaces s') k.1 k.2 := by
            apply hpt
            simp only [ifaces, Function.comp, hUp k.1 hkUp]
  · apply hpt
    simp only [snapView, hkUp, ite_false]

end Zinc.XCompiler
