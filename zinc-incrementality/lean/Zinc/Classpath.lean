import Zinc.NonLocalAns
import Zinc.Uniqueness

/-!
# The classpath: upstream subprojects, stored snapshots, libraries

A downstream project `S` compiles against the outputs of upstream units `Up` (another subproject,
or a library). Zinc does not see the upstream's build: it stores, in the downstream Analysis, a
*snapshot* of each upstream class's API (`apis.external`), and at the start of the next build
diffs every snapshot against the upstream's current API (`IncrementalCommon.detectAPIChanges`).
The downstream units holding a changed key start the loop (`invalidateClassesExternally`). A
library is the same, with a stamp (a content hash of the JAR or classfile) as the hash of every
key on it.

The snapshot is part of the downstream's state, and its correctness is a run invariant:

* `Fresh`: every key an up-to-date downstream unit recorded hashes the same over the snapshot as
  over the interfaces the unit was compiled against.

Results:

* **T5a** (`inv_external`): from an up-to-date downstream with fresh snapshots, replacing the
  upstream outputs and invalidating the holders of keys whose hash moved (plus changed sources)
  re-establishes the round invariant. **T5** (`downstream_sound`): with T3a″, if the downstream
  loop stops, the downstream is up to date against the new upstream.
* **Refreshing the snapshot.** Zinc refreshes an upstream class's snapshot when a recompiled
  source references it (`Analysis.addSource` → `markExternalAPI`), `refreshRef`.
  - `fresh_refreshAll`: refreshing every upstream unit keeps the snapshots fresh, whatever the
    hashes.
  - `fresh_refreshRef_local`: with local hashes (`hashDeps c = {c}`, Zinc today: an upstream
    class's stored API is its own), Zinc's rule keeps them fresh.
  - With non-local hashes (a key on `C` whose hash reads its ancestor `A`, as in the Merkle PoC's
    composition across subprojects), Zinc's rule is not enough: `Snapshot.lean` has the two-build
    counterexample (edit `A`, then revert it).
-/

namespace Zinc.NCompiler

/-! The definitions and theorems are `XCompiler`'s (`General.lean`), stated here for `NCompiler`
through its lift. -/

open Compiler (State Policy)

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : NCompiler CUnit Src Out Iface K Hash Q A)
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
theorem inv_external (ob : C.Obligations) (Up S : Finset CUnit) (hdisj : Disjoint Up S)
    (src₀ src : CUnit → Src) (s : State CUnit Out K) (snap : CUnit → Iface) (o : CUnit → Out)
    (D : Finset CUnit) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : C.Inv S src₀ s ∅) (hFresh : C.Fresh Up S s snap ∅) :
    C.Inv S src (withUpstream Up s o)
      (D ∪ C.extInvalidated Up S s snap (withUpstream Up s o)) :=
  C.toX.inv_external (C.toX_obligations ob).abstraction Up S hdisj src₀ src s snap o D hD hInv hFresh

variable [Fintype CUnit]

/-- **T5.** If the downstream loop, started from the changed sources and the external
invalidations, stops, every downstream unit is up to date against the new classpath. -/
theorem downstream_sound (ob : C.Obligations) (Up S : Finset CUnit) (hdisj : Disjoint Up S)
    (src₀ src : CUnit → Src) (s : State CUnit Out K) (snap : CUnit → Iface) (o : CUnit → Out)
    (D : Finset CUnit) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : C.Inv S src₀ s ∅) (hFresh : C.Fresh Up S s snap ∅)
    (P : Policy CUnit Out K) (hP : P.Sound S) (fuel : ℕ) (R₀ : Finset CUnit)
    (hR₀ : D ∪ C.extInvalidated Up S s snap (withUpstream Up s o) ⊆ R₀)
    (s' : State CUnit Out K) (h : C.zinc S src P fuel 0 R₀ (withUpstream Up s o) = some s') :
    C.Inv S src s' ∅ := by
  rw [← zinc_toX] at h
  exact C.toX.downstream_sound (C.toX_obligations ob) Up S hdisj src₀ src s snap o D hD hInv hFresh
    P hP fuel R₀ hR₀ s' h

/-! ## Refreshing the snapshot -/

/-- Refresh every upstream unit. -/
def refreshAll (Up : Finset CUnit) (s' : State CUnit Out K) (snap : CUnit → Iface) :
    CUnit → Iface :=
  fun u => if u ∈ Up then C.ifaces s' u else snap u

/-- Zinc's rule: refresh the upstream units referenced by a key of a recompiled unit. -/
def refreshRef (Up Rc : Finset CUnit) (s' : State CUnit Out K) (snap : CUnit → Iface) :
    CUnit → Iface :=
  fun u => if u ∈ Up ∧ ∃ d ∈ Rc, ∃ k ∈ s'.U d, k.1 = u then C.ifaces s' u else snap u

omit [DecidableEq K] [DecidableEq Hash] [Fintype CUnit] in
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
  intro fuel n R s hR s' h
  rw [← zinc_toX] at h
  exact C.toX.zinc_out_outside S src P hP fuel n R s hR s' h

omit [DecidableEq K] [Fintype CUnit] in
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
    C.Fresh Up S s' (C.refreshRef Up Rc s' snap) ∅ :=
  C.toX.fresh_refreshRef_local (C.toX_obligations ob) hloc Up S s snap o s' Rc hUp hext hRc

end Zinc.NCompiler
