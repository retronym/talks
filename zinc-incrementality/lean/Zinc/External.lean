import Zinc.Tree

/-!
# The external path, once for every compiler shape

`Classpath.lean`'s T5a needs little of a compiler: a unit's task, run against the interfaces of all
units; a hash per key over those interfaces; which keys cover which queries; and abstraction. It
does not look at how keys are recorded (`Compiler.keys` reads the trace, `TCompiler.keysOf` the
output) nor at the loop. `View` is that much, and `inv_external` is proved here once.

`NCompiler.view` (`Classpath.lean`) and `TCompiler.view` (here) are views whose `UpToDate` and `Inv`
are their compiler's own, definitionally, so T5 for each is `View.inv_external` composed with that
compiler's T3a: `NCompiler.downstream_sound` and `TCompiler.downstream_sound`.
-/

namespace Zinc

open Compiler (State Policy)

/-- What the external path reads of a compiler. -/
structure View (CUnit Src Out Iface K Hash Q : Type) (A : Q → Type) where
  unit   : Src → Task (CUnit × Q) (fun p => A p.2) Out
  iface  : Out → Iface
  answer : (CUnit → Iface) → (q : CUnit × Q) → A q.2
  π      : (CUnit → Iface) → CUnit → K → Hash
  covers : (CUnit → Iface) → (CUnit × Q) → (CUnit × K) → Prop

namespace View

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (V : View CUnit Src Out Iface K Hash Q A)

def ifaces (s : State CUnit Out K) : CUnit → Iface := V.iface ∘ s.out

/-- Equal hashes on a key give equal answers to the queries it covers, and it still covers them. -/
def Abstraction : Prop :=
  ∀ (I I' : CUnit → Iface) (k : CUnit × K), V.π I k.1 k.2 = V.π I' k.1 k.2 →
    ∀ q, V.covers I q k → V.answer I q = V.answer I' q ∧ V.covers I' q k

def UpToDate (src : CUnit → Src) (s : State CUnit Out K) (u : CUnit) : Prop :=
  s.out u = (V.unit (src u)).run (V.answer (V.ifaces s)) ∧
  ∀ q ∈ (V.unit (src u)).trace (V.answer (V.ifaces s)), ∃ k ∈ s.U u, V.covers (V.ifaces s) q k

def Inv (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) (D : Finset CUnit) : Prop :=
  ∀ u ∈ S, u ∉ D → V.UpToDate src s u

variable [DecidableEq CUnit]

/-- The interfaces the stored snapshot describes: upstream units from `snap`, the rest from `s`. -/
def snapView (Up : Finset CUnit) (s : State CUnit Out K) (snap : CUnit → Iface) : CUnit → Iface :=
  fun u => if u ∈ Up then snap u else V.ifaces s u

/-- Every key a downstream unit outside `D` recorded hashes the same over the snapshot as over the
interfaces it was compiled against. -/
def Fresh (Up S : Finset CUnit) (s : State CUnit Out K) (snap : CUnit → Iface)
    (D : Finset CUnit) : Prop :=
  ∀ d ∈ S, d ∉ D → ∀ k ∈ s.U d, V.π (V.snapView Up s snap) k.1 k.2 = V.π (V.ifaces s) k.1 k.2

/-- A new classpath: the upstream units get new outputs. -/
def withUpstream (Up : Finset CUnit) (s : State CUnit Out K) (o : CUnit → Out) : State CUnit Out K :=
  { s with out := fun u => if u ∈ Up then o u else s.out u }

variable [DecidableEq Hash]

/-- Zinc's initial external invalidation: downstream units holding a key whose hash over the
snapshot differs from its hash over the new classpath. -/
def extInvalidated (Up S : Finset CUnit) (s : State CUnit Out K) (snap : CUnit → Iface)
    (s₁ : State CUnit Out K) : Finset CUnit :=
  S.filter fun d => ∃ k ∈ s.U d, V.π (V.snapView Up s snap) k.1 k.2 ≠ V.π (V.ifaces s₁) k.1 k.2

/-- **T5a.** From an up-to-date downstream with fresh snapshots, the new classpath leaves dirty
only the changed sources and the holders of keys whose hash moved. -/
theorem inv_external (hab : V.Abstraction) (Up S : Finset CUnit) (hdisj : Disjoint Up S)
    (src₀ src : CUnit → Src) (s : State CUnit Out K) (snap : CUnit → Iface) (o : CUnit → Out)
    (D : Finset CUnit) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : V.Inv S src₀ s ∅) (hFresh : V.Fresh Up S s snap ∅) :
    V.Inv S src (withUpstream Up s o) (D ∪ V.extInvalidated Up S s snap (withUpstream Up s o)) := by
  intro u huS hu
  set s₁ := withUpstream Up s o
  have huD : u ∉ D := fun h => hu (Finset.mem_union_left _ h)
  have huE : u ∉ V.extInvalidated Up S s snap s₁ := fun h => hu (Finset.mem_union_right _ h)
  have hsrc : src₀ u = src u := by by_contra h; exact huD (hD u h)
  obtain ⟨hout, hcov⟩ := hInv u huS (Finset.notMem_empty u)
  rw [hsrc] at hout hcov
  have hhash : ∀ k ∈ s.U u, V.π (V.ifaces s) k.1 k.2 = V.π (V.ifaces s₁) k.1 k.2 := by
    intro k hk
    rw [← hFresh u huS (Finset.notMem_empty u) k hk]
    by_contra hne
    exact huE (Finset.mem_filter.2 ⟨huS, k, hk, hne⟩)
  have hagree : ∀ q ∈ (V.unit (src u)).trace (V.answer (V.ifaces s)),
      V.answer (V.ifaces s) q = V.answer (V.ifaces s₁) q := by
    intro q hq
    obtain ⟨k, hk, hc⟩ := hcov q hq
    exact (hab _ _ k (hhash k hk) q hc).1
  obtain ⟨hrun, htrace⟩ := Task.run_eq_of_trace _ _ _ hagree
  have huUp : u ∉ Up := fun h => Finset.disjoint_left.1 hdisj h huS
  have hout₁ : s₁.out u = s.out u := by simp [s₁, withUpstream, huUp]
  refine ⟨?_, ?_⟩
  · show s₁.out u = _
    rw [hout₁, hout, hrun]
  · rw [← htrace]
    intro q hq
    obtain ⟨k, hk, hc⟩ := hcov q hq
    exact ⟨k, hk, (hab _ _ k (hhash k hk) q hc).2⟩

end View

/-! ## `TCompiler` -/

namespace TCompiler

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : TCompiler CUnit Src Out Iface K Hash Q A)

/-- A `TCompiler`'s answers and hashes read one interface; a key covers a query to its own unit. -/
def view : View CUnit Src Out Iface K Hash Q A where
  unit := C.unit
  iface := C.iface
  answer := fun I q => C.answer (I q.1) q.2
  π := fun I c k => C.π (I c) k
  covers := fun _ q k => q.1 = k.1 ∧ C.covers q.2 k.2

theorem inv_view (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) (D : Finset CUnit) :
    C.view.Inv S src s D ↔ C.Inv S src s D := Iff.rfl

variable [DecidableEq CUnit]

theorem view_abstraction (ob : C.Obligations) : C.view.Abstraction := by
  intro I I' k h q hc
  obtain ⟨hq, hcov⟩ := hc
  refine ⟨?_, hq, hcov⟩
  show C.answer (I q.1) q.2 = C.answer (I' q.1) q.2
  rw [hq]
  exact ob.abstraction _ _ k.2 h q.2 hcov

variable [DecidableEq K] [DecidableEq Hash]

/-- **T5 for a `TCompiler`.** If the downstream loop, started from the changed sources and the
external invalidations, stops, every downstream unit is up to date against the new classpath. -/
theorem downstream_sound (ob : C.Obligations) (Up S : Finset CUnit) (hdisj : Disjoint Up S)
    (src₀ src : CUnit → Src) (s : State CUnit Out K) (snap : CUnit → Iface) (o : CUnit → Out)
    (D : Finset CUnit) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : C.Inv S src₀ s ∅) (hFresh : C.view.Fresh Up S s snap ∅)
    (P : Policy CUnit Out K) (hP : P.Sound S) (fuel : ℕ) (R₀ : Finset CUnit)
    (hR₀ : D ∪ C.view.extInvalidated Up S s snap (View.withUpstream Up s o) ⊆ R₀)
    (s' : State CUnit Out K) (h : C.zinc S src P fuel 0 R₀ (View.withUpstream Up s o) = some s') :
    C.Inv S src s' ∅ :=
  C.zinc_sound ob S src P hP fuel 0 R₀ _ _ hR₀
    (C.view.inv_external (C.view_abstraction ob) Up S hdisj src₀ src s snap o D hD hInv hFresh) s' h

end TCompiler
end Zinc
