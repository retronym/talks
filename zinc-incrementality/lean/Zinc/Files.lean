import Zinc.General
import Zinc.SplitProof

/-!
# Files as a layer (`PLAN-files.md`)

Zinc recompiles source files and records keys per class. This file adds files to the general form
`XCompiler` without changing it.

* **A file map** `file : CUnit → File`. Every existing instance has one class per file (`file :=
  id`), and nothing changes for it (`closed_id`).
* **Rounds are closed under files** as a property of the policy (`Policy.FileClosed`), not a change
  to the loop: Zinc's class-to-source-to-classes step is a policy that returns file-closed sets.
* **Charging.** A top-level import is a query of every class of the file, but Zinc records its key
  on one class, `charge : File → CUnit` (the first in Scala 2, the last in Scala 3). Charged
  coverage (`ChargedCoverage`) asks that every query of a class be covered by a key of the class or
  of its file's representative. It is implied by plain coverage (`charged_of_obligations`).
* **T2 and T3a under charging** (`round_preserves_charged`, `zinc_sound_charged`): with a file-closed
  first round and a file-closed sound policy, a class whose representative's key moved is dirty
  exactly when the representative is, and the representative is recompiled with it. For an
  instance meeting the plain obligations, `XCompiler.zinc_sound` applies unchanged, whatever the
  file map and the policy.
* **T5 under charging** (`inv_external_charged`, `downstream_sound_charged`): the snapshot results
  with the charged invariant. Freshness is the plain one, and Zinc's per-class external
  invalidation, closed under files, contains the charged one (`extInvalidatedCharged_subset`).

Two witnesses, both kernel `decide` or `simp` on concrete programs:

* **F3** (`FileSpec`): `Spec`'s lookup with a two-class client file. `Client` looks the name up
  through a wildcard import; `Other` (the file's first class in Scala 2, its last in Scala 3) does
  not use the name. Today's charging records the import on `Other`, filtered by `Other`'s used
  names, so nothing covers `Client`'s miss on the imported scope: charged coverage fails
  (`today_not_charged`). The fix, the import charged to every class of the file, meets the plain
  obligations for every program whose scopes are pinned or wildcard-imported (`every_obligations`),
  hence T3a (`every_sound`).
* **sbt/zinc#417** (`Fi`): `A` and `B extends A` share a file, `C extends B` is in another. The
  bridge drops the inheritance edge between `A` and `B`, so `C`'s inheritance key on `B` does not
  reach `A`, which lowering `C` reads (`fi_not_covered`; the dropped edge is a same-file one). With
  the edge kept, the key covers it. From an up-to-date build, an edit to `A` recompiles `A` and `B`
  (a file-closed round) and stops: `C` keeps output computed against the old `A` (`fi_loop`); with
  the edge kept, the loop recompiles `C` (`fi_loop_kept`). Keeping the edge meets the plain
  obligations for every program (`kept_obligations`), hence T3a (`kept_sound`).
-/

namespace Zinc.XCompiler

open Compiler (State Policy)

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : XCompiler CUnit Src Out Iface K Hash Q A)
variable [DecidableEq CUnit]
variable [DecidableEq K]
variable {File : Type} (file : CUnit → File) (charge : File → CUnit)

/-- `R` is closed under files: it contains every class of a file it touches. -/
def Closed (R : Finset CUnit) : Prop := ∀ u v, file u = file v → u ∈ R → v ∈ R

/-- One class per file: every set is closed. -/
theorem closed_id (R : Finset CUnit) : Closed id R := fun u v h hu => by
  simp only [id] at h; exact h ▸ hu

/-- Charged coverage: a query of class `d` is covered by a key `d` records, or by one its file's
representative `charge (file d)` records, each computed in the same program. -/
def ChargedCoverage : Prop :=
  ∀ (I : CUnit → Iface) (src : CUnit → Src) (d : CUnit),
    ∀ q ∈ (C.unit (src d)).trace (C.answer I),
      ∃ k ∈ C.keys d ((C.unit (src d)).run (C.answer I)) ((C.unit (src d)).trace (C.answer I)) ∪
          C.keys (charge (file d)) ((C.unit (src (charge (file d)))).run (C.answer I))
            ((C.unit (src (charge (file d)))).trace (C.answer I)),
        C.covers I q k

/-- The obligations with charged coverage in place of coverage. -/
structure Charged : Prop where
  comp : ∀ (G : Finset CUnit) (src : CUnit → Src) (I : CUnit → Iface), ∀ d ∈ G,
    C.group G src I d = (C.unit (src d)).run (C.answer (override I G (C.iface ∘ C.group G src I)))
  coverage : C.ChargedCoverage file charge
  abstraction : C.Abstraction
  locality : ∀ (I I' : CUnit → Iface) (c : CUnit), (∀ d ∈ C.hashDeps I c, I d = I' d) →
    ∀ k, C.π I c k = C.π I' c k

/-- Plain coverage implies charged coverage, for every file map and charge. -/
theorem charged_of_obligations (ob : C.Obligations) : C.Charged file charge where
  comp := ob.comp
  coverage I src d q hq := by
    obtain ⟨k, hk, hc⟩ := ob.coverage I d (src d) q hq
    exact ⟨k, Finset.mem_union_left _ hk, hc⟩
  abstraction := ob.abstraction
  locality := ob.locality

def UpToDateCharged (src : CUnit → Src) (s : State CUnit Out K) (u : CUnit) : Prop :=
  s.out u = (C.unit (src u)).run (C.answer (C.ifaces s)) ∧
  ∀ q ∈ (C.unit (src u)).trace (C.answer (C.ifaces s)),
    ∃ k ∈ s.U u ∪ s.U (charge (file u)), C.covers (C.ifaces s) q k

def InvCharged (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) (D : Finset CUnit) :
    Prop :=
  ∀ u ∈ S, u ∉ D → C.UpToDateCharged file charge src s u

variable [DecidableEq Hash]

/-- The classes holding, themselves or through their representative, a key that moved. -/
def invalidatedCharged (S R : Finset CUnit) (s s' : State CUnit Out K) : Finset CUnit :=
  S.filter fun d => ∃ p ∈ s'.U d ∪ s'.U (charge (file d)), C.changed R s s' p

/-- **T2 under charging.** With a file-closed round, one round preserves the charged invariant, with
`Δ` over the classes whose own or charged keys moved. -/
theorem round_preserves_charged (ob : C.Charged file charge) (hcf : ∀ f, file (charge f) = f)
    (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) (D R : Finset CUnit)
    (hD : D ⊆ R) (hR : Closed file R) (hInv : C.InvCharged file charge S src s D) :
    C.InvCharged file charge S src (C.round src R s)
      (C.invalidatedCharged file charge S R s (C.round src R s) \ R) := by
  intro u huS hu
  set s' := C.round src R s with hs'
  set c := charge (file u)
  have hcu : file c = file u := hcf _
  have hout_of : ∀ v ∈ R, s'.out v = (C.unit (src v)).run (C.answer (C.ifaces s')) := by
    intro v hv
    have h1 := ob.comp R src (C.ifaces s) v hv
    have h2 : s'.out v = C.group R src (C.ifaces s) v := by simp only [hs', round, hv, ite_true]
    rw [h2, h1, ← ifaces_round]
  have hU_of : ∀ v ∈ R, s'.U v =
      C.keys v (s'.out v) ((C.unit (src v)).trace (C.answer (C.ifaces s'))) := by
    intro v hv
    simp only [hs', round, hv, ite_true]; rfl
  by_cases huR : u ∈ R
  · have hcR : c ∈ R := hR u c hcu.symm huR
    refine ⟨hout_of u huR, ?_⟩
    intro q hq
    rw [hU_of u huR, hU_of c hcR, hout_of u huR, hout_of c hcR]
    exact ob.coverage _ src u q hq
  · have hcR : c ∉ R := fun h => huR (hR c u hcu h)
    have huI : u ∉ C.invalidatedCharged file charge S R s s' :=
      fun h => hu (Finset.mem_sdiff.2 ⟨h, huR⟩)
    have huD : u ∉ D := fun h => huR (hD h)
    obtain ⟨hout, hcov⟩ := hInv u huS huD
    have hUu : s'.U u = s.U u := by simp only [hs', round, huR, ite_false]
    have hUc : s'.U c = s.U c := by simp only [hs', round, hcR, ite_false]
    have hU : s'.U u ∪ s'.U c = s.U u ∪ s.U c := by rw [hUu, hUc]
    have hout' : s'.out u = s.out u := by simp only [hs', round, huR, ite_false]
    have hiface : ∀ d, d ∉ R → C.ifaces s d = C.ifaces s' d := by
      intro d hd
      simp only [hs', ifaces, round, hd, ite_false, Function.comp]
    have hhash : ∀ p ∈ s.U u ∪ s.U c, C.π (C.ifaces s) p.1 p.2 = C.π (C.ifaces s') p.1 p.2 := by
      intro p hp
      by_cases haff : C.Affected R s p.1
      · by_contra hne
        apply huI
        simp only [invalidatedCharged, Finset.mem_filter]
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

/-- A policy is file-closed when every round it chooses is. -/
def _root_.Zinc.Compiler.Policy.FileClosed (P : Policy CUnit Out K) : Prop :=
  ∀ n R s s' I, Closed file (P n R s s' I)

/-- **T3a under charging.** Hypotheses: the charged obligations; every representative is a class
of its file, and of `S` when its file has a class in `S`; the first round contains the dirty set
and is file-closed; the policy is sound and file-closed. If the loop stops, no class is dirty. -/
theorem zinc_sound_charged (ob : C.Charged file charge) (hcf : ∀ f, file (charge f) = f)
    (S : Finset CUnit) (hS : ∀ d ∈ S, charge (file d) ∈ S) (src : CUnit → Src)
    (P : Policy CUnit Out K) (hP : P.Sound S) (hPF : P.FileClosed file) :
    ∀ (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K) (D : Finset CUnit),
      D ⊆ R → Closed file R → C.InvCharged file charge S src s D →
      ∀ s', C.zinc S src P fuel n R s = some s' → C.InvCharged file charge S src s' ∅ := by
  intro fuel
  induction fuel with
  | zero => intro n R s D _ _ _ s' h; simp [zinc] at h
  | succ fuel ih =>
    intro n R s D hD hR hInv s' h
    simp only [zinc] at h
    have hstep := C.round_preserves_charged file charge ob hcf S src s D R hD hR hInv
    set s₁ := C.round src R s
    set I := C.invalidated S R s s₁
    have hsplit : ∀ d ∈ C.invalidatedCharged file charge S R s s₁, d ∉ R →
        d ∈ I ∨ (charge (file d) ∈ I ∧ charge (file d) ∉ R) := by
      intro d hd hdR
      obtain ⟨hdS, p, hp, hch⟩ := Finset.mem_filter.1 hd
      rcases Finset.mem_union.1 hp with hp | hp
      · exact .inl (Finset.mem_filter.2 ⟨hdS, p, hp, hch⟩)
      · refine .inr ⟨Finset.mem_filter.2 ⟨hS d hdS, p, hp, hch⟩, fun hc => hdR ?_⟩
        exact hR _ d (hcf _) hc
    split at h
    · rename_i hsub
      rw [← Option.some.inj h]
      have : C.invalidatedCharged file charge S R s s₁ \ R = ∅ := by
        rw [Finset.sdiff_eq_empty_iff_subset]
        intro d hd
        by_contra hdR
        rcases hsplit d hd hdR with h | ⟨h, hc⟩
        · exact hdR (hsub h)
        · exact hc (hsub h)
      rw [this] at hstep
      exact hstep
    · refine ih _ _ _ _ ?_ (hPF _ _ _ _ _) hstep s' h
      intro d hd
      obtain ⟨hd, hdR⟩ := Finset.mem_sdiff.1 hd
      have hIS : I ⊆ S := Finset.filter_subset _ _
      rcases hsplit d hd hdR with h | ⟨h, hc⟩
      · exact hP _ _ _ _ _ hIS (Finset.mem_sdiff.2 ⟨h, hdR⟩)
      · exact hPF _ _ _ _ _ _ d (hcf _) (hP _ _ _ _ _ hIS (Finset.mem_sdiff.2 ⟨h, hc⟩))

/-! ## T5 under charging -/

/-- Zinc's initial external invalidation under charging: downstream classes holding, themselves or
through their representative, a key whose hash over the snapshot differs from its hash over the
new classpath. -/
def extInvalidatedCharged (Up S : Finset CUnit) (s : State CUnit Out K) (snap : CUnit → Iface)
    (s₁ : State CUnit Out K) : Finset CUnit :=
  S.filter fun d => ∃ k ∈ s.U d ∪ s.U (charge (file d)),
    C.π (C.snapView Up s snap) k.1 k.2 ≠ C.π (C.ifaces s₁) k.1 k.2

/-- Zinc's per-class external invalidation, closed under files, contains the charged one. -/
theorem extInvalidatedCharged_subset (hcf : ∀ f, file (charge f) = f) (Up S : Finset CUnit)
    (hS : ∀ d ∈ S, charge (file d) ∈ S) (s : State CUnit Out K) (snap : CUnit → Iface)
    (s₁ : State CUnit Out K) (R : Finset CUnit) (hR : Closed file R)
    (h : C.extInvalidated Up S s snap s₁ ⊆ R) :
    C.extInvalidatedCharged file charge Up S s snap s₁ ⊆ R := by
  intro d hd
  obtain ⟨hdS, k, hk, hne⟩ := Finset.mem_filter.1 hd
  rcases Finset.mem_union.1 hk with hk | hk
  · exact h (Finset.mem_filter.2 ⟨hdS, k, hk, hne⟩)
  · exact hR _ d (hcf _) (h (Finset.mem_filter.2 ⟨hS d hdS, k, hk, hne⟩))

/-- **T5a under charging.** From a downstream up to date under charging, with fresh snapshots, the
new classpath leaves dirty only the changed sources and the classes whose own or charged keys
moved. Freshness is the plain one: a representative is a class of `S`. -/
theorem inv_external_charged (hab : C.Abstraction) (Up S : Finset CUnit) (hdisj : Disjoint Up S)
    (hS : ∀ d ∈ S, charge (file d) ∈ S)
    (src₀ src : CUnit → Src) (s : State CUnit Out K) (snap : CUnit → Iface) (o : CUnit → Out)
    (D : Finset CUnit) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : C.InvCharged file charge S src₀ s ∅) (hFresh : C.Fresh Up S s snap ∅) :
    C.InvCharged file charge S src (withUpstream Up s o)
      (D ∪ C.extInvalidatedCharged file charge Up S s snap (withUpstream Up s o)) := by
  intro u huS hu
  set s₁ := withUpstream Up s o
  set c := charge (file u)
  have huD : u ∉ D := fun h => hu (Finset.mem_union_left _ h)
  have huE : u ∉ C.extInvalidatedCharged file charge Up S s snap s₁ :=
    fun h => hu (Finset.mem_union_right _ h)
  have hsrc : src₀ u = src u := by by_contra h; exact huD (hD u h)
  obtain ⟨hout, hcov⟩ := hInv u huS (Finset.notMem_empty u)
  rw [hsrc] at hout hcov
  have hfresh : ∀ k ∈ s.U u ∪ s.U c,
      C.π (C.snapView Up s snap) k.1 k.2 = C.π (C.ifaces s) k.1 k.2 := by
    intro k hk
    rcases Finset.mem_union.1 hk with hk | hk
    · exact hFresh u huS (Finset.notMem_empty u) k hk
    · exact hFresh c (hS u huS) (Finset.notMem_empty c) k hk
  have hhash : ∀ k ∈ s.U u ∪ s.U c, C.π (C.ifaces s) k.1 k.2 = C.π (C.ifaces s₁) k.1 k.2 := by
    intro k hk
    rw [← hfresh k hk]
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

/-- **T5 under charging.** Hypotheses as `zinc_sound_charged`'s, with the first round containing
the changed sources and Zinc's per-class external invalidations, and closed under files. If the
downstream loop stops, every downstream class is up to date against the new classpath. -/
theorem downstream_sound_charged (ob : C.Charged file charge) (hcf : ∀ f, file (charge f) = f)
    (Up S : Finset CUnit) (hdisj : Disjoint Up S) (hS : ∀ d ∈ S, charge (file d) ∈ S)
    (src₀ src : CUnit → Src) (s : State CUnit Out K) (snap : CUnit → Iface) (o : CUnit → Out)
    (D : Finset CUnit) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : C.InvCharged file charge S src₀ s ∅) (hFresh : C.Fresh Up S s snap ∅)
    (P : Policy CUnit Out K) (hP : P.Sound S) (hPF : P.FileClosed file) (fuel : ℕ)
    (R₀ : Finset CUnit) (hR₀ : D ∪ C.extInvalidated Up S s snap (withUpstream Up s o) ⊆ R₀)
    (hR₀F : Closed file R₀)
    (s' : State CUnit Out K) (h : C.zinc S src P fuel 0 R₀ (withUpstream Up s o) = some s') :
    C.InvCharged file charge S src s' ∅ :=
  C.zinc_sound_charged file charge ob hcf S hS src P hP hPF fuel 0 R₀ _ _
    (Finset.union_subset (Finset.union_subset_left hR₀)
      (C.extInvalidatedCharged_subset file charge hcf Up S hS s snap _ R₀ hR₀F
        (Finset.union_subset_right hR₀)))
    hR₀F (C.inv_external_charged file charge ob.abstraction Up S hdisj hS src₀ src s snap o D hD
      hInv hFresh) s' h

end Zinc.XCompiler

/-! ## F3: a two-class client file on `Spec`'s lookup -/

namespace Zinc.FileSpec

open SplitProof

variable {n : ℕ}

/-- Units: `none` is `Other`, the class of the client's file that does not use the name; `some u`
is `Spec`'s unit `u` (`some none` the client, `some (some i)` scope `i`). -/
abbrev FU (n : ℕ) := Option (Spec.U n)

inductive FSrc (n : ℕ)
  | spec (s : Spec.Src)
  | other

def liftQ (q : Spec.U n × Spec.Q) : FU n × Spec.Q := (some q.1, q.2)

def lift {α : Type} : Task (Spec.U n × Spec.Q) (fun _ => Bool) α → Task (FU n × Spec.Q) (fun _ => Bool) α
  | .pure a => .pure a
  | .ask q k => .ask (liftQ q) fun x => lift (k x)

theorem run_lift {α : Type} (e : FU n × Spec.Q → Bool) :
    ∀ t : Task (Spec.U n × Spec.Q) (fun _ => Bool) α, (lift t).run e = t.run (e ∘ liftQ)
  | .pure _ => rfl
  | .ask q k => by simp only [lift, Task.run_ask]; exact run_lift e (k (e (liftQ q)))

theorem trace_lift {α : Type} (e : FU n × Spec.Q → Bool) :
    ∀ t : Task (Spec.U n × Spec.Q) (fun _ => Bool) α, (lift t).trace e = (t.trace (e ∘ liftQ)).map liftQ
  | .pure _ => rfl
  | .ask q k => by
    simp only [lift, Task.trace_ask, List.map_cons]
    exact congrArg _ (trace_lift e (k (e (liftQ q))))

def unit : FSrc n → Task (FU n × Spec.Q) (fun _ => Bool) Spec.Out
  | .spec s => lift (Spec.unit n s)
  | .other => .pure ⟨false, none⟩

def ifaceSrc : FSrc n → Bool
  | .spec s => Spec.ifaceSrc s
  | .other => false

def answer (I : FU n → Bool) (q : FU n × Spec.Q) : Bool := I q.1

theorem iface_unit (s : FSrc n) (e : FU n × Spec.Q → Bool) : ((unit s).run e).iface = ifaceSrc s := by
  cases s with
  | spec s => rw [unit, run_lift]; exact Spec.iface_run s _
  | other => rfl

def group (G : Finset (FU n)) (src : FU n → FSrc n) (I : FU n → Bool) : FU n → Spec.Out :=
  fun u => (unit (src u)).run (answer fun v => if v ∈ G then ifaceSrc (src v) else I v)

/-- The client's file is `none`; scope `i` is its own file. -/
def file : FU n → Option (Fin n)
  | none => none
  | some none => none
  | some (some i) => some i

/-- Today's representative of the client's file: `Other`, the first class (Scala 2) or the last
(Scala 3), which is not the client. -/
def charge : Option (Fin n) → FU n
  | none => none
  | some i => some (some i)

theorem charge_file (f : Option (Fin n)) : file (charge f) = f := by cases f <;> rfl

/-- Today: an existence key on the resolved scope and on the pinned ones. Every class: also on each
wildcard-imported scope its lookup asked. -/
inductive Design | today | every
  deriving DecidableEq

variable (pinned imported : Fin n → Bool)

def pinnedKeys : Finset (FU n × Unit) :=
  ((List.finRange n).filter pinned).map (fun i => (some (some i), ())) |>.toFinset

def keys : Design → List (FU n × Spec.Q) → Finset (FU n × Unit)
  | .today, tr => (tr.getLast?.map fun q => (q.1, ())).toList.toFinset ∪ pinnedKeys pinned
  | .every, tr => (tr.getLast?.map fun q => (q.1, ())).toList.toFinset ∪ pinnedKeys pinned ∪
      ((tr.filter fun q => match q.1 with | some (some i) => imported i | _ => false).map
        fun q => (q.1, ())).toFinset

def compiler (d : Design) :
    XCompiler (FU n) (FSrc n) Spec.Out Bool Unit Bool Spec.Q (fun _ => Bool) where
  unit := unit
  group := group
  iface := Spec.Out.iface
  answer := answer
  π I u _ := I u
  hashDeps _ u := {u}
  keys _ _ tr := keys pinned imported d tr
  covers _ q k := q.1 = k.1

theorem comp (d : Design) : ∀ (G : Finset (FU n)) (src : FU n → FSrc n) (I : FU n → Bool), ∀ u ∈ G,
    (compiler pinned imported d).group G src I u =
      ((compiler pinned imported d).unit (src u)).run ((compiler pinned imported d).answer
        (XCompiler.override I G ((compiler pinned imported d).iface ∘ (compiler pinned imported d).group G src I))) := by
  intro G src I u _
  simp only [compiler, group]
  congr 2
  funext v
  simp only [XCompiler.override, compiler, Function.comp, group, iface_unit]

theorem abstraction (d : Design) : (compiler pinned imported d).Abstraction := by
  intro I I' k h q hc
  exact ⟨by simp only [compiler, answer] at h hc ⊢; rw [hc]; exact h, hc⟩

theorem locality (d : Design) (I I' : FU n → Bool) (c : FU n)
    (h : ∀ u ∈ (compiler pinned imported d).hashDeps I c, I u = I' u) (k : Unit) :
    (compiler pinned imported d).π I c k = (compiler pinned imported d).π I' c k :=
  h c (Finset.mem_singleton_self c)

/-- The client's queries: a scope, and if it binds, the last query. -/
theorem trace_unit (I : FU n → Bool) (s : FSrc n) :
    ∀ q ∈ (unit s).trace (answer I), ∃ i, q = (some (some i), Spec.Q.binds) ∧
      (I (some (some i)) = true → ((unit s).trace (answer I)).getLast? = some q) := by
  intro q hq
  cases s with
  | other => simp [unit] at hq
  | spec s =>
    have he : answer I ∘ liftQ = Spec.answer (fun u => I (some u)) := rfl
    simp only [unit, trace_lift, he] at hq ⊢
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    obtain ⟨i, rfl, hlast⟩ := Spec.trace_unit (fun u => I (some u)) s q' hq'
    refine ⟨i, rfl, fun hI => ?_⟩
    rw [List.getLast?_map, hlast hI]
    rfl

/-- **The fix meets the obligations**: the import charged to every class of the file, for every
program whose scopes are pinned or wildcard-imported. -/
theorem every_obligations (hk : ∀ i, pinned i = true ∨ imported i = true) :
    (compiler pinned imported .every).Obligations where
  comp := comp pinned imported .every
  coverage I _ s q hq := by
    obtain ⟨i, rfl, hlast⟩ := trace_unit I s q hq
    refine ⟨(some (some i), ()), ?_, rfl⟩
    change (some (some i), ()) ∈ keys pinned imported .every ((unit s).trace (answer I))
    change (some (some i), Spec.Q.binds) ∈ (unit s).trace (answer I) at hq
    cases hI : I (some (some i))
    · rcases hk i with hp | himp
      · simp [keys, pinnedKeys, hp]
      · simp only [keys, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter]
        exact .inr ⟨_, ⟨hq, by simp [himp]⟩, rfl⟩
    · simp [keys, hlast hI]
  abstraction := abstraction pinned imported .every
  locality := locality pinned imported .every

/-- T3a for the fix, `XCompiler.zinc_sound` unchanged: no file-closed policy is needed. -/
theorem every_sound (hk : ∀ i, pinned i = true ∨ imported i = true) (S : Finset (FU n))
    (src : FU n → FSrc n) (P : Compiler.Policy (FU n) Spec.Out Unit) (hP : P.Sound S)
    (fuel : ℕ) (R : Finset (FU n)) (s : Compiler.State (FU n) Spec.Out Unit) (D : Finset (FU n))
    (hD : D ⊆ R) (hInv : (compiler pinned imported .every).Inv S src s D)
    (s' : Compiler.State (FU n) Spec.Out Unit)
    (h : (compiler pinned imported .every).zinc S src P fuel 0 R s = some s') :
    (compiler pinned imported .every).Inv S src s' ∅ :=
  (compiler pinned imported .every).zinc_sound (every_obligations pinned imported hk) S src P hP
    fuel 0 R s D hD hInv s' h

/-! ### The witness

Scope 0 is `W`, wildcard-imported by the client's file, which does not bind the name yet; scope 1
binds it (the package's `Foo`). Nothing is pinned. The client resolves to scope 1 after a miss on
`W`. -/

def noPin : Fin 2 → Bool := fun _ => false
def wImported : Fin 2 → Bool := fun i => i = 0

def src : FU 2 → FSrc 2
  | none => .other
  | some none => .spec .client
  | some (some i) => .spec (.bind (i = 1))

def I : FU 2 → Bool := fun u => ifaceSrc (src u)

theorem trace_client :
    (unit (src (some none))).trace (answer I) = [(some (some 0), .binds), (some (some 1), .binds)] := by
  simp [src, unit, trace_lift, Spec.unit, Spec.search, answer, I, ifaceSrc, Spec.ifaceSrc, liftQ]

/-- **F3: today's charging fails charged coverage.** The client's miss on `W` is covered neither
by the client's keys (the resolved scope 1) nor by `Other`'s (none: it does not use the name). -/
theorem today_not_charged :
    ¬ (compiler noPin wImported .today).ChargedCoverage file charge := by
  intro h
  obtain ⟨k, hk, hc⟩ := h I src (some none) (some (some 0), .binds)
    (by show _ ∈ (unit (src (some none))).trace (answer I); rw [trace_client]; simp)
  change k ∈ keys noPin wImported .today ((unit (src (some none))).trace (answer I)) ∪
    keys noPin wImported .today ((unit (src (charge (file (some none))))).trace (answer I)) at hk
  rw [trace_client] at hk
  simp [keys, pinnedKeys, noPin, charge, file, src, unit] at hk
  subst hk
  simp [compiler] at hc

/-- With the import charged to every class, the client itself records `W`. -/
theorem every_covers_w :
    (some (some (0 : Fin 2)), ()) ∈ keys noPin wImported .every
      ((unit (src (some none))).trace (answer I)) := by
  rw [trace_client]; simp [keys, wImported]

end Zinc.FileSpec

/-! ## sbt/zinc#417: a dropped inheritance edge between classes of one file -/

namespace Zinc.Fi

inductive Cls | a | b | c
  deriving DecidableEq, Repr

/-- A class: its parents and a body (what a subclass inherits, e.g. a trait's private field). -/
structure CSrc where
  parents : List Cls
  body : ℕ
  deriving DecidableEq, Repr

abbrev Out := CSrc × List ℕ

/-- Lowering a class reads its ancestors' declarations (its linearization), to depth `k`. -/
def walk : ℕ → List Cls → Task (Cls × Unit) (fun _ => CSrc) (List ℕ)
  | 0, _ => .pure []
  | k + 1, ps => ps.foldr (fun p acc => .ask (p, ()) fun sp =>
      (walk k sp.parents).bind fun l₁ => acc.bind fun l₂ => .pure (sp.body :: l₁ ++ l₂)) (.pure [])

def unit (s : CSrc) : Task (Cls × Unit) (fun _ => CSrc) Out :=
  (walk 3 s.parents).bind fun l => .pure (s, l)

def answer (I : Cls → CSrc) (q : Cls × Unit) : CSrc := I q.1

def group (G : Finset Cls) (src : Cls → CSrc) (I : Cls → CSrc) : Cls → Out :=
  fun u => (unit (src u)).run (answer fun v => if v ∈ G then src v else I v)

/-- `A` and `B` in one file, `C` in another. -/
def file : Cls → ℕ
  | .a => 0
  | .b => 0
  | .c => 1

/-- A class and its ancestors, through the stored inheritance edges; `drop`: the bridge drops the
edges between classes of one file (sbt/zinc#417). -/
def anc (drop : Bool) (I : Cls → CSrc) : ℕ → Cls → List Cls
  | 0, u => [u]
  | k + 1, u => u :: ((I u).parents.filter fun p => !(drop && file p == file u)).flatMap (anc drop I k)

/-- Inheritance keys on the parents; a key covers its class's ancestors and hashes their
declarations (Zinc's transitive invalidation over the stored edges). -/
def compiler (drop : Bool) : XCompiler Cls CSrc Out CSrc Unit (List CSrc) Unit (fun _ => CSrc) where
  unit := unit
  group := group
  iface := Prod.fst
  answer := answer
  π I u _ := (anc drop I 3 u).map I
  hashDeps I u := (anc drop I 3 u).toFinset
  keys _ o _ := (o.1.parents.map fun p => (p, ())).toFinset
  covers I q k := q.1 ∈ anc drop I 3 k.1

def src₀ : Cls → CSrc
  | .a => ⟨[], 0⟩
  | .b => ⟨[.a], 0⟩
  | .c => ⟨[.b], 0⟩

/-- `A`'s body changes. -/
def src₁ : Cls → CSrc
  | .a => ⟨[], 1⟩
  | .b => ⟨[.a], 0⟩
  | .c => ⟨[.b], 0⟩

/-- **The dropped edge.** Lowering `C` asks for `A`; `C`'s only key, on `B`, does not cover `A`
(`covers` is membership in `anc`),
because the edge `B → A` is between classes of one file. `A` is in another file than `C`, so no
file-closed round repairs it. With the edge kept, the key covers `A`. -/
theorem fi_not_covered :
    (Cls.a, ()) ∈ (unit (src₀ .c)).trace (answer src₀) ∧
    (∀ k ∈ (compiler true).keys .c ((unit (src₀ .c)).run (answer src₀))
        ((unit (src₀ .c)).trace (answer src₀)), Cls.a ∉ anc true src₀ 3 k.1) ∧
    file .a = file .b ∧ file .a ≠ file .c ∧
    (∃ k ∈ (compiler false).keys .c ((unit (src₀ .c)).run (answer src₀))
        ((unit (src₀ .c)).trace (answer src₀)), Cls.a ∈ anc false src₀ 3 k.1) := by
  decide +kernel

def S : Finset Cls := {.a, .b, .c}

/-- The old build, up to date, with its keys. -/
def old : Compiler.State Cls Out Unit where
  out := group S src₀ src₀
  U u := (compiler true).keys u (group S src₀ src₀ u) []

/-- Zinc's policy: the invalidated classes and the rest of their files. -/
def P : Compiler.Policy Cls Out Unit := fun _ _ _ _ I => S.filter fun u => ∃ v ∈ I, file u = file v

/-- **The loop.** `A` is edited; the first round is its file, `{A, B}`. Nothing is invalidated
(`B`'s declaration did not change), so the loop stops, and `C` keeps what it inherited from the
old `A`, unlike a clean build. -/
theorem fi_loop :
    ((compiler true).zinc S src₁ P 3 0 {.a, .b} old).map (fun s => (s.out .c).2) = some [0, 0] ∧
    (group S src₁ src₁ .c).2 = [0, 1] := by
  decide +kernel

/-- With the edge kept, the same edit invalidates `C` and the loop recompiles it. -/
theorem fi_loop_kept :
    ((compiler false).zinc S src₁ P 3 0 {.a, .b} old).map (fun s => (s.out .c).2) = some [0, 1] := by
  decide +kernel

/-! ### Keeping the edge meets the obligations, for every program

`walk` and `anc` read to the same depth, so every class lowering asks for is an ancestor its
inheritance key covers. A hierarchy deeper than the fuel is truncated alike in a clean and an
incremental build; no program is excluded. -/

theorem anc_succ (I : Cls → CSrc) (k : ℕ) (u : Cls) :
    anc false I (k + 1) u = u :: (I u).parents.flatMap (anc false I k) := by
  simp [anc]

theorem walk_cons (k : ℕ) (p : Cls) (ps : List Cls) :
    walk (k + 1) (p :: ps) = .ask (p, ()) fun sp => (walk k sp.parents).bind fun l₁ =>
      (walk (k + 1) ps).bind fun l₂ => .pure (sp.body :: l₁ ++ l₂) := rfl

/-- Every class `walk` asks for is an ancestor of one of the classes it started from. -/
theorem walk_trace (I : Cls → CSrc) (k : ℕ) :
    ∀ (ps : List Cls), ∀ q ∈ (walk k ps).trace (answer I), ∃ p ∈ ps, q.1 ∈ anc false I k p := by
  induction k with
  | zero => intro ps q hq; simp [walk] at hq
  | succ k ih =>
    intro ps
    induction ps with
    | nil => intro q hq; simp [walk] at hq
    | cons p ps ihps =>
      intro q hq
      rw [walk_cons, Task.trace_ask, Task.trace_bind, Task.trace_bind, Task.trace_pure,
        List.append_nil] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨p, List.mem_cons_self .., by simp [anc_succ]⟩
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨p', hp', hq'⟩ := ih (I p).parents q hq
        exact ⟨p, List.mem_cons_self .., by
          rw [anc_succ]; exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨p', hp', hq'⟩)⟩
      · obtain ⟨p', hp', hq'⟩ := ihps q hq
        exact ⟨p', List.mem_cons_of_mem _ hp', hq'⟩

theorem iface_run (s : CSrc) (e : Task.Env (Cls × Unit) (fun _ => CSrc)) :
    ((unit s).run e).1 = s := by
  simp [unit]

theorem comp (drop : Bool) : ∀ (G : Finset Cls) (src : Cls → CSrc) (I : Cls → CSrc), ∀ u ∈ G,
    (compiler drop).group G src I u =
      ((compiler drop).unit (src u)).run ((compiler drop).answer
        (XCompiler.override I G ((compiler drop).iface ∘ (compiler drop).group G src I))) := by
  intro G src I u _
  simp only [compiler, group]
  congr 2
  funext v
  simp only [XCompiler.override, Function.comp, group, iface_run]

theorem coverage (I : Cls → CSrc) (d : Cls) (s : CSrc) :
    ∀ q ∈ ((compiler false).unit s).trace ((compiler false).answer I),
      ∃ k ∈ (compiler false).keys d (((compiler false).unit s).run ((compiler false).answer I))
          (((compiler false).unit s).trace ((compiler false).answer I)),
        (compiler false).covers I q k := by
  intro q hq
  change q ∈ (unit s).trace (answer I) at hq
  simp only [unit, Task.trace_bind, Task.trace_pure, List.append_nil] at hq
  obtain ⟨p, hp, hq⟩ := walk_trace I 3 s.parents q hq
  refine ⟨(p, ()), ?_, hq⟩
  change (p, ()) ∈ (((unit s).run (answer I)).1.parents.map fun p => (p, ())).toFinset
  rw [iface_run]
  simp [hp]

/-- The values along an ancestor list, followed by anything, determine the list: each value
carries its class's parents. -/
theorem parse_flatMap {f g : Cls → List Cls} (I I' : Cls → CSrc)
    (h : ∀ u (l l' : List CSrc), (f u).map I ++ l = (g u).map I' ++ l' →
      f u = g u ∧ (∀ v ∈ f u, I v = I' v) ∧ l = l') :
    ∀ (ps : List Cls) (l l' : List CSrc),
      (ps.flatMap f).map I ++ l = (ps.flatMap g).map I' ++ l' →
      ps.flatMap f = ps.flatMap g ∧ (∀ v ∈ ps.flatMap f, I v = I' v) ∧ l = l'
  | [], l, l', hl => by simpa using hl
  | p :: ps, l, l', hl => by
    simp only [List.flatMap_cons, List.map_append, List.append_assoc] at hl ⊢
    obtain ⟨h1, h2, h3⟩ := h p _ _ hl
    obtain ⟨h4, h5, h6⟩ := parse_flatMap I I' h ps l l' h3
    refine ⟨by rw [h1, h4], fun v hv => ?_, h6⟩
    rcases List.mem_append.1 hv with hv | hv
    · exact h2 v hv
    · exact h5 v hv

theorem anc_parse (I I' : Cls → CSrc) : ∀ (k : ℕ) (u : Cls) (l l' : List CSrc),
    (anc false I k u).map I ++ l = (anc false I' k u).map I' ++ l' →
    anc false I k u = anc false I' k u ∧ (∀ v ∈ anc false I k u, I v = I' v) ∧ l = l'
  | 0, u, l, l', h => by
    simp only [anc, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq] at h
    refine ⟨rfl, fun v hv => ?_, h.2⟩
    simp only [anc, List.mem_singleton] at hv
    exact hv ▸ h.1
  | k + 1, u, l, l', h => by
    rw [anc_succ, anc_succ] at h ⊢
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨hu, h⟩ := h
    rw [← hu] at h
    obtain ⟨h1, h2, h3⟩ := parse_flatMap I I' (anc_parse I I' k) _ l l' h
    refine ⟨by rw [← hu, h1], fun v hv => ?_, h3⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hu
    · exact h2 v hv

theorem abstraction : (compiler false).Abstraction := by
  intro I I' k h q hc
  change (anc false I 3 k.1).map I = (anc false I' 3 k.1).map I' at h
  change q.1 ∈ anc false I 3 k.1 at hc
  obtain ⟨h1, h2, -⟩ := anc_parse I I' 3 k.1 [] [] (by simpa using h)
  exact ⟨h2 _ hc, by change q.1 ∈ anc false I' 3 k.1; rw [← h1]; exact hc⟩

theorem anc_congr (I I' : Cls → CSrc) :
    ∀ (k : ℕ) (u : Cls), (∀ v ∈ anc false I k u, I v = I' v) → anc false I k u = anc false I' k u
  | 0, _, _ => rfl
  | k + 1, u, h => by
    have hu : I u = I' u := h u (by simp [anc_succ])
    rw [anc_succ, anc_succ, ← hu]
    congr 1
    have : ∀ ps : List Cls, (∀ p ∈ ps, ∀ v ∈ anc false I k p, I v = I' v) →
        ps.flatMap (anc false I k) = ps.flatMap (anc false I' k) := by
      intro ps hps
      induction ps with
      | nil => rfl
      | cons p ps ih =>
        simp only [List.flatMap_cons]
        rw [anc_congr I I' k p (hps p (List.mem_cons_self ..)),
          ih fun p' hp' => hps p' (List.mem_cons_of_mem _ hp')]
    apply this
    intro p hp v hv
    apply h
    rw [anc_succ]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨p, hp, hv⟩)

theorem locality (I I' : Cls → CSrc) (u : Cls)
    (h : ∀ d ∈ (compiler false).hashDeps I u, I d = I' d) (k : Unit) :
    (compiler false).π I u k = (compiler false).π I' u k := by
  have h' : ∀ v ∈ anc false I 3 u, I v = I' v := fun v hv => h v (List.mem_toFinset.2 hv)
  change (anc false I 3 u).map I = (anc false I' 3 u).map I'
  rw [← anc_congr I I' 3 u h']
  exact List.map_congr_left h'

/-- **The fix meets the obligations**: with the same-file edge kept, for every program. -/
theorem kept_obligations : (compiler false).Obligations where
  comp := comp false
  coverage := coverage
  abstraction := abstraction
  locality := locality

/-- T3a for the fix, `XCompiler.zinc_sound` unchanged: no file-closed policy is needed. -/
theorem kept_sound (S : Finset Cls) (src : Cls → CSrc) (P : Compiler.Policy Cls Out Unit)
    (hP : P.Sound S) (fuel : ℕ) (R : Finset Cls) (s : Compiler.State Cls Out Unit) (D : Finset Cls)
    (hD : D ⊆ R) (hInv : (compiler false).Inv S src s D) (s' : Compiler.State Cls Out Unit)
    (h : (compiler false).zinc S src P fuel 0 R s = some s') :
    (compiler false).Inv S src s' ∅ :=
  (compiler false).zinc_sound kept_obligations S src P hP fuel 0 R s D hD hInv s' h

end Zinc.Fi
