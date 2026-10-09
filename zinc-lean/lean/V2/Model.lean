import V1.Soundness
import Mathlib.Data.Fintype.Basic

-- Snapshot of `zinc-incrementality/lean/Zinc/NonLocalAns.lean`, unchanged apart from the namespace.
-- In V2 this is the one general model; `V2/Embed.lean` shows V1's local model is a special case.

/-!
# Non-local answers and interface-dependent read sets

`GCompiler` (`NonLocal.lean`) lets a hash read several interfaces, but every *answer* still reads
one: `answer : Iface → Q → A`. That is enough for a Merkle hash that is the verifying trace of a
walk, but not for a hash that summarises the walk's *result*. The Zinc PoC's flattened Merkle hash
is of the second kind: it hashes, per name, the ancestors in the stored linearization that declare
it, so it cannot cover the individual `parents` queries of the walk. The client's member lookup
has to be a single query whose answer reads the receiver's stored linearization and its
ancestors' declarations.

`NCompiler` generalises `GCompiler` in three ways:

* `answer : (CUnit → Iface) → CUnit × Q → A`: an answer may read several interfaces;
* `hashDeps : (CUnit → Iface) → CUnit → Finset CUnit`: the read set of `π _ c _` may depend on the
  interfaces (the stored linearization of `c`);
* `keys : CUnit → …`: the extractor knows which unit it extracts for, so a model can drop
  self-references as Zinc does.

Joint compilation takes the *interfaces* of everything outside the group, since an answer about a
group-mate may read an outsider.

**T2″** (`round_preserves`) is T2′ with `Δ` over `affected R s = R ∪ {c | hashDeps(c) ∩ R ≠ ∅}`,
read sets taken in the state before the round. **T3a″** (`zinc_sound`) follows for any sound policy.
-/

namespace V2

open V1

structure NCompiler (CUnit Src Out Iface K Hash Q : Type) (A : Q → Type) where
  unit   : Src → Task (CUnit × Q) (fun p => A p.2) Out
  /-- Joint compilation of a group against the interfaces of everything else. -/
  group  : Finset CUnit → (CUnit → Src) → (CUnit → Iface) → (CUnit → Out)
  iface  : Out → Iface
  /-- An answer may read the interfaces of several units. -/
  answer : (CUnit → Iface) → (q : CUnit × Q) → A q.2
  π      : (CUnit → Iface) → CUnit → K → Hash
  /-- The units `π I c _` reads, which may depend on `I`. -/
  hashDeps : (CUnit → Iface) → CUnit → Finset CUnit
  /-- `U(d)`: the extractor for unit `d`. -/
  keys   : CUnit → List (CUnit × Q) → Finset (CUnit × K)
  covers : (CUnit → Iface) → (CUnit × Q) → (CUnit × K) → Prop

namespace NCompiler

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : NCompiler CUnit Src Out Iface K Hash Q A)
variable [DecidableEq CUnit]

/-- Replace the interfaces of `G`. -/
def override (I : CUnit → Iface) (G : Finset CUnit) (I' : CUnit → Iface) : CUnit → Iface :=
  fun u => if u ∈ G then I' u else I u

structure Obligations : Prop where
  comp : ∀ (G : Finset CUnit) (src : CUnit → Src) (I : CUnit → Iface), ∀ d ∈ G,
    C.group G src I d = (C.unit (src d)).run (C.answer (override I G (C.iface ∘ C.group G src I)))
  coverage : ∀ (I : CUnit → Iface) (d : CUnit) (s : Src), ∀ q ∈ (C.unit s).trace (C.answer I),
    ∃ k ∈ C.keys d ((C.unit s).trace (C.answer I)), C.covers I q k
  abstraction : ∀ (I I' : CUnit → Iface) (k : CUnit × K), C.π I k.1 k.2 = C.π I' k.1 k.2 →
    ∀ q, C.covers I q k → C.answer I q = C.answer I' q ∧ C.covers I' q k
  locality : ∀ (I I' : CUnit → Iface) (c : CUnit), (∀ d ∈ C.hashDeps I c, I d = I' d) →
    ∀ k, C.π I c k = C.π I' c k

open V1.Compiler (State Policy)

def ifaces (s : State CUnit Out K) : CUnit → Iface := C.iface ∘ s.out

def round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) : State CUnit Out K :=
  let o := C.group R src (C.ifaces s)
  let out' : CUnit → Out := fun u => if u ∈ R then o u else s.out u
  { out := out'
    U := fun d => if d ∈ R then C.keys d ((C.unit (src d)).trace (C.answer (C.iface ∘ out')))
      else s.U d }

variable [Fintype CUnit]

/-- The units whose hash may have changed after recompiling `R`, read sets taken in `s`. -/
def affected (R : Finset CUnit) (s : State CUnit Out K) : Finset CUnit :=
  R ∪ Finset.univ.filter fun c => ∃ d ∈ C.hashDeps (C.ifaces s) c, d ∈ R

def changed (Dom : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) : Prop :=
  p.1 ∈ Dom ∧ C.π (C.ifaces s) p.1 p.2 ≠ C.π (C.ifaces s') p.1 p.2

instance [DecidableEq Hash] (Dom : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) :
    Decidable (C.changed Dom s s' p) := by unfold changed; infer_instance

def invalidated [DecidableEq K] [DecidableEq Hash] (S Dom : Finset CUnit)
    (s s' : State CUnit Out K) : Finset CUnit :=
  S.filter fun d => ∃ p ∈ s'.U d, C.changed Dom s s' p

def UpToDate (src : CUnit → Src) (s : State CUnit Out K) (u : CUnit) : Prop :=
  s.out u = (C.unit (src u)).run (C.answer (C.ifaces s)) ∧
  ∀ q ∈ (C.unit (src u)).trace (C.answer (C.ifaces s)), ∃ k ∈ s.U u, C.covers (C.ifaces s) q k

def Inv (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) (D : Finset CUnit) : Prop :=
  ∀ u ∈ S, u ∉ D → C.UpToDate src s u

omit [Fintype CUnit] in
theorem ifaces_round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) :
    C.ifaces (C.round src R s) = override (C.ifaces s) R (C.iface ∘ C.group R src (C.ifaces s)) := by
  funext u
  simp only [ifaces, round, override, Function.comp]
  split <;> rfl

variable [DecidableEq K] [DecidableEq Hash]

/-- **T2″.** With `Δ` over `affected R s`, one round preserves the invariant. -/
theorem round_preserves (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) (D R : Finset CUnit) (hD : D ⊆ R) (hInv : C.Inv S src s D) :
    C.Inv S src (C.round src R s)
      (C.invalidated S (C.affected R s) s (C.round src R s) \ R) := by
  intro u huS hu
  set s' := C.round src R s with hs'
  by_cases huR : u ∈ R
  · refine ⟨?_, ?_⟩
    · have h1 := ob.comp R src (C.ifaces s) u huR
      have h2 : s'.out u = C.group R src (C.ifaces s) u := by
        simp only [hs', round, huR, ite_true]
      rw [h2, h1, ← ifaces_round]
    · intro q hq
      have hU : s'.U u = C.keys u ((C.unit (src u)).trace (C.answer (C.ifaces s'))) := by
        simp only [hs', round, huR, ite_true]; rfl
      rw [hU]
      exact ob.coverage _ u _ q hq
  · have huI : u ∉ C.invalidated S (C.affected R s) s s' :=
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
      by_cases haff : p.1 ∈ C.affected R s
      · by_contra hne
        apply huI
        simp only [invalidated, Finset.mem_filter]
        exact ⟨huS, p, hU ▸ hp, haff, hne⟩
      · apply ob.locality
        intro d hd
        apply hiface
        intro hdR
        apply haff
        simp only [affected, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨d, hd, hdR⟩
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

/-- Zinc's loop with `Δ` over `affected`. -/
def zinc (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) :
    ℕ → ℕ → Finset CUnit → State CUnit Out K → Option (State CUnit Out K)
  | 0, _, _, _ => none
  | fuel + 1, n, R, s =>
    let s' := C.round src R s
    let I := C.invalidated S (C.affected R s) s s'
    if I ⊆ R then some s' else zinc S src P fuel (n + 1) (P n R s s' I) s'

/-- **T3a″.** If the loop stops, no unit is dirty. -/
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
      have : C.invalidated S (C.affected R s) s (C.round src R s) \ R = ∅ :=
        Finset.sdiff_eq_empty_iff_subset.2 hsub
      rw [this] at hstep
      exact hstep
    · exact ih _ _ _ _ (hP _ _ _ _ _ (Finset.filter_subset _ _)) hstep s' h

end NCompiler
end V2
