import Zinc.Classpath
import Zinc.Termination

/-!
# Zinc's snapshot refresh rule with a non-local hash: edit, then revert

Three units. Upstream: `A` and `C`, each exposing a number. Downstream: `X` asks `C` for its
value, and the answer reads `A` as well (`C` inherits from `A`). `X` records one key, `(C, k)`,
whose hash reads `A` and `C` (`hashDeps C = {A, C}`), as the Merkle PoC's composed hash of an
upstream class reads its stored linearization. The obligations hold.

1. Edit `A`. The snapshot diff sees `(C, k)` move, and `X` is recompiled.
2. Zinc refreshes the snapshots of the upstream classes that a recompiled unit references: `C`
   only. `A`'s snapshot keeps the value from before the edit.
3. Revert `A`. Over the snapshot, `(C, k)` hashes as before the edit, which is also its hash now,
   so nothing is invalidated, and `X` keeps the output it got against the edited `A`
   (`stale_after_revert`).

Refreshing every upstream unit, or every unit in the read sets of the referenced keys, recompiles
`X` (`refreshAll_after_revert`). With local hashes Zinc's rule is enough
(`NCompiler.fresh_refreshRef_local`), which is the case for Zinc today: an upstream class's stored
API is its own, materialised members included. The PoC's composition across subprojects is the
non-local case, where `macro-upstream-member-removed` was found: lib's `B` gains a member, app's
`C extends B` is skipped, only the macro client `W` recompiles, `B`'s record stays old, and removing
the member again goes unseen. The PoC's fix (`9904df698`, "Refresh the stored API of every
processed upstream change") refreshes every changed upstream class after a compiling run, which is
`refreshAll` on the classes that changed (an unchanged class's record is already current).
-/

namespace Zinc.Snapshot

open Compiler (State)

inductive U | A | C | X
  deriving DecidableEq, Repr

instance : Fintype U := ⟨{.A, .C, .X}, by intro x; cases x <;> decide⟩

inductive Src | lib (n : ℕ) | client
  deriving DecidableEq, Repr

inductive Q | value
  deriving DecidableEq, Repr

/-- `C`'s value as seen by a client: `A`'s number and `C`'s. -/
def Ans : Q → Type
  | .value => ℕ × ℕ

inductive K | k
  deriving DecidableEq, Repr

abbrev Iface := ℕ
/-- An output: the interface it exposes, and what a client observed. -/
abbrev Out := ℕ × (ℕ × ℕ)

def answer (I : U → Iface) : (q : U × Q) → Ans q.2
  | (u, .value) => (I U.A, I u)

def unit : Src → Task (U × Q) (fun p => Ans p.2) Out
  | .lib n => .pure (n, (0, 0))
  | .client => .ask (U.C, Q.value) fun (v : ℕ × ℕ) => .pure (0, v)

def ifaceSrc : Src → Iface
  | .lib n => n
  | .client => 0

/-- Joint compilation: group-mates answered from their source interfaces. -/
def group (G : Finset U) (src : U → Src) (I : U → Iface) : U → Out :=
  fun u => if u ∈ G then (unit (src u)).run (answer fun v => if v ∈ G then ifaceSrc (src v) else I v)
    else (0, (0, 0))

def compiler : NCompiler U Src Out Iface K (ℕ × ℕ) Q Ans where
  unit := unit
  group := group
  iface := Prod.fst
  answer := answer
  π := fun I c _ => (I U.A, I c)
  hashDeps := fun _ c => {U.A, c}
  keys := fun _ tr => if tr.isEmpty then ∅ else {(U.C, K.k)}
  covers := fun _ q k => k = (U.C, K.k) ∧ q.1 = U.C

theorem group_iface (G : Finset U) (src : U → Src) (I : U → Iface) (v : U) (hv : v ∈ G) :
    (group G src I v).1 = ifaceSrc (src v) := by
  simp only [group, hv, ite_true]
  cases src v <;> rfl

theorem trace_C (s : Src) (e : (q : U × Q) → Ans q.2) : ∀ q ∈ (unit s).trace e, q = (U.C, Q.value) := by
  intro q hq
  cases s <;> simp [unit, Task.trace] at hq
  exact hq

theorem obligations : compiler.Obligations where
  comp := by
    intro G src I d hd
    change group G src I d = (unit (src d)).run (answer (NCompiler.override I G (Prod.fst ∘ group G src I)))
    have : NCompiler.override I G (Prod.fst ∘ group G src I) =
        fun v => if v ∈ G then ifaceSrc (src v) else I v := by
      funext v
      simp only [NCompiler.override, Function.comp]
      split
      · rename_i hv; exact group_iface G src I v hv
      · rfl
    rw [this]
    simp only [group, hd, ite_true]
  coverage := by
    intro I d s q hq
    refine ⟨(U.C, K.k), ?_, rfl, by rw [trace_C s _ q hq]⟩
    have : ¬ ((compiler.unit s).trace (compiler.answer I)).isEmpty := by
      intro h; rw [List.isEmpty_iff] at h; rw [h] at hq; simp at hq
    show (U.C, K.k) ∈ (if ((compiler.unit s).trace (compiler.answer I)).isEmpty then ∅ else {(U.C, K.k)})
    simp [this]
  abstraction := by
    intro I I' k h q hc
    obtain ⟨hk, hq⟩ := hc
    subst hk
    change (I U.A, I U.C) = (I' U.A, I' U.C) at h
    refine ⟨?_, rfl, hq⟩
    rcases q with ⟨u, ⟨⟩⟩
    simp only at hq
    subst hq
    exact h
  locality := by
    intro I I' c h _
    show (I U.A, I c) = (I' U.A, I' c)
    rw [h U.A (by simp [compiler]), h c (by simp [compiler])]

/-! ## The scenario -/

abbrev Up : Finset U := {U.A, U.C}
abbrev S : Finset U := {U.X}

def src : U → Src
  | .A => .lib 1
  | .C => .lib 5
  | .X => .client

/-- The previous clean build, with recorded keys, and a fresh snapshot. -/
def s₀ : State U Out K := compiler.round src {U.A, U.C, U.X} { out := fun _ => (0, (0, 0)), U := fun _ => ∅ }
def snap₀ : U → Iface := compiler.ifaces s₀

/-- Upstream outputs: `A` exposes `a`, `C` exposes 5. -/
def upstream (a : ℕ) : U → Out
  | .A => (a, (0, 0))
  | _ => (5, (0, 0))

/-- One downstream build: diff the snapshot, run the loop, refresh. -/
def build (refresh : Finset U → State U Out K → (U → Iface) → U → Iface)
    (s : State U Out K) (snap : U → Iface) (a : ℕ) : Option (State U Out K × (U → Iface)) :=
  let s₁ := NCompiler.withUpstream Up s (upstream a)
  let R₀ := compiler.extInvalidated Up S s snap s₁
  (compiler.zinc S src Compiler.Policy.plain 3 0 R₀ s₁).map fun s' => (s', refresh R₀ s' snap)

def zincRule : Finset U → State U Out K → (U → Iface) → U → Iface := compiler.refreshRef Up
def allRule : Finset U → State U Out K → (U → Iface) → U → Iface := fun _ => compiler.refreshAll Up

/-- What `X` observed after editing `A` to 2, then reverting it to 1. -/
def afterRevert (refresh : Finset U → State U Out K → (U → Iface) → U → Iface) : Option (ℕ × ℕ) := do
  let (s₁, snap₁) ← build refresh s₀ snap₀ 2
  let (s₂, _) ← build refresh s₁ snap₁ 1
  pure (s₂.out U.X).2

example : (s₀.out U.X).2 = (1, 5) := by native_decide

/-- The edit: `X` is invalidated and observes `A = 2`. -/
example : ((build zincRule s₀ snap₀ 2).map fun r => (r.1.out U.X).2) = some (2, 5) := by native_decide

/-- Zinc's rule refreshed `C` but not `A`. -/
example : ((build zincRule s₀ snap₀ 2).map fun r => (r.2 U.A, r.2 U.C)) = some (1, 5) := by
  native_decide

/-- `stale_after_revert`: **After the revert, `X` is stale**: it still observes `A = 2`; a clean build observes 1. -/
example : afterRevert zincRule = some (2, 5) := by native_decide

/-- `refreshAll_after_revert`: Refreshing every upstream unit recompiles `X` after the revert. -/
example : afterRevert allRule = some (1, 5) := by native_decide

end Zinc.Snapshot
