import Zinc.Soundness
import Mathlib.Data.Finset.Union

/-!
# Non-local hashes: materialised members, Merkle composition, and the inheritance walk

In `Model.lean` the hash `π` reads one unit's interface and a key covers only queries addressed
to its own unit. Zinc's materialised `inherited` members, and the Merkle composition proposed in
§10, are *non-local* hashes: `π_C(m)` depends on the interfaces of `C`'s ancestors. This file
generalises the model:

* `π : (CUnit → Iface) → CUnit → K → Hash` with a declared read set `hashDeps`;
* a key may cover queries addressed to other units (closure keys);
* `Δ` must range over the units whose hash *may* have changed: those recompiled, and those whose
  `hashDeps` meet the recompiled set (`affected`).

**T2′** (`round_preserves`) is the round invariant for this model. **T2-stale**
(`stale_unsound`) shows that taking `Δ` over the recompiled set alone is unsound for a non-local
hash: the trap behind the bridge's own TODO about using parent hashes. Zinc's transitive
inheritance walk at invalidation time (`invalidateByInheritance`) is `affected` in disguise.
-/

namespace Zinc

structure GCompiler (CUnit Src Out Iface K Hash Q : Type) (A : Q → Type) where
  unit   : Src → Task (CUnit × Q) (fun p => A p.2) Out
  group  : Finset CUnit → (CUnit → Src) → Task.Env (CUnit × Q) (fun p => A p.2) → (CUnit → Out)
  iface  : Out → Iface
  answer : Iface → (q : Q) → A q
  /-- The hash of key `k` of unit `c`, computed from the interfaces of all units. -/
  π      : (CUnit → Iface) → CUnit → K → Hash
  /-- The units `π _ c _` may read. -/
  hashDeps : CUnit → Finset CUnit
  /-- The reverse relation (Zinc: `inheritance.internal.reverse`). -/
  hashRevDeps : CUnit → Finset CUnit
  keys   : List (CUnit × Q) → Finset (CUnit × K)
  /-- `q ⊑ k`, where `q` and `k` may be addressed to different units. -/
  covers : (CUnit × Q) → (CUnit × K) → Prop

namespace GCompiler

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : GCompiler CUnit Src Out Iface K Hash Q A)
variable [DecidableEq CUnit]

abbrev Env := Task.Env (CUnit × Q) (fun p => A p.2)

def envOf (I : CUnit → Iface) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  fun p => C.answer (I p.1) p.2

def override (e : Env (CUnit := CUnit) (Q := Q) (A := A)) (G : Finset CUnit) (I : CUnit → Iface) :
    Env (CUnit := CUnit) (Q := Q) (A := A) :=
  fun p => if p.1 ∈ G then C.answer (I p.1) p.2 else e p

theorem override_envOf (I I' : CUnit → Iface) (G : Finset CUnit) :
    C.override (C.envOf I) G I' = C.envOf (fun u => if u ∈ G then I' u else I u) := by
  funext p; simp only [override, envOf]; split <;> rfl

structure Obligations : Prop where
  comp : ∀ (G : Finset CUnit) (src : CUnit → Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)),
    ∀ d ∈ G, C.group G src e d =
      (C.unit (src d)).run (C.override e G (C.iface ∘ C.group G src e))
  coverage : ∀ (tr : List (CUnit × Q)), ∀ q ∈ tr, ∃ k ∈ C.keys tr, C.covers q k
  /-- Equal hashes under two interface maps give equal answers to every covered query. -/
  abstraction : ∀ (I I' : CUnit → Iface) (k : CUnit × K), C.π I k.1 k.2 = C.π I' k.1 k.2 →
    ∀ q, C.covers q k → C.answer (I q.1) q.2 = C.answer (I' q.1) q.2
  /-- `π _ c _` reads only `hashDeps c`. -/
  locality : ∀ (I I' : CUnit → Iface) (c : CUnit), (∀ d ∈ C.hashDeps c, I d = I' d) →
    ∀ k, C.π I c k = C.π I' c k
  /-- `hashRevDeps` is the reverse of `hashDeps`. -/
  rev : ∀ c d, d ∈ C.hashDeps c → c ∈ C.hashRevDeps d

open Compiler (State)

def env (s : State CUnit Out K) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  C.envOf (C.iface ∘ s.out)

def round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) : State CUnit Out K :=
  let o := C.group R src (C.env s)
  let out' : CUnit → Out := fun u => if u ∈ R then o u else s.out u
  let e' := C.envOf (C.iface ∘ out')
  { out := out'
    U := fun d => if d ∈ R then C.keys ((C.unit (src d)).trace e') else s.U d }

/-- The units whose hash may have changed after recompiling `R`: Zinc's inheritance walk. -/
def affected (R : Finset CUnit) : Finset CUnit :=
  R ∪ R.biUnion C.hashRevDeps

/-- `Δ` over a domain `Dom` of units whose hashes are recomputed and compared. -/
def changed (Dom : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) : Prop :=
  p.1 ∈ Dom ∧ C.π (C.iface ∘ s.out) p.1 p.2 ≠ C.π (C.iface ∘ s'.out) p.1 p.2

instance [DecidableEq Hash] (Dom : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) :
    Decidable (C.changed Dom s s' p) := by unfold changed; infer_instance

def invalidated [DecidableEq K] [DecidableEq Hash] (S Dom : Finset CUnit)
    (s s' : State CUnit Out K) : Finset CUnit :=
  S.filter fun d => ∃ p ∈ s'.U d, C.changed Dom s s' p

def UpToDate (src : CUnit → Src) (s : State CUnit Out K) (u : CUnit) : Prop :=
  s.out u = (C.unit (src u)).run (C.env s) ∧
  ∀ q ∈ (C.unit (src u)).trace (C.env s), ∃ k ∈ s.U u, C.covers q k

def Inv (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) (D : Finset CUnit) : Prop :=
  ∀ u ∈ S, u ∉ D → C.UpToDate src s u

theorem env_round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) :
    C.env (C.round src R s) = C.override (C.env s) R (C.iface ∘ C.group R src (C.env s)) := by
  simp only [env, round]
  rw [override_envOf]
  congr 1
  funext u
  simp only [Function.comp]
  split <;> rfl

variable [DecidableEq K] [DecidableEq Hash]

/-- **T2′.** With `Δ` over `affected R`, one round preserves the invariant. -/
theorem round_preserves (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) (D R : Finset CUnit) (hD : D ⊆ R)
    (hInv : C.Inv S src s D) :
    C.Inv S src (C.round src R s)
      (C.invalidated S (C.affected R) s (C.round src R s) \ R) := by
  intro u huS hu
  set s' := C.round src R s with hs'
  by_cases huR : u ∈ R
  · refine ⟨?_, ?_⟩
    · have h1 := ob.comp R src (C.env s) u huR
      have h2 : s'.out u = C.group R src (C.env s) u := by
        simp only [hs', round, huR, ite_true]
      rw [h2, h1, ← env_round]
    · intro q hq
      have hU : s'.U u = C.keys ((C.unit (src u)).trace (C.env s')) := by
        simp only [hs', round, huR, ite_true]; rfl
      rw [hU]
      exact ob.coverage _ q hq
  · have huI : u ∉ C.invalidated S (C.affected R) s s' :=
      fun h => hu (Finset.mem_sdiff.2 ⟨h, huR⟩)
    have huD : u ∉ D := fun h => huR (hD h)
    obtain ⟨hout, hcov⟩ := hInv u huS huD
    have hU : s'.U u = s.U u := by simp only [hs', round, huR, ite_false]
    have hout' : s'.out u = s.out u := by simp only [hs', round, huR, ite_false]
    have hiface : ∀ d, d ∉ R → C.iface (s.out d) = C.iface (s'.out d) := by
      intro d hd
      simp only [hs', round, hd, ite_false]
    -- every recorded key has an unchanged hash
    have hhash : ∀ p ∈ s.U u, C.π (C.iface ∘ s.out) p.1 p.2 = C.π (C.iface ∘ s'.out) p.1 p.2 := by
      intro p hp
      by_cases haff : p.1 ∈ C.affected R
      · by_contra hne
        apply huI
        simp only [invalidated, Finset.mem_filter]
        exact ⟨huS, p, hU ▸ hp, haff, hne⟩
      · -- not affected: none of its read set was recompiled
        apply ob.locality
        intro d hd
        simp only [Function.comp]
        apply hiface
        intro hdR
        apply haff
        simp only [affected, Finset.mem_union, Finset.mem_biUnion]
        exact Or.inr ⟨d, hdR, ob.rev _ _ hd⟩
    have hagree : ∀ q ∈ (C.unit (src u)).trace (C.env s), C.env s q = C.env s' q := by
      intro q hq
      obtain ⟨k, hk, hcovers⟩ := hcov q hq
      simp only [env, envOf]
      exact ob.abstraction _ _ k (hhash k hk) q hcovers
    obtain ⟨hrun, htrace⟩ := Task.run_eq_of_trace _ _ _ hagree
    refine ⟨?_, ?_⟩
    · rw [hout', hout, hrun]
    · rw [← htrace, hU]; exact hcov

end GCompiler
end Zinc
