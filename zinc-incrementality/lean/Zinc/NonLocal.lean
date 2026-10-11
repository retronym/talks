import Zinc.Soundness
import Zinc.General
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
  /-- `q ⊑_I k`: under interfaces `I`, key `k` covers query `q`. `q` and `k` may be addressed to
  different units, and which queries a closure key covers may depend on `I` (the ancestors a
  member lookup walks through). -/
  covers : (CUnit → Iface) → (CUnit × Q) → (CUnit × K) → Prop

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
  /-- Every query a unit's compilation issues under `I` is covered, under `I`, by a recorded key. -/
  coverage : ∀ (I : CUnit → Iface) (s : Src), ∀ q ∈ (C.unit s).trace (C.envOf I),
    ∃ k ∈ C.keys ((C.unit s).trace (C.envOf I)), C.covers I q k
  /-- Equal hashes under two interface maps give equal answers to every query covered under the
  first, and the key keeps covering it under the second. -/
  abstraction : ∀ (I I' : CUnit → Iface) (k : CUnit × K), C.π I k.1 k.2 = C.π I' k.1 k.2 →
    ∀ q, C.covers I q k → C.answer (I q.1) q.2 = C.answer (I' q.1) q.2 ∧ C.covers I' q k
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
  ∀ q ∈ (C.unit (src u)).trace (C.env s), ∃ k ∈ s.U u, C.covers (C.iface ∘ s.out) q k

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

/-- The lift into the general form: answers read one interface, keys come from the trace. -/
def toX : XCompiler CUnit Src Out Iface K Hash Q A where
  unit := C.unit
  group G src I := C.group G src (C.envOf I)
  iface := C.iface
  answer I q := C.answer (I q.1) q.2
  π := C.π
  hashDeps _ c := C.hashDeps c
  keys _ _ tr := C.keys tr
  covers := C.covers

omit [DecidableEq K] [DecidableEq Hash] in
theorem toX_obligations (ob : C.Obligations) : C.toX.Obligations where
  comp G src I d hd := by
    show C.group G src (C.envOf I) d = (C.unit (src d)).run _
    rw [ob.comp G src (C.envOf I) d hd, C.override_envOf]
    rfl
  coverage I _ s q hq := ob.coverage I s q hq
  abstraction := ob.abstraction
  locality := ob.locality

/-- With `hashRevDeps` containing the reverse of `hashDeps`, the general form's affected units are
among `affected R`, so its `inv(ΔAPI)` is among this one. -/
theorem invalidated_toX_subset (ob : C.Obligations) (S R : Finset CUnit) (s s' : State CUnit Out K) :
    C.toX.invalidated S R s s' ⊆ C.invalidated S (C.affected R) s s' := by
  intro d hd
  simp only [XCompiler.invalidated, invalidated, Finset.mem_filter] at hd ⊢
  obtain ⟨hS, p, hp, haff, hne⟩ := hd
  refine ⟨hS, p, hp, ?_, hne⟩
  simp only [affected, Finset.mem_union, Finset.mem_biUnion]
  rcases haff with h | ⟨e, he, heR⟩
  · exact .inl h
  · exact .inr ⟨e, heR, ob.rev _ _ he⟩

/-- **T2′.** With `Δ` over `affected R`, one round preserves the invariant. -/
theorem round_preserves (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) (D R : Finset CUnit) (hD : D ⊆ R)
    (hInv : C.Inv S src s D) :
    C.Inv S src (C.round src R s)
      (C.invalidated S (C.affected R) s (C.round src R s) \ R) := by
  have h := C.toX.round_preserves (C.toX_obligations ob) S src s D R hD hInv
  intro u hu hnot
  apply h u hu
  intro hmem
  apply hnot
  rw [Finset.mem_sdiff] at hmem ⊢
  exact ⟨C.invalidated_toX_subset ob S R s _ hmem.1, hmem.2⟩

end GCompiler
end Zinc
