import Zinc.Soundness

/-!
# Keys from the typed tree

`Compiler.keys` maps a unit's *trace* to the keys Zinc records: an idealised extractor that sees
every query the compilation asked. Zinc's extractors (`ExtractUsedNames`, `ExtractDependencies`)
read the *typed tree* instead, at a fixed point in the pipeline. Two kinds of query never reach it:

* lookups the typer made and then discarded: a failed lookup of `+=` before desugaring `x += y`
  to `x = x + y`, `selectDynamic` for `Dynamic`;
* lookups made by phases after extraction: the pattern matcher's `_1`, `_2` and arity checks,
  erasure, mixin.

`TCompiler` is `Compiler` with `keysOf : Out → Finset Key`, a function of the output (which
contains the typed tree). The obligations and the loop are unchanged otherwise; coverage now
relates the trace to what the tree shows. T2 and T3a carry over with the same proofs
(`round_preserves`, `zinc_sound`). `TreeToy.lean` has the counterexamples and the fixes:
recording failed lookups, and anticipatory keys for the names a later phase will ask.
-/

namespace Zinc

structure TCompiler (CUnit Src Out Iface K Hash Q : Type) (A : Q → Type) where
  unit   : Src → Task (CUnit × Q) (fun p => A p.2) Out
  group  : Finset CUnit → (CUnit → Src) → Task.Env (CUnit × Q) (fun p => A p.2) → (CUnit → Out)
  iface  : Out → Iface
  answer : Iface → (q : Q) → A q
  π      : Iface → K → Hash
  /-- `U(d)`, extracted from the output (the typed tree), not from the trace. -/
  keysOf : Out → Finset (CUnit × K)
  covers : Q → K → Prop

namespace TCompiler

open Compiler (State Policy)

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : TCompiler CUnit Src Out Iface K Hash Q A)

abbrev Env := Task.Env (CUnit × Q) (fun p => A p.2)

def envOf (I : CUnit → Iface) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  fun p => C.answer (I p.1) p.2

variable [DecidableEq CUnit]

def override (e : Env (CUnit := CUnit) (Q := Q) (A := A)) (G : Finset CUnit)
    (I : CUnit → Iface) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  fun p => if p.1 ∈ G then C.answer (I p.1) p.2 else e p

theorem override_envOf (I I' : CUnit → Iface) (G : Finset CUnit) :
    C.override (C.envOf I) G I' = C.envOf (fun u => if u ∈ G then I' u else I u) := by
  funext p
  simp only [override, envOf]
  split <;> rfl

structure Obligations : Prop where
  comp : ∀ (G : Finset CUnit) (src : CUnit → Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)),
    ∀ d ∈ G, C.group G src e d =
      (C.unit (src d)).run (C.override e G (C.iface ∘ C.group G src e))
  /-- Every traced query has a key among those the tree yields. -/
  coverage : ∀ (s : Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)),
    ∀ q ∈ (C.unit s).trace e, ∃ k ∈ C.keysOf ((C.unit s).run e), q.1 = k.1 ∧ C.covers q.2 k.2
  abstraction : ∀ (i i' : Iface) (k : K), C.π i k = C.π i' k →
    ∀ q, C.covers q k → C.answer i q = C.answer i' q

def env (s : State CUnit Out K) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  C.envOf (C.iface ∘ s.out)

def round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) : State CUnit Out K :=
  let o := C.group R src (C.env s)
  let out' : CUnit → Out := fun u => if u ∈ R then o u else s.out u
  { out := out'
    U := fun d => if d ∈ R then C.keysOf (out' d) else s.U d }

def changed (R : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) : Prop :=
  p.1 ∈ R ∧ C.π (C.iface (s.out p.1)) p.2 ≠ C.π (C.iface (s'.out p.1)) p.2

instance [DecidableEq Hash] (R : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) :
    Decidable (C.changed R s s' p) := by unfold changed; infer_instance

def invalidated [DecidableEq K] [DecidableEq Hash] (S R : Finset CUnit)
    (s s' : State CUnit Out K) : Finset CUnit :=
  S.filter fun d => ∃ p ∈ s'.U d, C.changed R s s' p

def zinc [DecidableEq K] [DecidableEq Hash] (S : Finset CUnit) (src : CUnit → Src)
    (P : Policy CUnit Out K) : ℕ → ℕ → Finset CUnit → State CUnit Out K → Option (State CUnit Out K)
  | 0, _, _, _ => none
  | fuel + 1, n, R, s =>
    let s' := C.round src R s
    let I := C.invalidated S R s s'
    if I ⊆ R then some s' else zinc S src P fuel (n + 1) (P n R s s' I) s'

def UpToDate (src : CUnit → Src) (s : State CUnit Out K) (u : CUnit) : Prop :=
  s.out u = (C.unit (src u)).run (C.env s) ∧
  ∀ q ∈ (C.unit (src u)).trace (C.env s), ∃ k ∈ s.U u, q.1 = k.1 ∧ C.covers q.2 k.2

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

/-- **T2, keys from the tree.** -/
theorem round_preserves (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) (D R : Finset CUnit) (hD : D ⊆ R) (hInv : C.Inv S src s D) :
    C.Inv S src (C.round src R s) (C.invalidated S R s (C.round src R s) \ R) := by
  intro u huS hu
  set s' := C.round src R s with hs'
  by_cases huR : u ∈ R
  · have h2 : s'.out u = C.group R src (C.env s) u := by simp only [hs', round, huR, ite_true]
    have hout : s'.out u = (C.unit (src u)).run (C.env s') := by
      rw [h2, ob.comp R src (C.env s) u huR, ← env_round]
    refine ⟨hout, ?_⟩
    intro q hq
    have hU : s'.U u = C.keysOf (s'.out u) := by simp only [hs', round, huR, ite_true]
    rw [hU, hout]
    exact ob.coverage _ _ q hq
  · have huI : u ∉ C.invalidated S R s s' := fun h => hu (Finset.mem_sdiff.2 ⟨h, huR⟩)
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

/-- **T3a, keys from the tree.** -/
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

end TCompiler
end Zinc
