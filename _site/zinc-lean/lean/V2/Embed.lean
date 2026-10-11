import V2.Model

/-!
# V1's local model is a special case of the general one

New in this snapshot (the full model keeps `Compiler`, `GCompiler` and `NCompiler` side by side).
A V1 `Compiler`, whose answers and hashes read one interface, lifts to an `NCompiler` with
`hashDeps c = {c}`:

* `lift_obligations`: the lift meets the general obligations whenever the original meets V1's;
* `affected_lift`: with `hashDeps c = {c}`, the units whose hash may change are exactly `R`;
* `zinc_lift`: the general loop on the lift is V1's loop, round for round.

So T2″ and T3a″ cover everything V1 proved, and the talk can present one compiler structure.
-/

namespace V2

open V1

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : V1.Compiler CUnit Src Out Iface K Hash Q A)

/-- A local compiler as an `NCompiler`: every answer and hash reads one interface. -/
def lift [DecidableEq CUnit] : NCompiler CUnit Src Out Iface K Hash Q A where
  unit := C.unit
  group G src I := C.group G src (C.envOf I)
  iface := C.iface
  answer I q := C.answer (I q.1) q.2
  π I c k := C.π (I c) k
  hashDeps _ c := {c}
  keys _ tr := C.keys tr
  covers _ q k := q.1 = k.1 ∧ C.covers q.2 k.2

variable [DecidableEq CUnit]

theorem lift_obligations (ob : C.Obligations) : (lift C).Obligations where
  comp G src I d hd := by
    show C.group G src (C.envOf I) d = (C.unit (src d)).run _
    rw [ob.comp G src (C.envOf I) d hd, C.override_envOf]
    rfl
  coverage I d s q hq := by
    obtain ⟨k, hk, h1, h2⟩ := ob.coverage _ q hq
    exact ⟨k, hk, h1, h2⟩
  abstraction I I' k h q hc := by
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, h1, h2⟩
    show C.answer (I q.1) q.2 = C.answer (I' q.1) q.2
    rw [h1]
    exact ob.abstraction _ _ k.2 h q.2 h2
  locality I I' c h k := by
    show C.π (I c) k = C.π (I' c) k
    rw [h c (Finset.mem_singleton_self c)]

theorem round_lift (src : CUnit → Src) (R : Finset CUnit) (s : Compiler.State CUnit Out K) :
    (lift C).round src R s = C.round src R s := rfl

variable [Fintype CUnit]

theorem affected_lift (R : Finset CUnit) (s : Compiler.State CUnit Out K) :
    (lift C).affected R s = R := by
  ext c
  simp [NCompiler.affected, lift]

variable [DecidableEq K] [DecidableEq Hash]

theorem invalidated_lift (S R : Finset CUnit) (s s' : Compiler.State CUnit Out K) :
    (lift C).invalidated S ((lift C).affected R s) s s' = C.invalidated S R s s' := by
  rw [affected_lift]
  unfold NCompiler.invalidated Compiler.invalidated
  exact Finset.filter_congr fun _ _ => Iff.rfl

/-- The general loop on the lift is V1's loop. -/
theorem zinc_lift (S : Finset CUnit) (src : CUnit → Src) (P : Compiler.Policy CUnit Out K) :
    ∀ fuel n R s, (lift C).zinc S src P fuel n R s = C.zinc S src P fuel n R s := by
  intro fuel
  induction fuel with
  | zero => intro n R s; rfl
  | succ fuel ih =>
    intro n R s
    simp only [NCompiler.zinc, Compiler.zinc, round_lift, invalidated_lift, ih]

end V2
