import Zinc.Termination

/-!
# Without `transitiveStep`, Zinc's loop need not terminate

Three classes whose interfaces are inferred from one another, in a cycle: `A.x = B.y`,
`B.y = C.z`, `C.z = h(A.x)`. Each class reads one other class and applies a table to its
interface; values past the table map to 3, so 3 is always a common fixed point, and a group that
contains a whole cycle compiles to it. A group that contains part of a cycle computes along it
from the classes outside. The compiler meets the obligations (`obligations`).

**Zinc's next round** is the invalidated classes *and* the classes whose API changed (the seed of
`invalidateByInheritance`, logged as "transitive inheritance"), `zincPolicy`. That is why two
mutually inferred classes do not alternate in Zinc: the changed class is recompiled together with
its dependent. Three can: every round compiles a pair, and no pair holds the whole cycle.

**The run.** Start from a per-unit fixed point of the old sources (`A.x = B.y = C.z = 2`, all
tables the identity) and change `C`'s table to `0 ↦ 1, 1 ↦ 0, 2 ↦ 0`:

| round | compiles | `A.x` | `B.y` | `C.z` |
|---|---|---|---|---|
| 1 | `C` | 2 | 2 | 0 |
| 2 | `B C` | 2 | 0 | 0 |
| 3 | `A B` | 0 | 0 | 0 |
| 4 | `A C` | 0 | 0 | 1 |
| 5 | `B C` | 0 | 1 | 1 |
| … | … | | | |
| 10 | `A C` | 0 | 0 | 1 (as after round 4) |

* `zinc_diverges`: with Zinc's rule and no `transitiveStep`, the loop does not stop, for every
  amount of fuel.
* `transitiveStep_stops`: with `transitiveStep 3` the brute-force round compiles all three
  together and the loop stops at the joint fixed point.

In Scala the table is a type constructor: `C.z = Some(A.x)` makes the types grow by one `Some` per
round, and the brute-force round's joint compile reports the cyclic inference, as a clean build
does (Zinc scripted test `inferred-type-cycle-rounds`, retronym/zinc branch
`claude/inferred-type-cycle-rounds`).

`lake exe exhaustive pingpong` searches every read graph on three classes, every new table for
one class (the others copy), from every per-unit fixed point: 12,402 runs. With the model's old
loop (invalidated classes only) 1,080 never stop, 900 of them on two-class cycles. With Zinc's
next round, 180 never stop, every one on a three-class cycle; 936 stop after round 2, where
`transitiveStep 3` would already apply. With `transitiveStep 3`, none.
-/

namespace Zinc.PingPong

open Compiler (State Policy)

inductive U | A | B | C
  deriving DecidableEq, Repr

instance : Fintype U := ⟨{.A, .B, .C}, by intro x; cases x <;> decide⟩

inductive Q | val
  deriving DecidableEq, Repr

abbrev Ans (_ : Q) : Type := ℕ

inductive K | val
  deriving DecidableEq, Repr

/-- A class's source: the class it reads, and a table for the values 0, 1, 2. -/
structure Src where
  reads : U
  table : Fin 3 → ℕ

def Src.f (s : Src) (v : ℕ) : ℕ := if h : v < 3 then s.table ⟨v, h⟩ else 3

theorem Src.f_three (s : Src) : s.f 3 = 3 := by simp [Src.f]

abbrev Out := ℕ
abbrev Iface := ℕ

def unit (s : Src) : Task (U × Q) (fun p => Ans p.2) Out :=
  .ask (s.reads, .val) fun v => .pure (s.f v)

/-- The values of a group's classes: follow the reads inside the group, from the interfaces of
the classes outside; a cycle inside the group gives 3. -/
def val (G : Finset U) (rd : U → U) (f : U → ℕ → ℕ) (ext : U → ℕ) : ℕ → U → ℕ
  | 0, u => if rd u ∈ G then 3 else f u (ext (rd u))
  | k + 1, u => if rd u ∈ G then f u (val G rd f ext k (rd u)) else f u (ext (rd u))

/-- With three classes, two steps along the reads are as good as three. -/
theorem val_stable (G : Finset U) (rd : U → U) (f : U → ℕ → ℕ) (ext : U → ℕ)
    (hf : ∀ u, f u 3 = 3) (r : U) : val G rd f ext 2 r = val G rd f ext 3 r := by
  simp only [val]
  cases r <;> cases hA : rd .A <;> cases hB : rd .B <;> cases hC : rd .C <;>
    by_cases a : U.A ∈ G <;> by_cases b : U.B ∈ G <;> by_cases c : U.C ∈ G <;>
    simp [hA, hB, hC, a, b, c, hf]

def group (G : Finset U) (src : U → Src) (e : Task.Env (U × Q) (fun p => Ans p.2)) : U → Out :=
  fun u => if u ∈ G then val G (fun x => (src x).reads) (fun x => (src x).f) (fun x => e (x, .val)) 3 u
    else 0

def compiler : Compiler U Src Out Iface K ℕ Q Ans where
  unit := unit
  group := group
  iface := id
  answer := fun i _ => i
  π := fun i _ => i
  keys := fun tr => (tr.map fun p => (p.1, K.val)).toFinset
  covers := fun _ _ => True

theorem obligations : compiler.Obligations where
  comp := by
    intro G src e d hd
    show group G src e d = (unit (src d)).run _
    simp only [unit, Task.run_ask, Task.run_pure, Compiler.override, compiler, Function.comp, id]
    simp only [group, hd, ite_true]
    rw [show (3 : ℕ) = 2 + 1 from rfl, val]
    by_cases hr : (src d).reads ∈ G
    · simp only [hr, ite_true]
      rw [val_stable G _ _ _ (fun x => Src.f_three _)]
    · simp only [hr, ite_false]
  coverage := by
    intro tr q hq
    refine ⟨(q.1, K.val), ?_, rfl, trivial⟩
    show (q.1, K.val) ∈ (tr.map fun p => (p.1, K.val)).toFinset
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, rfl⟩
  abstraction := by
    intro i i' _ h _ _
    exact h

/-- Zinc's next round: the invalidated classes and the classes whose API changed. -/
def zincPolicy : Policy U Out K := fun _ R s s' I => I ∪ R.filter fun u => s.out u ≠ s'.out u

theorem zincPolicy_sound (S : Finset U) : zincPolicy.Sound S :=
  fun _ _ _ _ _ _ _ hp => Finset.mem_union_left _ (Finset.mem_sdiff.1 hp).1

/-! ## The run -/

abbrev S : Finset U := {U.A, U.B, U.C}

def ident : Fin 3 → ℕ := fun i => i.val

/-- `C`'s new table: `0 ↦ 1, 1 ↦ 0, 2 ↦ 0`. -/
def h₁ : Fin 3 → ℕ := fun i => if i.val = 0 then 1 else 0

def srcOld : U → Src
  | .A => ⟨.B, ident⟩
  | .B => ⟨.C, ident⟩
  | .C => ⟨.A, ident⟩

def src : U → Src
  | .C => ⟨.A, h₁⟩
  | u => srcOld u

/-- A per-unit fixed point of the old sources, with the keys each class recorded. -/
def s₀ : State U Out K :=
  { out := fun _ => 2
    U := fun u => match u with
      | .A => {(U.B, K.val)} | .B => {(U.C, K.val)} | .C => {(U.A, K.val)} }

example : ∀ u, s₀.out u = (compiler.unit (srcOld u)).run (compiler.env s₀) := by
  intro u; cases u <;> rfl

/-- The next round after compiling `R` in `s`, or `none` if the loop stops. -/
def next (R : Finset U) (s : State U Out K) : Option (Finset U) :=
  let s' := compiler.round src R s
  let I := compiler.invalidated S R s s'
  if I ⊆ R then none else some (zincPolicy 0 R s s' I)

theorem step (fuel n : ℕ) (R R' : Finset U) (s : State U Out K) (h : next R s = some R') :
    compiler.zinc S src zincPolicy (fuel + 1) n R s =
      compiler.zinc S src zincPolicy fuel (n + 1) R' (compiler.round src R s) := by
  simp only [next] at h
  simp only [Compiler.zinc]
  split at h
  · cases h
  · rename_i hI
    simp only [hI, ite_false]
    cases h
    rfl

def R₁ : Finset U := {U.C}
def RBC : Finset U := {U.B, U.C}
def RAB : Finset U := {U.A, U.B}
def RAC : Finset U := {U.A, U.C}

def s₁ := compiler.round src R₁ s₀
def s₂ := compiler.round src RBC s₁
def s₃ := compiler.round src RAB s₂
def s₄ := compiler.round src RAC s₃
def s₅ := compiler.round src RBC s₄
def s₆ := compiler.round src RAB s₅
def s₇ := compiler.round src RAC s₆
def s₈ := compiler.round src RBC s₇
def s₉ := compiler.round src RAB s₈
def s₁₀ := compiler.round src RAC s₉

example : [s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀].map (fun s => (s.out .A, s.out .B, s.out .C)) =
    [(2, 2, 0), (2, 0, 0), (0, 0, 0), (0, 0, 1), (0, 1, 1), (1, 1, 1), (1, 1, 0), (1, 0, 0),
     (0, 0, 0), (0, 0, 1)] := by native_decide

theorem n₀ : next R₁ s₀ = some RBC := by native_decide
theorem n₁ : next RBC s₁ = some RAB := by native_decide
theorem n₂ : next RAB s₂ = some RAC := by native_decide
theorem n₃ : next RAC s₃ = some RBC := by native_decide
theorem n₄ : next RBC s₄ = some RAB := by native_decide
theorem n₅ : next RAB s₅ = some RAC := by native_decide
theorem n₆ : next RAC s₆ = some RBC := by native_decide
theorem n₇ : next RBC s₇ = some RAB := by native_decide
theorem n₈ : next RAB s₈ = some RAC := by native_decide
theorem n₉ : next RAC s₉ = some RBC := by native_decide

theorem State.ext' (s t : State U Out K) (h₁ : s.out = t.out) (h₂ : s.U = t.U) : s = t := by
  cases s; cases t; simp_all

/-- Round 10 is back at round 4. -/
theorem s₁₀_eq_s₄ : s₁₀ = s₄ :=
  State.ext' _ _ (funext fun u => by cases u <;> native_decide)
    (funext fun u => by cases u <;> native_decide)

/-- **Zinc's loop without `transitiveStep` does not stop**, whatever the fuel. -/
theorem zinc_diverges : ∀ fuel, compiler.zinc S src zincPolicy fuel 0 R₁ s₀ = none := by
  have cycle : ∀ k n,
      compiler.zinc S src zincPolicy k n RBC s₄ = none ∧
      compiler.zinc S src zincPolicy k n RAB s₅ = none ∧
      compiler.zinc S src zincPolicy k n RAC s₆ = none ∧
      compiler.zinc S src zincPolicy k n RBC s₇ = none ∧
      compiler.zinc S src zincPolicy k n RAB s₈ = none ∧
      compiler.zinc S src zincPolicy k n RAC s₉ = none := by
    intro k
    induction k with
    | zero => intro n; simp [Compiler.zinc]
    | succ k ih =>
      intro n
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [step k n _ _ _ n₄]; exact (ih _).2.1
      · rw [step k n _ _ _ n₅]; exact (ih _).2.2.1
      · rw [step k n _ _ _ n₆]; exact (ih _).2.2.2.1
      · rw [step k n _ _ _ n₇]; exact (ih _).2.2.2.2.1
      · rw [step k n _ _ _ n₈]; exact (ih _).2.2.2.2.2
      · rw [step k n _ _ _ n₉]
        show compiler.zinc S src zincPolicy k (n + 1) RBC s₁₀ = none
        rw [s₁₀_eq_s₄]; exact (ih _).1
  intro fuel
  match fuel with
  | 0 => rfl
  | 1 => rw [step 0 0 _ _ _ n₀]; rfl
  | 2 =>
    rw [step 1 0 _ _ _ n₀]
    change compiler.zinc S src zincPolicy 1 1 RBC s₁ = none
    rw [step 0 1 _ _ _ n₁]; rfl
  | 3 =>
    rw [step 2 0 _ _ _ n₀]
    change compiler.zinc S src zincPolicy 2 1 RBC s₁ = none
    rw [step 1 1 _ _ _ n₁]
    change compiler.zinc S src zincPolicy 1 2 RAB s₂ = none
    rw [step 0 2 _ _ _ n₂]; rfl
  | k + 4 =>
    rw [step (k + 3) 0 _ _ _ n₀]
    change compiler.zinc S src zincPolicy (k + 3) 1 RBC s₁ = none
    rw [step (k + 2) 1 _ _ _ n₁]
    change compiler.zinc S src zincPolicy (k + 2) 2 RAB s₂ = none
    rw [step (k + 1) 2 _ _ _ n₂]
    change compiler.zinc S src zincPolicy (k + 1) 3 RAC s₃ = none
    rw [step k 3 _ _ _ n₃]
    exact (cycle k 4).1

/-- **`transitiveStep` stops**: the brute-force round compiles all three together and the loop
stops at the joint fixed point. -/
theorem transitiveStep_stops :
    ((compiler.zinc S src (Policy.transitiveStep S 3) 8 0 R₁ s₀).map
      fun s => (s.out .A, s.out .B, s.out .C)) = some (3, 3, 3) := by native_decide

end Zinc.PingPong
