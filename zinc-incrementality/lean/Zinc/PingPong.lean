import Zinc.Termination

/-!
# The plain policy need not terminate; `transitiveStep` does

Two classes whose interfaces are inferred from each other: `A`'s from `B`'s (`A.x = B.y`), `B`'s
from `A`'s through a table (`B.y = h(A.x)`). Separately compiled, each takes the other's current
interface; jointly compiled, the pair takes a common fixed point (every table maps 3 to 3, so
`(3, 3)` always is one). The compiler meets the obligations (`obligations`).

Start from a state in which both classes are up to date with `A.x = B.y = 2`, a per-unit fixed
point of the old table, and change `B`'s table so that `2 ↦ 0, 0 ↦ 1, 1 ↦ 0`. With Zinc's plain
policy each round recompiles one class against the other's previous interface, which changes, and
invalidates the other:

| round | compiles | `A.x` | `B.y` |
|---|---|---|---|
| 1 | `B` | 2 | 0 |
| 2 | `A` | 0 | 0 |
| 3 | `B` | 0 | 1 |
| 4 | `A` | 1 | 1 |
| 5 | `B` | 1 | 0 |
| 6 | `A` | 0 | 0 (as after round 2) |

* `plain_diverges`: for every amount of fuel, the plain loop does not stop.
* `transitiveStep_stops`: with `transitiveStep 2`, round 3 compiles both classes together and the
  loop stops at the joint fixed point, as T4 (`zinc_some_of_monotoneFrom`) guarantees in general.

So `transitiveStep` is what makes Zinc terminate on mutually recursive inferred types, not a
heuristic for speed (`zinc-incrementality` §4, §22).
-/

namespace Zinc.PingPong

open Compiler (State Policy)

inductive U | A | B
  deriving DecidableEq, Repr

instance : Fintype U := ⟨{.A, .B}, by intro x; cases x <;> decide⟩

inductive Q | val
  deriving DecidableEq, Repr

abbrev Ans (_ : Q) : Type := ℕ

inductive K | val
  deriving DecidableEq, Repr

/-- A class's source: the class whose interface it reads, and a table applied to that interface
(entries past the table's end map to 3). -/
structure Src where
  reads : U
  table : List ℕ
  deriving DecidableEq, Repr

def Src.f (s : Src) (v : ℕ) : ℕ := s.table.getD v 3

abbrev Out := ℕ
abbrev Iface := ℕ

def unit (s : Src) : Task (U × Q) (fun p => Ans p.2) Out :=
  .ask (s.reads, .val) fun v => .pure (s.f v)

/-- Joint compilation: a class reading a group-mate gets 3 (the common fixed point), one reading
an outsider applies its table to the outsider's interface. -/
def group (G : Finset U) (src : U → Src) (e : Task.Env (U × Q) (fun p => Ans p.2)) : U → Out :=
  fun u => if (src u).reads ∈ G then 3 else (src u).f (e ((src u).reads, .val))

def compiler : Compiler U Src Out Iface K ℕ Q Ans where
  unit := unit
  group := group
  iface := id
  answer := fun i _ => i
  π := fun i _ => i
  keys := fun tr => (tr.map fun p => (p.1, K.val)).toFinset
  covers := fun _ _ => True

/-- Tables map 3 to 3 when they have at most three entries. -/
def Src.Ok (s : Src) : Prop := s.table.length ≤ 3

theorem f_three (s : Src) (h : s.Ok) : s.f 3 = 3 := by
  simp [Src.f, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by unfold Src.Ok at h; omega)]

/-! The obligations hold for sources whose tables have at most three entries. -/

theorem obligations (hok : ∀ s : Src, s.Ok) : compiler.Obligations where
  comp := by
    intro G src e d hd
    show group G src e d = (unit (src d)).run _
    simp only [unit, Task.run_ask, Task.run_pure, group, Compiler.override, compiler,
      Function.comp, id]
    by_cases hr : (src d).reads ∈ G
    · -- with two classes, the class `d` reads reads a group-mate too
      have hr2 : (src (src d).reads).reads ∈ G := by
        by_cases hdr : (src d).reads = d
        · rw [hdr]; exact hr
        · have key : ∀ u : U, u ∈ G := by
            intro u
            have : u = d ∨ u = (src d).reads := by
              generalize (src d).reads = r at hdr ⊢
              cases u <;> cases d <;> cases r <;> simp_all
            rcases this with h | h <;> rw [h] <;> assumption
          exact key _
      simp only [hr, hr2, ite_true]
      exact (f_three _ (hok _)).symm
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

/-! ## The scenario -/

abbrev S : Finset U := {U.A, U.B}

/-- After the edit: `A.x = B.y`, `B.y = h₁(A.x)` with `h₁ = [1, 0, 0]`. -/
def src : U → Src
  | .A => ⟨.B, [0, 1, 2]⟩
  | .B => ⟨.A, [1, 0, 0]⟩

/-- Before the edit `B`'s table was the identity, and `(2, 2)` was a per-unit fixed point. -/
def srcOld : U → Src
  | .A => ⟨.B, [0, 1, 2]⟩
  | .B => ⟨.A, [0, 1, 2]⟩

def s₀ : State U Out K :=
  { out := fun _ => 2, U := fun u => match u with | .A => {(U.B, K.val)} | .B => {(U.A, K.val)} }

/-- `s₀` is up to date for the old sources: both outputs are their own compilation against the
other's interface, and the recorded keys cover the trace. -/
example : ∀ u, s₀.out u = (compiler.unit (srcOld u)).run (compiler.env s₀) := by
  intro u; cases u <;> rfl

example : ∀ u, (compiler.unit (srcOld u)).trace (compiler.env s₀) =
    [((srcOld u).reads, Q.val)] ∧ ((srcOld u).reads, K.val) ∈ s₀.U u := by
  intro u; cases u <;> decide

def s₁ := compiler.round src {U.B} s₀
def s₂ := compiler.round src {U.A} s₁
def s₃ := compiler.round src {U.B} s₂
def s₄ := compiler.round src {U.A} s₃
def s₅ := compiler.round src {U.B} s₄
def s₆ := compiler.round src {U.A} s₅

example : [s₁, s₂, s₃, s₄, s₅, s₆].map (fun s => (s.out U.A, s.out U.B)) =
    [(2, 0), (0, 0), (0, 1), (1, 1), (1, 0), (0, 0)] := by native_decide

theorem State.ext' (s t : State U Out K) (h₁ : s.out = t.out) (h₂ : s.U = t.U) : s = t := by
  cases s; cases t; simp_all

/-- Round 6 is back at round 2. -/
theorem s₆_eq_s₂ : s₆ = s₂ :=
  State.ext' _ _ (funext fun u => by cases u <;> native_decide)
    (funext fun u => by cases u <;> native_decide)

theorem inv₀ : compiler.invalidated S {U.B} s₀ s₁ = {U.A} := by native_decide
theorem inv₂ : compiler.invalidated S {U.B} s₂ s₃ = {U.A} := by native_decide
theorem inv₃ : compiler.invalidated S {U.A} s₃ s₄ = {U.B} := by native_decide
theorem inv₄ : compiler.invalidated S {U.B} s₄ s₅ = {U.A} := by native_decide
theorem inv₅ : compiler.invalidated S {U.A} s₅ s₆ = {U.B} := by native_decide
theorem inv₁ : compiler.invalidated S {U.A} s₁ s₂ = {U.B} := by native_decide

theorem notAB : ¬ ({U.A} : Finset U) ⊆ {U.B} := by decide
theorem notBA : ¬ ({U.B} : Finset U) ⊆ {U.A} := by decide

/-- One plain round that does not stop. -/
theorem step (fuel n : ℕ) (R R' : Finset U) (s : State U Out K)
    (hI : compiler.invalidated S R s (compiler.round src R s) = R') (hR : ¬ R' ⊆ R) :
    compiler.zinc S src Policy.plain (fuel + 1) n R s =
      compiler.zinc S src Policy.plain fuel (n + 1) R' (compiler.round src R s) := by
  simp only [Compiler.zinc, hI, hR, ite_false, Policy.plain]

/-- **The plain policy does not stop**, whatever the fuel. -/
theorem plain_diverges : ∀ fuel, compiler.zinc S src Policy.plain fuel 0 {U.B} s₀ = none := by
  have cycle : ∀ k n, compiler.zinc S src Policy.plain k n {U.B} s₂ = none ∧
      compiler.zinc S src Policy.plain k n {U.A} s₃ = none ∧
      compiler.zinc S src Policy.plain k n {U.B} s₄ = none ∧
      compiler.zinc S src Policy.plain k n {U.A} s₅ = none := by
    intro k
    induction k with
    | zero => intro n; simp [Compiler.zinc]
    | succ k ih =>
      intro n
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [step k n _ _ _ inv₂ notAB]; exact (ih _).2.1
      · rw [step k n _ _ _ inv₃ notBA]; exact (ih _).2.2.1
      · rw [step k n _ _ _ inv₄ notAB]; exact (ih _).2.2.2
      · rw [step k n _ _ _ inv₅ notBA]
        show compiler.zinc S src Policy.plain k (n + 1) {U.B} s₆ = none
        rw [s₆_eq_s₂]; exact (ih _).1
  intro fuel
  match fuel with
  | 0 => rfl
  | 1 => rw [step 0 0 _ _ _ inv₀ notAB]; rfl
  | k + 2 =>
    rw [step (k + 1) 0 _ _ _ inv₀ notAB]
    change compiler.zinc S src Policy.plain (k + 1) 1 {U.A} s₁ = none
    rw [step k 1 _ _ _ inv₁ notBA]
    exact (cycle k 2).1

/-- **`transitiveStep` stops**: from round 2 on, the round includes the last one, so `A` and `B`
compile together and land on the joint fixed point. -/
theorem transitiveStep_stops :
    ((compiler.zinc S src (Policy.transitiveStep S 2) 6 0 {U.B} s₀).map
      fun s => (s.out U.A, s.out U.B)) = some (3, 3) := by native_decide

end Zinc.PingPong
