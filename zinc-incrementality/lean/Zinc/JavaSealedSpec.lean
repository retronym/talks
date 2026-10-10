import Zinc.Tree

/-!
# Exhaustivity against a Java sealed hierarchy, as a specification

A `TCompiler` instance for a client that matches on a sealed class `s` with cases `cs` (Scala's
match under `-Werror`, or Java's `switch` without `default`). Units are classes; a class's
interface is its permitted subclasses (`some ks`) or `none` (not sealed, or absent). The client's
task is the exhaustivity check: walk down from `s`; a class among the cases covers its subtree; a
sealed class asks for its children; any other class is an uncovered leaf. It returns whether the
match is exhaustive and the classes whose children it asked.

Two independent choices make a design:

* the hash of a class's key (`Hashing`): `noChildren` is `ClassToAPI` before retronym/zinc#21,
  which kept no children for a Java class; `children` is #21 (and the Scala bridge);
* the keys a client records (`Keys`): `cases` is Zinc's Scala client (the scrutinee and the classes
  of the type patterns; `ExtractUsedNames` records the scrutinee with `PatMatTarget`); `visited` is
  the fix, a key on every sealed class the check descended through.

Results, over arbitrary hierarchies and clients: `noChildren` fails abstraction (**S1**,
`s1_noChildren`); `children` with `cases` fails coverage on a nested sealed class (**S2**,
`s2_cases`); `children` with `visited` meets the obligations (`obligations_fix`) and inherits T3a
(`fix_sound`).

Not modelled: a Java client's keys. Zinc gives it the ancestors of the classes it names
(sbt/zinc#148), which is `visited` whenever every sealed class on the way down is an ancestor of a
case; the harness showed it catching S2. And a hierarchy in one file, where Zinc recompiles the
parent with the nested class and the Scala bridge's hash lists descendants: per-unit keys cannot
express that, and it is why S2 needs `T` in a file of its own.
-/

set_option linter.unusedSectionVars false

namespace Zinc.JavaSealedSpec

open Compiler (State Policy)

variable {U : Type} [DecidableEq U]

inductive Q | children
  deriving DecidableEq

abbrev Iface (U : Type) := Option (List U)

abbrev Ans (U : Type) (_ : Q) : Type := Iface U

inductive Src (U : Type)
  | absent
  /-- A class: `some ks` if sealed with permitted subclasses `ks`. -/
  | cls (sealedKids : Option (List U))
  /-- `s match { case _: c₁ => …; … }`, checked to depth `fuel`. -/
  | client (s : U) (cs : List U) (fuel : ℕ)

structure Out (U : Type) where
  iface : Iface U
  exhaustive : Bool
  scrut : List U
  cases : List U
  visited : List U

abbrev T (U : Type) := Task (U × Q) (fun p => Ans U p.2)
abbrev Env (U : Type) := Task.Env (U × Q) (fun p => Ans U p.2)

/-- The exhaustivity walk over a worklist: the uncovered leaves, and the classes asked. -/
def walk (cs : List U) : ℕ → List U → T U (List U × List U)
  | 0, ws => .pure (ws, [])
  | _ + 1, [] => .pure ([], [])
  | n + 1, u :: ws =>
    if u ∈ cs then walk cs n ws
    else .ask (u, .children) fun r =>
      match r with
      | none => (walk cs n ws).bind fun (ls, vs) => .pure (u :: ls, u :: vs)
      | some ks => (walk cs n (ks ++ ws)).bind fun (ls, vs) => .pure (ls, u :: vs)

def unit : Src U → T U (Out U)
  | .absent => .pure ⟨none, true, [], [], []⟩
  | .cls k => .pure ⟨k, true, [], [], []⟩
  | .client s cs n => (walk cs n [s]).bind fun (ls, vs) => .pure ⟨none, ls.isEmpty, [s], cs, vs⟩

def ifaceOf : Src U → Iface U
  | .absent => none
  | .cls k => k
  | .client _ _ _ => none

theorem iface_unit (e : Env U) (s : Src U) : ((unit s).run e).iface = ifaceOf s := by
  cases s with
  | absent => rfl
  | cls k => rfl
  | client s cs n => simp only [unit, Task.run_bind, Task.run_pure]; rfl

/-- Every query the walk asks is for the children of a class it reports as visited. -/
theorem trace_walk (cs : List U) (e : Env U) :
    ∀ (n : ℕ) (ws : List U), ∀ q ∈ (walk cs n ws).trace e, q.1 ∈ ((walk cs n ws).run e).2
  | 0, ws, q, h => by simp [walk] at h
  | _ + 1, [], q, h => by simp [walk] at h
  | n + 1, u :: ws, q, h => by
    by_cases hu : u ∈ cs
    · simp only [walk, hu, if_true] at h ⊢
      exact trace_walk cs e n ws q h
    · simp only [walk, hu, if_false, Task.trace_ask, Task.run_ask, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · split <;> simp [Task.run_bind]
      · revert h
        split
        · intro h
          simp only [Task.trace_bind, Task.trace_pure, List.append_nil, Task.run_bind,
            Task.run_pure] at h ⊢
          exact List.mem_cons_of_mem _ (trace_walk cs e n ws q h)
        · intro h
          simp only [Task.trace_bind, Task.trace_pure, List.append_nil, Task.run_bind,
            Task.run_pure] at h ⊢
          exact List.mem_cons_of_mem _ (trace_walk cs e n _ q h)

inductive K | cls
  deriving DecidableEq

inductive Hashing | noChildren | children
  deriving DecidableEq

inductive Keys | cases | visited
  deriving DecidableEq

def π : Hashing → Iface U → K → Iface U
  | .noChildren, i, _ => i.map fun _ => []
  | .children, i, _ => i

def keysOf : Keys → Out U → Finset (U × K)
  | .cases, o => ((o.scrut ++ o.cases).map (·, K.cls)).toFinset
  | .visited, o => ((o.scrut ++ o.cases ++ o.visited).map (·, K.cls)).toFinset

def group (G : Finset U) (src : U → Src U) (e : Env U) : U → Out U :=
  fun u => (unit (src u)).run fun p => if p.1 ∈ G then ifaceOf (src p.1) else e p

def compiler (h : Hashing) (k : Keys) : TCompiler U (Src U) (Out U) (Iface U) K (Iface U) Q (Ans U) where
  unit := unit
  group := group
  iface := Out.iface
  answer := fun i _ => i
  π := π h
  keysOf := keysOf k
  covers := fun _ _ => True

theorem iface_group (G : Finset U) (src : U → Src U) (e : Env U) (u : U) :
    (group G src e u).iface = ifaceOf (src u) := iface_unit _ _

theorem run_client_visited (e : Env U) (s : U) (cs : List U) (n : ℕ) :
    ((unit (.client s cs n)).run e).visited = ((walk cs n [s]).run e).2 := by
  simp only [unit, Task.run_bind, Task.run_pure]

/-- **The fix meets the obligations**: hash the children (#21), and record a key on every sealed
class the check descended through. -/
theorem obligations_fix : (compiler .children .visited (U := U)).Obligations where
  comp := by
    intro G src e u _
    show (unit (src u)).run _ = (unit (src u)).run _
    congr 1
    funext p
    simp only [TCompiler.override, compiler, Function.comp, iface_group]
  coverage := by
    intro s e q hq
    refine ⟨(q.1, .cls), ?_, rfl, trivial⟩
    cases s with
    | absent => simp [compiler, unit] at hq
    | cls k => simp [compiler, unit] at hq
    | client sc cs n =>
      change q ∈ (unit (.client sc cs n)).trace e at hq
      simp only [unit, Task.trace_bind, Task.trace_pure, List.append_nil] at hq
      have hv := trace_walk cs e n [sc] q hq
      change (q.1, K.cls) ∈ keysOf .visited ((unit (.client sc cs n)).run e)
      simp only [keysOf, List.mem_toFinset, List.mem_map, Prod.mk.injEq, and_true, exists_eq_right,
        List.mem_append]
      right
      rw [run_client_visited]
      exact hv
  abstraction := by
    intro i i' _ h _ _
    exact h

/-- **T3a for the fix.** -/
theorem fix_sound (S : Finset U) (src : U → Src U) (P : Policy U (Out U) K) (hP : P.Sound S)
    (fuel n : ℕ) (R : Finset U) (s : State U (Out U) K) (D : Finset U) (hD : D ⊆ R)
    (hInv : (compiler .children .visited).Inv S src s D) (s' : State U (Out U) K)
    (h : (compiler .children .visited).zinc S src P fuel n R s = some s') :
    (compiler .children .visited).Inv S src s' ∅ :=
  (compiler .children .visited).zinc_sound obligations_fix S src P hP fuel n R s D hD hInv s' h

/-- **S1** (retronym/zinc#21's case): without the children in the hash, two interfaces of a sealed
class that differ by a permitted subclass hash alike, whatever keys the client records. -/
theorem s1_noChildren (k : Keys) (a b c : U) :
    ¬ (compiler .noChildren k (U := U)).Obligations := by
  intro ob
  have := ob.abstraction (some [a, b]) (some [a, b, c]) .cls rfl .children trivial
  simp [compiler] at this

end Zinc.JavaSealedSpec

namespace Zinc.JavaSealedSpec.Witness

open Zinc.JavaSealedSpec

/-- `S` (0) permits `A` (1) and `T` (2); `T` permits `B` (3). -/
def env : Env (Fin 4) := fun p =>
  if p.1 = 0 then some [1, 2] else if p.1 = 2 then some [3] else none

/-- **S2**: with the children hashed (#21), a Scala client of `S` with cases `A` and `B` asks for
the children of `T` and records no key on it, so adding `C` to `T`'s `permits` (`T`'s file alone)
leaves it without its error. -/
theorem s2_cases : ¬ (compiler .children .cases (U := Fin 4)).Obligations := by
  intro ob
  obtain ⟨k, hk, h1, _⟩ := ob.coverage (.client 0 [1, 3] 4) env (2, .children) (by decide)
  have hkeys : (compiler .children .cases (U := Fin 4)).keysOf
      (((compiler .children .cases (U := Fin 4)).unit (.client 0 [1, 3] 4)).run env) =
        {(0, .cls), (1, .cls), (3, .cls)} := by decide
  rw [hkeys] at hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl <;> simp at h1

end Zinc.JavaSealedSpec.Witness
