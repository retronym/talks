import Zinc.Tree
import Zinc.Termination

/-!
# Added and deleted classes

The model's set of classes is fixed, but nothing stops a class from having no source: adding a
class is an edit from `absent`, deleting one an edit to `absent`. An absent class answers every
query with "no such class", and its hash says so.

A client in `package a; package b` refers to `Foo`. The compiler looks in the inner package first
(`a.b.Foo`), then the outer (`a.Foo`). With only `a.Foo` present, the inner lookup is a miss.

Zinc's extractor records the class a reference resolved to, from the typed tree (`today`); the
miss on `a.b.Foo` leaves nothing in the tree. When `a.b.Foo` is added, Zinc invalidates the
dependents of the new class (none, nobody resolved it yet) and nothing else
(`IncrementalCommon.invalidateInitial` only schedules added sources), so the client keeps `a.Foo`
(`added_today_wrong`). Recording the scopes searched (`fixed`) meets the obligations
(`obligations_fixed`) and recompiles it.

Confirmed on Zinc `develop` (`e65e35a8d`), Scala 2.13 and 3: the incremental build compiles only
the added file and succeeds, a clean build fails. The same holds wherever the new class sits in a
scope searched before the one that resolved: a wildcard import that now supplies `Foo` over the
client's own package, or `Option` over `scala.Option`. It does not hold for an explicit or wildcard
import over a class added to the client's package: the import wins, resolution is unchanged.
Pending scripted tests `added-class-*` on retronym/zinc branch `claude/added-class-inner-package`.

The model's `inner`/`outer` stand for any two scopes in search order. A cheap fix in Zinc, coarser
than `fixed`: when a class is added, invalidate the classes that use its simple name (the used-names
relation already indexes them).

Deletion is already handled by keys: the client recorded the class it resolved, whose hash moves
when it becomes absent (`deleted_today_clean`); Zinc also invalidates dependents of removed
classes directly.
-/

namespace Zinc.Added

open Compiler (State Policy)

inductive Cls | outer | inner | client
  deriving DecidableEq, Repr

instance : Fintype Cls := ⟨{.outer, .inner, .client}, by intro x; cases x <;> decide⟩

inductive Src
  | absent
  /-- A class `Foo` with a value. -/
  | foo (v : ℕ)
  /-- `package a; package b; object Client { Foo.v }`. -/
  | client
  deriving DecidableEq, Repr

inductive Q | exists
  deriving DecidableEq, Repr

/-- `some v` if the addressed class exists. -/
abbrev Ans (_ : Q) : Type := Option ℕ

/-- A reference in the typed tree: the classes looked up, and the one it resolved to. -/
structure Ref where
  searched : List Cls
  resolved : Option Cls
  deriving DecidableEq, Repr

structure Out where
  iface : Option ℕ
  refs : List Ref
  value : Option ℕ
  deriving DecidableEq, Repr

inductive K | name
  deriving DecidableEq, Repr

abbrev T := Task (Cls × Q) (fun p => Ans p.2)
abbrev Env := Task.Env (Cls × Q) (fun p => Ans p.2)

def unit : Src → T Out
  | .absent => .pure ⟨none, [], none⟩
  | .foo v => .pure ⟨some v, [], none⟩
  | .client => .ask (.inner, .exists) fun r =>
      match r with
      | some v => .pure ⟨none, [⟨[.inner], some .inner⟩], some v⟩
      | none => .ask (.outer, .exists) fun r' =>
          .pure ⟨none, [⟨[.inner, .outer], r'.map fun _ => .outer⟩], r'⟩

inductive Extractor | today | fixed
  deriving DecidableEq, Repr

def refKeys : Extractor → Ref → List (Cls × K)
  | .today, r => r.resolved.toList.map (·, K.name)
  | .fixed, r => r.searched.map (·, K.name)

def keysOf (x : Extractor) (o : Out) : Finset (Cls × K) := (o.refs.flatMap (refKeys x)).toFinset

def group (G : Finset Cls) (src : Cls → Src) (e : Env) : Cls → Out :=
  fun u => (unit (src u)).run fun p => if p.1 ∈ G then ((unit (src p.1)).run fun _ => none).iface else e p

theorem iface_client (e : Env) : ((unit .client).run e).iface = none := by
  simp only [unit, Task.run_ask]
  split <;> simp [Task.run_ask]

/-- A class's interface does not depend on what it asks. -/
theorem iface_run (s : Src) (e e' : Env) : ((unit s).run e).iface = ((unit s).run e').iface := by
  cases s with
  | absent => rfl
  | foo v => rfl
  | client => rw [iface_client, iface_client]

def compiler (x : Extractor) : TCompiler Cls Src Out (Option ℕ) K (Option ℕ) Q Ans where
  unit := unit
  group := group
  iface := Out.iface
  answer := fun i _ => i
  π := fun i _ => i
  keysOf := keysOf x
  covers := fun _ _ => True

theorem obligations_fixed : (compiler .fixed).Obligations where
  comp := by
    intro G src e d _
    show (unit (src d)).run _ = (unit (src d)).run _
    congr 1
    funext p
    simp only [TCompiler.override, compiler, Function.comp]
    split
    · simp only [group]; exact iface_run _ _ _
    · rfl
  coverage := by
    intro s e q hq
    refine ⟨(q.1, K.name), ?_, rfl, trivial⟩
    change q ∈ (unit s).trace e at hq
    change (q.1, K.name) ∈ keysOf .fixed ((unit s).run e)
    simp only [keysOf, List.mem_toFinset, List.mem_flatMap]
    cases s with
    | absent => simp [unit] at hq
    | foo v => simp [unit] at hq
    | client =>
      simp only [unit, Task.trace_ask, Task.run_ask] at hq ⊢
      revert hq
      split
      · intro hq
        simp only [Task.trace_pure, List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [Task.run_pure, exists_eq_left, refKeys, List.mem_map,
          List.mem_cons, List.not_mem_nil, or_false]
        simp_all
      · intro hq
        simp only [Task.trace_ask, Task.trace_pure, List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [Task.run_ask, Task.run_pure, exists_eq_left, refKeys,
          List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
        rcases hq with h | h <;> simp_all
  abstraction := by
    intro i i' _ h _ _
    exact h

/-- Zinc's extractor misses the inner-scope lookup. -/
theorem not_obligations_today : ¬ (compiler .today).Obligations := by
  intro ob
  obtain ⟨k, hk, h1, _⟩ := ob.coverage .client (fun _ => none) (.inner, .exists)
    (by simp [compiler, unit])
  simp [compiler, unit, keysOf, refKeys] at hk

/-! ## Scripted tests -/

open Cls

abbrev S : Finset Cls := {outer, inner, client}

def dummyOut : Out := ⟨none, [], none⟩

def initial (x : Extractor) (src : Cls → Src) : State Cls Out K :=
  (compiler x).round src S { out := fun _ => dummyOut, U := fun _ => ∅ }

def incremental (x : Extractor) (R₀ : Finset Cls) (src₀ src₁ : Cls → Src) : Option (State Cls Out K) :=
  (compiler x).zinc S src₁ Policy.plain 5 0 R₀ (initial x src₀)

def clean (src : Cls → Src) (u : Cls) : Out := group S src (fun _ => none) u

def clientValue (x : Extractor) (R₀ : Finset Cls) (src₀ src₁ : Cls → Src) : Option (Option ℕ) :=
  (incremental x R₀ src₀ src₁).map (·.out client |>.value)

def before : Cls → Src
  | outer => .foo 1
  | inner => .absent
  | client => .client

def after : Cls → Src
  | inner => .foo 2
  | c => before c

example : (clean before client).value = some 1 := by native_decide
example : (clean after client).value = some 2 := by native_decide

/-- **Adding `a.b.Foo`**: with Zinc's extractor the client keeps `a.Foo`. -/
theorem added_today_wrong : clientValue .today {inner} before after = some (some 1) := by native_decide

/-- Recording the scopes searched recompiles it. -/
theorem added_fixed_clean : clientValue .fixed {inner} before after = some (some 2) := by native_decide

/-- **Deleting `a.b.Foo`** is caught by the key on the class the client resolved. -/
theorem deleted_today_clean : clientValue .today {inner} after before = some (some 1) := by native_decide

end Zinc.Added
