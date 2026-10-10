import Zinc.JavaSpec

/-!
# Class-name agreement between the bridge and Zinc

`Model.lean` addresses queries and keys to one `CUnit`. In Zinc a class has (at least) two names:
the one its output carries, through which the compiler reads it (the classfile, the analysed class
name), and the one the bridge records a dependency under. Here a unit is reached through `read`
and recorded through `rec`, both into names; the named task asks `(read u, q)` where the underlying
one asks `(u, q)`, and the named keys are `(rec u, k)`. Coverage then asks `read u = rec u` for every
unit a trace reaches.

* `coverage_named`: if the spellings agree, the named compiler's coverage is the underlying one's.
* `not_coverage_named`: a traced unit whose read spelling no key carries breaks it, whatever the
  underlying compiler; `spelling_bugs` instantiates it for each bug of the cluster.
* `collision`: two units read through one name (one file on a case-insensitive filesystem) cannot
  be served by any named oracle when their answers differ.
* `default_package_1812`: on `JavaSpec`'s instance (whose fix meets the obligations), a client in
  the default package that resolves `A` in its own package asks for `A` and records `<empty>.A`.
-/

namespace Zinc.Naming

variable {CUnit Name Q : Type} {A : Q → Type} {α : Type}

/-- The task with every query's unit replaced by its name. -/
def rename (f : CUnit → Name) : Task (CUnit × Q) (fun p => A p.2) α → Task (Name × Q) (fun p => A p.2) α
  | .pure a => .pure a
  | .ask q k => .ask (f q.1, q.2) fun a => rename f (k a)

/-- The oracle on units that a named oracle induces. -/
def pull (f : CUnit → Name) (e : Task.Env (Name × Q) (fun p => A p.2)) : Task.Env (CUnit × Q) (fun p => A p.2) :=
  fun p => e (f p.1, p.2)

theorem run_rename (f : CUnit → Name) (e : Task.Env (Name × Q) (fun p => A p.2)) :
    ∀ t : Task (CUnit × Q) (fun p => A p.2) α, (rename f t).run e = t.run (pull f e)
  | .pure _ => rfl
  | .ask q k => by
    simp only [rename, Task.run_ask]
    exact run_rename f e (k (e (f q.1, q.2)))

theorem trace_rename (f : CUnit → Name) (e : Task.Env (Name × Q) (fun p => A p.2)) :
    ∀ t : Task (CUnit × Q) (fun p => A p.2) α,
      (rename f t).trace e = (t.trace (pull f e)).map fun p => (f p.1, p.2)
  | .pure _ => rfl
  | .ask q k => by
    simp only [rename, Task.trace_ask, List.map_cons]
    exact congrArg _ (trace_rename f e (k (e (f q.1, q.2))))

variable {Src Out Iface K Hash : Type} [DecidableEq Name] [DecidableEq K]

/-- The named compiler's coverage: every query of a unit's renamed task has a renamed key. -/
def NamedCoverage (C : TCompiler CUnit Src Out Iface K Hash Q A) (read rec : CUnit → Name) : Prop :=
  ∀ (s : Src) (e : Task.Env (Name × Q) (fun p => A p.2)), ∀ q ∈ (rename read (C.unit s)).trace e,
    ∃ k ∈ (C.keysOf ((rename read (C.unit s)).run e)).image (fun k => (rec k.1, k.2)),
      q.1 = k.1 ∧ C.covers q.2 k.2

/-- **Agreement suffices**: with one spelling, the named compiler covers what the underlying one
covers. -/
theorem coverage_named (C : TCompiler CUnit Src Out Iface K Hash Q A) (read rec : CUnit → Name)
    (hcov : ∀ (s : Src) (e : Task.Env (CUnit × Q) (fun p => A p.2)), ∀ q ∈ (C.unit s).trace e,
      ∃ k ∈ C.keysOf ((C.unit s).run e), q.1 = k.1 ∧ C.covers q.2 k.2)
    (hagree : ∀ u, read u = rec u) : NamedCoverage C read rec := by
  intro s e q hq
  rw [trace_rename, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  obtain ⟨k, hk, h1, h2⟩ := hcov s (pull read e) p hp
  refine ⟨(rec k.1, k.2), ?_, ?_, h2⟩
  · rw [run_rename]; exact Finset.mem_image_of_mem _ hk
  · simp only [h1, hagree]

/-- **Disagreement breaks coverage**: a traced unit whose read spelling no covering key carries. -/
theorem not_coverage_named (C : TCompiler CUnit Src Out Iface K Hash Q A) (read rec : CUnit → Name)
    (s : Src) (e : Task.Env (Name × Q) (fun p => A p.2)) (q : CUnit × Q)
    (hq : q ∈ (C.unit s).trace (pull read e))
    (hnot : ∀ k ∈ C.keysOf ((C.unit s).run (pull read e)), C.covers q.2 k.2 → rec k.1 ≠ read q.1) :
    ¬ NamedCoverage C read rec := by
  intro h
  obtain ⟨k, hk, h1, h2⟩ := h s e (read q.1, q.2)
    (by rw [trace_rename, List.mem_map]; exact ⟨q, hq, rfl⟩)
  rw [run_rename, Finset.mem_image] at hk
  obtain ⟨k', hk', rfl⟩ := hk
  exact hnot k' hk' h2 h1.symm

/-- **A collision**: two units read through one name get the same answers from any named oracle,
so none serves interfaces that answer them differently. -/
theorem collision (read : CUnit → Name) (answer : CUnit → (q : Q) → A q) (u v : CUnit) (q : Q)
    (hname : read u = read v) (hdiff : answer u q ≠ answer v q) :
    ¬ ∃ e : Task.Env (Name × Q) (fun p => A p.2), ∀ w (x : Q), e (read w, x) = answer w x := by
  rintro ⟨e, he⟩
  apply hdiff
  rw [← he u q, ← he v q, hname]

end Zinc.Naming

/-! ## The cluster's bugs, on a minimal compiler

A client (unit 1) reads one class (unit 0) and records a key on it, as Zinc's bridges do; each bug
is a pair of spellings of unit 0. -/

namespace Zinc.Naming.Mini

open Zinc.Naming

inductive Q | get
  deriving DecidableEq

abbrev Ans (_ : Q) : Type := ℕ

def unit : Bool → Task (Fin 2 × Q) (fun p => Ans p.2) ℕ
  | true => .ask (0, .get) .pure
  | false => .pure 0

def compiler : TCompiler (Fin 2) Bool ℕ ℕ Unit ℕ Q Ans where
  unit := unit
  group := fun _ src e u => (unit (src u)).run e
  iface := id
  answer := fun i _ => i
  π := fun i _ => i
  keysOf := fun _ => {(0, ())}
  covers := fun _ _ => True

/-- The cluster: the name the compiler reads class 0 through, and the name the bridge records. -/
def bugs : List (String × String × String) :=
  [("sbt/zinc#1812, scala/scala3#27134: Java class in the default package", "A", "<empty>.A"),
   ("sbt/zinc#127: Java inner class, expanded name", "A$Inner", "A.Inner"),
   ("sbt/zinc#1351: Java nested class under Scala 3 pipelining", "A.Inner", "A$Inner"),
   ("scala/scala3#9694: inner class reported through its top-level associatedFile", "O$I", "O"),
   ("sbt/zinc#716, #1233: compactified classfile name", "p.Outer$$Inner$$$$abc123$Leaf", "p.Outer$Inner$VeryLong$Leaf")]

def spell (r k : String) (u : Fin 2) : String := if u = 0 then r else "Client"

/-- **Every bug of the cluster breaks coverage.** -/
theorem spelling_bugs : ∀ b ∈ bugs, ¬ NamedCoverage compiler (spell b.2.1 b.2.2) (spell b.2.2 b.2.2) := by
  intro b hb
  apply not_coverage_named compiler _ _ true (fun _ => 0) (0, .get) (by simp [compiler, unit, pull])
  intro k hk _
  have : k = (0, ()) := by simpa [compiler] using hk
  subst this
  simp only [spell, if_true]
  revert b
  decide

/-- With one spelling the minimal compiler is covered. -/
example (r : String) : NamedCoverage compiler (spell r r) (spell r r) :=
  coverage_named compiler _ _ (by
    intro s e q hq
    cases s with
    | true => exact ⟨(0, ()), by simp [compiler], by simp_all [compiler, unit], trivial⟩
    | false => simp [compiler, unit] at hq) (fun _ => rfl)

/-- **sbt/zinc#1553**: `A` and `a` on a case-insensitive filesystem are one file. -/
example : ¬ ∃ e : Task.Env (String × Q) (fun p => Ans p.2), ∀ w (x : Q),
    e ((fun u : Fin 2 => "A") w, x) = (fun u _ => if u = 0 then 1 else 2) w x :=
  collision (fun _ => "A") (fun u _ => if u = 0 then 1 else 2) 0 1 .get rfl (by decide)

end Zinc.Naming.Mini

/-! ## sbt/zinc#1812 on `JavaSpec`'s instance

`JavaSpec`'s fix meets the obligations with one spelling of a unit. In the default package the
compiler reads `A` (the classfile's name), the Scala 3 bridge records `<empty>.A`. -/

namespace Zinc.Naming.DefaultPackage

open Zinc.Naming Zinc.JavaSpec

abbrev P := Fin 2
abbrev Nm := Fin 1

/-- Package 0 is the default package; package 1 is `q`. -/
def pkgName (p : P) : String := if p = 0 then "" else "q."

def readName (u : CU P Nm) : String := pkgName u.1 ++ "A"
def recName (u : CU P Nm) : String := (if u.1 = 0 then "<empty>." else pkgName u.1) ++ "A"

/-- A client in the default package that names `A`. -/
def client : Client P Nm := ⟨0, 0, [], [], [], [], []⟩

def env : Task.Env (String × JavaSpec.Q Nm) (fun p => JavaSpec.Ans p.2) := fun p => decide (p = ("A", .present))

theorem default_package_1812 :
    ¬ NamedCoverage (compiler (1 : P) .fix (Pkg := P) (N := Nm)) readName recName := by
  apply not_coverage_named _ readName recName (.client client) env ((0, 0), .present) (by decide)
  intro k _ _
  have h : ∀ u : CU P Nm, recName u ≠ readName ((0 : P), (0 : Nm)) := by decide
  exact h k.1

/-- With one spelling, the fix's coverage carries over. -/
example : NamedCoverage (compiler (1 : P) .fix (Pkg := P) (N := Nm)) readName readName :=
  coverage_named _ _ _ (obligations_fix (1 : P)).coverage (fun _ => rfl)

end Zinc.Naming.DefaultPackage
