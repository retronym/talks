import Zinc.Termination

/-!
# Sealed hierarchies and exhaustivity

A client matches on a sealed `P` and the compiler checks that the cases cover `P`'s children: a
warning, or an error under `-Werror`, depends on a *negative* fact about the hierarchy (no other
child). In Scala the children of a sealed class must be declared in its file, so they are part of
the parent's source and of its interface: the query is local to `P`, and a key on `P` whose hash
covers the children is enough. Zinc hashes the children of a sealed class into its API
(`ExtractAPI`, `childrenOfSealedClass`).

A Java `sealed interface P permits A, B` names its children in the parent too. Without pipelining
Zinc reads a Java class's API from its classfile (`ClassToAPI`), which listed sealed children only
for enums. The hash then misses the children, abstraction fails (`not_obligations_noChildren`), and
adding a permitted subclass leaves the client without its exhaustivity warning
(`java_permits_wrong`, the case of retronym/zinc#21, which reads `getPermittedSubclasses`).
-/

namespace Zinc.Sealed

open Compiler (State Policy)

inductive Cls | P | A | B | C | M
  deriving DecidableEq, Repr

instance : Fintype Cls := ⟨{.P, .A, .B, .C, .M}, by intro x; cases x <;> decide⟩

inductive Src
  /-- A sealed parent with its children (declared in its file, or named by `permits`). -/
  | sealedParent (children : List Cls)
  | plain
  /-- `x: P match { case … }` over these children. -/
  | client (cases : List Cls)
  deriving DecidableEq, Repr

/-- An interface: the children, if the class is sealed. -/
abbrev Iface := Option (List Cls)

structure Out where
  iface : Iface
  /-- Children not covered by the match. -/
  missing : List Cls
  deriving DecidableEq, Repr

inductive Q | children
  deriving DecidableEq, Repr

abbrev Ans (_ : Q) : Type := Iface

inductive K | sealedChildren
  deriving DecidableEq, Repr

abbrev T := Task (Cls × Q) (fun p => Ans p.2)
abbrev Env := Task.Env (Cls × Q) (fun p => Ans p.2)

def unit : Src → T Out
  | .sealedParent cs => .pure ⟨some cs, []⟩
  | .plain => .pure ⟨none, []⟩
  | .client cases => .ask (.P, .children) fun r =>
      .pure ⟨none, match r with
        | some cs => cs.filter (· ∉ cases)
        | none => []⟩

inductive Hashing
  /-- Children in the parent's hash (Scala, and Java after retronym/zinc#21). -/
  | withChildren
  /-- `ClassToAPI` before the fix: a sealed Java interface with no children listed. -/
  | noChildren
  deriving DecidableEq, Repr

def π : Hashing → Iface → K → Iface
  | .withChildren, i, _ => i
  | .noChildren, i, _ => i.map fun _ => []

theorem iface_run (s : Src) (e : Env) : ((unit s).run e).iface =
    match s with | .sealedParent cs => some cs | _ => none := by
  cases s <;> rfl

def group (G : Finset Cls) (src : Cls → Src) (e : Env) : Cls → Out :=
  fun u => (unit (src u)).run fun p => if p.1 ∈ G then ((unit (src p.1)).run e).iface else e p

def compiler (h : Hashing) : Compiler Cls Src Out Iface K Iface Q Ans where
  unit := unit
  group := group
  iface := Out.iface
  answer := fun i _ => i
  π := π h
  keys := fun tr => (tr.map fun p => (p.1, K.sealedChildren)).toFinset
  covers := fun _ _ => True

theorem obligations_withChildren : (compiler .withChildren).Obligations where
  comp := by
    intro G src e d _
    show (unit (src d)).run _ = (unit (src d)).run _
    congr 1
    funext p
    simp only [Compiler.override, compiler, Function.comp]
    split
    · simp only [group]; rw [iface_run, iface_run]
    · rfl
  coverage := by
    intro tr q hq
    refine ⟨(q.1, K.sealedChildren), ?_, rfl, trivial⟩
    show (q.1, K.sealedChildren) ∈ (tr.map fun p => (p.1, K.sealedChildren)).toFinset
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, rfl⟩
  abstraction := by
    intro i i' _ h _ _
    exact h

/-- Without the children in the hash, two sealed parents with different children look alike. -/
theorem not_obligations_noChildren : ¬ (compiler .noChildren).Obligations := by
  intro ob
  have := ob.abstraction (some [.A]) (some [.A, .B]) .sealedChildren rfl .children trivial
  simp [compiler] at this

/-! ## Scripted tests -/

open Cls

abbrev S : Finset Cls := {P, A, B, C, M}

def dummyOut : Out := ⟨none, []⟩

def initial (h : Hashing) (src : Cls → Src) : State Cls Out K :=
  (compiler h).round src S { out := fun _ => dummyOut, U := fun _ => ∅ }

def missingAfter (h : Hashing) (src₀ src₁ : Cls → Src) : Option (List Cls) :=
  ((compiler h).zinc S src₁ Policy.plain 5 0 {P, C} (initial h src₀)).map (·.out M |>.missing)

def clean (src : Cls → Src) (u : Cls) : Out := group S src (fun _ => none) u

/-- `sealed interface P permits A, B`; `M` matches `A` and `B`. -/
def src₀ : Cls → Src
  | P => .sealedParent [A, B]
  | M => .client [A, B]
  | _ => .plain

/-- `C` is added and permitted. -/
def src₁ : Cls → Src
  | P => .sealedParent [A, B, C]
  | c => src₀ c

example : (clean src₁ M).missing = [C] := by native_decide

/-- **The children not hashed**: `M` keeps an exhaustive match, with no warning. -/
theorem java_permits_wrong : missingAfter .noChildren src₀ src₁ = some [] := by native_decide

/-- The children hashed: `M` is recompiled and warns about `C`. -/
theorem withChildren_clean : missingAfter .withChildren src₀ src₁ = some [C] := by native_decide

end Zinc.Sealed
