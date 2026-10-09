namespace Primer

/-! P1. Types, inductives, functions -/

inductive Cls | A | B
  deriving DecidableEq, Repr

inductive Name | m | g
  deriving DecidableEq, Repr

inductive Ty | int | str
  deriving DecidableEq, Repr

structure Member where
  name : Name
  ty   : Ty
  deriving DecidableEq, Repr

def members : Cls → List Member
  | .A => [⟨.m, .int⟩]
  | .B => [⟨.g, .str⟩]

def parent : Cls → Option Cls
  | .A => none
  | .B => some .A

def lookup (c : Cls) (n : Name) : Option Ty :=
  ((members c).find? (·.name == n)).map (·.ty)

#eval lookup .A .m   -- some Ty.int
#eval lookup .B .m   -- none: a miss

/-! P2. A query whose answer type depends on the query -/

inductive Task (Q : Type) (A : Q → Type) (α : Type) : Type
  | pure (a : α)
  | ask (q : Q) (k : A q → Task Q A α)

namespace Task
variable {Q : Type} {A : Q → Type} {α β : Type}

def run (e : (q : Q) → A q) : Task Q A α → α
  | pure a => a
  | ask q k => (k (e q)).run e

def trace (e : (q : Q) → A q) : Task Q A α → List Q
  | pure _ => []
  | ask q k => q :: (k (e q)).trace e

def bind : Task Q A α → (α → Task Q A β) → Task Q A β
  | pure a, f => f a
  | ask q k, f => ask q fun a => (k a).bind f

instance : Monad (Task Q A) where
  pure := Task.pure
  bind := Task.bind
end Task

inductive Query
  | lookup (c : Cls) (n : Name)
  | parent (c : Cls)
  deriving DecidableEq, Repr

def Answer : Query → Type
  | .lookup .. => Option Ty
  | .parent _ => Option Cls

def ask (q : Query) : Task Query Answer (Answer q) := .ask q .pure

/-- Resolve `n` in `c`, else in its parent. The second query depends on the first answer. -/
def resolve : Nat → Cls → Name → Task Query Answer (Option Ty)
  | 0, _, _ => pure none
  | fuel + 1, c, n => do
    match (← ask (.lookup c n) : Option Ty) with
    | some t => pure (some t)
    | none =>
      match (← ask (.parent c) : Option Cls) with
      | some p => resolve fuel p n
      | none => pure none

def env : (q : Query) → Answer q
  | .lookup c n => lookup c n
  | .parent c => parent c

#eval (resolve 3 .B .m).run env     -- some Ty.int
#eval (resolve 3 .B .m).trace env   -- [lookup B m, parent B, lookup A m]

/-! P3. Propositions as types -/

theorem run_eq_of_trace (t : Task Q A α) (e e' : (q : Q) → A q)
    (h : ∀ q ∈ t.trace e, e q = e' q) :
    t.run e = t.run e' ∧ t.trace e = t.trace e' := by
  induction t with
  | pure a => simp [Task.run, Task.trace]
  | ask q k ih =>
    have hq : e q = e' q := h q (by simp [Task.trace])
    obtain ⟨hr, ht⟩ := ih (e q) (fun q' hq' => h q' (by simp [Task.trace, hq']))
    simp only [Task.run, Task.trace]
    rw [hr, ht, hq]
    exact ⟨rfl, rfl⟩

/-! P4. Specs as structures, facts by evaluation -/

/-- The trace records the miss in `B` as well as the hit in `A`. -/
example : (resolve 3 .B .m).trace env =
    [.lookup .B .m, .parent .B, .lookup .A .m] := by decide

end Primer
