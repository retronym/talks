import Mathlib.Data.Finset.Basic

/-!
# Tasks with dynamic dependencies

A compilation task is a query tree: it either returns, or asks a query `q` and continues with a
function of the answer. This is the free monad over the query interface (Build Systems à la Carte,
`Task Monad`). Running it against an oracle `e` gives the output; the *trace* is the list of queries
asked along the way. Both are functions of the task and `e` only, which is the purity assumption.
-/

namespace Zinc

inductive Task (Q : Type) (A : Q → Type) (α : Type) : Type
  | pure (a : α)
  | ask (q : Q) (k : A q → Task Q A α)

namespace Task

variable {Q : Type} {A : Q → Type} {α : Type}

/-- An oracle answering every query. -/
abbrev Env (Q : Type) (A : Q → Type) := (q : Q) → A q

def run (e : Env Q A) : Task Q A α → α
  | pure a => a
  | ask q k => (k (e q)).run e

def trace (e : Env Q A) : Task Q A α → List Q
  | pure _ => []
  | ask q k => q :: (k (e q)).trace e

@[simp] theorem run_pure (e : Env Q A) (a : α) : (pure a : Task Q A α).run e = a := rfl
@[simp] theorem run_ask (e : Env Q A) (q : Q) (k : A q → Task Q A α) :
    (ask q k).run e = (k (e q)).run e := rfl
@[simp] theorem trace_pure (e : Env Q A) (a : α) : (pure a : Task Q A α).trace e = [] := rfl
@[simp] theorem trace_ask (e : Env Q A) (q : Q) (k : A q → Task Q A α) :
    (ask q k).trace e = q :: (k (e q)).trace e := rfl

/-- **T1, trace soundness.** Two oracles that agree on every query in the trace of a task under the
first give the same output (and the same trace). Induction on the query tree. -/
theorem run_eq_of_trace (t : Task Q A α) (e e' : Env Q A)
    (h : ∀ q ∈ t.trace e, e q = e' q) :
    t.run e = t.run e' ∧ t.trace e = t.trace e' := by
  induction t with
  | pure a => simp
  | ask q k ih =>
    have hq : e q = e' q := h q (by simp)
    have h' : ∀ q' ∈ (k (e q)).trace e, e q' = e' q' := fun q' hq' => h q' (by simp [hq'])
    obtain ⟨hr, ht⟩ := ih (e q) h'
    refine ⟨?_, ?_⟩
    · simp only [run_ask]; rw [hr, hq]
    · simp only [trace_ask]; rw [ht, hq]

theorem run_congr (t : Task Q A α) (e e' : Env Q A) (h : ∀ q ∈ t.trace e, e q = e' q) :
    t.run e = t.run e' := (run_eq_of_trace t e e' h).1

theorem trace_congr (t : Task Q A α) (e e' : Env Q A) (h : ∀ q ∈ t.trace e, e q = e' q) :
    t.trace e = t.trace e' := (run_eq_of_trace t e e' h).2

end Task
end Zinc
