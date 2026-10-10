import Zinc

/-! The core theorems' axioms, checked by `scripts/check_axioms.py`: only `propext`,
`Classical.choice` and `Quot.sound` are allowed (no `sorryAx`, no `Lean.ofReduceBool` from
`native_decide`). -/

-- T1
#print axioms Zinc.Task.run_eq_of_trace
-- T2, T3a, per framework variant
#print axioms Zinc.Compiler.round_preserves
#print axioms Zinc.Compiler.zinc_sound
#print axioms Zinc.GCompiler.round_preserves
#print axioms Zinc.TCompiler.round_preserves
#print axioms Zinc.TCompiler.zinc_sound
#print axioms Zinc.NCompiler.round_preserves
#print axioms Zinc.NCompiler.zinc_sound
-- T3b, T3
#print axioms Zinc.Compiler.fixpoint_unique_of_wf
#print axioms Zinc.Compiler.fixpoint_unique_of_explicit
#print axioms Zinc.Compiler.zinc_eq_clean_of_wf
#print axioms Zinc.Compiler.zinc_eq_clean_of_explicit
-- T4
#print axioms Zinc.Compiler.zinc_some_of_monotoneFrom
#print axioms Zinc.Compiler.zinc_some_of_explicit
#print axioms Zinc.Compiler.zinc_some_of_wf
-- T5
#print axioms Zinc.NCompiler.downstream_sound
-- a proved counterexample that used to lean on native_decide
#print axioms Zinc.PingPong.zinc_diverges
