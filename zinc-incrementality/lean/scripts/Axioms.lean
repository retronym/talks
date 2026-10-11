import Zinc
import Scala
import BinCompat.ZincBridgeScala3
import BinCompat.ZincBridgeKeys
import BinCompat.ZincBridgeLibs

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
-- the instances' soundness theorems and witnesses
#print axioms Zinc.JavaSpec.fix_sound
#print axioms Zinc.JavaSealedSpec.fix_sound
#print axioms Zinc.JavaOrder.mixed_sound
#print axioms Zinc.SplitProof.Spec.cross_downstream_sound
#print axioms Zinc.SplitProof.Spec.global_obligations
#print axioms Zinc.SplitProof.Spec.narrowed_obligations
#print axioms Zinc.SplitProof.Spec.joint_not_comp
#print axioms Zinc.Cycles.zinc_ne_clean
#print axioms Zinc.Cycles.annotated_eq_clean
#print axioms Zinc.Annotations.fix_sound
#print axioms Zinc.HashForms.conservative_sound
#print axioms Zinc.Naming.Mini.spelling_bugs
#print axioms Zinc.PipelineLifecycle.rollback_preserves
#print axioms Zinc.Synthetic.sound_of_agree
#print axioms Zinc.InlineOpaqueSpec.fix_sound
-- the general form (General.lean), where T2, T3a, T4 (monotone) and T5 are proved once
#print axioms Zinc.XCompiler.round_preserves
#print axioms Zinc.XCompiler.zinc_sound
#print axioms Zinc.XCompiler.zinc_some_of_monotoneFrom
#print axioms Zinc.XCompiler.downstream_sound
-- T3 for keys from the tree, through the forgetful map
#print axioms Zinc.TCompiler.zinc_eq_clean_of_explicit
#print axioms Zinc.SplitProof.Spec.g_global_obligations
#print axioms Zinc.SplitProof.Spec.g_narrowed_obligations
#print axioms Zinc.SplitProof.Spec.g12_today
#print axioms Zinc.TCompiler.downstream_sound
-- the shared asSeenFrom (Scala/AsSeenFrom.lean) and T1 for lowering
#print axioms AsSeenFrom.compose
#print axioms AsSeenFrom.chain_is_single
#print axioms Scala.lower_congr
-- B4 and its extensions
#print axioms Zinc.XCompiler.untouched_eq_clean
#print axioms BinCompat.ZincBridge.gap_witness
#print axioms BinCompat.ZincBridgeScala3.not_comp
#print axioms BinCompat.ZincBridgeScala3.after_eq_fresh_fix
#print axioms BinCompat.ZincBridgeKeys.coverage_fails
#print axioms BinCompat.ZincBridgeKeys.loop_witness
#print axioms BinCompat.ZincBridgeLibs.library_client
-- files as a layer
#print axioms Zinc.XCompiler.round_preserves_charged
#print axioms Zinc.XCompiler.zinc_sound_charged
#print axioms Zinc.FileSpec.today_not_charged
#print axioms Zinc.FileSpec.every_obligations
#print axioms Zinc.Fi.fi_not_covered
#print axioms Zinc.Fi.fi_loop
-- SAM conversion and local classes
#print axioms Zinc.Sam.fix_sound
#print axioms Zinc.Sam.today_sound_argFree
