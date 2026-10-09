# Zinc soundness, mechanised

A Lean 4 + Mathlib model of §22 of the talk. It proves Zinc's invalidation loop sound relative to stated obligations on the compiler bridge; it does not verify scalac. The hypotheses are the point: they are the bridge spec.

```bash
lake exe cache get && lake build
```

Lean `v4.34.1`, Mathlib tag `v4.34.1`. No `sorry`. The scripted examples use `native_decide`.

## Layout

| File | Contents |
|---|---|
| `Zinc/Task.lean` | Free monad of query trees; `run`, `trace`; **T1** `run_eq_of_trace` (trace soundness) |
| `Zinc/Model.lean` | `Compiler` (per-unit task, joint compiler, `iface`, `answer`, `π`, `keys`, `covers`), `Obligations` (compositionality, coverage, abstraction), `State`, `round`, `invalidated`, `Policy`, fuelled `zinc` loop |
| `Zinc/Soundness.lean` | `UpToDate`/`Inv`; **T2** `round_preserves`; **T3a** `zinc_sound` (termination ⇒ per-unit fixed point); `inv_of_changed` |
| `Zinc/Uniqueness.lean` | **T3b** `fixpoint_unique_of_wf`, `fixpoint_unique_of_explicit`; **T3** `zinc_eq_clean_of_wf`, `zinc_eq_clean_of_explicit` |
| `Zinc/Termination.lean` | **T4** `zinc_some_of_monotoneFrom` (`transitiveStep`), `zinc_some_of_explicit` (2 rounds), `zinc_some_of_wf` (height + 2 rounds) |
| `Zinc/Toy.lean` | Toy object language (members, value classes, implicits with shadowing), name-only vs repaired extractors, `obligations_repaired`, `not_obligations_nameOnly` |
| `Zinc/Examples.lean` | §15b value class and §15a implicit addition/shadowing as `example`s; `repaired_sound`, `repaired_terminates` |
| `Zinc/NonLocal.lean` | `GCompiler`: non-local `π` with `hashDeps`, interface-dependent closure keys; **T2′** `round_preserves` with `Δ` over `affected` |
| `Zinc/Stale.lean` | **T2-stale**: a non-local hash diffed over the recompiled set alone undercompiles (two-unit counterexample) |
| `Zinc/Hier.lean` | Toy class hierarchy (type argument, linearization walk, misses); designs `D` (decls + walk), `W` (materialised), `Mk` (Merkle, verifying-trace hash); Zinc's hierarchy walk as `walkPolicy`; three scenarios as checked `example`s (invalidated sets, rounds, equals clean) |
| `Zinc/HierSound.lean` | `D_obligations`, `W_obligations`, `Mk_obligations`: all three designs are sound instances |
| `Zinc/NonLocalAns.lean` | `NCompiler`: answers and hash read sets may read several interfaces; **T2″** `round_preserves`, **T3a″** `zinc_sound` |
| `Zinc/Flat.lean` | The Zinc PoC's flattened Merkle hash over a *stored* linearization; `Fl_obligations`/`flat_sound` (sound with header keys); header rule as keys vs as a policy, transitive vs direct-children counterexample; refchecks prelude (override, conflict, abstract queries) and codegen epilogue (mixin and static forwarders, `final` parents) and their per-kind ablation |
| `Zinc/Erasure.lean` | Erasure through inheritance: rendering as seen from (Scala 2) or as declared (Scala 3); erasure inputs (type parameters, a value class, an intersection); witnesses (sbt/zinc#1844's annotation, erased signature at definition, recomputed, divergence-only), a dependency edge, a kind-covering class-name hash; `asf_of_decl`; `Er_obligations`; the scripted cases as checked examples; `lake exe exhaustive erasure` compares 13 variants |
| `Zinc/FlatRules.lean`, `Exhaustive.lean` | The PoC's descendant rules as a policy (no refchecks keys); bounded exhaustive check (`lake exe exhaustive`): the `abstract` rule as stated is unsound, widened it is clean, `trait` can be narrowed to direct mixins; minimal counterexample per rule as checked examples |
| `Conformance.lean` | `lake exe conformance`: the `FlatRules` program space as JSON lines, with the model's verdict per edit, for the Zinc conformance harness (`sbt.internal.inc.bench.Conformance`), which compares incremental and clean classfiles |

See `PLAN.md` for the design, the encoding choices and the two findings that fed back into the talk (Zinc's actual loop formula; the fixed-point uniqueness hypothesis T3 needs).
