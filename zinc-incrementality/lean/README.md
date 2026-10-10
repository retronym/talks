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
| `Zinc/ImplicitScope.lean` | Implicit scope through an ancestor's companion across projects (sbt/zinc#1845): search over base classes' companions, Zinc's name hashes (inherited members included), projects as policies; the fix stored (Zinc) or recomputed; `is_obligations`/`is_sound` (recomputed, published for objects too: sound with no in-project rule); `stored_eq_recomputed` (cold vs warm, on consistent states); the scripted tests, the `apiHash`-fold ablation and the object-singleton gap as checked examples; `lake exe exhaustive implicit` compares against the in-project fallback; `reportComposed` runs one loop per project, and `lake exe exhaustive composed` compares it with the single loop |
| `Zinc/FlatRules.lean`, `Exhaustive.lean` | The PoC's descendant rules as a policy (no refchecks keys); bounded exhaustive check (`lake exe exhaustive`): the `abstract` rule as stated is unsound, widened it is clean, `trait` can be narrowed to direct mixins; minimal counterexample per rule as checked examples |
| `Zinc/Classpath.lean`, `Zinc/Snapshot.lean` | Upstream subprojects and libraries: stored snapshots, Zinc's external invalidation; **T5** `inv_external`, `downstream_sound`; snapshot refresh: `fresh_refreshAll`, `fresh_refreshRef_local`, and the edit-then-revert counterexample for a non-local hash (`stale_after_revert`, the PoC's `macro-upstream-member-removed`) |
| `Zinc/Pipelining.lean`, `Zinc/Inline.lean` | Early outputs: `early_agreement`; a failed upstream after its early output (`stale_after_failed_upstream`); bodies as API (Scala 2 `@inline`, Scala 3 `inline`, Java constants), `pipelined_ne_final` |
| `Zinc/Tree.lean`, `Zinc/TreeToy.lean` | Keys extracted from the typed tree (`TCompiler`, T2/T3a); `+=` desugaring and pattern-matcher selectors: Zinc's extractor fails coverage, failed lookups and an arity sentinel fix it |
| `Zinc/PingPong.lean` | Without `transitiveStep`, Zinc's loop (next round = invalidated + API-changed classes) need not terminate on three mutually inferred classes: `zinc_diverges` (every amount of fuel), `transitiveStep_stops`; `lake exe exhaustive pingpong` searches the space |
| `Zinc/Embed.lean` | `Compiler` lifts to `NCompiler`: `lift_obligations`, `zinc_lift` |
| `Zinc/Added.lean`, `Zinc/Sealed.lean` | Added and deleted classes (a class added in an inner package scope is missed, confirmed on Zinc `develop`); sealed children and Java `permits` |
| `Zinc/Names.lean`, `Zinc/Givens.lean` | Name resolution: a simple name bound in nine scopes (a block import, an inherited member, explicit and wildcard imports, inner and outer packages, the package object, `scala._`, Scala 3 exports), and an instance found by type (Scala 2 implicits, Scala 3 givens); Scala's resolution per version, Zinc's recorded edges, the verdict per edit; the divergence families as checked examples; recording the scopes searched, or invalidating a name's users on every added or removed binding, is clean on the whole space |
| `Zinc/InlineOpaque.lean` | Scala 3 `inline` bodies and opaque types: a small Zinc loop over keys, with what dotc 3.9.0 records and hashes; inline constants through a path, type-level reads of an alias and transparent expansions leave the client stale, and so does an opaque type's erasure in an inherited signature (mixin forwarder, inherited bridge); hashing constants and types in inline bodies, or recording the body's references, and recording the types an inherited signature's erasure reads, are clean on the whole space |
| `Zinc/InlineOpaqueSound.lean` | The same observables as an `NCompiler` instance over every program of a slot language (inline bodies issue their reads in the client's trace, tagged with their context): recording the expansion's references and the types a forwarder's erasure reads, or hashing what an inline def's references denote, meets the obligations, so T2″/T3a″ hold; today's recording fails coverage, with one counterexample per family |
| `Zinc/JavaNames.lean`, `Zinc/JavaSealed.lean` | Java in mixed builds: a Java or Scala client's simple name bound by Java sources (member classes, single-static and on-demand imports, the package, `java.lang`), with Java's and Scala's rules and Zinc's Java edges (constant pool, no used names, no import edges); exhaustivity of a Java `switch` or a Scala match against a Java sealed hierarchy, one and two levels deep; the families as checked examples, and the fixes clean on the spaces |
| `Conformance.lean` | `lake exe conformance`: the `FlatRules` program space as JSON lines, with the model's verdict per edit, for the Zinc conformance harness (`sbt.internal.inc.bench.Conformance`), which compares incremental and clean classfiles; `conformance names 2\|3` and `conformance givens 2\|3` dump the name-resolution spaces as source files, `conformance inline\|opaque [mode]` the Scala 3 spaces of `InlineOpaque.lean` (`scripts/` selects, analyses and counts); `JConformance.lean` (`lake exe jconformance`) dumps the Java spaces |

See `PLAN.md` for the design, the encoding choices and the two findings that fed back into the talk (Zinc's actual loop formula; the fixed-point uniqueness hypothesis T3 needs).
