# Zinc soundness, mechanised

A Lean 4 + Mathlib model of §22 of the talk. It proves Zinc's invalidation loop sound relative to stated obligations on the compiler bridge; it does not verify scalac. The hypotheses are the point: they are the bridge spec.

```bash
lake exe cache get && lake build
```

Lean `v4.34.1`, Mathlib tag `v4.34.1`. No `sorry`. The scripted examples use `native_decide`.

**Start here.** `Zinc/Model.lean` is the specification's first page. `DESIGN-spec.md` says what the model is: a specification whose obligations a compiler bridge and Zinc's rules must meet. `PLAN.md` opens with a table of what is proved for every program and what is only checked on a space, phase by phase. The phase files (`PLAN-names.md`, `PLAN-inline.md`, `PLAN-java.md`, `PLAN-split.md`, `PLAN-order.md`) hold the details. `REVIEW-2026-10-11.md` is a review of the framework and its next steps. `BUGS-catalogue.md` and `TESTS-catalogue.md` list Zinc's incremental-compilation bugs and pending scripted tests; `BUG-MAP.md` maps each to the instance that covers it, or to a gap.

## Layout, by role

### Framework

The compiler as a task with a trace, the bridge as keys, the obligations, and Zinc's loop with its soundness, uniqueness and termination theorems, in four variants (local hash, non-local hash, keys from the output, upstream snapshots; REVIEW finding 1 proposes merging them).

| File | Contents |
|---|---|
| `Zinc/Task.lean` | Free monad of query trees; `run`, `trace`; **T1** `run_eq_of_trace` (trace soundness) |
| `Zinc/Model.lean` | `Compiler` (per-unit task, joint compiler, `iface`, `answer`, `π`, `keys`, `covers`), `Obligations` (compositionality, coverage, abstraction), `State`, `round`, `invalidated`, `Policy`, fuelled `zinc` loop |
| `Zinc/General.lean` | `XCompiler`, the general form every variant lifts into: non-local answers and hashes (`hashDeps`), keys from the output and the trace; **T2** `round_preserves`, **T3a** `zinc_sound`, **T4** for monotone policies, **T5** `downstream_sound` and the snapshot results, proved once. `Compiler`, `TCompiler`, `GCompiler` and `NCompiler` each have a lift `toX` with `toX_obligations` (and `zinc_toX` where the variant has a loop), and their theorems are corollaries |
| `Zinc/Soundness.lean` | `UpToDate`/`Inv`; **T2** `round_preserves`; **T3a** `zinc_sound` (termination ⇒ per-unit fixed point); `inv_of_changed` |
| `Zinc/Uniqueness.lean` | **T3b** `fixpoint_unique_of_wf`, `fixpoint_unique_of_explicit`; **T3** `zinc_eq_clean_of_wf`, `zinc_eq_clean_of_explicit` |
| `Zinc/Termination.lean` | **T4** `zinc_some_of_monotoneFrom` (`transitiveStep`), `zinc_some_of_explicit` (2 rounds), `zinc_some_of_wf` (height + 2 rounds) |
| `Zinc/NonLocal.lean` | `GCompiler`: non-local `π` with `hashDeps`, interface-dependent closure keys; **T2′** `round_preserves` with `Δ` over `affected` |
| `Zinc/NonLocalAns.lean` | `NCompiler`: answers and hash read sets may read several interfaces; **T2″** `round_preserves`, **T3a″** `zinc_sound` |
| `Zinc/Tree.lean`, `Zinc/TreeToy.lean` | Keys extracted from the typed tree (`TCompiler`, T2/T3a); `+=` desugaring and pattern-matcher selectors: Zinc's extractor fails coverage, failed lookups and an arity sentinel fix it |
| `Zinc/Classpath.lean`, `Zinc/Snapshot.lean` | Upstream subprojects and libraries: stored snapshots, Zinc's external invalidation; **T5** `inv_external`, `downstream_sound`; snapshot refresh: `fresh_refreshAll`, `fresh_refreshRef_local`, and the edit-then-revert counterexample for a non-local hash (`stale_after_revert`, the PoC's `macro-upstream-member-removed`) |
| `Zinc/Embed.lean` | `Compiler` lifts to `NCompiler`: `lift_obligations`, `zinc_lift` |

### Specifications

Instances of the framework for a language feature: today's bridge as keys, the families as failed obligations with witnesses, the fixes with the obligations proved for every program.

| File | Contents |
|---|---|
| `Zinc/Toy.lean` | Toy object language (members, value classes, implicits with shadowing), name-only vs repaired extractors, `obligations_repaired`, `not_obligations_nameOnly` |
| `Zinc/Hier.lean` | Toy class hierarchy (type argument, linearization walk, misses); designs `D` (decls + walk), `W` (materialised), `Mk` (Merkle, verifying-trace hash); Zinc's hierarchy walk as `walkPolicy`; three scenarios as checked `example`s (invalidated sets, rounds, equals clean) |
| `Zinc/HierSound.lean` | `D_obligations`, `W_obligations`, `Mk_obligations`: all three designs are sound instances |
| `Zinc/Flat.lean` | The Zinc PoC's flattened Merkle hash over a *stored* linearization; `Fl_obligations`/`flat_sound` (sound with header keys); header rule as keys vs as a policy, transitive vs direct-children counterexample; refchecks prelude (override, conflict, abstract queries) and codegen epilogue (mixin and static forwarders, `final` parents) and their per-kind ablation |
| `Zinc/Erasure.lean` | Erasure through inheritance: rendering as seen from (Scala 2) or as declared (Scala 3); erasure inputs (type parameters, a value class, an intersection); witnesses (sbt/zinc#1844's annotation, erased signature at definition, recomputed, divergence-only), a dependency edge, a kind-covering class-name hash; `asf_of_decl`; `Er_obligations`; the scripted cases as checked examples; `lake exe exhaustive erasure` compares 13 variants |
| `Zinc/ImplicitScope.lean` | Implicit scope through an ancestor's companion across projects (sbt/zinc#1845): search over base classes' companions, Zinc's name hashes (inherited members included), projects as policies; the fix stored (Zinc) or recomputed; `is_obligations`/`is_sound` (recomputed, published for objects too: sound with no in-project rule); `stored_eq_recomputed` (cold vs warm, on consistent states); the scripted tests, the `apiHash`-fold ablation and the object-singleton gap as checked examples; `lake exe exhaustive implicit` compares against the in-project fallback; `reportComposed` runs one loop per project, and `lake exe exhaustive composed` compares it with the single loop |
| `Zinc/Pipelining.lean`, `Zinc/Inline.lean` | Early outputs: `early_agreement`; a failed upstream after its early output (`stale_after_failed_upstream`); bodies as API (Scala 2 `@inline`, Scala 3 `inline`, Java constants), `pipelined_ne_final` |
| `Zinc/Added.lean`, `Zinc/Sealed.lean` | Added and deleted classes (a class added in an inner package scope is missed, confirmed on Zinc `develop`); sealed children and Java `permits` |
| `Zinc/SplitProof.lean`, `Zinc/Split.lean` | The shared names instance `SplitProof.Spec` (an `NCompiler` over a client and its scopes, units split into `Up` and `S`): today fails coverage upstream, #34's key fails abstraction across subprojects, the cross-subproject key meets T5 (`cross_downstream_sound`); the Phase 10 rules (`rules_obligations`, `global_obligations`, `narrowed_obligations` given recorded package imports), precision (`necessary_invalidated`, `searched_exact`, `narrowed_le_global`, `rules_over`), F4/F5 as `joint_not_comp`; the slot language's `proposed_sound`. `Split.lean` checks the slot language against `Names.lean` on the bases |
| `Zinc/SpecGivens.lean` | Implicit search on the shared names instance's scopes, as an `XCompiler` (keys read the output's resolved scope; the search asks the whole level of its hit): today fails coverage on G1/G2 (`g12_today`); the G rule meets the obligations, global (`g_global_obligations`) or narrowed given recorded package imports (`g_narrowed_obligations`), and so does `searched`; narrowed without the recorded import fails (`g_narrowed_without_imports`); #24's declarations-only hash fails abstraction on an inherited instance (`g_decls_not_abstraction`) |
| `Zinc/JavaSpec.lean`, `Zinc/JavaSealedSpec.lean` | Java name resolution and sealed exhaustivity as `TCompiler` instances: today fails coverage (J1–J4, S1, S2), the fixes' `obligations_fix` and T3a |
| `Zinc/JavaOrder.lean` | A Java class's two views (scalac's source view, javac's classfile): `obligations_mixed`, `mixed_sound` under view agreement; compile orders and pipelining's early output fail `comp` otherwise (V1, V2, O1, O2); Zinc's exclusion of passed-in Java classes is exact (`exclusion_exact`), the hash flip spurious (`flip_spurious`) |

### Executable models and checks

Bounded program spaces with each compiler's rules and Zinc's verdict per edit, checked by `native_decide` (`example`s) and dumped for the conformance harness, which compares them with Zinc, scalac, dotc and javac. They found most families and give the costs.

| File | Contents |
|---|---|
| `ZincNames/Names.lean`, `ZincNames/Givens.lean`, `Zinc/NamesRules.lean` | Name resolution: a simple name bound in nine scopes (a block import, an inherited member, explicit and wildcard imports, inner and outer packages, the package object, `scala._`, Scala 3 exports; the package object's and `W`'s member possibly inherited), and an instance found by type (Scala 2 implicits, Scala 3 givens); Scala's resolution per version, Zinc's recorded edges, the verdict per edit; the divergence families and the extensions of retronym/zinc#34 (a rule per family, global or narrowed, on develop's and #24's API) as checks on a bounded space, with what each recompiles beyond the necessary. `ZincNames` is a precompiled library, so the whole-space checks in `NamesRules.lean` run natively |
| `Zinc/InlineOpaque.lean` | Scala 3 `inline` bodies and opaque types: a small Zinc loop over keys, with what dotc 3.9.0 records and hashes; inline constants through a path, type-level reads of an alias and transparent expansions leave the client stale, and so does an opaque type's erasure in an inherited signature (mixin forwarder, inherited bridge); hashing constants and types in inline bodies, or recording the body's references, and recording the types an inherited signature's erasure reads, are clean on the whole space |
| `Zinc/InlineOpaqueSpec.lean` | The specification: a `TCompiler` whose task is dotc's inlining and erasure (queries `inlineBody`, `constant`, `aliasRhs`, `sig`, `erasure`, `meths`) and whose keys are read off the tree after inlining; today's bridge fails coverage (witnesses I1–I3, O1), recording folded and transparent references and a forwarder's erased types meets the obligations (T3a), with precision per key |
| `Zinc/InlineOpaqueSound.lean` | The same observables as an `NCompiler` instance over every program of a slot language (inline bodies issue their reads in the client's trace, tagged with their context): recording the expansion's references and the types a forwarder's erasure reads, or hashing what an inline def's references denote, meets the obligations, so T2″/T3a″ hold; today's recording fails coverage, with one counterexample per family |
| `Zinc/JavaNames.lean`, `Zinc/JavaSealed.lean` | Java in mixed builds: a Java or Scala client's simple name bound by Java sources (member classes, single-static and on-demand imports, the package, `java.lang`), with Java's and Scala's rules and Zinc's Java edges (constant pool, no used names, no import edges); exhaustivity of a Java `switch` or a Scala match against a Java sealed hierarchy, one and two levels deep; the families as checked examples, and the fixes clean on the spaces |
| `Zinc/FlatRules.lean`, `Exhaustive.lean` | The PoC's descendant rules as a policy (no refchecks keys); bounded exhaustive check (`lake exe exhaustive`): the `abstract` rule as stated is unsound, widened it is clean, `trait` can be narrowed to direct mixins; minimal counterexample per rule as checked examples |

### Counterexamples

Small witnesses of what goes wrong without a hypothesis.

| File | Contents |
|---|---|
| `Zinc/Examples.lean` | §15b value class and §15a implicit addition/shadowing as `example`s; `repaired_sound`, `repaired_terminates` |
| `Zinc/Stale.lean` | **T2-stale**: a non-local hash diffed over the recompiled set alone undercompiles (two-unit counterexample) |
| `Zinc/PingPong.lean` | Without `transitiveStep`, Zinc's loop (next round = invalidated + API-changed classes) need not terminate on three mutually inferred classes: `zinc_diverges` (every amount of fuel), `transitiveStep_stops`; `lake exe exhaustive pingpong` searches the space |

### Tools

| File | Contents |
|---|---|
| `Conformance.lean` | `lake exe conformance`: the `FlatRules` program space as JSON lines, with the model's verdict per edit, for the Zinc conformance harness (`sbt.internal.inc.bench.Conformance`), which compares incremental and clean classfiles; `conformance names\|givens 2\|3 [mode]` dump the name-resolution spaces as source files with the verdict and recompiled classes under a mode, `conformance cost` tabulates soundness and precision per mode, `conformance inline\|opaque [mode]` the Scala 3 spaces of `InlineOpaque.lean` (`scripts/` selects, analyses and counts); `JConformance.lean` (`lake exe jconformance`) dumps the Java spaces |
| `JConformance.lean` | `lake exe jconformance`: the Java spaces of `JavaNames.lean`/`JavaSealed.lean` for the harness |

See `PLAN.md` for the design, the encoding choices and the two findings that fed back into the talk (Zinc's actual loop formula; the fixed-point uniqueness hypothesis T3 needs).
