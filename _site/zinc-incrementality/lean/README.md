# Zinc incrementality, modelled in Lean

A Lean 4 + Mathlib model of Zinc's incremental compilation. It states the obligations that a compiler bridge's recorded keys, and Zinc's invalidation policy, must meet so that an incremental build equals a clean one, and proves Zinc's loop sound under them. It instantiates that framework for real language features (name resolution, implicits and givens, inline and opaque types, erasure, Java in mixed builds, SAM conversion, macros, …): today's bridge as keys, each bug family as a failed obligation with a witness, each fix as keys with the obligations proved for every program. Bounded program spaces calibrate the model against the real tools: Zinc (through the conformance harness), scalac and dotc, javac, HotSpot and MiMa. The hypotheses are the point: they are the bridge spec. The model does not verify scalac.

```bash
lake exe cache get && lake build
```

Lean `v4.34.1`, Mathlib tag `v4.34.1`. `BinCompat/Sound.lean` is outside the default targets: `lake build BinCompat.Sound` (about half an hour).

## Start here, by goal

**Understand the theory.** Read `Zinc/Task.lean` (a compilation as a query tree with a trace), then `Zinc/Model.lean` (the specification's first page: `Compiler`, `Obligations`, `round`, `zinc`), then `Zinc/General.lean` (`XCompiler`, where T2, T3a, T4 and T5 are proved once). `Zinc/Uniqueness.lean` and `Zinc/Cycles.lean` show when incremental equals clean and where it fails. The statements are in [The theorems](#the-theorems); `DESIGN-spec.md` gives the rationale for the method.

**Add a language feature.** Phase 28 is the template. `PLAN-sam.md` asks what the compiler reads (a SAM target's whole ancestry) and whether today's keys cover it. `Zinc/Sam.lean` writes the compiler's algorithm as the unit task of a `TCompiler`, today's bridge as keys, the failing cases as witnesses (`p1_today`, `p2_today`), and the fix with `obligations_fix` and `fix_sound`. The witnesses became scripted tests in retronym/zinc#58, which fail on `develop` as predicted. BUG-MAP.md's gap clusters are the candidate features.

**Test Zinc.** The conformance harness (`sbt.internal.inc.bench.Conformance` in Zinc's `zincScripted` tests, from retronym/zinc#25) renders each program of a dump, applies each edit, and compares the incremental build's classfiles with a clean build's. `lake exe conformance` and `lake exe jconformance` write the Scala and Java dumps with the model's verdict per edit; `scripts/select.py` and `scripts/jselect.py` pick bases that cover every signature; `scripts/analyse.py`, `scripts/janalyse.py` and `scripts/inline_opaque.py` compare a run with the model; `scripts/families.py` names the divergence families. The workflow is in `PLAN-names.md` and `PLAN-java.md`; pending tests are in `TESTS-catalogue.md`.

**Binary compatibility.** `Jvm/` models JVM linkage as a `Task`, so a library edit that agrees with the old library on a client's linkage footprint links it the same way (`link_congr`); its catalogue is checked on HotSpot (`probes/jvm`). `Scala/` and `Java/` lower source to classfiles, calibrated against scalac and dotc (`probes/scala`) and javac (`probes/java`). `BinCompat/` models MiMa as a bridge design (calibrated by `probes/mima`), finds its gaps (`Keys.lean`), corrects them (`Fixed.lean`, `Sound.lean`), and proves B4: a unit Zinc never recompiles is what a clean build gives, so it links as a fresh build does (`ZincBridge*.lean`). `PLAN-track-b.md` has the results; ROADMAP.md has what is open.

## The theorems

This is the canonical statement of the obligations and T1–T5; other documents point here.

**The obligations.** A compiler is a per-unit task that queries an oracle, plus a bridge: `keys` (what it records), `π` (a hash per key) and `covers` (which queries a key vouches for). On `XCompiler` (`General.lean:45`):

- **comp** (compositionality): joint compilation of a group is a fixed point of the per-unit tasks, with group-mates answered from their fresh interfaces;
- **coverage**: every traced query, misses included, is covered by a recorded key;
- **abstraction**: equal hashes on a key give equal answers to every query it covers;
- **locality**: a key's hash reads only the interfaces in its declared `hashDeps`.

The local `Compiler` (`Model.lean:67`) has the first three. The policy's one obligation is `Policy.Sound` (`Model.lean:117`): never drop an invalidated unit outside the round just compiled.

| | Name | Statement | Hypotheses |
|---|---|---|---|
| T1 | `Task.run_eq_of_trace` (`Task.lean:42`) | Oracles that agree on a run's trace give the same output and trace | none |
| T2 | `XCompiler.round_preserves` (`General.lean:108`) | One round, with `Δ` over the affected units, preserves the invariant | the obligations; dirty set `D ⊆ R` |
| T3a | `XCompiler.zinc_sound` (`General.lean:169`) | If the loop returns, every unit is up to date: a per-unit fixed point | plus `Policy.Sound` |
| T3b | `Compiler.fixpoint_unique_of_wf`, `_of_explicit` (`Uniqueness.lean:65`, `:82`) | Per-unit fixed points are unique | traced dependencies well-founded under every oracle, or every interface a function of the source alone |
| T3 | `Compiler.zinc_eq_clean_of_wf`, `_of_explicit` (`Uniqueness.lean:121`, `:136`) | Incremental = clean | T3a's and T3b's; on `Compiler`, and on `TCompiler` through `toCompiler` (`:189`, `:204`) |
| T4 | `XCompiler.zinc_some_of_monotoneFrom` (`General.lean:218`); `Compiler.zinc_some_of_explicit`, `_of_wf` (`Termination.lean:100`, `:184`) | The loop returns within a bound: `k + \|S\| + 1` rounds; 2; height + 2 | a policy monotone from round `k` (`transitiveStep`); or T3b's hypotheses, `Compiler` only |
| | `PingPong.zinc_diverges` (`PingPong.lean:218`) | Without `transitiveStep`, Zinc's loop diverges for every fuel on three mutually inferred classes | kernel `decide` |
| T5 | `XCompiler.downstream_sound` (`General.lean:316`) | A downstream subproject's loop, seeded from changed sources and external invalidations, ends sound against the new classpath | fresh snapshots; T5a `inv_external` (`:281`) needs only abstraction |
| | `Stale.stale_unsound`, `stale_affected` (`Stale.lean:131`, `:136`) | T2-stale: a non-local hash diffed over the recompiled set alone undercompiles; over `affected` it does not | kernel `decide` |
| | `Cycles.zinc_ne_clean`, `annotated_eq_clean` (`Cycles.lean:190`, `:219`) | T3a without T3 for inferred types in a cycle; T3 when every member is annotated | |
| B4 | `XCompiler.untouched_eq_clean` (`BinCompat/ZincBridge.lean:131`) | A unit Zinc never recompiles equals the clean build's, so it links as a fresh build does | explicit interfaces, through `XCompiler.fixpoint_unique_of_explicit` (`:100`) |
| | `zinc_sound_charged` (`Files.lean:175`) | T3a with file-closed rounds and imports charged to one class of the file | charged obligations; file-closed policy |

**Where the hypotheses bite.**

- Abstraction is perfect hashing: collisions of Zinc's 32-bit name hashes are excluded by fiat.
- T3's well-founded case covers every traced query under every oracle, which rules out self-queries and body-level cycles; uniqueness should need only that the dependencies affecting interfaces are well-founded (sbt/zinc#1284's condition). Its explicit case needs every interface independent of every oracle, so a mix of annotated and inferred members is unproved.
- T3 and T4's explicit and well-founded cases are on `Compiler` (and `TCompiler` for T3). On `XCompiler` only the explicit T3b exists, inside `BinCompat`.
- `comp` fails for F4, F5 and F6 (`SplitProof.Spec.joint_not_comp`, `ZincBridgeScala3.not_comp`).
- The set of units is fixed; additions and deletions are absent sources (`Added.lean`).
- T3a covers only runs that return within fuel.
- Precision has no framework definition; it is proved per instance.

## Trust

- No `sorry`, `admit` or `axiom` declarations.
- `native_decide` appears only in `example`s, never in a `theorem` or `lemma`: those are checks on a bounded space, not results (DESIGN-spec.md). `scripts/lint_native_decide.py` enforces this over every `.lean` file, in CI.
- `scripts/Axioms.lean` prints the axioms of the core theorems, of the counterexamples proved by `decide`, and of the instances' soundness theorems; `scripts/check_axioms.py` fails unless each uses only `propext`, `Classical.choice` and `Quot.sound` (so no `sorryAx` and no `Lean.ofReduceBool`), in CI.

## Files

### `Zinc/`: the framework

| File | Contents |
|---|---|
| `Task.lean` | Free monad of query trees; `run`, `trace`; T1 `run_eq_of_trace`, `run_congr` |
| `Model.lean` | `Compiler` (task, joint compiler, `iface`, `answer`, `π`, `keys`, `covers`), its three `Obligations`, `State`, `round`, `invalidated`, `Policy` and `Policy.Sound`, the fuelled `zinc` loop |
| `General.lean` | `XCompiler`, the general form: non-local answers and hashes, keys from output and trace; T2, T3a, T4 (monotone), T5a, T5 and snapshot refresh, proved once |
| `Soundness.lean` | `UpToDate` and `Inv` for `Compiler`; T2 and T3a through the lift `toX` (`zinc_toX`) |
| `Uniqueness.lean` | T3b `fixpoint_unique_of_wf`, `_of_explicit`; T3 `zinc_eq_clean_of_*`, for `Compiler` and `TCompiler` |
| `Termination.lean` | T4: monotone policies, explicit interfaces (2 rounds), acyclic (height + 2) |
| `NonLocal.lean` | `GCompiler`: non-local `π` with `hashDeps`, closure keys, `Δ` over `affected`; T2′ through `toX` |
| `NonLocalAns.lean` | `NCompiler`: answers and hash read sets over several interfaces; T2″, T3a″ through `toX` |
| `Tree.lean` | `TCompiler`: keys read off the output (the typed tree), not the trace; T2, T3a through `toX` |
| `Classpath.lean` | Upstream subprojects and libraries: stored snapshots, external invalidation; T5a, T5 |
| `Files.lean` | Files as a layer: file-closed policies, imports charged to one class of a file; `zinc_sound_charged`, T5 under charging (`downstream_sound_charged`), the sbt/zinc#417 fix for every program (`Fi.kept_sound`) |
| `Naming.lean` | Class-name agreement between what the compiler reads and what the bridge records; `spelling_bugs`, case-insensitive collisions |
| `HashForms.lean` | Hash stability across forms (tree, pickle, TASTy, classfile): abstraction holds iff no form masks a difference; canonical forms |

### `Zinc/`: instances, proved for every program

| File | Contents |
|---|---|
| `Hier.lean`, `HierSound.lean` | Toy class hierarchy; designs `D` (decls + walk), `W` (materialised members), `Mk` (Merkle) all meet their obligations |
| `Flat.lean` | The Merkle PoC's flattened hash over a stored linearization: `Fl_obligations`, `flat_sound`; header and refchecks keys and their ablation |
| `Erasure.lean` | Erasure through inheritance (as seen from vs as declared; value classes, intersections): witnesses, a dependency edge, `dep_sound`; `lake exe exhaustive erasure` |
| `ImplicitScope.lean` | Implicit scope through an ancestor's companion across projects (sbt/zinc#1845): `is_obligations`, `is_sound`, `stored_eq_recomputed`; `lake exe exhaustive implicit` |
| `SplitProof.lean` | The shared names instance `Spec` (a slot language, units split upstream and downstream): today's and #34's failures, the rules' obligations, precision, F4/F5 as `joint_not_comp`, `cross_downstream_sound` |
| `SpecGivens.lean` | Implicit search on `Spec`'s scopes, as an `XCompiler`: G1/G2 (`g12_today`), the G rule's obligations, #24's `g_decls_not_abstraction` |
| `Extensions.lean` | Member selection through extensions (Scala 3 `extension`, Scala 2 implicit classes) on `SpecGivens`' search: `ext_rule_obligations`, today's failures |
| `Added.lean`, `Sealed.lean` | Added and deleted classes as absent sources (F1); sealed children in the hash, Java `permits` |
| `Inline.lean` | Bodies as API (Scala 3 `inline`, Scala 2 `@inline`, Java constants) with pipelining: `obligations_withBodies`, `pipelined_ne_final` |
| `PipelineLifecycle.lean` | Pipelining's early output: `rollback_preserves` with sbt/zinc#1843; `noRollback_breaks`, `stale_after_revert` without it |
| `InlineOpaqueSpec.lean` | Scala 3 `inline` and opaque types as a `TCompiler`: I1–I3 and O1 witnesses, `fix_sound`, precision per key |
| `InlineOpaqueSound.lean` | The same observables as an `NCompiler`: the denotation hash's `denot_sound`, `I1_abstraction` |
| `MacroDeps.lean` | Scala 3 macro dependencies: a witness per bug, `fix_sound`, costs; `private_today`, a prediction not yet run |
| `Annotations.lean` | Annotations as API and as dependencies: sbt/zinc#1842's fix (`fix_sound`), `today_not_coverage`, scala/scala3#22999 |
| `DerivedApi.lean` | Export forwarders and used types' supertypes: `fix_sound`, `export_not_coverage`, `usedType_not_coverage` |
| `Synthetic.lean` | Constructors and synthetic case-class members: manglings that agree are sound, ones that disagree under- or over-invalidate |
| `ExtraHash.lean` | Companion pairs under one name: merged keys are spurious, per-namespace keys precise and sound; private members of ancestors |
| `JavaSpec.lean`, `JavaSealedSpec.lean` | Java name resolution (JLS 6.4.1, 7.5) and sealed exhaustivity as `TCompiler`s: J1–J4, S1, S2, `fix_sound` |
| `JavaOrder.lean` | A Java class's source and classfile views: `mixed_sound` under view agreement, `early_view`, `exclusion_exact`, `flip_spurious` (sbt/zinc#1819) |
| `Sam.lean` | SAM conversion and local classes: P1/P2 witnesses, `fix_sound` (Phase 28, retronym/zinc#58) |

### `Zinc/`: counterexamples and toys

| File | Contents |
|---|---|
| `Toy.lean`, `Examples.lean` | A toy language for §15a (implicits) and §15b (value classes); name-only vs repaired keys, `repaired_sound`, `repaired_terminates` |
| `TreeToy.lean` | `+=` desugaring and pattern-matcher selectors: Zinc's tree extractor fails coverage; failed lookups and an arity sentinel fix it |
| `Stale.lean` | T2-stale: `stale_unsound`, `stale_affected`, `stale_none_invalidated`, `stale_repaired`, by kernel `decide` |
| `Snapshot.lean` | Zinc's snapshot refresh with a non-local hash: edit then revert leaves the downstream stale (`stale_after_revert`) |
| `PingPong.lean` | `zinc_diverges` without `transitiveStep`; `transitiveStep_stops`; `lake exe exhaustive pingpong` |
| `Cycles.lean` | Inferred types in a cycle: `zinc_ne_clean`, `two_fixpoints`, `annotated_eq_clean`; sbt/zinc#1284's and #1780's rules |

### `Zinc/` and `ZincNames/`: bounded spaces for the harness

Each is a program space with the compiler's rules and Zinc's verdict per edit, checked whole by `native_decide` in `example`s and dumped for the conformance harness. They found most families, and give the costs.

| File | Contents |
|---|---|
| `ZincNames/Names.lean`, `ZincNames/Givens.lean` | Name resolution over nine binding scopes, and instances found by type (implicits, givens), per Scala version, with Zinc's recorded edges; a precompiled library, so the checks run natively |
| `Zinc/NamesRules.lean` | The whole-space checks of the names and givens spaces, per rule and mode |
| `Zinc/Split.lean` | The names spaces split across subprojects; checks `SplitProof`'s slot language against `Names` |
| `Zinc/InlineOpaque.lean` | Scala 3 `inline` and opaque types as a small key loop, with what dotc 3.9.0 records |
| `Zinc/JavaNames.lean`, `Zinc/JavaSealed.lean` | Java name resolution and sealed exhaustivity in mixed builds |
| `Zinc/FlatRules.lean` | The Merkle PoC's descendant rules as a policy; `lake exe exhaustive` |
| `Zinc/Companions.lean` | Companion pairs in a hierarchy; the bridge before retronym/zinc#56 loses a half (`check_pre56_exact`) |

### `Jvm/`, `Scala/`, `Java/`: the object languages

| File | Contents |
|---|---|
| `Jvm/Link.lean` | JVM linkage (JVMS §5.4) as a `Task` over the class table; T1 as `link_congr` |
| `Jvm/Catalogue.lean` | Library edits with a client; the outcome before and after by kernel `decide`, with MiMa's problem |
| `Jvm/Clients.lean` | Bounded client spaces: does an edit break some client? |
| `Jvm/Dump.lean` | Catalogue cases as JSON for `probes/jvm` |
| `Scala/Syntax.lean` | A typed Scala subset, as the back end sees it |
| `Scala/AsSeenFrom.lean` | `asSeenFrom`, once, for any type language: `compose`, `chain_is_single` |
| `Scala/Lower.lean` | Lowering to classfiles as a `Task` (forwarders, bridges, `$init$`, erasure); `lower_congr` |
| `Scala/Desugar.lean` | Case classes and case objects desugared onto a library prelude |
| `Scala/Members.lean` | Membership and overriding (refchecks) as a `Task` |
| `Scala/Facts.lean` | F6 as a compositionality failure, by kernel `decide` |
| `Scala/Space.lean` | Program spaces for calibrating lowering against scalac and dotc |
| `Scala/Catalogue.lean` | Scala library edits, lowered and linked: before, after, fresh |
| `Java/Syntax.lean` | An attributed Java subset, as javac's back end sees it |
| `Java/Lower.lean` | Lowering to classfiles as a `Task`, constants folded (JLS §13.4.9); `lower_congr` |
| `Java/Space.lean` | Program spaces for calibrating lowering against javac |
| `Java/Catalogue.lean` | Java library edits, lowered and linked |
| `Java/Jls13.lean` | JLS chapter 13's rules, checked against `Jvm` linkage |

### `BinCompat/`: MiMa and B4

| File | Contents |
|---|---|
| `Mima.lean` | `mima-core` 1.2.1's `Analyzer` as a function of the old and new classfiles |
| `Edits.lean` | The space of single library edits, and their clients |
| `Keys.lean` | MiMa as a bridge design: keys, covering, and its gaps as missed footprint queries |
| `Fixed.lean` | A corrected rule set, one key per gap |
| `Sound.lean` | The corrected rules are sound on the space (kernel `decide`; built on demand) |
| `ZincBridge.lean` | Scala lowering as an `XCompiler`; T3b (explicit) for `XCompiler`; B4 `untouched_eq_clean` |
| `ZincBridgeKeys.lean` | B4 with Zinc's actual keys (inheritance, member refs): `loop_witness` (retronym/zinc#57) |
| `ZincBridgeLibs.lean` | B4 for a client of a library JAR (stamp keys) |
| `ZincBridgeScala3.lean` | B4 for Scala 3: `comp` fails under F6 (`not_comp`) and holds with retronym/scala3#10 (`after_eq_fresh_fix`) |

### Root: library roots and executables (`lakefile.toml`)

| File | Contents |
|---|---|
| `Zinc.lean`, `ZincNames.lean`, `Jvm.lean`, `Scala.lean`, `Java.lean`, `BinCompat.lean` | Library roots (imports only) |
| `Exhaustive.lean` | `lake exe exhaustive [erasure\|implicit\|composed\|pingpong\|v]`: the bounded exhaustive checks, natively |
| `Conformance.lean` | `lake exe conformance`: the `FlatRules`, names, givens, inline and opaque spaces with verdicts, for the harness; `conformance cost` tabulates soundness and precision per mode |
| `JConformance.lean` | `lake exe jconformance names\|sealed …`: the Java spaces, for the harness |
| `JvmCases.lean` | `lake exe jvmcases [space\|verdicts]`: the JVM catalogue, for `probes/jvm` |
| `ScalaProbe.lean` | `lake exe scalaprobe OUT`: Scala sources and the model's classfiles, for `probes/scala` |
| `JavaProbe.lean` | `lake exe javaprobe OUT`: Java sources and the model's classfiles, for `probes/java` |
| `BinCompatMain.lean` | `lake exe bincompat edits\|mima\|gaps\|scala\|verdicts`: the edit space and MiMa verdicts, for `probes/mima` |

### `probes/`: calibration against the real tools

| Path | Contents |
|---|---|
| `probes/jvm/` | `probe.sh` renders `jvmcases` with the Classfile API (`Render.java`, JDK 24+) and runs each client on HotSpot (`Run.java`, `ProbeLog.java`, `Json.java`) |
| `probes/scala/probe.py` | Compiles `scalaprobe`'s sources with scalac 2.12, 2.13 and 3 and diffs the classfiles against the model |
| `probes/scala/members.py` | Calibrates `Scala/Members.lean` against scalac's and dotc's override errors |
| `probes/java/probe.py` | Compiles `javaprobe`'s sources with javac per release and diffs the classfiles against the model |
| `probes/mima/` | `Mima.scala` runs MiMa on rendered cases, `scala.sh` on the Scala catalogue, `compare.py` diffs MiMa against the model |

### `scripts/`

| File | Contents |
|---|---|
| `lint_native_decide.py` | Fails if a `theorem` or `lemma` uses `native_decide` |
| `Axioms.lean`, `check_axioms.py` | The core theorems' axioms, and the check that they are standard |
| `select.py`, `jselect.py` | Pick bases from a `conformance names` or `jconformance names` dump until every signature has an edit |
| `analyse.py`, `janalyse.py` | Compare a harness run of the names or Java spaces with the model: resolution, verdict, recompiled sets, divergences |
| `inline_opaque.py` | The same for the inline and opaque spaces |
| `families.py` | The names space's divergence families, for `analyse.py` and `modelcount.py` |
| `modelcount.py` | Counts the edits of a dump that the model calls unclean, by family |

## Documents

- `PLAN.md`: phase status, with what is proved for every program and what is checked on a space.
- `PLAN-*.md`: one per phase or topic, with its question, design and results; `PLAN-framework.md` for the `XCompiler` merge, `PLAN-names.md` and `PLAN-java.md` for the harness workflow, `PLAN-sam.md` as the template for a new feature.
- `ROADMAP.md`: open work on the JVM, Scala, Java and binary-compatibility layers.
- `BUGS-catalogue.md`: Zinc's incremental-compilation bugs. `TESTS-catalogue.md`: pending and disabled scripted tests. `BUG-MAP.md`: each mapped to the instance that covers it, or to a gap.
- `DESIGN-spec.md`: why the model is a specification, and the rules that follow from it.
- `REVIEW-2026-10-11.md`, `REVIEW-2026-10-11-central.md`: reviews of the framework, the findings and the documents.
