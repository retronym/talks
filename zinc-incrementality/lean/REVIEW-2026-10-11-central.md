# Central review, 11 October 2026

A review of the Lean model, its findings, and the talk and documents, taken at `master` `e320f2c` after the parallel work of 10 and 11 October finished. It replaces nothing: `REVIEW-2026-10-11.md` (the morning review) stays as history, and its status is given below.

## Bottom line

- **The method works, and now has evidence for it.**
  - The model predicted 16 Zinc bugs before anyone ran them, and every one reproduced on `develop`.
  - Checked against the real compilers, the model's lowering agrees with scalac on 1,348 programs (2.12, 2.13) and 1,363 (3.9), and with javac on 99. Its JVM linkage agrees with HotSpot on about 58,000 client programs.
  - It checked MiMa, a tool it wasn't built for, and found five gaps.
- **The proof core is trustworthy but narrower than the documents suggest.**
  - There are no `sorry`, `axiom` or `native_decide` theorems.
  - The headline uniqueness theorem (incremental = clean, T3) rests on hypotheses real Scala code doesn't meet. Several counterexamples are still checked examples rather than theorems.
- **The documents are the weakest part.**
  - The README, ROADMAP, PLAN status table and BUG-MAP all lag the Lean.
  - The talk has about a dozen stale or overstated claims, including the prediction count and the Merkle headline.
  - None of this is hard to fix, and it matters most for the goal of enlisting others.
- **Upstream is the bottleneck.**
  - Four upstream PRs are merged, one of which didn't come from the model.
  - About ten fixes sit in forks, and about ten issues are unfiled.
  - The work now waits on review and filing, not on more modelling.

## 1. The model

About 27k lines, 618 theorems and 544 examples:

| Directory | Lines |
|---|---|
| `Zinc/` | 18.1k (52 files) |
| `ZincNames/` | 1.1k |
| `Jvm/` | 1.4k |
| `Scala/` | 2.2k |
| `Java/` | 1.1k |
| `BinCompat/` | 1.7k |

### Trust

- No `sorry`, `admit` or `axiom` declarations, and no declaration of any kind is proved by `native_decide`; it appears only in `example`s.
- `scripts/Axioms.lean` checks 59 declarations: T1–T5 across the framework variants, B4, Files, Sam, Cycles and about 15 instance theorems.
- **Holes in the CI checks:**
  - `lint_native_decide.py` only globs `Zinc/`, `ZincNames/` and the root. It skips `Jvm/`, `Scala/`, `Java/` and `BinCompat/`.
  - Its regex misses `@[simp] theorem`, `private theorem` and `protected theorem`. These are clean today, so this is a future risk.
  - `Axioms.lean` omits several instance soundness theorems: `MacroDeps`, `Erasure.dep_sound`, `ImplicitScope.is_sound`, `Flat.flat_sound`, `HierSound.*`, `InlineOpaqueSound.denot_sound`, `Classpath`. PLAN-framework.md's "every instance's soundness theorem" overstates this.
- **Counterexamples still checked only as examples:**
  - T2-stale, the Merkle trap: `Stale.lean`, `native_decide` examples.
  - §15a and §15b (`Examples.lean`).
  - Hier's scenarios.
  - `Pipelining`'s scenarios.
  - Every whole-space rule table: `NamesRules`, `FlatRules`, `Split.check_*`, `InlineOpaque`, `JavaNames`.

### The theorems a reader should know

| | Name | Statement | Hypotheses |
|---|---|---|---|
| T1 | `Task.run_eq_of_trace` (`Task.lean:42`) | Oracles agreeing on the trace give the same run | none |
| T2 | `XCompiler.round_preserves` (`General.lean:108`) | A round keeps the invariant | the four obligations; `D ⊆ R` |
| T3a | `XCompiler.zinc_sound` (`General.lean:169`) | A loop that returns ends at a per-unit fixed point | plus `Policy.Sound` |
| T3 | `fixpoint_unique_of_wf` / `_of_explicit`, `zinc_eq_clean_of_*` (`Uniqueness.lean`) | Incremental = clean | well-founded traced dependencies for every oracle, or interfaces independent of every oracle; `Compiler` only |
| T4 | `zinc_some_of_monotoneFrom` (`General.lean:218`); `_of_explicit`, `_of_wf` (`Termination.lean`) | Termination | the last two are `Compiler` only |
| | `PingPong.zinc_diverges` | Without `transitiveStep`, the loop can diverge for any fuel | kernel `decide` |
| T5 | `XCompiler.downstream_sound` (`General.lean:316`) | Downstream subprojects sound | fresh snapshots; T5a needs only abstraction |
| | `Cycles.zinc_ne_clean`, `annotated_eq_clean` | T3a without T3; T3 when every member is annotated | |
| B4 | `XCompiler.untouched_eq_clean` (`BinCompat/ZincBridge.lean:131`) | A unit Zinc never recompiles equals the clean build's, so it links as a fresh build does | explicit interfaces |
| | `zinc_sound_charged` (`Files.lean:170`) | T2 and T3a with file-closed rounds and charged imports | file-closed policy |

### Architecture

- **One soundness framework, several object languages.**
  - `XCompiler` proves T2, T3a, T4 (monotone) and T5 once. The older `Compiler`, `TCompiler`, `GCompiler` and `NCompiler` lift into it.
  - They still define their own `round`, `invalidated` and `zinc`, and instances use all four (about 20, 9, 2 and 8 files).
  - T3 and T4 (explicit, well-founded) exist only on `Compiler`. B4 restates the explicit case for `XCompiler` inside `BinCompat` (`ZincBridge.lean:100`), so a framework theorem lives in a consumer.
- **The object languages are still duplicated.**
  - `Hier`, `Erasure`, `Flat` and `ImplicitScope` each have their own toy Scala, their own `asSeenFrom` and their own `run_askQ`/`trace_askQ`.
  - The shared `Scala/AsSeenFrom.lean` is used by `Scala/` and the IntelliJ TCK, but no `Zinc/` file imports it.
- **Layering is clean, with no back-edges.** The import order is `Zinc.Task ← Jvm ← Scala, Java ← BinCompat → Zinc.General`. `Task` is the de facto core but lives inside the `Zinc` library.
- **Dead or superseded files:**
  - `Embed.lean`, superseded by `Compiler.toX`.
  - `Pipelining.lean`. Its `early_agreement` is `Task.run_congr` under another name, and its scenarios are subsumed by `PipelineLifecycle`.

### The morning review's eight findings

| # | Finding | Status |
|---|---|---|
| 1 | Four copies of the framework | Addressed (`XCompiler`); residue: T3/T4 are not general, and the per-variant loops remain |
| 2 | Cyclic inference never tested | Addressed (Phase 15, `Cycles.lean`, retronym/zinc#49) |
| 3 | F4/F5 filed as coverage, really `comp` | Addressed (`SplitProof.joint_not_comp`, `ZincBridgeScala3.not_comp`) |
| 4 | Precision has no framework definition | **Not addressed.** There is no `necessary` or `overInvalidated` in `Model.lean`/`General.lean`; precision is defined per instance |
| 5 | Files not in the model | Addressed (Phase 26, `Files.lean`) |
| 6 | Recorded keys never checked against the Analysis | Addressed by talks#70 and retronym/zinc#54. The dumps carry the model's keys, and the harness compares them: 0 uncovered in 10,653 cases with #47; 144/352 names and 215/351 givens uncovered without it, 136 of them on clean builds |
| 7 | Trust and labelling | Addressed (lint, axioms CI), with the holes above |
| 8 | Organisation | Partly. README rewritten once but already stale; `Zinc/` still flat; phase numbering ad hoc |

### Risks in the hypotheses

- **Abstraction is perfect hashing.** Zinc's name hashes are 32-bit; collisions are excluded by fiat.
- **T3's well-foundedness hypothesis is too strong.** It covers every traced query of every oracle, which rules out self-queries and body-level cycles. Uniqueness only needs acyclicity of the dependencies that affect interfaces, which is sbt/zinc#1284's real condition.
- **The explicit case needs every interface independent of every oracle.** The realistic mixed case (some members annotated, some inferred) is unproved, so the theorem a Scala user gets is weaker than the talk implies.
- **`comp` assumes joint compilation is a per-unit fixed point.** F4, F5 and F6 break it; this is documented.
- **The set of units is fixed.** Additions and deletions are encoded through absent sources (`Added.lean`).
- **T3a covers only runs that return within fuel.**

### Next modelling steps, in order

1. **T3 under a realistic hypothesis.** Make uniqueness hold when only the dependencies that affect interfaces are well-founded, with bodies allowed to be cyclic, or under mixed explicit and inferred interfaces. Prove it on `XCompiler`. This is the property the harness actually tests (classfile equality).
2. **Precision in `General.lean`.** Define necessary invalidation as the units whose traced answers changed. Prove `invalidated ⊇ necessary` generally, and an ordering on key designs. Then retire the per-instance definitions. This makes "correct without invalidating the world" a theorem.
3. **Port `Hier`, `Erasure`, `Flat` and `ImplicitScope` onto `Scala/`** (the shared `AsSeenFrom` and `Lower`). Then Zinc's bridge instances, B4 and MiMa share one Scala semantics, and the B4 key model stops being separate from the Zinc one.
4. **Hygiene, one PR:**
   - Delete `Embed.lean` and `Pipelining.lean`.
   - Widen the lint glob and regex.
   - Add the missing instance theorems to `Axioms.lean`.
   - Promote T2-stale to a kernel-`decide` theorem.
   - Fix the dangling theorem names: `vEdge_*` and `wit_*` in PLAN and BUG-MAP, `j1_pipe`/`s1_pipe` in PLAN-java, `asf_eq` in ROADMAP, and the `Lifts.lean` reference in `General.lean`.
5. **More language features.** The BUG-MAP gap clusters are next: inner and path-dependent types (IC), phantom binary dependencies (PB), mirrors (MR), naming (N), hash forms (H1). Also the about 14 BUG-MAP §4 predictions never run, and `MacroDeps.private_today`.

## 2. Findings

### The ledger

Status codes:
- **M**: model only.
- **R**: reproduced on the real tool.
- **F**: fix in a fork.
- **U**: upstream PR.

rz = retronym/zinc, sz = sbt/zinc.

| Finding | At fault | Status | Where |
|---|---|---|---|
| F1: an added class shadows a resolved name | Zinc policy, bridge | R F | rz#32, rz#34 · `Added` |
| F1 upstream: the same, added in another subproject | Zinc policy | R | rz#46 (fails on #34 too) · `Split` |
| F2, F3, G1, G2: package-object/export/top-level members, imports charged to one class, added implicits/givens | bridge | R F | rz#35, rz#47, retronym/scala3#11 · `SplitProof.Spec`, `SpecGivens` |
| Extensions (4 tests) | bridge (as G) | R | rz#53 · `Extensions` |
| Scala 3.7 given priority (2 tests) | bridge (G1, new trigger) | R | rz#58 · `general_added_stale`, `type_widened_stale` |
| F4: Scala 2 stale mirror | scalac (`comp`) | M | `staleMirror`, `joint_not_comp` |
| F5: Scala 3 clash reported only jointly | dotc (`comp`) | R | rz#35 · `missedClash` |
| F6/G3: trait `$init$` skipped when compiled against TASTy, including extension methods | dotc TASTy reader | R F | rz#35, rz#52; retronym/scala3#10 · `separateInit`, `f6_witness` |
| F7: joint `writeReplace` gets the inherited module | dotc | R (harness) | `staleModule` |
| I1–I3: inline constants, `constValue`, transparent expansion | dotc bridge | R | rz#40 · `InlineOpaqueSpec` |
| O1: opaque type in an inherited signature, stale forwarder | API key design | R | rz#40, rz#51 |
| Value-class/intersection/type-parameter erasure, stale forwarders and bridges | bridge API hash | R F | sz#1844 (closed), rz#26–#28, rz#51, rz#57 · `Erasure`, `ZincBridgeKeys.loop_witness` |
| Class kind and modifiers not hashed | Zinc `HashAPI` | U open | sz#1841 |
| Implicit scope through an ancestor's companion, across projects | Zinc | **U merged** | sz#1845 · `ImplicitScope` |
| The same for an object's singleton type | Zinc | U draft | sz#1846 |
| J1–J4: Java name resolution | Zinc Java analysis | R F | rz#42, rz#43 · `JavaSpec` |
| S1/S2: Java `permits` not hashed; nested sealed leaf | Zinc `ClassToAPI` | R F (S1) | rz#14, rz#21, rz#42 · `JavaSealedSpec` |
| N1: `classOf` records no used name | scalac bridge | R | rz#42 |
| Java source view vs classfile view | scalac and dotc Java parsers | R U open | rz#50; scala/scala3#27264, scala/scala#11290, #11292 · `JavaOrder` |
| A failed javac leaves a stale product | Zinc | R | rz#50 |
| `selectDynamic` records no used name | scalac bridge | R F | rz#50, rz#17 |
| Pattern-matcher selectors (`_N+1`) | dotc bridge | **U merged** | scala/scala3#26262 · `TreeToy` |
| sz#1819: pipelining compares source-view and classfile-view hashes | Zinc policy | R | `pipelining/java-comment-change` · `flip_spurious` |
| C1/C2: inferred types in a cycle | Zinc policy | R | rz#49 · `Cycles` |
| No termination without `transitiveStep` | Zinc loop (by design) | R | rz#33 · `PingPong` |
| SAM P1/P2: Java lambda argument; overload alternative becomes functional | Zinc Java analysis, all bridges | R | rz#58 · `Sam` |
| Failed pipelined compile leaves stale early output | Zinc | **U merged** | sz#1843 |
| No dependencies on annotations | bridges | U draft | sz#1842 · `Annotations` |
| Deferred terms not marked abstract | dotc bridge | U open | scala/scala3#27271, #27272 |
| scalac output depends on the compilation batch | scalac | U (#11293 merged; #11289–92 open) | found by IncBench, not the model |
| Merkle PoC design rules (`abstract` rule, header, private trait members, macro keys, snapshot refresh) | PoC | fixed in PoC | rz#24 · `FlatRules`, `Flat`, `Stale`, `Snapshot` |
| Merkle companion bug | PoC bridge | R F | rz#56; `Companions` afterwards; found on Spark, not by the model |
| Pipelined Java self-dependency (~1,700-class floor) | Zinc / PoC | F | rz#55; found by IncBench; latent on develop |
| MiMa F1, M1, F2, D1, P1 (40 false negatives) | MiMa | R (HotSpot) | `BinCompat/Mima`, `Fixed`, `Sound`; drafts in ROADMAP §B |
| Trait val re-abstracted by a def: missing setter, `AbstractMethodError` | scalac 2.12/2.13 | R F (draft) | retronym/scala#136 |
| JDK-8356942, JDK-8350029 | HotSpot | known, fixed in 25 | ROADMAP §J |
| Macro reflecting a private member | dotc bridge | M | `MacroDeps.private_today` |

### How many predictions

- **The run count.** 20 tests were predicted by the model and then run on `develop`, and all 20 failed as predicted:
  - rz#33: 1
  - rz#49: 2
  - rz#50: 3
  - rz#51: 5
  - rz#53: 4
  - rz#57: 1
  - rz#58: 4
- **Which of those 20 are novel bug predictions: 16.**
  - rz#33 is a termination property, not a bug.
  - Three tests (rz#51's intersection and Scala 3 value-class tests, and rz#57) restate a family you had already reproduced and fixed by hand in sbt/zinc#1844 and rz#26–#28.
- **Two more qualify but aren't in the 20.** F1 (rz#32) and its upstream variant (rz#46) give 18 if counted.
- **Unrun predictions.** About 14 BUG-MAP §4 predictions, and `private_today`, have never been run, so the denominator is predictions that were run.
- **Discovery is not prediction.** Families found while the model's spaces and the harness ran together (F2–F7, G, I1–I3, O1, J1–J4, S2, N1, sz#1846) count as discovery.
- **Corrections.** The talk's "15 predicted, all 15 reproduced" cites PRs that hold 12 tests. The dashboard's "16 of 16" and "20 of 20" were corrected today.

### Credit

The talk attributes some findings to the model that it only explained afterwards:
- sz#1843 was fixed before `Pipelining.lean` modelled it.
- sz#1842 came before `Annotations.lean`.
- rz#56 came before `Companions.lean`.

The two directions are worth stating separately, because the honest version is the stronger story. In one direction, the model predicted bugs that real Zinc then reproduced. In the other, benchmarks on real code found gaps that the model then had to absorb.

### Upstream queue

Recommended order. Ask before opening anything on sbt/zinc, scala/scala or scala/scala3.

1. Un-draft sz#1846; its base, #1845, is merged.
2. Merge sz#1841.
3. The erasure fix (rz#27 + rz#28) to sbt/zinc, with the tests from rz#26, rz#51 and rz#57 deduplicated. `value-class-mixin-forwarder-scala3` is in both #51 and #57.
4. rz#32 + rz#34, then rz#47, together with retronym/scala3#11 to scala/scala3 and a port to scala2-sbt-bridge. Carry the tests from rz#35, rz#53 and rz#58's givens.
5. rz#42 + rz#43 (Java names).
6. Un-draft sz#1842, and file the scala3 `ExtractDependencies` issue.
7. retronym/scala3#10 to scala/scala3 (F6).
8. rz#49 tests, with a comment on sz#1780 (it catches C2, not C1).
9. **File the issues:**
   - on scala/bug: the trait-setter `AbstractMethodError` (with scala#136);
   - on scala3: F7, I1–I3, and the skipped Scala 2 ancestor implicits;
   - on MiMa: five issues.
10. Fixes for rz#50 and the rz#58 SAM tests. Keep rz#33 as documentation.

## 3. The talk and documents

### Stale or wrong in `zinc-lean/talk.md`

| § | Now says | Should say |
|---|---|---|
| §18, §18a, §27a | Headline 420 vs 1,371; "~1,700 until #55" | Pipelining on: 661 vs develop's 1,612. Off: 420 vs 1,371. After #55 the companion bug (#56) still cost 1,587. Lead with the on pair or show both |
| §25 | "15 predicted, all 15 reproduced" | The counts above: 16 novel, 20 run, which ones |
| §25 | Credit for sz#1843 to `Pipelining.lean` | Found and fixed first, modelled afterwards (likewise #1842, #56) |
| §25 | No #56, #57 or #58 rows | Add them |
| §27b | "MiMa is next"; the Zinc ⇒ binary-compatible theorem as a goal | Both done: #64 (five gaps, 40 misses), #59/#62 (B4 proved; converse fails; Scala 3 via scala3#10; library JARs) |
| §27b | "29 library edits"; JDK bugs "found" | 45 cases plus `space5`; "hit" known JDK bugs |
| §27b | Scala layer ends at #39; no Java | Add #60 (Java, JLS 13) and #65 (case classes, enums, inline, nested) |
| §23d, §28 | SAM open; files "designed, not built" | Phase 26 (files), 27 (imports, given priority) and 28 (SAM) are done |
| §24 | "41 theorems" | 59; add instance rows for files, SAM, selectors, companions |
| §23c | talks#21 "open" | Merged |
| §27a | "No undercompilation on either side" | Remove |
| §16 | Two notes paragraphs | Merge |
| Contents | ~60 min | Sums to 62; Parts VII and IX budgets don't match their slides |

The older `zinc-incrementality/talk.md` §22 still says "~1,100 lines". It should become a pointer to the zinc-lean talk.

### Story

The spine still holds: obligations, then the recipe, then findings, then the harness. The newest evidence fits both goals better than some current slides.

- **Add §27c, "A JVM-linkage theorem found a Zinc bug" (1.5 min).** B4 with Zinc's real keys gave `loop_witness`, and rz#57 confirmed it. A model built for MiMa predicted a Zinc bug, which is the strongest "formalism as a pragmatic tool" beat available.
- **Add §23e, "A new language version, a new prediction" (1.5 min).** Scala 3.7's given priority led to `prio_differs` and `general_added_stale`, which rz#58 confirmed. Mention SAM P1/P2 in one line. This shows goal (a) on a feature that changed recently.
- **Fold in without new slides:**
  - #56 and Phase 25 into §18 and a §25 row. The loop runs both ways: real code found a gap in the model.
  - MiMa's five gaps as one line of §27b.
  - Files as a row of §24.
- **Replace §29's agents line with "Join in", by role.**
  - Modellers: a BUG-MAP gap cluster, with Phase 28 (PLAN-sam.md → `Sam.lean` → rz#58) as the template.
  - Testers: turn predictions into pending tests, and run the harness.
  - Remediators: the upstream queue above.
- **Cuts to stay near 60 minutes (about 6.5):**
  - §2a to one sentence (−1).
  - §14a without the cycle listing (−1).
  - P4 from 3 to 2 minutes (−1).
  - §23a and §23b to overflow, with T5 as one line in §24 (−3).
  - §27a's name-rule table to overflow (−0.5).

### Documents for newcomers

- **README.md isn't a front door yet.**
  - It still opens as "a model of §22 of the talk".
  - It says the four framework variants are yet to be merged.
  - It omits 12 `Zinc/` files and all of `Jvm/`, `Scala/`, `Java/`, `BinCompat/`, `probes/` and `scripts/`.
  - Proposal: a "Start here, by goal" section (understand; add a feature; test Zinc; binary compatibility), with the file tables below it.
- **ROADMAP.md is mostly history.**
  - J1, J2, J5, S1–S6, B1, B2 and B4 are done.
  - Its track rules and dependency order are obsolete.
  - Proposal: move the results into phase files like the rest, and cut ROADMAP to what's open:
    - J3 nestmates and J4 behaviour;
    - B3 source-level spaces;
    - a general proof for the corrected MiMa rules;
    - the port onto the shared `asSeenFrom`;
    - the contributor repository.
- **PLAN.md's status table is behind.**
  - It has no rows for phases 16–21 and 23–25, and no section heading for 26.
  - It lists the dead `Embed.lift_obligations` and `Pipelining.early_agreement` as results.
- **BUG-MAP.md's summary predates phases 15–28.** Its counts disagree with its own rows: 25 covered, 39 partial and 80 gaps, against 18/42/84 in the summary. **BUGS-catalogue.md** still shows sz#1843 and #1845 as open.
- **Per-phase plans not updated after their tests landed:** PLAN-imports, PLAN-extensions (P24.3), PLAN-sam (P28.3), ROADMAP B4.
- **ID collisions:**
  - C1/C2: BUG-MAP clusters vs cycle families.
  - O1: opaque vs JavaOrder.
  - P1, F1, F2: SAM and names vs MiMa.
  - S1/S2: Java sealed vs ROADMAP tracks.
  - Suggestion: prefix the MiMa gaps (`MiMa-F1`) and the tracks (`Track S1`).
- **The obligations and T1–T5 are restated in four places:** the talk, PLAN, DESIGN-spec and README. One canonical statement, with pointers from the others, would stop the drift.

### "Notes for Jason", the C list

- **Done:** Lean syntax highlighting.
- **Remaining:**
  - §10/§18 quoting the full model;
  - screenshots (none exist yet);
  - the Embed vs General decision, which this review settles: delete Embed;
  - §18 as one instance per scheme, which needs the port in modelling step 3;
  - stale line counts and theorem names;
  - precision (P2.6, modelling step 2);
  - freezing the numbers at a commit (add #56, #57, #58).

## 4. The parallel way of working

What worked:
- **Splitting by layer.** Each track owned one directory (`Jvm/`, `Scala/`, `Java/`, `BinCompat/`), with the shared types changed only additively. That let three to five sessions write at once without conflicts.
- **Calibrating each layer against its real tool.** HotSpot, scalac, javac and MiMa did this before any claims were built on the layer.
- **One owner for the shared dashboard.** Each session updated only its own row.

What didn't:
- **Timestamps.** Times were estimated instead of read from `date` or GitHub, and the dashboard had to be corrected. The rule is now in memory.
- **Counts.** "N of N predictions" figures were repeated without checking what each one counted. The ledger above is the corrected version.
- **Credit.** Findings found by benchmarks or by hand were credited to the model.
- **Plans.** Documents fell behind the code in every session. No step updated README, PLAN or BUG-MAP when a PR landed.
- **Session starts.** The app often refused to start sessions on your word, so work went to existing sessions instead of new ones. That worked, but session titles stopped matching their histories.
- **Two coordinators.** The overnight coordinator and this session both assigned work for a while. Until that was settled, the dashboard missed tasks and two sessions got overlapping briefs.
- **Memory.** Five heavy sessions at once ran near the machine's limit.

For next time:
- Have a single orchestrator.
- Give each task a definition of done that includes updating README, PLAN and BUG-MAP.
- Count predictions only from a ledger.
- Cap heavy sessions at four.

## 5. Decisions for you

1. **Which upstream items to open, and in what order.** The queue in §2 is the proposal.
2. **Whether the talk takes the two new slides and the "Join in" slide, with the cuts.**
3. **Whether to do the documentation pass now:** README by goal, ROADMAP cut down, PLAN/BUG-MAP refreshed, IDs prefixed. It's mechanical, one PR, and it unblocks the contributor goal.
4. **Which modelling step comes first:** T3 under realistic hypotheses, precision in the framework, or the port onto `Scala/`.
5. **Whether to file the trait-setter bug and the five MiMa issues, and post the coverage note on zinc#54.**
