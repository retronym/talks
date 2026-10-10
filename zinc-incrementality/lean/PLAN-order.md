# Phase 13 — compile order and pipelining: a Java unit's two interfaces (design, for review)

## Question

In a mixed build a Java source is compiled twice, by different compilers, and each run produces a view of it. scalac parses it for symbols (no classfiles), and Scala units in the same run resolve against that **source view**. javac compiles it to classfiles, and Zinc reads that **classfile view** for the Java unit's keys (`JavaAnalyze`) and API (`ClassToAPI`); every later round, and every downstream project, reads it too. sbt's `compileOrder` and `pipelining` decide which view each reader gets, and when. The question is whether, per strategy, the incremental build still equals the clean one. Concretely: does the two-stage joint compilation meet `comp`, and does the hash Zinc stores for a Java unit, computed from one view, determine the answers of the other?

Known instances of the views disagreeing: scala/scala#11292 (Java parents parsed from source) and scala/scala3#27264. Zinc already knows about one disagreement. Under pipelining, `IncrementalCommon` excludes the unchanged Java classes it passed to scalac from API change detection, because "their stored API was read from the compiled classes and never equals the one from scalac".

## What Zinc does, read off the code (develop)

`MixedAnalyzingCompiler.compile`, per cycle, given the invalidated sources:

| Strategy | Stage 1 | Stage 2 | Java API / keys from |
|---|---|---|---|
| `Mixed` (default) | scalac over the invalidated `.scala` **and** `.java` sources (Java parsed, no classfiles) | javac over the invalidated `.java`, against stage 1's classfiles | javac classfiles (`ClassToAPI`, `JavaAnalyze`); the bridge skips Java units (`API.scala`: `unit.isJava && !isPickleJava`) |
| `ScalaThenJava` | scalac over the `.scala` only, Java from the classpath (last round's classfiles) | javac as in `Mixed` | classfiles |
| `JavaThenScala` | javac over the `.java`, Scala from the classpath (last round's classfiles) | scalac over the `.scala` | classfiles |
| `pipelining` (with `Mixed`; rejected with `JavaThenScala`) | scalac only, with `-Ypickle-java`, and from the second cycle on **every** Java source of the project (`nextChangedSources`) | none in the cycle; after the last cycle `compileAllJava` runs javac over every Java source | during the cycles the bridge's (source view, `-Ypickle-java`); the passed-in unchanged Java classes are excluded from change detection; after `compileAllJava`, classfiles |

Downstream projects under pipelining compile against the early output: pickles, including the Java pickles, i.e. the source view.

## Model

Reuse `JavaSpec.lean`'s instance and add the second view, not a new compiler.

* **Units and sources.** As in `JavaSpec`, plus Scala units: a Scala client is the same lookup task with Scala's levels (Phase 10's rules), compiled by scalac. A Java unit's source has two readings: `srcView : Src → Iface` (scalac's Java parser) and `cfView : Src → Iface` (javac). They are equal except where a parser difference is modelled (a flag per difference: parents read from source vs from the classfile; the `permits` clause; a member type's staticness, …).
* **Outputs and the interface.** A Java unit's output is javac's: `iface = cfView`, keys from the classfile. A Scala unit's output is scalac's.
* **`group` per strategy, as a two-stage `Task` composition.** For a round `G`:
  - `Mixed`: Scala members of `G` run against `e` overridden on `G`'s Java members by their **source** views; Java members of `G` then run against `e` overridden on `G`'s Scala members by stage 1's outputs.
  - `ScalaThenJava`: Scala members against `e` alone (`G`'s Java members answered from the state, i.e. last round's classfiles); Java members as in `Mixed`.
  - `JavaThenScala`: the mirror image.
  - `pipelining`: `G` is widened to every Java unit; Scala members run against source views of all Java units; Java outputs are the source views (pickles) until a final javac stage over all Java units replaces them with classfile views.
* **Obligations, read for each strategy.**
  - `comp` asks that the group's output be a fixed point of the per-unit tasks answered from the group's fresh interfaces, where those interfaces are the classfile views. Under `Mixed` it therefore holds exactly when, for every query a Scala member asks a Java member, the source view and the classfile view answer alike. **View agreement** is the obligation the parser differences break. Under `ScalaThenJava` and `JavaThenScala`, `comp` holds only under a hypothesis on dependency direction: no Scala unit of the project queries a Java unit (resp. the reverse). The clean build needs the same hypothesis, and the theorem states it.
  - `abstraction` between views: Zinc hashes a Java unit from its classfile view, but a Scala unit compiled in the same `Mixed` round read the source view. An edit that changes the source view and not the classfile view, or the reverse, can leave equal hashes and different answers. Under pipelining the stored hash flips between views across runs (bridge during cycles, `ClassToAPI` after `compileAllJava`), and Zinc's exclusion of unchanged Java classes is a policy that hides the flip; whether it also hides real changes is the question to check.
  - `coverage`: Java keys come from javac's classfile, but in `Mixed` the Scala units' queries to Java units go through the bridge (Scala keys), so coverage splits by reader. A Java unit's own queries against Scala units in stage 2 are answered from stage 1's classfiles and covered by its constant pool, as in `JavaSpec`.
  - Pipelining's early output: downstream reads the source view (Java pickles) while the final jar holds the classfile view. That is `Pipelining.lean`'s `early_agreement` with two different interfaces, which holds only under view agreement.

## Policies, existing and possible

* Existing: pass Java sources to scalac (`Mixed`), or not (`ScalaThenJava`/`JavaThenScala`); under pipelining, recompile every Java source in every cycle and all of them with javac at the end, and exclude the passed-in Java classes from API change detection; reject `JavaThenScala` with pipelining.
* Possible: hash a Java unit from one view consistently (always scalac's, `-Ypickle-java` without pipelining; or always the classfile's), or from both (a key per view, so either view's change invalidates); after a `Mixed` round, compare each recompiled Java unit's source view with its classfile view and recompile its Scala dependents in a further round if they differ (a cheap, local check of view agreement); under `ScalaThenJava`/`JavaThenScala`, report a dependency against the order instead of compiling against stale classfiles.

## Expected results

* A `Compiler`/`TCompiler` instance per strategy (one `group` each, shared unit tasks), with `Obligations` proved for `Mixed` under view agreement, and for the fixed orders under their dependency-direction hypothesis.
* For each known parser difference, a counterexample to `comp` (`Mixed`) or `abstraction` (the stored hash's view against the reader's view), stated as a theorem with a witness.
* Pipelining: the view flip as an abstraction statement, and Zinc's exclusion policy checked against it, which is the one place a real-compiler check (harness) may be predicted to diverge.

## Harness (only for a predicted violation)

The conformance harness writes `build.json` and `incOptions.properties` per layout. It needs per-base `compileOrder` (scripted's `build.json` already accepts `compileOrder` per project), per-base `pipelining` (today a run-wide `--inc-option`), and per-base `javacOptions` (scripted passes `javacOptions = Array()`; needed for `--release`, `-parameters`, preview features). The dump gains these fields; no other harness code.

## Results (`JavaOrder.lean`)

`JavaSpec`'s instance with a second view: a Java class `java sv cv` has the member types `sv` in scalac's source view and `cv` in javac's classfile view; a query that tells them apart stands for whichever detail the parsers disagree on (the `Object` parent of scala/scala#11292, the `throws` clauses and constant expressions of scala/scala3#27264). Scala clients run the same lookup task, compiled by scalac. `group` per order is the two-stage composition above (`stageEnv`: the round's units answered from a chosen view where a predicate holds, the rest from the state); keys and hashes are `JavaSpec`'s fix. Pipelining's cycles are `Mixed` with every Java source in the round, so the early-output statement is the pipelining-specific one.

| Result | Status |
|---|---|
| `obligations_mixed`, `mixed_sound`: `Mixed` meets the obligations, and T3a holds, on sources whose two views agree (a subtype of the sources) | proved, every program |
| **V1** `mixed_not_comp`: a Java class whose views differ breaks `comp` under `Mixed`: the Scala client compiled in the class's batch reads the source view, a round that recompiles it alone reads the classfile (the clean build is the first, the incremental the second) | proved, one witness |
| `early_view`: a downstream unit compiled against the upstream Java classes' source views (pickles, pipelining's early output) equals one compiled against their classfiles when the views agree on what it asks | proved, every task |
| **V2** `early_view_differs`: otherwise it differs | proved, one witness |
| **O1** `scalaThenJava_not_comp`, **O2** `javaThenScala_not_comp`: under a fixed order a unit of the first stage that asks a unit of the second stage of the same round reads last round's classfile; this fails even with agreeing views | proved, one witness each |

So the two views are an obligation on the compilers, not on Zinc: view agreement is what `Mixed`, and pipelining's early output, need, and each parser difference fixed in scalac or dotc (scala/scala#11292, scala/scala3#27264) discharges an instance of it. On Zinc's side, the options are those under "Policies": a check of view agreement after a `Mixed` round (compare a recompiled Java class's source view with its classfile, and recompile its Scala readers on a difference) would turn V1 into a further round; the fixed orders need the direction hypothesis or a rejection.

Not yet modelled: pipelining's hash flip across runs (the bridge's source-view API during cycles, `ClassToAPI` after `compileAllJava`) and Zinc's exclusion of the passed-in Java classes from change detection; that is the next step, and the one where a harness run may be predicted to diverge.

## Steps

- [x] P13.1 This design (approved by the coordinating session).
- [x] P13.2 `JavaOrder.lean`: two views per Java class, Scala clients, `group` per order; `Obligations` and T3a for `Mixed` under view agreement; counterexamples V1, O1, O2.
- [x] P13.3a Pipelining's early output: `early_view`, V2.
- [ ] P13.3b Pipelining's hash flip across runs and Zinc's exclusion policy.
- [ ] P13.4 Probe the differences with scalac and javac (no sbt); harness only for a predicted divergence, with the per-base fields above.
