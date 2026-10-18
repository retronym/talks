# Plan: an IncBench campaign over scala/scala and scala/scala3

**Status:** reviewed; the open questions are answered below. Only the dashboard mockup exists. scala/scala goes first as a tracer bullet through the whole pipeline; scala/scala3 follows.

## Problem

We have three kinds of improvement in flight and no shared way to measure them on real builds:

1. **The compilers.** scala/scala and scala/scala3 performance PRs (lub/glb, allocation, the patmat analysis, the optimizer bailout, the `ContextBase` leak) are measured one at a time, on synthetic benchmarks or `compiler-benchmark`, never in an incremental build.
2. **Zinc's own overhead.** The leaner `NameHashing` (sbt/zinc#1852, rz#68), printing annotation arguments once (sbt/zinc#1851) and the bridge allocation cuts reduce the work Zinc does per class, but we have only allocation figures for one phase.
3. **The invalidation algorithm.** Merkle recompiles fewer sources (rz#24, rz#48), but its evidence is class counts and wall time on catalyst. It doesn't show what Merkle costs per step, or how much of a step is scalac and how much is Zinc.

A single campaign should answer all three on the two builds we know best, with every step broken down far enough to see which side of the bridge moved: scalac phase by phase, and Zinc's own work beside it. It should also record every invalidation cycle, so a change in time can be traced to a change in what was recompiled.

The campaign takes hours. We want to watch it run and read partial results that already compare like with like, not wait for the end.

This is not a precision benchmark. It is meant to show where time and recompilation go and which way each change moves them, on real builds. Effects that need many repetitions to resolve are for `compiler-benchmark` or JMH afterwards.

The dashboard mockup, with sample data, is at <https://claude.ai/artifact/UiitoMvUkQD64vUYbHjH6Z>. Its six datasets are the data model below, less a few fields the mockup doesn't draw yet.

## The matrix

Twelve cells: two builds × two compilers × three Zincs.

| Axis | Values |
|---|---|
| Build | scala/scala at a pinned `2.13.x` commit; scala/scala3 at a pinned `main` commit |
| Compiler | base; integration. *Base* is the commit the integration branch is built on, and *integration* is `integration/2.13.x` or `integration/scala3-main` (decision 4) |
| Zinc | released 1.12; `integration/develop-1.12.x` (Zinc perf fixes, name hashing); `integration/merkle-1.12.x` (Merkle) |

Each comparison is a pair of cells that differ in one axis:

- **Compiler:** base vs. integration compiler, on released Zinc.
- **Zinc performance:** released Zinc vs. `develop-1.12.x`, on the base compiler.
- **Algorithm:** `develop-1.12.x` vs. `merkle-1.12.x`. Both carry the Zinc perf fixes, so the difference is the algorithm alone.
- **All together:** the base compiler on released Zinc vs. the integration compiler with Merkle Zinc.

Every cell runs the same edit script for its build, so a step means the same edit in all six cells of a build.

## Key decisions

### 1. Drive Zinc in-process through IncBench

Each cell is one JVM running IncBench from that cell's Zinc checkout, which calls Zinc through scripted's `IncHandler`, with the compiler bridge built from the same checkout. We control exactly what runs: no sbt task graph, no sbt caches, no plugin or server overhead in the timings, and the per-cycle hooks (`PhaseTimings`, the invalidation profiler) are reachable directly.

The cost is that IncBench needs each build described as a `build.json` (decision 3), and the numbers are Zinc's and scalac's, not what an sbt user waits for. That's what we want to compare here. The user-facing view is `PLAN-user-harness.md`'s job.

### 2. One harness, identical in every Zinc

The three Zincs must differ only in the changes being measured, so IncBench, `PhaseTimings` and the measurement hooks have to be byte-identical in all three. Today IncBench and `PhaseTimings` exist only on the Merkle lines, inside rz#48's series (and rz#24 on develop).

So the harness gets its own PR on `1.12.x`, which doesn't depend on Merkle:

- `merkle-1.12.x` gets the harness from that PR instead of rz#48. rz#48 gets a fixup that deletes its copy, rather than a rewrite of its series.
- `develop-1.12.x` adds the same PR.
- The released-Zinc cell is a new integration branch, `bench-1.12.x`: the `v1.12.x` release tag plus the harness PR and nothing else.

A harness change then rebuilds all three, and the dashboard records the harness commit per cell.

### 3. Export each build to `build.json` once, and freeze it

The pinned commit of each build is exported once by a small sbt command: per module its sources (generated ones included), classpath, `scalacOptions`, `javacOptions` and output directory, in dependency order. The exported build is then fixed for the whole campaign. Every cell compiles the same files with the same options; only the compiler jars and the bridge differ.

Scope, so a clean build stays in minutes:

- **scala/scala:** `library`, `reflect`, `compiler`. These modules hold the deep hierarchies the edits target. scaladoc, the REPL and partest add time, not information.
- **scala/scala3:** `scala3-interfaces`, `scala3-library-nonbootstrapped`, `tasty-core-nonbootstrapped` and `scala3-compiler-nonbootstrapped`, as in the earlier compile cycles.

Generated sources (scala/scala's version properties, scala/scala3's unpacked scalajs-ir) are captured by the export as plain files, so no generator runs during the campaign.

### 4. The compiler is a set of jars, built from source on both sides

Both builds compile themselves with an earlier compiler: STARR for scala/scala, the reference compiler for scala/scala3. In-process, that compiler is just the jars IncBench hands Zinc as its `ScalaInstance`, so a compiler cell swaps jars and leaves the frozen sources alone. Nothing has to be published under a version the build would accept.

The baseline is not the last release. It is the commit the integration branch is built on, built the same way as the integration compiler. Against a release, the comparison would also carry every upstream change since that release; against its own base, it measures our open PRs and nothing else.

- **scala/scala:** upstream `2.13.x` at `integration/2.13.x`'s base, and `integration/2.13.x`, each built as `publish-scala2-starr` builds STARR (optimized, as a release is). The frozen build is that same base commit.
- **scala/scala3:** upstream `main` at `integration/scala3-main`'s base, and `integration/scala3-main`, each as its non-bootstrapped compiler, library, tasty-core, interfaces and sbt bridge jars. The frozen build is that base commit's non-bootstrapped modules, which the bootstrapped build already compiles with a compiler built from the same sources.

For Scala 2 the bridge is compiled from the cell's Zinc checkout. For Scala 3 the bridge comes with the compiler, so the Scala 3 Zinc cells differ only in Zinc's own code. Merkle's bridge-side hashing for Scala 3 is only in `integration/scala3-merkle`. Using it as the integration compiler would mix two axes, so the Scala 3 Merkle cells run Merkle with the standard bridge, and bridge hashing on Scala 3 is a follow-up campaign.

### 5. Lockstep, one compile at a time, one build at a time

An orchestrator, a Python script in this directory beside `build-integration`, starts every cell's JVM once and sends it commands on stdin: `prepare` (load the build, clean build, warm up), `step k`, `shutdown`. Each command answers with one JSON line.

For each step *k*:

1. Shuffle the cells.
2. Run step *k* in each cell in that order, one at a time, so no two compiles compete for the machine.
3. Barrier: write the data files and push them to the dashboard.

Only one cell compiles at any moment, so the others' JVMs are idle. Results are comparable after every step, and drift in the machine (thermals, background work) spreads evenly over cells instead of landing on whichever ran last.

**Two waves.** Twelve warm JVMs don't fit comfortably in 48 GB, so the campaign runs as two waves of six cells: scala/scala first, then scala/scala3. Lockstep holds within a wave. The dashboard shows the second build's cells as queued until its wave starts.

### 6. What each step records

A step applies its edit and compiles, once. `prepare` warms the JVM with the clean build and a few no-op and body-edit compiles before step 1, so the first timed step isn't paying for JIT. One repetition is the starting point: the campaign is about direction and attribution, not precise timings. `reps` stays an option, and a step can be rerun on its own when a number looks wrong.

- **Wall time** of the whole incremental compile.
- **scalac, per phase:** scalac's profiler (`-Yprofile-enabled -Yprofile-destination`) per compiler run, summed over the step's cycles. Phases are mapped to shared groups so both compilers chart alike: parse and name, typer, pickle and checks, API extraction, dependencies, transforms, backend. API extraction includes Zinc's per-class hashing, which runs inside it through `callback.api`.
- **Zinc, per part:** `PhaseTimings` (`initialChanges`, `invalidate`, `detectAPIChanges`, `analysis`, `merge`, `prune`) plus IncBench's own timing of the analysis store's read and write. Zinc's time is wall time minus scalac's.
- **Invalidation cycles:** for each cycle, the sources and classes it compiled and the reason that started it. The reasons come from the invalidation profiler, extended where it lacks one (Merkle's descendant rules), rather than from parsing debug logs.
- **Correctness:** on the first repetition, untimed, `--verify` compares the result with a clean build by classfile digest. A mismatch marks the step on the dashboard.
- **Allocation:** scalac's profiler already reports allocated bytes per phase. It's recorded, but not charted in the first version.

### 7. The edit script

Twelve steps per build: a clean build, no-ops at both ends, body-only edits, public members added to widely inherited types, a private change, and reverts. Each step is a patch file applied to the frozen build.

The targets are chosen from the build's class hierarchy (`Hierarchy`, as `catalyst-edits.py` does), so that the member additions hit the most-inherited types of each build: `SubComponent`, `Symbol`, `IterableOps` for scala/scala, and `MiniPhase`, `Context`, `Symbol` for scala/scala3. The mockup's edit list is a first cut.

### 8. Feeding the dashboard

After each barrier the orchestrator writes the six data files that the mockup's datasets read: `campaign`, `cells`, `steps`, `phases`, `cycles`, `edits`. A Claude session watching the results directory uploads them to the dashboard and repoints its datasets, one push per lockstep step. Viewers see each step land as it finishes.

## Data model

| File | One row per | Fields |
|---|---|---|
| `campaign` | campaign | name, start, wave, reps, cells, steps per cell, steps done, current step, elapsed, estimated remaining, machine, harness commit |
| `cells` | cell | id, build, compiler and its version, Zinc and its commit, algorithm |
| `steps` | cell × step | edit, status, order in its lockstep round, start offset, wall time (median, min and max when `reps` > 1), scalac time, Zinc time, sources, classes, cycles, verify verdict |
| `phases` | cell × step × part | group, phase name, milliseconds, allocated bytes |
| `cycles` | cell × step × cycle | sources, classes, reason |
| `edits` | build × step | kind, file, description, patch |

## Milestones

scala/scala is the tracer bullet: every stage of the pipeline works end to end for it, with the dashboard live, before scala/scala3 starts.

- [x] Dashboard mockup with sample data.
- [ ] **M1 Harness PR on 1.12.x.** IncBench, `PhaseTimings` and `--verify` in their own PR. Add it to `develop-1.12.x` and `merkle-1.12.x`, with a fixup in rz#48 that deletes its copy, and create the `bench-1.12.x` manifest.
- [ ] **M2 scala/scala export.** The sbt export command, the frozen `build.json` for `library`, `reflect` and `compiler` at `integration/2.13.x`'s base, and a clean build through IncBench in one cell whose classfiles match sbt's.
- [ ] **M3 Measurements.** Per-phase scalac timings, the Zinc split and cycles with reasons, as JSON lines from one cell.
- [ ] **M4 Lockstep.** The `serve` mode and the orchestrator, first with the two scala/scala cells that differ only in algorithm, then all six.
- [ ] **M5 Live dashboard.** Real files replace the sample data, pushed after each lockstep step.
- [ ] **M6 Wave 1: scala/scala,** all six cells, with a short write-up of what each comparison showed.
- [ ] **M7 scala/scala3.** Its export, the compiler jars for both sides, and a check that Scala 3's profiler output reads like Scala 2's.
- [ ] **M8 Wave 2: scala/scala3,** and the combined write-up.

## Answered questions

1. **Scala 3's profiler.** Scala 3 has had `-Yprofile-enabled` and `-Yprofile-destination` since 0.7.0, a port of scalac's profiler (scala/scala3@fcc30d4c7c), plus `-Yprofile-trace` for a Chrome trace. M7 checks that its per-phase output parses like Scala 2's.
2. **The integration compiler for scala/scala3.** In-process, the compiler is jars, so nothing is published under the reference compiler's version (decision 4).
3. **Memory.** Two waves of six, scala/scala first (decision 5).
4. **Reps.** One, as the starting point. The campaign isn't for precise timings (decision 6).
5. **rz#48.** A fixup that deletes the harness from it, not a rewrite of its series (decision 2).

## Prior art

- IncBench itself (rz#24, rz#30, rz#31): edits on generated trees and on Spark catalyst, with `--verify`.
- scalac's profiler and `scala/compiler-benchmark`, for per-phase timing and warm-JVM methodology.
- `build-integration` and `zinc-sbt` in this directory, for building and pinning each toolchain.
- `PLAN-user-harness.md`, the sbt-driven counterpart for users' own builds.
