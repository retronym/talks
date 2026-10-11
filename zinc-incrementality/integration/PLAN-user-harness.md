# Plan: users run the incremental ≡ clean check on their own builds

**Status:** draft for review. Nothing below is implemented.

## Problem

Every Zinc bug found since October came from code we chose: model-generated programs, 146 edits to Spark catalyst, and the 20 predictions. Users have the real variety (macros, compiler plugins, source generators, Java mixes, Scala 3 features, odd build layouts) and a real edit history. Today they report a bug only when a build breaks visibly, and the report is "sometimes I have to clean".

We want a user to run one command against their build, have it compare incremental output with clean output across real edits, and get a report we can act on. Two things make that harder than shipping the existing harness:

1. **Fixed but unreleased.** Many bugs we would hear about are already fixed in an open PR (retronym/zinc#32–#58, sbt/zinc#1841, scala/scala#11289–#11292). A user on released sbt and Scala will rediscover them. They need to rerun a finding on the integration toolchain before reporting it.
2. **The clean build is not a fixed reference** on a released scalac. Without #11289–#11292 (still open; only #11293 is merged), mixed Scala/Java builds show differences that are batch dependence, not staleness. A report must separate the two, or we drown in noise.

## Review of what exists

What carries over:

- **The oracle:** after each incremental build, compare every classfile with a clean build's, with verdicts (`same`, `signature`, `java-context`, `fresh-mismatch`, `bytecode`) that separate batch dependence from staleness. This is `IncBench --verify` (retronym/zinc#31), and it works on real code (catalyst, 292 steps).
- **Edits from a real build:** `Hierarchy` plus `bin/catalyst-edits.py` generate edits targeted at the most-inherited and most-used classes.
- **A toolchain from a branch:** `build-integration` with manifests and lock files gives a named, reproducible set of unreleased fixes; `zinc-sbt` runs a project's own sbt with that Zinc (and optionally that compiler as STARR).

What blocks handing it to users:

- **It runs only inside a Zinc checkout.** IncBench is in `zinc-scripted`'s test sources and drives Zinc through scripted's `IncHandler`, not through sbt. `--build` needs a hand-written `build.json` with dependency jars in `lib/`; source generators, compiler plugins, per-project `scalacOptions` and inter-project dependencies have to be reproduced by hand. That was fine for one module of Spark, not for arbitrary builds.
- **`--verify` is on the Merkle line only.** It is in `integration/merkle` and `integration/merkle-1.12.x` but not in `integration/develop` or the develop conformance branches (#36, #54). It does not depend on Merkle and should land on its own.
- **`zinc-sbt` builds from source** (sbt, coursier and a JDK, minutes per branch), assumes `~/code/.integration`, replaces jars inside sbt's boot directory, and is tested only on sbt 1.12 with scala/scala. sbt 2 is untested.
- **`KeyCheck` does not transfer.** It checks the Analysis against keys the Lean model predicts for a generated program; for real code there is no prediction. It stays an internal oracle.
- **Verdicts assume our compiler.** On stock 2.13.x, `fresh-mismatch` (explained by none of the extra clean builds) can still be batch dependence, so for users it means "needs triage", not "bug".

## Key decisions

### 1. Run the user's own sbt, not a replay of their build

The tool drives the user's sbt (`sbt --client`) on their checkout, rather than exporting the build into IncBench. Everything that makes real builds interesting (generators, plugins, macros, settings) then comes along for free, and the same tool works with any toolchain `zinc-sbt` can swap in. IncBench `--build` stays our tool for reproducing a finding in depth once we have one.

To keep paths identical (Scala 3 TASTy and some macros embed them), the clean build happens in the same directory: after an incremental compile, move the build's class directories and Zinc analyses aside, compile clean, compare, then move the incremental ones back and carry on. That costs a clean build per checked step, so steps are sampled (see 2).

Things to switch off for the clean build, or they make it a non-reference: sbt 2's local and remote compile caches, `sbt-buildinfo` and other generators that stamp time or SHA, pipelining (until we know it is stable here).

### 2. Edits come from the user's git history first

Replay commits: check out `A`, build, then step through `A..B` one commit at a time (or jump between non-adjacent commits, which makes bigger edits). Each step is a real edit someone made, so a finding is a bug real users hit. Generated edits (`Hierarchy` + the edit generator) are an opt-in second mode for builds with short histories.

Checking every step costs a clean build each. Default to checking every *k*-th step plus the last, and on a difference, bisect the steps in between.

### 3. Lift the verdict code into a standalone comparator

Extract the classfile comparison and verdicts from `IncBench` into a small module, published, with a CLI: `compare INCREMENTAL CLEAN` → a verdict and the differing classes. The user-facing driver calls it; IncBench calls it too, so there is one implementation. `java-context` needs extra clean builds (Java as classfiles, the rounds' batches); in the user-facing tool, run those only for steps that otherwise come out `fresh-mismatch` or `bytecode`.

### 4. Every report says what toolchain it ran on, and is rechecked on the integration toolchain

A finding is reported with sbt, Zinc and Scala versions and, for integration builds, the `MANIFEST.lock` SHAs. Before a user files anything, the tool reruns the failing step on the current integration toolchain (`--toolchain integration`). Three outcomes: fixed there (report as "fixed, unreleased", useful as a test case for the PR), still failing (a real report), or a different result (interesting too).

### 5. Ship prebuilt integration toolchains from CI, not build them on the user's machine

CI builds each integration branch on push and publishes Zinc, the bridges, and the matching Scala 2 and Scala 3 compilers to a public static Maven repository, with versions that carry the SHA (`1.12.15-bin-<sha>`, `2.13.19-bin-<sha>`). The toolchain is then a download, not a build.

- **Scala.** A compiler at a SHA is an ordinary dependency: `scalaVersion` plus a resolver. Merged upstream commits already have one (scala-integration for 2.13, the Scala 3 nightlies on Maven Central); our repository adds integration-branch and PR SHAs.
- **Zinc.** Harder, because sbt loads Zinc from its own classpath. Options, to settle in a spike: (a) keep `zinc-sbt`'s approach, swapping jars in a private boot directory, but fetching them prebuilt; (b) publish an sbt build at `<sbt-version>-zinc-<sha>` that depends on the Zinc SHA, so the user only sets `sbt.version` and a repository in `project/build.properties` and `~/.sbt/repositories`. (b) is cleaner for users and works with the stock launcher; it costs a republish of sbt's modules per Zinc SHA; (c) change sbt so a build can choose its Zinc, e.g. a `-Dsbt.zinc.version` the launcher honours when it resolves sbt, or loading Zinc in its own classloader the way the compiler bridge already is. (c) is the right end state and useful beyond this tool (trying a Zinc fix without waiting for an sbt release), but it helps only sbt versions released after it lands, so it goes upstream in parallel and (a) or (b) covers sbt 1.12 and current sbt 2 meanwhile.
- **Hosting.** A static Maven layout on object storage or a GitHub Pages repository. Not GitHub Packages: it requires a token even to read public packages.

`zinc-sbt` keeps its current from-source mode for us; users get the download mode.

### 6. Reports stay local until the user decides what to send

Findings involve the user's code: the edit's diff and the differing classfiles. The tool writes a local report directory (toolchain, step, verdict, differing class names, `javap` diffs, the edit's diff) and a short summary that contains no code (verdict, toolchain, class kinds and counts, which features are involved: Java, macros, Scala 3). The user sends what they are allowed to. Minimising is up to the user for now; a guided minimisation (delta-debugging the edit and the sources, possibly agent-assisted) is future work.

### 7. The same replay compares two Zinc implementations

A second use: a bakeoff between two Zinc builds on the user's own code, e.g. the Merkle PoC against the Zinc it branched from. This is what `IncBench` did on catalyst (develop vs PoC: recompiled classes, rounds, wall time, and verification on both sides), but on the user's build and history instead of edits we picked. The driver should take a list of toolchains, not one.

- **The baseline is the Merkle branch's own base** (`integration/develop` for `integration/merkle`; `integration/develop-1.12.x`, rz#48's non-Merkle commits, for `integration/merkle-1.12.x`), not a released Zinc. Otherwise unrelated fixes on the integration branch confound the comparison.
- **Each toolchain keeps its own incremental state.** Their analyses differ (Merkle stores different hashes), so the driver keeps one set of outputs and analyses per toolchain and swaps them in, as it already does for the clean build. They share the source checkout and its paths.
- **One clean build serves both** when the compiler is the same: Merkle changes what is recorded and invalidated, not the bytecode. That makes a bakeoff step cost two incremental builds and one clean build, not two of each.
- **Per step, per toolchain:** the verdict against the clean build, the classes recompiled, the rounds, and the wall time. Run the toolchains alternately on each step and report medians, since the user's machine is noisy.
- **The summary contains no code**, only counts, times and verdicts, so bakeoff results are easy to share. Results across many users' builds are the evidence for upstreaming Merkle, and the cases where Merkle recompiles *more* are what we want to see.

## Phases

| phase | outcome |
|---|---|
| 0 | Land `--verify` on develop and 1.12.x independently of Merkle. Extract the comparator. |
| 1 | CI publishes integration toolchains to the static repository. Spike sbt-at-a-Zinc-SHA vs boot-jar swap; pick one. Open the sbt PR for choosing Zinc per build. |
| 2 | The driver: git-history replay on the user's sbt, sampled verification, bisect on difference, local report. Several toolchains per run (the bakeoff). Dogfood on scala/scala, Spark, Scala 3 itself, and one or two community builds with Java and macros. |
| 3 | `--toolchain integration` recheck; summary format; a "how to report" page and issue template on retronym/zinc. |
| 4 | Invite users: a short post with the one command, for both bug hunting and the Merkle bakeoff; collect results. |

Future work: generated edits as a user mode; a CI mode (incremental from the main branch's cached build vs clean, on each PR); matching findings against `BUG-MAP.md` families automatically; guided minimisation; Mill and Bleep (both use Zinc).

## Open questions

1. Which Zinc delivery for released sbt, (a) or (b) in decision 5? I lean to (b) if republishing sbt per SHA is cheap in CI. And the shape of the sbt change (c): a launcher property, or Zinc behind its own classloader? The second is bigger, since sbt's own code links against Zinc's API.
2. Should the user-facing tool require the batch-stable scalac (or at least treat `java-context`/`signature` as clean) to cut noise, given #11289–#11292 are still open?
3. Where do reports go: issues on retronym/zinc, or a form we triage before anything public?
4. Scope of the first release: Scala 2.13 on sbt 1.12 only, or 2.13 and 3 together?
