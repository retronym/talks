# Integration branches

The Zinc fixes are spread over many open PRs across retronym/zinc, sbt/zinc, retronym/scala, scala/scala, retronym/scala3 and scala/scala3. These branches are built from them, so there is one build to run IncBench and the conformance harness against, to see which pending tests the fixes turn green, and to hand to a collaborator.

| Branch | Repository | Base | Manifest |
|---|---|---|---|
| `integration/develop` | retronym/zinc | sbt/zinc `develop` | [zinc-develop](zinc-develop/manifest.toml) |
| `integration/merkle` | retronym/zinc | `integration/develop` | [zinc-merkle](zinc-merkle/manifest.toml) |
| `integration/merkle-1.12.x` | retronym/zinc | sbt/zinc `1.12.x` | [zinc-merkle-1.12.x](zinc-merkle-1.12.x/manifest.toml) |
| `integration/2.13.x` | retronym/scala | scala/scala `2.13.x` | [scala-2.13.x](scala-2.13.x/manifest.toml) |
| `integration/scala3-main` | retronym/scala3 | scala/scala3 `main` | [scala3-main](scala3-main/manifest.toml) |
| `integration/scala3-merkle` | retronym/scala3 | `integration/scala3-main` | [scala3-merkle](scala3-merkle/manifest.toml) |

## How they are built

The branches are built, not maintained, like git.git's `seen` or linux-next. [`build-integration`](build-integration) reads a manifest (the base, the ordered member PRs, and the PRs left out with the reason) and merges each member's head with `--no-ff` onto a fresh branch from the base. A `MANIFEST.lock` commit at the tip lists the SHA of every member, and `--push` force-pushes with a lease.

```bash
./build-integration zinc-develop/manifest.toml --dry-run
./build-integration zinc-develop/manifest.toml --push
```

- The PR branches are the source of truth. A problem in a member, such as two PRs adding a test of the same name, is fixed in the PR.
- Merging keeps each PR's SHAs, so `git branch -r --contains <sha>` answers whether a PR is in.
- Each manifest's `rr-cache/` holds the conflict resolutions recorded by `git rerere`. The build runs in a private clone under `~/code/.integration/` whose `.git/rr-cache` links to it, so a rebuild needs a human only when a member changes in a conflicting region. Then the build stops mid-merge; resolve, `git commit --no-edit`, rerun, and commit the new `rr-cache` entries.
- A resolution that needs edits outside the conflicting hunks (rerere records only those) goes in a patch beside the manifest, applied as a `patch` member.

The order within a manifest is fixes, then pending tests, then tooling. When a fix makes a pending test pass, the integration build's scripted run reports `Pending test … passed`; flipping the test to `test` is a change for the PR.

## Scala snapshots

The Zinc branches run their `3.x` scripted tests against the Scala 3 integration builds, since some fixes are compiler-side (the package wildcard imports, `AnalysisCallback5`). [`publish-scala3-snapshot`](publish-scala3-snapshot) publishes a scala3 checkout to a private Ivy home, and the Zinc sbt server is started with it and `-Dzinc.scala3ForBridge` (retronym/zinc#60):

```bash
./publish-scala3-snapshot ~/code/.integration/integration-scala3-main /tmp/ivy-develop
cd ~/code/.integration/integration-develop
sbt -Dzinc.scala3ForBridge=3.10.1-RC1-bin-SNAPSHOT --ivy /tmp/ivy-develop --client scripted
```

`integration/scala3-main` and `integration/scala3-merkle` publish the same version, so each gets its own Ivy home. Rebuild whenever a member's head moves or a base advances.

## Running a project's sbt on an integration branch

[`zinc-sbt`](zinc-sbt) starts sbt in the current directory with Zinc replaced by an integration branch. It publishes the branch into a private Ivy home under `~/code/.integration/`, at the Zinc version the project's `sbt.version` depends on, and replaces the Zinc jars in a private boot directory, so `~/.ivy2`, `~/.sbt` and other sbt servers are untouched. Scala 2.13 projects also get the branch's compiler bridge instead of scala2-sbt-bridge.

```bash
cd ~/code/scala/scala
~/code/retronym/talks/zinc-incrementality/integration/zinc-sbt merkle-1.12.x
```

The first run publishes the branch (a few minutes); later runs republish only when the branch's tip moves.

The argument can also be any other branch of retronym/zinc, such as a PR branch, to try it before the integration branch is rebuilt:

```bash
~/code/retronym/talks/zinc-incrementality/integration/zinc-sbt backport/1.12.x-merkle-hash-poc
```
