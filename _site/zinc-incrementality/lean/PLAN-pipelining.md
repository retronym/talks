# Phase 19 — pipelining's early-output lifecycle (`PipelineLifecycle.lean`)

## Question

With pipelining an upstream writes its early output (pickles, the early analysis) before its compile is known to succeed, and the downstream compiles against it at once. `Pipelining.lean` stated two obligations on the upstream's outputs: early agreement (the early view answers like the final one; Phase 14 made it `JavaOrder.early_view` for Java) and "published = built" (the early output describes the sources as last built successfully), the latter only as a checked scenario. BUG-MAP's cluster PL: sbt/zinc#1843 (the user's open PR: a failed pipelined compile leaves stale early output), scala/scala3#27139 (a cancelled async write drops callbacks and TASTy files), #27125 (keys arrive after the decision that needs them), #20119 (a spurious cyclic-macro error only under early output), sbt/zinc#918 (Java sources under pipelining).

## Model

An upstream unit's lifecycle state is three views: the source of its last successful build, that build's interface (`built`), and the interface of its early output (`early`). A run with source `s` does nothing when `s` is the last built source; otherwise it writes `early := fresh` and then succeeds (`built := early := fresh`) or fails. On failure, Zinc rolls back the classfiles and the analysis; the early output is rolled back too only with #1843 (`Rollback`). The downstream reads `early` and stores its hash as a snapshot; its next build invalidates when the hash it reads differs from the snapshot.

## Results (`PipelineLifecycle.lean`)

| Result | Status |
|---|---|
| `rollback_preserves`: with #1843 every run keeps the early output equal to the last successful build | proved, every state and run |
| `noRollback_breaks`: without it a failed run publishes an interface that never built | proved |
| `stale_after_revert`: the revert, whose sources equal the last build's, leaves that interface published, with the hash the downstream stored during the failed run, so nothing invalidates the downstream (`Pipelining.stale_after_failed_upstream`, now for every interface and hash) | proved |
| `rollback_detects`: with #1843, the restored early output's hash differs from the downstream's snapshot of the failed one whenever the hash tells them apart, so the downstream recompiles (`Pipelining.rollback_after_failed_upstream`) | proved |
| `downstream_reads_built`: under the invariant the downstream's oracle on the upstream is the built one, so `Classpath.downstream_sound` holds relative to the last successful build | proved |
| `partial_write`: a cancelled write (scala/scala3#27139) leaves an early output that never built; rolling it back restores the invariant | proved |

So #1843 is a policy, not a key: it restores the invariant every downstream key relies on ("what I hashed is what was built"), and the downstream's existing snapshot key then detects the transient failure. The early output remains a third view of the upstream (beside Phase 14's source and classfile views): `JavaOrder.early_view` is its agreement with the final view, this phase its agreement with the last successful build.

Open, with no model: #27125 (the early analysis's keys arrive after the downstream's invalidation decision: the framework's rounds have no time between `keys` and `invalidated`), #20119 (`comp` for a pipelined group with macros), #918 (partially `JavaOrder.lean`: a Java unit not passed to scalac has no view in the round), and Phase 14's exclusion flip.

## The cluster's scripted tests

On develop the pipelining tests (`subproject-pipelining*`, `java-only-round*`, `trait-*-3`, `java-then-scala-order`, ...) pass; `pipelining/java-comment-change` is pending (Phase 14's flip). #1843 adds `pipelining-failed-upstream-revert` and `-bytecode`, the instances of `stale_after_revert` (spurious error, and stale bytecode with no error), fixed by `rollback_preserves`.

## Steps

- [x] P19.1 `PipelineLifecycle.lean`: the lifecycle, the invariant, #1843 as the policy that preserves it, the stale-after-revert theorem, detection, the downstream's oracle.
- [x] P19.2 The cluster's scripted tests mapped.
- [ ] Future: a time-ordered round (keys written, decision taken) for #27125.
