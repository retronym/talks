# IncBench anomalies: apache/pekko

- **Build:** apache/pekko at `main` (shallow clone, 2026-10-19), Scala 2.13.18, modules `actor` (203 Scala + 28 Java sources) and `actor-typed` (90 Scala + 1 Java). Options as the build sets them, except that the optimizer and the lints are removed (`builds/pekko-noopt`): the sbt-pekko-build plugin sets `-opt:l:inline -opt-inline-from:org.apache.pekko.**`, and cross-class inlining is not a supported configuration for Zinc, so this report runs without it. The generated `incOptions.properties` of every cell contains no `-opt` flag. Also dropped with the lints: `-Xfatal-warnings` and `-Wconf:any:e`. Mixed Java/Scala, deep `ActorRef`/`Actor` hierarchies, `-release 17`.
- **Run:** `lockstep --verify --profile`, the three cells as in `cats.md` (bench f7b7642c03, develop 5615b62e16, merkle 556464169f), with `recompileOnMacroDef=true` (sbt's default; confirmed in every cell's generated `incOptions.properties`). Clean build ~5 s warm. Edit script: `edits/pekko.tsv`. Results: `~/code/.integration/campaigns/2026-10-20-pekko-macrodef-true`. Timings were taken on a loaded machine and are provisional.

## Correction to the first campaign

The first campaign ran pekko with the optimizer on and `recompileOnMacroDef=false`. Its anomaly 1 (stale inlined code after editing an `@inline` method) and anomaly 2 (inlining decisions depend on the batch) arose from running with the optimizer, which Zinc does not support. They are not Zinc or Merkle bugs and are retracted as findings. With the optimizer off, none of this appears: `inline-method-body` recompiles one source and verifies `signature`, and no step shows a java-context or inlining difference.

## Steps

All cells, all 18 steps (edits and reverts): `signature` (no `fresh-mismatch`, no `bytecode`).

| Step | released / perf | merkle |
|---|---|---|
| actor-unhandled-body | actor 1 (31 cl) | same |
| actorref-add-member | actor 1+10 (98 cl) | actor 1+4 (36 cl) |
| actor-private-member | actor 1 | same |
| fsm-reason-add-case | actor 1+4 (31-32 cl) | same |
| timeout-add-implicit | actor 1+14, actor-typed 6 (156 cl) | same |
| pattern-package-object-add-def | 1 | 1 |
| inline-method-body | 1 | 1 |
| java-receivebuilder-body | 1 (javac only) | 1 |
| java-nodequeue-add-method | actor 1+4 (55 cl) | same |

## Anomalies

None new. With `recompileOnMacroDef=true` and the optimizer off, the build behaves like an ordinary non-macro build; the second cycle that `actor-unhandled-body` and `actor-private-member` had in the first campaign (1+1) is gone, because `ReceiveTimeoutCompat` no longer counts as macro-defining. (The bridge marks an `@inline` method as a macro only when the inliner is enabled.) Pekko has no macro-defining classes in these modules, so `recompileOnMacroDef` has no effect on any recompile count here.

### Merkle wins on `ActorRef` (expected)

`actorref-add-member` (add `def zincCheck` to `abstract class ActorRef`): Merkle 1+4 sources, 36 classes vs. 1+10, 98 classes. Unchanged from the first campaign. The one clear Merkle win outside scala/scala.

## Performance

Timings are provisional (loaded machine). Merkle's `analysis` phase is higher on every step; that is partly the harness bug in the pinned cells (uncached `Locate.definesClass` in IncHandler, fixed in rz#71 4cba55a47, about 100 ms per step) and is not attributable to Merkle.
