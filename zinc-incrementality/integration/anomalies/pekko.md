# IncBench anomalies: apache/pekko

- **Build:** apache/pekko at `main` (shallow clone, 2026-10-19), Scala 2.13.18, modules `actor` (203 Scala + 28 Java sources) and `actor-typed` (90 Scala + 1 Java). Options as the build sets them: `-Xfatal-warnings` with `-Wconf:any:e`, `-release 17`, and the optimizer with cross-file inlining (`-opt:l:inline -opt-inline-from:org.apache.pekko.**`, set by the sbt-pekko-build plugin, not in pekko's own build files). Mixed Java/Scala, deep `ActorRef`/`Actor` hierarchies.
- **Run:** `lockstep --verify --profile`, the three cells as in `cats.md`, lockstep's defaults (recompileOnMacroDef false). Clean build ~5 s warm. Edit script: `edits/pekko.tsv`. Results: `~/code/.integration/campaigns/2026-10-19-pekko`, plus `2026-10-19-pekko-macrodef` (one step with recompileOnMacroDef true).

## Steps

| Step | released / perf | merkle | Verdict |
|---|---|---|---|
| actor-unhandled-body | actor 1+1 (32 cl) | same | signature |
| actorref-add-member | actor 1+10 (98 cl) | actor 1+4 (36 cl) | fresh-mismatch (noise) / signature |
| actor-private-member | actor 1+1 | same | signature |
| fsm-reason-add-case | actor 1+4 (32 cl) | same | fresh-mismatch (noise) |
| timeout-add-implicit | actor 1+14, actor-typed 6 (156 cl) | same | fresh-mismatch (noise) |
| pattern-package-object-add-def | 1 | 1 | same |
| inline-method-body | 1 | 1 | **bytecode** (all) |
| java-receivebuilder-body | 1 (javac only) | 1 | same |
| java-nodequeue-add-method | actor 1+4 (55 cl) | same | fresh-mismatch (noise) |

## Anomalies

### 1. Stale inlined code after editing an `@inline` method (correctness, all Zincs, only with recompileOnMacroDef=false)

- **Step:** `inline-method-body`: swap the two `isInstanceOf` tests in `@inline def ReceiveTimeoutCompat.isNotInfluenceReceiveTimeout`.
- **Verdict:** `bytecode` on all three: `actor/dungeon/ReceiveTimeout.class`, `actor/TimerSchedulerImpl.class` and `actor-typed/.../typed/internal/TimerSchedulerImpl.class` still contain the old inlined `instanceof` order; only `ReceiveTimeoutCompat.scala` was recompiled.
- **Why:** the bridge marks an `@inline` method as a macro when the inliner is enabled (`ExtractAPI.getModifiers`: `s.hasFlag(MACRO) || hasInline`; the `optInlinerEnabled` guard came in eb69747e4), so that its callers recompile through `APIChangeDueToMacroDefinition`. lockstep runs every cell with `recompileOnMacroDef=false`, which turns that off.
- **With recompileOnMacroDef=true** (bench Zinc, same step): 1+2 in actor plus 1 in actor-typed, 20 classes, and the callers carry the new code. The only remaining difference is a LocalVariableTable range in `TimerSchedulerImpl$`.
- **Reading:** Zinc's default handles inlining correctly; the campaign's choice of optimistic macro invalidation (made so that rz#73's fast-track wasn't credited to the other Zincs) makes inlining builds unsound in all cells. Same lesson as shapeless anomaly 1.
- **Related cost (all Zincs):** because `ReceiveTimeoutCompat` counts as macro-defining, the "macro classes depending on recompiled classes" rule recompiles it after any body edit in its dependencies, which is the second cycle in `actor-unhandled-body` and `actor-private-member` (1+1 instead of 1).

### 2. Inlining decisions depend on the batch (correctness noise, scalac optimizer)

- **Steps:** `fsm-reason-add-case`: `actor/AbstractFSM.class` differs because the incremental build inlined `new UnitPFBuilder().matchUnchecked(...)` (a Java class) and the clean build didn't. `java-nodequeue-add-method`: `Mailbox`, `BoundedNodeMessageQueue`, `DefaultSystemMessageQueue` differ the same way around `AbstractMailbox`'s `VarHandle` accessors (Java). `actorref-add-member` and `timeout-add-implicit`: `LoggingBus`, `AsyncDnsManager`, `PromiseActorRef$` and others differ only in local-variable slot numbers.
- **Why (reading):** the inliner can only inline from bytecode. In a clean mixed compile the Java classes are sources in the same run, with no bytecode, so calls into them aren't inlined; in an incremental compile they're classfiles from the previous run and they are. The slot-number differences fit the same story (inlined bodies bring their locals). `--verify`'s `java-context` check compares against a build that saw all Java as classfiles; these differ from both sides because some Java classes were sources in the round and others not.
- **Follow-up:** not a Zinc bug. Worth knowing for reproducible builds: with cross-file inlining enabled, sbt's output depends on compile history. IncBench could build its per-round reference with the round's Scala sources against all Java as classfiles to classify these as `java-context`.

### 3. Merkle wins on `ActorRef` (expected)

`actorref-add-member` (add `def zincCheck` to `abstract class ActorRef`): Merkle 1+4 sources, 36 classes vs. 1+10, 98 classes, and it verifies `signature` while the name-hashing cells pick up anomaly-2 noise from the extra classes they recompile. The one clear Merkle win outside scala/scala.

## Performance

- Merkle's `analysis` phase: 37-101 ms on the larger steps vs. 10-29 ms; 438 vs. 175 ms on the clean build. The same composition cost as in the other reports.
- A Java-only body edit (`java-receivebuilder-body`) takes 155-270 ms of Zinc and javac time with no scalac, ~65-75 ms of it writing the analysis.
