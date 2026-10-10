# Phase 15 — inferred types in a cycle: T3a holds, T3 fails (`Cycles.lean`)

## Question

`Uniqueness.lean` proves a per-unit fixed point equals the clean build under acyclic traced dependencies (`fixpoint_unique_of_wf`) or source-determined interfaces (`fixpoint_unique_of_explicit`). Scala members whose result types are inferred from each other satisfy neither. Is there an edit where Zinc's keys are sound (the obligations hold, so the loop stops in a per-unit fixed point, T3a) and the result still differs from the clean build? And can any key fix it?

## Probed (scalac 2.13.16, 3.3.6, by scala-cli)

`object A { def x = B.y }`, `object B { def y = A.x }` compiled together: "recursive method x needs result type" (Scala 3: cyclic error). `A` recompiled alone against `B.class` (from `A.x: Int = B.y`): compiles, `x: Int`. From `A.x: Long = B.y`, changing `A` to `def x: Int = B.y` and compiling it alone against `B.class` (`B.y: Long`): type mismatch; compiled together: fine, `B.y` infers `Int`.

## Model

Units `a`, `b`; a unit's interface is its member's type (`none`: an error). `ann t r` is `def x: t = r.y`, checked against `r.y`'s type with Scala's numeric widening; `inf r` is `def x = r.y`. Joint compilation follows the reads inside the round and gives a cycle of inferred members no type (scalac's cyclic error); an annotation on the cycle fixes the rest. Keys: a member-ref key to the class read; hash = the type.

## Results

| Result | Status |
|---|---|
| `obligations`: the compiler meets comp, coverage, abstraction (on any source type, including the annotated subtype) | proved, every program |
| `zinc_stops_at_old`, `clean_fails`, `zinc_ne_clean`: from the clean build of `A.x: Int = B.y`, `B.y = A.x`, removing the annotation, Zinc's loop recompiles `A`, stops with both `Int`; the clean build has both in error | proved, kernel `decide` |
| `two_fixpoints`: both outcomes are per-unit fixed points of the edited sources | proved |
| `annotated_eq_clean`: with every member annotated, Zinc's result is the clean build, every program, edit and sound policy (T3 via `zinc_eq_clean_of_explicit`) | proved |
| C1, C2 on Zinc's real loop (next round = invalidated ∪ API-changed, abort on an error) | checked (`example`s) and on the harness |

Families, on Zinc `develop` (the harness agrees with the model on all 36 edits, Scala 2.13 and 3, verdicts and recompiled classes):

* **C1, an annotation removed in a cycle**: `A.x: Int = B.y` → `A.x = B.y` with `B.y = A.x`. Incremental: `A` alone, `x: Int`, no API change, done. Clean: cyclic error. Missed error (4 of 36 edits).
* **C2, an annotation changed in a cycle**: `A.x: Long = B.y` → `A.x: Int = B.y` with `B.y = A.x`. Incremental: `A` alone against `B.y: Long`, type mismatch. Clean: `B.y` infers `Int`, fine. Spurious error (2 of 36; the reverts of `Int` → `Long` hit it again).

Nothing is stale in either: the incremental state is a per-unit fixed point; it is the other one.

## Policies

* **No key fixes this.** The obligations hold; what differs is which fixed point, and that is decided by what is compiled jointly. The remedies are joint recompilation of the cycle, or annotations (`annotated_eq_clean`).
* sbt/zinc#1284 (merged 2023, reverted by #1462): in the first round, add every unit with member-ref edges both to and from a changed unit. Clean on this space (`Mode.mutual`), but it fires on every edit inside a 2-cycle, a comment included (#1462: "invalidating everything based on whitespace"), and misses longer cycles.
* The precise rule (`Mode.precise`): add the cycle through a changed unit only when the edit changes whether, or how, a member's type is written. Clean on this space with 36 unit recompilations against #1284's 48 (the body-only edits). For longer cycles it needs the strongly connected component of the member-ref graph, which Zinc can compute from its relations; it fires only on annotation edits inside a cycle, which are rare.
* sbt/zinc#1780 (open; retry the first round with "bridging" classes, the forward ∩ backward closure of the changed classes, when it fails; `Mode.retry`): clean on C2 (the round-1 type mismatch triggers a joint retry), not on C1 (round 1 compiles, at the wrong fixed point, so nothing triggers). Run against #1780's branch: the scripted tests `inferred-type-cycle-annotation-changed{,-scala3}` pass, `inferred-type-cycle-annotation-removed{,-scala3}` still fail. On the space: 4 of 36 edits unclean (every C1), 36 unit compilations (failed round included).

| Rule | Unclean edits (of 36) | Unit compilations |
|---|---|---|
| Zinc today | 6 (C1 4, C2 2) | 30, plus the failed rounds |
| #1284 (mutual dependents, first round) | 0 | 48 |
| precise (cycle on a written-type edit) | 0 | 36 |
| #1780 (retry with bridging classes on a first-round error) | 4 (C1) | 36 |

So #1780 reaches the precise rule's cost but catches only the cases that fail: a cycle whose wrong fixed point compiles without error (C1) needs a trigger before or after a *successful* round, which only a written-type signal gives: a per-member "result type inferred" bit in the API (Scala 2 bridge in Zinc, dotty's bridge for Scala 3), compared across runs.
* `transitiveStep`'s brute-force round recompiles everything after `transitiveStep` rounds; it does not apply here, since C1 stops after one round and C2 aborts in the first.

## Harness

`lake exe jconformance cycles [mutual|precise]` dumps 6 bases (every pair of annotated/inferred members that compiles) with their 36 single edits (another annotation, or a body-only edit). Run once on develop, Scala 2.13 and 3, one JVM.

## Steps

- [x] P15.1 Probes (scalac 2.13, 3).
- [x] P15.2 `Cycles.lean`: the instance, obligations, the witness, two fixed points, T3 with annotations.
- [x] P15.3 The space and Zinc's real loop; modes today, #1284, precise; harness run on develop.
- [x] P15.4 sbt/zinc#1780's retry in the model (`Mode.retry`) and against C1/C2 (pending scripted tests on retronym/zinc).
- [ ] Future: the precise rule in Zinc (SCC of the member-ref relation, triggered by a change of a member's written type), with C1 and C2 as scripted tests; vals (initialisation order is a runtime matter, compile behaviour is the same).
