# Plan: a bug hunt over the integration lines

## Goal

Find the remaining incrementality bugs, and the performance anomalies, in today's integration branches before anything more lands: the Scala lines (`integration/2.13.x`, `integration/scala3-main`, `integration/scala3-merkle`) with the Zinc lines (`integration/develop-1.12.x`, `integration/merkle-1.12.x`, and their develop counterparts), each Zinc in both `hashing=names` and `hashing=merkle`.

## Approach

- **Re-run the previous campaigns** (cats, shapeless, scala-steward, pekko, scala/scala) on today's integration heads, with `--verify`, `recompileOnMacroDef=true` (sbt's default; `false` only for the scala/scala fast-track comparison) and no `-opt` (Zinc doesn't support cross-class inlining).
- **Explore beyond the edit scripts**: edits aimed at what the Merkle rules and the composition rely on (trait parents, companions, library ancestors, implicits in ancestors' companions, header changes, nested classes, cross-module ancestors), plus the conformance harness on generated programs.
- **Triage each finding** first against the stray work: open PRs and local branches not in any manifest. A fix may already exist, unmerged. Only a finding with no fix anywhere is new; fix those directly, with a scripted test.
- **Keep the integration branches current** as fixes land: add each to its manifest and rebuild.

## Status

- DONE Survey of open PRs against the manifests. The 1.12.x line already has rz#63 (squashed into rz#48 as `9a7cfa344`), the composition cache (`9e99fb249`) and the trait extraHash fix (`f83791118`). The develop line (`integration/merkle`) has none of them.
- DONE rz#80/#81 rebased. Their own commit was already in rz#24/rz#48 (`6df63a4cb`, `238ef4921`), so they now carry only rz#77/#79's commits, which are already in the manifests. No manifest change; close them as superseded.
- DONE (running) The macro-def re-run of cats, shapeless, scala-steward and pekko (`incbench-macrodef` session).
- DONE rz#63 reviewed (no soundness bug; the `ancestorDecls` doc claims `main` declarations of internal base classes are taken, but only annotated ones are) and integrated: `integration/merkle` = ae6ac7e70, with `fixup-83-63` (its new test opts into `hashing=merkle`).
- DONE Composition cache A/B on scala-steward (`campaigns/2026-10-20-ab-cache-scala-steward`, 3 reps): no difference (`initialChanges` 4.0 vs 4.1 ms, `analysis` 110 vs 117 ms), as expected for a one-module build with nothing upstream to look up.
- DONE Composition cache A/B on cats (`2026-10-20-ab-cache-cats`, 3 reps): no difference either (`initialChanges` 13.9 vs 14.2 ms). cats's upstream lookups are cheap; the cache was motivated by scala/scala, where `compiler` looks up all of `library` and `reflect`.
- DONE (provisional) Composition cache A/B on scala/scala (`2026-10-20-ab-cache-scala`, 2 reps, `recompileOnMacroDef=false`), paired by step: `initialChanges` -19 ms, Zinc's own time -91 ms, wall -108 ms per step (of ~0.9-1.3 s). Most of the saving is inside `compile`, where the callback composes upstream classes per dependency.
- TODO Rerun every timing A/B of this plan on an idle machine. They ran alongside the macro-def campaign and each other; only the jar-index fix's 10x `analysis` drop is robust to that.
- DONE Merkle's flat ~100 ms `analysis` cost: a harness artifact, fixed (finding 1).
- DONE Port the composition cache to the develop line (`claude/merkle-develop-ports` 9edd4d729, a patch member of `zinc-merkle`). The trait extraHash fix was already there (rz#83 brought it in under `merkle`, with its three chain tests).
- TODO Re-run on today's integration heads, both hashing modes, both Scala lines.
- TODO Exploratory edits and conformance runs.

## Findings

(One entry per finding: what, where it reproduces, verdict, and the fix: stray branch, open PR, or new.)

1. **IncBench charged Merkle ~100 ms per step for reindexing jars** (new; harness, not Zinc). `Locate.entry` asks for the index of every classpath entry before the one that defines a class, on every lookup, and `IncHandler` passed the uncached `Locate.definesClass`; sbt caches jar indexes across compiles (`classpathDefinesClassCache`). Merkle looks up the jar of every library ancestor of each class it analyses, once per cycle (`libraryFingerprint`), so on scala-steward 80% of its `analysis` phase was `Locate$JarDefinesClass.<init>` (async-profiler). Fix: `IncHandler.definesClass` caches by path, mtime and size; rz#71 4cba55a47, and a patch member of `zinc-develop`. Measured on scala-steward (`2026-10-20-ab-dcc-scala-steward`, 3 reps, paired by step): `analysis` -109 ms, wall -76 ms, Merkle's Zinc-side time 141 → 39 ms (name hashing: 24 ms). Every earlier campaign's Merkle `analysis` and wall numbers carry this cost.
2. **23 pending scripted tests pass on `integration/develop` and `integration/merkle`** (bookkeeping). The pending-test PRs (#35, #42, #50-#53, #57, #59, ...) mark them pending; other members (#34, #43, #47, ...) fix them. The integration build reports them as failures ("Pending test … passed").
3. **Merkle missed library ancestors that are nested in an object or take type arguments** (new; Merkle only; undercompiles). `LibraryAncestors.ancestorNames` named parents with `Discovery.simpleName`, which gives no name for `extends L[Int]` (a `Parameterized`) nor for `extends O.L` (the bridge renders it `Projection(Projection(Projection(Singleton(This), dep), O), L)`). So when the jar changed, D recompiled but its descendant E, whose override no longer conformed, did not. Fix: name ancestors with `MerkleHashes.typeName`, which now follows a projection on a projection (and already dropped type arguments); the linearization uses it too. Develop: `merkle-nested-library-ancestors` patch member; 1.12.x: rz#48 28e41a9ac. Tests `merkle-libjar-override-nested`, `-parameterized` (fail without the fix), `merkle-x-member-type-nested` (regression only).
4. **Merkle's descendant rules missed upstream ancestors nested in objects, or reached through an object** (new; Merkle only; undercompiles). The rules read a descendant's ancestors from its stored linearization by source name (`p.O.A`) and looked them up among upstream APIs, keyed by binary name (`p.O$A`); `class C extends Inst.B` (with `object Inst extends Outer`) stores parents `p.Inst.B`, `p.Inst.A`, which no class is called. So removing an implementation from an upstream nested class left a concrete downstream descendant uncompiled. Composition's `Lookup.ownAnalyzedClass` had the same source-vs-binary lookup. Fix: `HierarchyView` resolves names through binary-name candidates, takes upstream parents from the external inheritance relation plus their stored linearizations, and `conflicts` drops the changed class under either name; `ownAnalyzedClass` tries the candidates. Develop: `merkle-upstream-nested-ancestors` patch member; 1.12.x: rz#48 ea98a1e94. Tests `merkle-x-abstract-ancestor-nested`, `-instance` (fail without), `merkle-x-abstract-nested` (regression only). Not fixed: a class downstream of C composes C's hashes from the same bogus `p.Inst.*` names, so a third subproject still misses those ancestors' contributions.
