# Plan: Merkle hashing and in-bridge hashing talk

`talk.md` is a first draft. This file tracks the work behind it: the analysis notation and the tool that prints it, the scripted tests the talk relies on, the performance tests, and the demos. Facts quoted in the talk come from `PLAN-merkle-poc.md` on `claude/merkle-stable-hashes` in sbt/zinc unless noted.

## Arc

Four parts, ~40 minutes, aimed at people who know what a name hash is:

1. **What the analysis stores.** Sources, classes, inheritance and memberRef edges; a notation for the analysis file; the running example (`zinc-incrementality` §10a) as stored today; one edit, and why `B` and `C` recompile; the cost on catalyst.
2. **What we are free to change.** Zinc as traces, keys, hashes and invalidation; the four obligations of `NCompiler`; a table of what is a choice (π, keys, `hashDeps`, who computes π, the descendant policy) and what is fixed (the compiler's traces); two consequences (recompute over `affected`; a hash must be a function of the interface).
3. **Merkle hashing.** The composed hash; the running example under Merkle, side by side; inside vs across subprojects; the descendant rules as keys of the descendant's own trace; where it is more precise and where not.
4. **In-bridge hashing.** The tree built to be discarded; the obligation is about equality only, and check mode tests it; H1/H2/H3 with allocation numbers; library ancestors; the visitor design.

Then measurements so far and what is measured next.

The Lean notation is used only in Part II, as tables and one formula (`affected`), to justify that hashing and relations may change. The model's proofs are cited in the notes, not shown.

DONE:

- Outline and first draft of every slide (`talk.md`), built (`index.html`).
- `zan` highlighting and a two-column layout in `template.html`.
- Test-coverage review of the PoC's `merkle*` tests: `research/test-coverage.md`.

TODO:

- D1, then replace the hand-written listings in §3–§5 and §12.
- §15's table now cites the `merkle-precision-*` tests (done).
- Review pass for plain prose; check every Lean link with `bin/lean_refs.py`.

## The analysis notation (`zan`)

One block per source and per class. Field names follow `AnalyzedClass` and `Relations`:

| line | from |
|---|---|
| `source F` / `defines` / `products` | `stamps.sources`, `relations.classes`, `relations.srcProd` |
| `class C` / `header` | `apis.internal(C).api`: name, kind, access, modifiers, type parameters |
| `parents` | `structure.parents` of the stored (minimized) API: the linearization, as seen from `C` |
| `decls` | declarations kept in the stored API (develop: `main` methods only; PoC: a stub per declaration) |
| `api`, `extra` | `apiHash`, `extraHash` |
| `names` | `nameHashes`, one line per (name, scope); scope shown only when not `Default` |
| `inherits`, `memberRef`, `uses` | `relations.inheritance.internal`, `relations.memberRef.internal`, `relations.names` |

Hashes print as `h(…)` with the rendering they hash when known (hand-written listings), or as short symbolic ids (`#B1`) assigned by first appearance (tool output), so equal hashes get equal ids across the two analyses of a diff. Diff gutter: `~` changed hash, `+` added, `-` removed. External APIs (`apis.external`) print the same way, marked `external`, with composed hashes shown as `h_C(n)` when the PoC composes them.

### D1. A tool that prints a real analysis in this notation

A `main` in the PoC's test sources (beside `IncBench`), or a scala-cli script against the published integration jars:

```
zan <analysis-file> [--diff <other-analysis-file>] [--classes A,B,C] [--platform collapse|show]
```

- Reads with `ConsistentFileAnalysisStore` (binary or text), so it works on sbt's `target/.../inc_compile.zip` and on scripted tests' analyses.
- Prints the blocks above; `--diff` aligns two analyses by class and name and prints only changed lines.
- Collapses names that every class has from `AnyRef`/`Any` into `+N platform names` unless asked.
- The scripted harness gets a `> dumpAnalysis <file>` command, so a scripted test can write its analysis before and after an edit; the talk's listings are then the output of `merkle-member-type` on `integration/develop` and `integration/merkle`, committed under `research/listings/`.

Acceptance: the §4/§5/§12 listings regenerate from one command per side, and the platform-name count on the slides is the real one.

## Scripted tests

The coverage review is in `research/test-coverage.md`: of the 74 `merkle*` tests, five failed on develop for precision, the rest pin soundness or pass either way, and the baseline's recompiled sets were written down only in history.

DONE, on retronym/zinc `claude/merkle-precision-tests` (13014e466, on top of rz#24's head fba089141), merged into `integration/merkle` as [retronym/zinc#70](https://github.com/retronym/zinc/pull/70) and added to its manifest:

- Ten `merkle-precision-*` tests, each compiling one program as two projects, `merkle` (`descendantRules = default`) and `all` (`descendantRules = all`), and pinning both recompiled sets: `member-type`, `deep`, `remove-unused`, `uses-other`, `add-overload`, `trait-vs-class`, `protected`, `conflict`, `case-class`, `header`. All pass. The `all` side was rerun on `integration/develop` (38cb22d04): the same sets, except that develop takes a third round on the header edit (`B C`, then `X Z`; the PoC does all four in round 2).
- `merkle-precision-decls-only`, with new scripted commands `checkNameHash` / `checkNoNameHash` over the subproject's own analysis: `B` has a name hash for its own member, none for `A`'s; a library ancestor's members stay.
- Round-0 pins added to `merkle-member-type`, `merkle-trait-direct`, `merkle-subproject`, `merkle-exports-scala2-fbound`, `merkle-x-member-type`. The middle two also passed on develop before.

TODO:

- T9: run every rule test under `descendantRules=-<rule>` and `none`, and keep the table of which fail (the talk's ablation claim is checked by hand only).
- Gap 6: a cross-subproject chain with an upstream intermediate class (`lib.B` not recompiled, `app.C` not recompiled).
- Gap 8: a sealed root with an open grandchild in another file; the child-added step needs checking.
- A scripted test in check mode (`apiCheck = true`) asserting no `[api-check]` disagreements, so the equivalence claim of §17 is tested in CI.
- The four upstream tests whose expectations rz#24 changed run with `apiDebug = true` (tree path); add `apiDebug = false` variants.
- Run the `merkle-precision-*` tests under Scala 3 (`ZINC_SCRIPTED_DEFAULT_LABEL=3.x`) on the patched compiler.
- `merkle-x-trait-class-ancestor` (rz#30) needs its round-0 pin (`app/checkRecompilations 0 p.B`).
- When ready, move rz#70 into rz#24.

## Performance tests

### Configurations

| id | Zinc | bridge | notes |
|---|---|---|---|
| A | `integration/develop` | in-repo Scala 2 bridge / stock Scala 3 | today |
| A′ | `integration/merkle`, `descendantRules=all`, `bridgeHashing=false`, `libraryAncestors=members` | | today's invalidation inside the PoC build, to separate harness effects from design effects |
| B | `integration/merkle`, `bridgeHashing=false` | tree path | Merkle only |
| C | `integration/merkle` | H2 + per-run caches (default) | Merkle + in-bridge hashing |
| C′ | as C, `apiCheck=true` | | equivalence run, not timed |

For Scala 3 corpora, B and C need `integration/scala3-merkle`; A uses stock Scala 3. On 1.12.x builds (scala/scala, most of the ecosystem) the pair is `integration/develop-1.12.x` and `integration/merkle-1.12.x` through `zinc-sbt`.

### Corpora

Minimal (generated by IncBench's `Hierarchy`, parameterised):

- `tree(depth, fanout, modules, kind)`: the existing 511-class tree; vary `kind` = class / trait / mixed, and `modules` = 1 / 4, so the trait and cross-module cases are separate rows.
- `wide(n)`: one base class, `n` direct subclasses, a client per subclass: measures the per-descendant cost of the rules and of composition.
- `deep(n)`: a chain of `n` classes, a client of the leaf: measures composition depth across subprojects (the lookup composes over the whole stored linearization).
- `cake(k)`: `k` traits mixed into one class (the cake pattern): the case Merkle helps least.

Real:

| corpus | why | status |
|---|---|---|
| Spark 4.0.1 `sql/catalyst` | deep class hierarchies in one module | measured (A, B, C) |
| catalyst → `sql/core` | cross-module descendants | measured (A, B) |
| scala/scala: library, reflect, compiler | the compiler's own build; `Global`'s phase objects, `Types`, cake pattern | partly: stability bugs found (rz#69); no edit matrix yet |
| Pekko | cross-module inheritance, mostly traits (346 of 429 edges) | not yet |
| joern (Scala 3.8.3) | a base class extended across 15 frontends | measured (A, C) |
| sbt/sbt, zinc (Scala 3) | shallow hierarchies, macros: the control group | measured (A, B, C) |

### Edit kinds

Each edit kind is applied to the §2 program (minimal), to the generated corpora, and to one named class per real corpus. Expected sets for the minimal program:

| id | edit | A | B/C |
|---|---|---|---|
| E1 | ancestor body only | `A` | `A` |
| E2 | ancestor gains an unused concrete member | `A B C` | `A` |
| E3 | ancestor member's type changes, used via a descendant | `A B C X Y` | `A X Y` |
| E4 | ancestor gains an overload of a used member | descendants + clients | clients |
| E5 | ancestor loses an unused member | `A B C` | `A` |
| E6 | ancestor gains an abstract member | descendants | concrete descendants (`abstract`) |
| E7 | a parent's type argument changes | `B C X Y Z` | `B C X Y Z` |
| E8 | ancestor gains a parent | all descendants and clients | the same |
| E9 | trait member added | all descendants | direct mixers (`trait`) |
| E10 | private member changed in an ancestor | `A` | `A` |
| E11 | a library jar changes an inherited member | per today's library invalidation | classes whose linearization contains the jar |
| E12 | add a new subclass | the subclass | the subclass |

E1, E7, E8, E10 and E12 are controls: B/C must not be worse.

### Metrics

Per incremental compile:

- classes and sources recompiled, rounds; for a real corpus also the list, so a regression can be explained class by class;
- wall time of the compile, and of Zinc's own steps (`PhaseTimings`: invalidation, analysis build, store), from the `[zinc-timing]` debug line;
- `xsbt-api` time and allocation, and of `xsbt-dependency`, from `-Yprofile-enabled`;
- the invalidation log's rule reasons, counted per rule.

Per clean build:

- wall time and `xsbt-api` allocation (C must not be slower than A);
- analysis size on disk; name hashes, used names and stored definitions, counted;
- analysis load and store time, and the retained heap of the loaded analysis (heap histogram after a forced GC).

### Method

- Warm JVM: three discarded warm-up builds, then N = 5 repetitions per edit; report the median and the range. Machine otherwise idle; record the machine and JDK. The earlier ±30 MB allocation noise is the threshold for calling an allocation change real.
- Each repetition restores the pre-edit state from a saved snapshot (sources, classes, analysis), so edits are independent.
- `apiDebug` off in timed runs; the first PoC timings with it on were void.
- Every run also compares its classfiles (and TASTy, through `javap`/`tasty` printing for Scala 3) with a clean build's (`IncBench --verify`). A run that differs is reported as a correctness failure, and its timing is discarded.
- Reports: `bin/incbench-report.py` renders A/B/C side by side; publish each corpus's report as an artifact and link it from the talk's notes.

### Order

1. P1: rerun catalyst (A, B, C) with N = 5 on an idle machine, so the talk's catalyst numbers have ranges.
2. P2: the edit-kind matrix on the minimal program and the generated corpora (fast; finds regressions in the controls).
3. P3: scala/scala through `zinc-sbt` (A vs C), E2/E3/E9 on `Types`, `Symbols`, `SubComponent`, and a no-op compile (must recompile nothing).
4. P4: catalyst → core with C, and Pekko.
5. P5: analysis load/store and retained heap on scala/scala and catalyst.

## Demos

- **M1, minimal.** The §2 program in a scratch sbt project, run under `zinc-sbt` on `develop` and `merkle`: compile, `zan` the analysis, apply E3, compile, `zan --diff`, show the invalidation log (`B: no rule fired`; `X: memberRef A, name m`). Scripted as a shell transcript so it can be replayed or recorded.
- **M2, real.** catalyst E2 on `TreeNode`, recorded: 1,371 against 420 classes, with the clean-build time beside it.
- **M3, check mode.** One catalyst edit under C′: the `[api-check]` summary; then the broken-hasher build and its disagreements.
- **M4, cross-module (optional).** catalyst → core, `LogicalPlan` E2: 148 classes in core against 2.

## Open questions

1. Should Part II show one Lean listing, or only the tables?
2. Is the side-by-side layout readable on a projector, or should §12 be two cards?
3. §15 shows ten rows; is that too many for one slide, or should the minor ones (`protected`, `case-class`) move to the notes?
