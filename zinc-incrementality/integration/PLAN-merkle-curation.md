# Curating the Merkle PoC branches

## Problem

The Merkle PoC is spread over two lines that were meant to be the same series and have drifted.

- **develop:** rz#24 (`claude/merkle-hash-poc-path-ec0cd8`) is 127 commits on develop, including eleven merges of sub-PRs (#25, #29, #31, #38, #39, #41, #55, #56, #61, #69, #72, #78), about 20 "record … in the plan" commits, and benchmark and conformance tooling. Two draft PRs are stacked on it (rz#30, rz#63), and integration/merkle adds ten patch members on top: the composition cache and the eight bug-hunt fixes from 2026-10-20, plus a Scala 3 test.
- **1.12.x:** rz#48 (`backport/1.12.x-merkle-hash-poc`) is 31 commits. It started as one squashed `[1.x]` commit per upstream unit, but it now also carries a CI fix, two "move X into rz#71" commits, an audit doc, a stray test commit and the seven bug-hunt fixes as separate commits.
- **The lines differ in what the series contains.** The harness (IncBench, the benchmark generator, HashCost, `bin/incbench-report.py`, the scripted local-Scala labels) left rz#48 for rz#71 but is still inside rz#24. rz#30 and rz#63 are separate PRs on develop but squashed units on 1.12.x. The composition cache is a unit on 1.12.x and a patch on develop.

A reviewer, or anyone porting a fix, can't line up the two lines unit by unit, and a fix to one rule has to be found in a different place on each line.

## Goal

The two lines carry the same short list of units, in the same order and under the same titles (1.12.x prefixed `[1.x]`). Each unit is one commit, or a few, that compiles and passes its own tests. Each bug-hunt fix is folded into the unit whose rule it corrects. Everything that isn't Merkle leaves the series for its own PR, on both lines. The integration branches rebuild to the same trees with shorter manifests.

## Proposed units

1.12.x keeps its prerequisites in front of these, unchanged: the pipelining backports (#1817, #1818, #1822) and #1765.

1. **Hashing mode.** `incOptions` `hashing=names|merkle`, the `AnalysisCallback5`/`ClassHashes` interface, and `MERKLE-HASHING-MODE.md`. With `names`, nothing changes. Today this is the last commit on both lines (rz#83); see decision 1.
2. **Composed hashes.** Stored APIs omit inherited members; `MerkleHashes` composes them for other subprojects. This unit also takes: hashes stable across JVM runs (#69), reuse of composed classes from an unchanged upstream analysis (the cache), and a trait's extraHash covering only its own members.
3. **Descendant rules.** `DescendantRules`/`HierarchyView` (abstract, conflicts, header, trait, traitDirect, mirror, annotated, exports), and the rules reading upstream ancestors' APIs. Folded in:
   - rz#30's traitDirect fix;
   - static annotations (#61) and the overridden-annotation test;
   - the anonymous subclass in a trait's companion (#78);
   - from the bug hunt: upstream nested ancestors, composition through an object, mirror for nested ancestors, and the header rule's Scala 3 constructor names.
4. **Library ancestors.** The coarse treatment: stubbed members, jar stamps folded into descendants. Folded in: a nested class of this subproject is not a library ancestor (#72), and from the bug hunt, nested and parameterized ancestor names, Scala 3 `p.O$.A` names, and own output not being a library.
5. **Bridge-side hashing (H2).** The Scala 2 bridge hashes from symbols and types, with its caches and allocation cuts. Folded in: companion hashing (#56), value-class erasure, type-parameter naming (#79/#81), and ancestors' declarations without override checks with one-pass composition (rz#63).
6. **Merkle name invalidation (#41).** Added classes, package-object members and implicits, composing inherited members, with its pending tests. See decision 2.
7. **Design doc.** One document: why, the rules and the decisions. It replaces `PLAN-merkle-poc.md`, `CATALYST-DIFFERENTIAL.md`, `MERKLE-SPARK-CROSSMODULE.md` and the audit doc. Measurement logs move to talks, next to the campaign records.

## Out of the series, as their own PRs on both lines

- **IncBench and its tools** go to rz#71, and develop gets a port of rz#71: IncBench, the benchmark generator, HashCost, SyntheticCorpus, Hierarchy, `bin/incbench-report.py`, `bin/catalyst-edits.py`, `--inv-log` from rz#30, the 2.13.local and Scala 3 local scripted labels, and TASTy as auxiliary class files in scripted. Today develop gets IncBench only through rz#24, so every develop Zinc the campaign compares carries the PoC's harness version.
- **Conformance harness** (`Conformance`, `ConformanceOrder`, `bin/conformance-spaces.py`). It found stock name-hashing bugs too (the classOf literal used-name bug and the Java sealed-permits bug, both on develop), so it isn't Merkle-specific.
- **General fixes found along the way:**
  - with pipelining, write early output only on a cycle's last pass (fae4ce759);
  - with pipelining, record Java's dependencies on its own subproject's classes as internal (#55);
  - per-phase wall time (rz#71 has it on 1.12.x);
  - the bridge allocation fixes in used names, the non-local class lookup and the macro-attachment scan.

  Each is checked against what develop and 1.12.x already have before it gets a PR.

## Invariants (how we know it's coherent)

- **Same trees:** after curation, the tip of each series plus the PRs that left it gives the old tip's tree. integration/merkle and integration/merkle-1.12.x rebuilt from the new manifests are byte-identical to today's (6d9ea48c9-based f8e9d1d9f and 16c00317b), apart from the moved doc files.
- **Lines match unit by unit:** `git range-diff` between the two series pairs every unit. Differences are limited to Scala 2 vs Scala 3 syntax and code that differs between develop and 1.12.x.
- **Every unit is green:** each unit's commit compiles, and the scripted tests it introduces pass at that commit, on both lines.
- **Nothing lost:** the old tips are tagged `archive/merkle-poc-develop-<date>` and `archive/merkle-poc-1.12.x-<date>` before any force-push. Folded PRs (rz#30, rz#63, rz#80, rz#81) are closed with a pointer to the unit that now holds them.

## Approach

Use the 1.12.x series as the template: it is already mostly one commit per unit. First write a mapping of every develop commit and patch member to a unit, or to "leaves" or "drop" (plan-only commits). Linearize rz#24 by cherry-picking its non-merge commits, then reorder and squash by that mapping, resolving conflicts with rerere. Do the same on 1.12.x for its 13 commits after the PoC unit. Then check the invariants, simplify the two manifests (zinc-merkle drops its ten patch members and rz#30/#63), and rebuild both integration branches with `--dry-run` before `--push`.

The git work is light. Builds and per-unit test runs are heavy, so they wait until the bughunt3 campaign has finished; its cells use the merkle-1.12.x checkout at 16c00317b.

## Decisions for Jason

1. **Hashing mode first or last.** Making it unit 1 means every later unit lands gated and stock-safe, which a reviewer can follow, but reordering it conflicts with every unit. Keeping it last is mechanical, but until that commit every unit changes stock behaviour. Recommendation: first.
2. **#41 on develop.** Its name-resolution invalidation overlaps rz#34/#47 on the develop line, and integration/merkle resolves that overlap in Merkle's favour. Options: keep #41 whole as unit 6, or reduce it to the Merkle-specific part (composing inherited members into the package scope) and leave the general mechanism to rz#34/#47. Recommendation: reduce it, if the reduced version passes #41's tests.
3. **Granularity.** One commit per unit, or a unit as a short series (for example, the descendant rules as one commit per rule). Recommendation: one commit per unit, except descendant rules and H2, as short series.
4. **Harness and conformance out of the series** (above). Recommendation: yes; it is what made the lines drift.

## Out of scope

- integration/scala3-merkle (the Scala 3 bridge-side hashing, in scala/scala3).
- The experimental branches `claude-merkle-inherited-per-base` and `claude-merkle-members-walk`, which stay as they are.
