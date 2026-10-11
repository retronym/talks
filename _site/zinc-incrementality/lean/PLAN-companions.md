# Phase 25 — companion pairs in a hierarchy space (`Companions.lean`)

## Question

retronym/zinc#56 fixed a bug in the Merkle PoC's Scala 2 bridge that no conformance space reached: the bridge kept the extracted classes in a map keyed by name, a class and its companion object share it, and the half extracted last replaced the other. Zinc stored an empty placeholder for the lost half, so a change to its members was no API change (unsound), and with no stored parents the `exports` rule misfired (on Spark catalyst, 821 of `TreeNode`'s descendants). No space had a class with a companion in an edited hierarchy. Which space would have caught it, and does the model predict the harness on it?

## Model

Phase 23 (`ExtraHash.lean`) models a pair as two units under one name. `Companions.lean` puts pairs in a source-file space:

- the type half: `class A(val i: Int)`, `case class A(i: Int)` or `trait A`, with `def m`, optionally `extends P` (`def p`);
- the term half: none, a case class's synthetic companion, or an explicit `object A` (`def x`, optionally `extends Q` with `def q`), written before or after the class;
- readers of each half: `UseM.u(a: A) = a.m`, `UseX.u = A.x`, `UseP`, `UseQ`, and `class D extends A { def k = m }`;
- edits: the type of `m`, `x`, `p` or `q` (Int to String), or a member added to either half (`n`, `y`).

30 programs, 135 edits. The loop is `InlineOpaque.lean`'s key loop, with the pair as one Zinc class whose keys are both halves' names. Three bridges:

- `today`: develop, both halves stored, every descendant of a changed class recompiles;
- `merkle`: the Merkle PoC since #56: both halves stored, a descendant recompiles when its compilation reads the change (descendant rules), plus where a rule fires through the merged pair (`mergedFires`: `mirror` on an object with a companion class, `exports` through the pair's merged parents, #1795, and `traitDirect` when the object half of a trait's pair changes, `ExtraHash.merged_spurious`);
- `pre56`: the PoC before #56: the half extracted first is lost (the class half for a synthetic companion or an object written after the class; the object half for an object written first). Its keys never move, `exports` misfires on `A` and `D` when `P` changes, and `traitDirect` sees no trait.

## Results

Checked by kernel `decide` (`Companions.lean`):

| check | statement |
|---|---|
| `check_today_clean` | under `today` every edit is clean |
| `check_merkle_clean` | under `merkle` every edit is clean |
| `check_merkle_subset` | `merkle` recompiles a subset of `today`, and what it recompiles without reading the change is exactly what the merged pair makes fire |
| `check_pre56_exact` | under `pre56` an edit is unclean exactly when it changes a member of the lost half that a class reads: `m` (read by `UseM`, `D`), `x` (`UseX`), or a member added to a trait (`D`'s mixin forwarders) |

This is `ExtraHash.qualified_sound` with its hypothesis failing for the lost half: a constant hash determines nothing.

Against the harness (`lake exe conformance companions today|merkle|pre56`, Scala 2.13, single layout):

| Zinc | mode | edits | incremental ≠ clean | verdicts = model | recompiled sets = model | classes recompiled |
|---|---|---|---|---|---|---|
| develop | `today` | 135 | 0 | 135 | 135 | 378 |
| Merkle PoC with #55, #56 | `merkle` | 135 | 0 | 135 | 135 | 311 |
| Merkle PoC before #56 (`cf9c3ccec`) | `pre56` | 135 | 30 | 135 | 135 | 258 |

The 30 before #56: `m` with the class half lost (case class with a synthetic companion 2, object after the class 4 per kind), `x` with the object half lost (object before the class, 4 per kind), and a member added to a trait whose class half is lost (4: `D` keeps its mixin forwarders). Every revert is clean.

Reconciliation: the first model had 26 unclean edits; the harness found 4 more, a member added to a trait whose class half is lost (`D` needs a new mixin forwarder), and the model now reads it. The recompiled sets first differed for the Merkle PoC: the `today` loop recompiles every descendant, and the merged pair makes `mirror`, `exports` and `traitDirect` fire where nothing reads the change; `merkle` and `mergedFires` account for both.

## Steps

- [x] P25.1 `Companions.lean`: the space, three bridges, kernel-checked results.
- [x] P25.2 `conformance companions [today|merkle|pre56]`, run against develop and the Merkle PoC before and after #56.
- [ ] Future: Scala 3 (dotc's bridge reports both halves); companions in the name-resolution spaces (an object member shadowing).
