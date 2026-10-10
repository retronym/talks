# Files as a layer (design note, for review)

## Problem

Zinc recompiles source files, not classes, but records keys per class. The framework has only classes: a unit is a class, a round recompiles a set of classes, and every class records its own keys. Three things Zinc does with files have no place in it:

- **Rounds are closed under files.** Invalidating one class recompiles every class of its file. The model's rounds can split a file. Today this is harmless: a policy may compile more, and `Policy.Sound` allows it. It matters once a file's classes share recorded keys.
- **Keys are charged to one class of the file.** A top-level import records its qualifier as a dependency of one class of the file: the first in Scala 2, the last in Scala 3 (`Dependency.firstClassOrModuleClass`, dotc's `responsibleForImports`). `MemberRefInvalidator` then checks the used names of that class only. F3 is exactly this: the import is charged to a class that does not use the name, and the class that does use it holds no key. `Names.lean` models it with an ad hoc `first` flag. The framework cannot say it, because coverage is per class and the import's query belongs to the file.
- **Edges inside a file.** sbt/zinc#417 is the bridge dropping inheritance edges between classes of one file. BUG-MAP's FI cluster has more. With per-class units and no files, "same file" is not a predicate the model has.

## Decision

**A file map on the general form, defaulting to one file per class.** `XCompiler` gains `file : CUnit → File`, with `file := id` (one file per class) for every existing instance, so nothing changes until an instance sets it. Two consequences follow.

1. **Rounds are closed under files.** The loop recompiles `close R = {u | ∃ v ∈ R, file u = file v}`. This is Zinc's class-to-source-to-classes step, applied in `round`. T2 and T3a are re-proved once in `General.lean`, with `close` in place of `R`. With `file := id`, `close R = R`, and every corollary is unchanged.
2. **Keys are recorded per file, through a charging function.** A unit's queries split in two:
   - its *own* queries, those of its members' bodies;
   - its *file's* queries, those of the top-level imports, which every class of the file reads.

   The bridge charges the file's queries to a representative, `charge : File → CUnit`, and checks them against that representative's used names. Coverage becomes **charged coverage**: every query a class's compilation asks is covered by a key recorded for that class, or, for a file query, by a key recorded for `charge (file u)`. A key on a charged class covers the query only if the filter of that class (its used names) admits the query's name.

**F3 becomes a framework statement.** Today's charging (first, or last, class of the file) fails charged coverage, and the witness is the F3 trace. The fix, an import charged to every class of the file (F3's `f3Keys`), or the file's used names taken as the union, meets it. Both are proved once, for any instance that sets `file`, not only for `Names.lean`'s space.

**FI becomes expressible.** A dropped same-file edge is a coverage failure whose missing key would be a same-file one: the predicate `file u = file v` is now available, so the witness can be stated.

## What changes

- `General.lean`: `file`, `close`; `round` compiles `close R`; T2, T3a and T5 re-proved with `close`; `ChargedCoverage` as an alternative coverage obligation, implied by plain coverage when `charge` is the identity.
- The lifts: every variant sets `file := id`. No instance file changes.
- `SplitProof.Spec` (names): the client file's classes (client, `First`/`Last`) become units of one file, and the wildcard import becomes a file query charged per version. F3's witness and fix move from the `wildOther` flag to the framework's charging. The flag stays, as the abstraction, `Split.check_abstract`-style.
- PLAN-names and the status table: F3 is listed as a failure of charged coverage.

## Rejected

- **Files as units** (`CUnit := File`). It loses per-class keys, so Zinc's name filter per class, and with it F3's cause, could not be stated. It also changes every instance.
- **Charging inside each instance**, as `Names.lean` does with `first`. It is what we have, and it is why F3 is not a framework statement.

## Steps

1. This note, for review.
2. `General.lean`: `file`, `close`, T2/T3a/T5 with closed rounds; the lifts set `file := id`; the axioms check covers the new statements.
3. `ChargedCoverage`, with `charged_of_coverage`; the F3 witness and fix on `SplitProof.Spec` with a two-class client file.
4. FI: one witness for sbt/zinc#417 (an inheritance edge between classes of one file, dropped).
