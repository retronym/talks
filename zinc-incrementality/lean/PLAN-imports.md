# Phase 26 — import selectors and Scala 3.7's given prioritisation (`SplitProof.Spec`, `SpecGivens`)

## Questions

1. Import selectors that rename or hide (`import a.X.{Foo => Bar}`, `import a.X.{Foo => _, _}`, Scala 3's `as`) and given selectors (`import a.X.{given, *}`). Which queries does the lookup ask under a rename or a hiding, what does each bridge record, and does an edit escape the keys: a hidden name un-hidden, a renamed target added or removed?
2. Scala 3.7 changed given prioritisation: at one nesting level, the most general instance now wins where the most specific did. Does that change what implicit search reads, or only what it selects, and does Zinc's key see an edit to a given's type?

## Probes

`scala-cli` on Scala 3.9.0 and 2.13.16 (probe sources in the session's scratchpad; `RESOLVED` is what the program printed). `X` has `Foo` and `Baz`, `Y` has `Foo` and `Bar`, `a.Foo` is a class of the client's package in another file.

| # | Client | 2.13.16 | 3.9.0 |
|---|---|---|---|
| p1 | `import a.X.{Nope => Bar}` | error: `Nope is not a member of a.X` | error (E008, not found) |
| p2 | `import a.X.{Nope => _, _}` | error: not a member | error (E008) |
| p3 | `import a.X.{Foo => Bar}`, `a.Bar` in another file; `Bar` | `X.Foo` | `X.Foo` |
| p4 | `import a.X.{Foo => Bar, _}`; `Foo` | `a.Foo` (renamed away from the wildcard) | `a.Foo` |
| p5 | `import a.X.{Foo => _, _}; import a.Y._`; `Foo` | `Y.Foo` (no ambiguity) | `Y.Foo` |
| p6 | `import a.X.{Foo => Bar}; import a.Y._` (`Y.Bar`); `Bar` | `X.Foo` (explicit beats wildcard) | `X.Foo` |
| p7 | `import a.X.{Baz => Foo, _}` (`X.Foo` exists); `Foo` | `X.Baz` | `X.Baz` |
| p8 | `package a; package b; import a.X.{Foo => _, _}`; `Foo` | `a.Foo` | `a.Foo` |

Givens: `trait A`, `class B extends A`; `summon[A]` (`implicitly[A]` in 2.13).

| # | Instances | 3.9.0 | 3.9.0 `-source:3.6` | 3.9.0 `-source:3.7-migration` | 2.13.16 |
|---|---|---|---|---|---|
| g1 | `X { given A; given B }`, `import X.given` | `A` | `B` | `A` (warning E205: "Given search preference … has changed") | `B` |
| g2 | `X { given A }`, `Y { given B }`, both imported | `A` | `B` | `A` | `B` |
| g3 | g1, `summon[B]` | `B` | `B` | `B` | — |
| g4 | `given B`, `given C` (both `<: A`, unrelated) | ambiguous | ambiguous | ambiguous | — |
| g5 | `import X.given` (`A`) and a top-level `given B` in the client's package `a.b` | `A` (one level) | `B` | `A` | — |

## What the bridges record

* Scala 2 (`Dependency.scala`, `Import` case): for every selector but the wildcard, a member-ref dependency on the imported member (term and type) when it exists, charged with top-level imports to the file's first class; `ExtractUsedNames` adds the selector's name and its rename (not `_`) to the used names of that class (the first class for a top-level import).
* Scala 3 (`ExtractDependencies.recordTree`, 3.9.0): the same for every selector that is not a wildcard, `isWildcard` being `*` or a `given` selector (`isGiven ⇒ isWildcard`); the rename is a used raw name. The qualifier is traversed, so it has a member-ref edge either way (an object; a package records nothing).

## Answers (prediction)

1. **Selectors are covered today.** A renaming or hiding selector asks the qualifier for the original name, and both compilers require it to exist (p1, p2): the query is in the trace whether or not the name is used. Both bridges record that very member with its name, for the class charged with the import, which is invalidated when the member changes and takes the client's file with it: the selector's scope is pinned (and required). The other scopes are asked for the new name, as for any name. So the predicted failures do not happen: a renamed target removed breaks the import, which is keyed; a renamed target added is impossible without the import already failing; a hidden name is un-hidden only by editing the client's own file; a member added under the new name beside a rename does not change resolution (p7, p6). Selectors add no family; F1–F3 apply to the remaining scopes unchanged.
2. **3.7 changes selection, not the trace.** Scala 3 asks every scope of the decisive level to detect an ambiguity; the rule only chooses among the level's hits (g1, g2, g5), so the obligations of every design are the same under both rules. What moves is which edits change resolution: under 3.7 adding a more general instance at the client's level, or editing an instance's type to be more general, changes the choice; before, a more specific one did. Zinc's key for an instance is its implicit name hash, which includes its type, on its container: an edit of the type is seen exactly where the container is keyed (an import qualifier, a parent, the companion, the resolved container). In a package-level container (G1, G2) neither the old nor the new rule's edits are seen.

## Model

* `Spec`, imports: the client's compilation first asks its selector checks (`chk`, scopes asked for existence, as JavaSpec's import checks), then searches. A check is pinned when the bridge records the selector (both do). `selCompiler`; coverage of the checks by pinned keys; the obligations for `cross` and `searched` with checks; the witness that an unrecorded selector would fail coverage.
* `SpecGivens`, prioritisation: `Prio` (`general`, Scala 3.7+; `specific`, Scala 3 before 3.7 and Scala 2), a preorder on instance types per scope, `gselect` choosing among the decisive level's hits; today's keys read the selected scope. A type edit is two scopes of one container flipping. Theorems: the trace does not depend on the rule; the obligations of the G rule hold under both; witnesses by kernel `decide` that the rules select differently (g1) and that under `general` a more general instance added to a package-level container changes the choice while today's keys do not move (and under `specific` it does not change the choice).

## Proved, for every program of the slot language (no `native_decide`)

* `Spec.sel_check_covered`: with selector checks, a pinned check (a selector the bridge records, as both do) is covered by today's keys (and #34's, the cross-subproject key's); `Spec.sel_cross_obligations`: the cross-subproject key meets the obligations with any checks.
* `Spec.hide_unrecorded_not_obligations` (kernel `decide` on the trace): a hiding selector whose check no key covers, in a client resolving `a.Foo`, fails coverage under #34's key; it is the case neither bridge leaves open.
* `SpecGivens.gP_rule_obligations`, `gP_global_obligations`, `gP_searched_obligations`: the G rule (global, or narrowed with recorded package imports) and `searched` meet the obligations under either prioritisation rule, with today's keys reading the scope the rule picks.
* `SpecGivens.prio_differs` (g1), `general_added_stale`, `type_widened_stale` (kernel `decide`, on the search's own output): under 3.7+ a more general instance added to a package object, or a package object's instance retyped to a more general type, moves the choice while no key today's bridge recorded moves; under the old rule the first edit does not move it.

## Checked, on a bounded space

* `SpecGivens`, an `example` (`native_decide`): over every pair of environments of the three-scope witness and both rules, when no key of the global G rule moves, the choice does not.
* The precedence facts (p3–p8, g1–g5) are probes, not theorems: the slot language takes the search order as given; `Names.lean`/`Givens.lean` and their harness runs check the order for the scopes they model, not selectors.

Not modelled: a selector's rename in the scopes searched for the new name is any scope of the slot language; which scopes a selector adds to the search order (p6, p7) is taken from the probes.

## Pending tests (predicted, not run)

* `added-general-given-package-object-scala3`: the client in `package a.b` imports `a.X.given` (`given B`); `package object b` gains `given A` (`B <: A`). Scala 3.7+ picks `A`; Zinc recompiles the package object only; the client keeps `B` (behavioural: print the choice). Under `-source:3.6` the choice stays `B`. (`general_added_stale`.)
* `given-type-widened-package-object-scala3`: as above, with `package object b`'s `given g: C` (`C <: B`) retyped to `given g: A`: the choice moves from `B` to `A` under 3.7+, and Zinc keeps `B`. (`type_widened_stale`.)

Both are G1 (an instance in a package object, reached through no edge) under a new trigger; retronym/zinc#47's G rule covers them.

## Steps

- [x] P26.1 Probes and bridge reading (above).
- [x] P26.2 `Spec`: selector checks, coverage, obligations, witness.
- [x] P26.3 `SpecGivens`: `Prio`, `best`, today's keys on the picked scope, obligations under both rules, witnesses, a bounded check.
- [x] P26.4 Proved vs checked; PLAN.md pointer.
