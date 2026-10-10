# Phase 20 — constructors and synthetic case-class members (`Synthetic.lean`)

## Question

A client's `new C(…)`, `C(…)`, `c.copy(…)` or `case C(a, b)` asks for the signature of a constructor or of a member the compiler synthesised. Zinc's key for it is a used name, checked against the name hashes of the classes the client depends on; a used name does not record which class it came from. Every constructor is called `<init>`, and synthetic members have shapes that need not follow the fields they stand for. BUG-MAP's cluster C1: sbt/zinc#97 (fixed by #288), #1324, scala/scala3#12401 (fixed by #12712), #12898, #19910 / sbt/zinc#1334 (fixed by #19911), sbt/zinc#572, scala/scala3#26231's abstraction half.

## Model

A class's members (constructors, default getters, the companion's `apply`, `unapply`, `copy`) with signatures. A mangling gives each member a name, separately on the definition side (the API's name hashes) and on the use side (the client's used names). The name hash of a name is the list of members with that name and their signatures. Zinc invalidates a client that depends on `C` when a name it used has a different hash in `C`'s new API; the client needs it when the signature it used changed.

## Results (`Synthetic.lean`)

| Result | Status |
|---|---|
| `sound_of_agree`: with one mangling on both sides, a changed signature of a member the client used invalidates it | proved, every mangling, class and API |
| `under_of_disagree` (#19910: `p;C;init;` against `C;init;`), `under_12401` (unmangled API against a mangled use): a constructor parameter added invalidates nothing | witnesses, kernel `decide` |
| `over_plain` (#97): with `<init>` for every class, `C`'s constructor change invalidates a client of `B`'s constructor whose use of `C` (`copy`) did not change; #288's names do not | witness |
| `over_default` (#1324): the same through `<init>$default$1`, which #288 left unmangled; #1324's names do not | witness |
| `unapply_26231`: a field added leaves `unapply : (C): C` unchanged, so a pattern keyed on `unapply` alone misses it; keyed also on `C;init;`, it is invalidated | witness |
| `apply_572`: without the synthetic companion in the API, a change to `apply` invalidates nothing; with it, it does | witness |

Why three fixes were needed for one key: the key for a constructor is a name, the name has a definition-side spelling and a use-side spelling, and the two must agree (`sound_of_agree`'s hypothesis) and be specific to the class (the precision of #97). #288 made the use and definition sides class-specific for `<init>` in Scala 2; #1324 extended it to the default getters, a second name for the same constructor; Scala 3's bridge mangled the use side but not the API (#12401, fixed by #12712), then mangled the API with the package and the use side without (#19910, fixed by #19911). Each was one member or one side left out of a single rule: the definition and the use go through one mangling function, and every name derived from a constructor (default getters, `copy`'s defaults, the companion's `apply`) goes through it.

The disagreement cases are Phase 16's coverage failure one level down (names instead of classes); the synthetic `unapply` is abstraction (a key whose hash ignores what the client's bytecode reads); #572 is coverage (no key at all).

## The cluster's scripted tests

All pass on develop: `value-class-underlying`, `constructors-unrelated`, `constructors-unrelated-2` (#97, #1324), `default-params`, `default-arguments-separate-compilation(-210)`, `case-classes-no-companion`, `naha-synthetic`, `nested-case-class` (#572), `named`, each a regression test of one member or side brought under the mangling.

## Steps

- [x] P20.1 `Synthetic.lean`: the name-level model, the theorems, a witness per bug.
- [x] P20.2 The cluster's scripted tests mapped.
- [ ] Future: the name-level model as keys of a `TCompiler` instance (used names over classes), joining `Naming.lean`.
