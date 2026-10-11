# The model as a specification: obligations on the compiler and on Zinc

## Problem

`Model.lean` already states what Zinc needs from a compiler. A `Compiler` is a per-unit task that queries an oracle (`unit`), a bridge that abstracts the task's query trace into recorded keys (`keys`), a hash per key (`π`), and a covering relation between queries and keys (`covers`). Three `Obligations` on it (compositionality, coverage, abstraction) and one on the invalidation policy (`Policy.Sound`) give T3a: the incremental loop stops in the clean build's state. Phases 2 and 6 instantiate this (`Hier.lean`'s `D`, `W`, `Mk` compilers, each with an `_obligations` proof). Start reading there: `Model.lean`'s `Compiler` is the specification's first page. Its variants (keys from the output, non-local hashes and answers, upstream subprojects) all lift into the general form `XCompiler` (`General.lean`, `PLAN-framework.md`), where the theorems are proved once.

Phases 7 to 11 did not. `Names.lean`, `Givens.lean`, `InlineOpaque.lean`, `Split.lean` each define a standalone `verdict` and check it by `native_decide` over a bounded enumeration (at most two bindings, single edits). They say nothing about what the bridge must record, prove nothing beyond the enumerated bases, and cannot compose with the framework's external-invalidation results (`Classpath.lean`). The enumerations found real bugs, but as a method they are a test generator with a verdict oracle, not a specification.

## Decisions

**Every observable is a query, and the unit task is the compiler's own algorithm.** Name resolution asks `bound (scope, name)` for each scope in search order and stops at the first hit; implicit search asks `instances (scope, type)` per nesting level; inlining asks `inlineBody sym`, `constant path`, `aliasRhs T`; erasure asks `erasure T`. The task's trace is the ground truth of what a compilation read, misses included. The families are then facts about traces: F1 is the query `bound (inner, Foo)` answered "no" and later "yes".

**A bridge design is a `keys` function and a `π`.** Today's bridge records a member-ref edge to the owner of the symbol a reference resolved to, the used name, and import qualifiers (objects only). Each family is a coverage violation: a theorem exhibiting a trace with a query no key covers. `names_today_violates_coverage : ¬ C_today.Obligations` with the F1 trace as witness, and the same for F2, F3, G1, G2, the upstream F1, I1 to I3, O1. This replaces "unclean under `today`" on an enumeration.

**A fix is a key, with a proof of the three obligations.** Two shapes:

- *Bridge-side, precise.* `searched`: a key per scope queried, hit or miss; this is what Kotlin's `LookupTracker` records (name, scope) for exactly this reason. Recording package wildcard imports is the same shape for one scope kind.
- *Zinc-side, coarse.* retronym/zinc#34 is the key `anyTopLevelNamed Foo`, whose hash is the set of top-level classes with that simple name over the project, and which covers every `bound (s, Foo)` for a top-level scope `s`. Abstraction holds because adding a class changes that set. Coverage holds for in-project scopes only; the upstream case fails because the hash is computed over one project's analysis, which is the split-layout finding stated as a failed obligation rather than a failed run.

Both prove `Obligations` and inherit T3a and the `Classpath` results. The narrowed rules (package, nested packages, importers) are keys whose `covers` is smaller; their soundness depends on the recorded-import key being present, which is now a hypothesis in the theorem, not a remark.

**Precision is a theorem next to soundness.** For a key, the queries it covers beyond the ones traced are its over-approximation; per edit, the units whose keys changed minus the units whose traced answers changed is the over-invalidation. The user's constraint, correctness without invalidating the world, is this number. The coarse key's precision loss is visible in its `covers`, and the enumerated spaces give its magnitude.

**Enumeration is for testing, and is labelled as such.** Two uses remain: checking the instance against the real compiler (the harness probes show what scalac resolved; `resolve` must agree), and checking an obligation on a bounded space before proving it. These are `example`s or `check_` definitions, never `theorem`.

**Zinc's rules are obligations on Zinc, stated as keys.** A Zinc PR that adds an invalidation rule states its key, `π`, `covers`, and which obligation each part discharges. `invalidated` in the framework already is "units with a changed key"; a rule that cannot be written as a key is suspect.

## Supporting changes

- `Names.lean`, `Givens.lean`, `InlineOpaque.lean`, `Split.lean`, `JavaNames.lean`: a `Compiler` instance each (the search algorithm as the task, the bridge as `keys`), the violation theorems for today's bridge, and `Obligations` proofs for the fixes. The existing enumerations stay as checks of the instance against the compiler.
- `Model.lean`: whatever generalisation the instances need. Likely: a key whose hash is computed over a set of units (the coarse key), so that the upstream failure is expressible; and `covers` as a relation that may depend on the unit, for package-relative keys.
- `PLAN.md` and the phase files: a "proved generally / checked on a space" column per result.
- Zinc PR descriptions (retronym/zinc#34 and the rule PRs): the key, hash and covering of each rule.

## Prior art

Build systems à la carte (Mokhov, Mitchell, Peyton Jones): a build task as a monadic computation whose trace is its dependencies, which is `Task` here. Kotlin's incremental JPS compilation: a `LookupTracker` records every name lookup per scope, misses included, and invalidation is by lookup, not by resolved symbol. Zinc's own `ExtractUsedNames` records the name but not the scope, which is the gap the families fall through.
