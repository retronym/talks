# Phase 13 — name resolution across subprojects (`Split.lean`, the `split` layout)

## Question

Phase 10 put the client and every binding in one subproject. In a real build the binding is as often upstream: a class of an inner package, a package object member, a wildcard-imported object or a top-level given in a library subproject, the client downstream. Zinc then never sees the edit as a changed source of the client's subproject. The downstream run learns of it only through its external dependencies: `detectInitialChanges` compares, for each upstream class in `apis.allExternals` (the classes the downstream recorded an edge to), the stored `AnalyzedClass` with the upstream analysis's (a missing one is `emptyAnalyzedClass`), behind the `apiHash` gate (`hashesMatch`), and `invalidateClassesExternally` applies the same name-hash and inheritance rules as inside a subproject. Do F1–F6 and G1–G3 change across the boundary? And retronym/zinc#34's `invalidateByAddedClasses` reads the classes a cycle of the *current* subproject added: does F1 come back when the added class is upstream?

## Prediction

* The external path reproduces the internal one in this space. Each edge the client's file records to a binding (the block import's `V`, the inherited `P`, the explicit import's `X` and its selector, the wildcard import's `W` charged to one class, the resolved class or package object) becomes an external edge to the same class, and the upstream class's name hashes include its own simple name, so a deleted or renamed class reaches the users of its name, as a deleted source does inside a subproject. An added upstream class is in no one's `allExternals`, as an added source has no dependents. So F1, F2, F3 and G1, G2 keep their counts on develop.
* F4 (Scala 2's stale mirror) and F5 (Scala 3's missed clash) are between two upstream files: unchanged.
* F6 and G3 vanish: the client is compiled apart from `P` in the clean build too (it reads `P` from the upstream's TASTy), so both builds omit the `P.$init$` call. The underlying dotc bug stays; across subprojects it is simply the normal case.
* #34 fixes F1 only inside a subproject: the downstream's cycles add no class, and the upstream's added class has no users there. So under #34 F1 is back in the split layout with develop's count.

## Model

Two files, separate from `Names.lean` and `Givens.lean`.

`SplitProof.lean` (proofs, no enumeration). The slot language: a client looks a name up in scopes `0 … n-1`, any number, in any search order; each scope binds or not, and is pinned (Zinc records an edge to it from a class that uses the name: inherited `P`, block import `V`, explicit import `X`, a wildcard import charged to a user of the name), required (explicit import selector), top-level (a class file) and upstream or not. Resolution is the first binding scope unless an ambiguity applies; ambiguities need two bindings, so they are monotone. An edit changes any set of bindings. Rules: `today` (a changed scope with an edge: pinned, or the resolved one; inside a subproject or, through `allExternals`, across), `cheap` (#34: also an added top-level class in the client's own subproject), `proposed` (also any unpinned scope that gained a binding, in any subproject: an added top-level class anywhere on the classpath, a member added to a package object).

`Split.lean` (the concrete space, as in Phase 10): `Layout` (`single`, or `split` with every binding upstream and the client's file downstream), Zinc's external rule on its own terms (the client file's edges as charged class, target slot, inheritance), modes `today`, `cheap`, `upstream` (#34 across subprojects, classes only) and `names` (the proposal), the trait initialiser only in `single`. `lake exe conformance names|givens 2|3 [cheap|upstream|proposed] split` dumps the verdicts with each file's tier.

### Proved, for every program of the slot language

* `proposed_sound`: under the proposal, for every client that compiles and every edit, the client is invalidated or it still compiles and resolves to the same scope.
* `cheap_sound_of_local`: #34 has the same guarantee exactly when every unpinned scope is a top-level class of the client's own subproject.
* Counterexamples, two scopes each, by evaluation (`decide`): `today_misses_added_class` (F1, either side), `cheap_misses_upstream_class` (#34 across subprojects), `cheap_misses_package_object` (F2, either side); `cheap_catches_local_class`, `proposed_catches`.
* The specification (`SplitProof.Spec`), per `DESIGN-spec.md`: an `NCompiler` over the client and `n` scopes with any flags, units split into `Up` and `S` as in `Classpath.lean`; the client's task asks `bound i` per scope and stops at the first hit. Designs are keys:
  * `today` (an existence key on the scope the lookup stopped at and on pinned scopes) fails coverage on the upstream miss `bound a.b.Foo` (`today_not_obligations`);
  * `cheap`, #34 as the key `named false` whose `covers` claims every top-level scope and whose hash reads the top-level scopes of `S` only, fails abstraction across subprojects: equal hash before and after the upstream adds `a.b.Foo`, different answer (`cheap_not_abstraction`, `cheap_not_obligations`, the trace of `added-class-upstream`); it meets the obligations within one subproject (`cheap_obligations_of_local`: every scope pinned or a top-level class, every top-level class in `S`);
  * `cross`, the same key with its hash over every scope of `Up ∪ S`, meets the obligations (`cross_obligations`), and so inherits T5 (`cross_downstream_sound`, via `NCompiler.downstream_sound`); `searched` (a key per scope asked, Kotlin's `LookupTracker`) too (`searched_obligations`).
* Precision: `cross` hashes every binding of the name, so it also fires on a deletion in a scope the lookup never reached; `proposed_sound` shows additions (and the resolved scope's key) are enough, so that is its over-invalidation.

None of these use `native_decide` (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`).

### Checked, on the enumerated bases (`check_*`, `native_decide`)

* `check_abstract`: the concrete model is an instance of the slot language: resolution is the first binding slot in the version's search order, and `today` and #34 are the slot language's rules (the concrete proposal also fires on a binding added outside the client's scopes, the safe direction).
* `check_ext_eq_internal`: the external rule on the client file's edges equals Phase 10's internal `invalidates`.
* `check_split_cheap_is_today`, `check_upstream_added_clean`, `check_names_clean`: #34 changes nothing across subprojects; extended to classes it removes F1; the proposal leaves only the divergences beside resolution (F4, F5).
* `check_single_is_names`, `check_givens_single_is_givens`: the `single` layout is Phase 10's model.

Not proved: that the concrete Names/Givens rules (Scala 2's and 3's ambiguities, the package object searched before the package's classes) are an instance of the slot language for every program, only for the bases; the givens space's rules (instances by type, no name) are not in the slot language.

## Harness

retronym/zinc#36's `Conformance` already has a `split` layout (`macros`, `up`, `down`) and places a file by its base's `tiers`, falling back to the flat space's names. Source-file bases need every file an edit can create in `tiers` (an added `Inner.scala` must go upstream), which the dump supplies; run with `--layouts split`.

## Results

Harness runs (retronym/zinc#36's `Conformance` with `--layouts split`), the same base selections as Phase 10 (names 2.13 narrowed to 286 bases). Model and harness agree on every case; resolution agrees with the compiler on every case.

| Space | Cases | split, develop | single, develop (Phase 10) | single, #34, same cases |
|---|---|---|---|---|
| names, 2.13 | 1,852 | F1 131 / F2 42 / F3 38 / F4 28 | (other selection) | F1 0 / F2 39 / F3 36 / F4 28 (1,774 of the cases) |
| names, 3 | 3,876 | F1 256 / F2 42 / F3 78 / F5 270 / F6 0 | F1 256 / F2 42 / F3 78 / F5 270 / F6 150 | F1 0 / F2 42 / F3 78 / F5 270 / F6 450 |
| givens, 2.13 | 1,076 | G1 128 / G2 (package object `a`) 128 | same | same |
| givens, 3 | 2,355 | G1 148 / G2 208 / G3 0 | G1 148 / G2 208 / G3 289 | same as develop |

Model over the whole space (split): names 2.13 today 5,892 unclean (F1 3,228), #34 the same, proposal 1,296 (F4 only, beside resolution); names 3 today 17,392 (F1 6,400; no F6), #34 the same, proposal 8,256 (F5 only).

#34 (scratch branch: `claude/names-conformance` + #34) on the split layout: partial runs only (names 2.13 238 cases, names 3 175), stopped on purpose since they reconfirm the model and the scripted tests; they agree with the model, F1 still present (27 and 14).

Pending scripted tests (retronym/zinc, stacked on `claude/names-conformance`): `added-class-upstream`, `added-class-upstream-scala3`; each fails only at its last step on develop and on #34.

## Fixing F1 across subprojects (pragmatically)

The downstream has to learn which upstream classes are new to it. Options, cheapest first:

* Users of the simple names of upstream classes compiled since the downstream's last compilation and absent from its `allExternals`. No format change, but it fires on recompiled (not only added) classes whose simple name the downstream uses and resolves elsewhere.
* The upstream records the classes each of its compilations added (#34 already computes them per cycle); the downstream reads those newer than its last compilation. Exact; an `Analysis` field.
* The downstream stores the upstream's top-level simple names (or a hash per package) and diffs them. Exact; storage per upstream.

All of them invalidate only the users of a name that something upstream started to define, which in practice is rare; none invalidates the world.
