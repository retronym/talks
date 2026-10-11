# Phase 10 — name resolution, mechanically (`ZincNames/Names.lean`, `ZincNames/Givens.lean`, `Zinc/NamesRules.lean`)

P9.3 found one way an edit changes what a name resolves to without Zinc noticing. This phase searches the family mechanically: a program space over Scala's scopes, the model's verdict per edit, the conformance harness on Zinc `develop`, and a pending scripted test per family.

## Model

`Names.lean`: the client's simple name `Foo` (or `Option`, with `scala.Option` as the last resort) can be bound by a block's wildcard import, an inherited member, an explicit import, a wildcard import of an object or of a package, a class of the inner package, the inner package's package object, a class of the outer package, and `scala._`. Client factors: the package clause (`package a; package b`, `package a.b`, `package a`), which imports and `extends` are present, another class in the client's file, and (Scala 3) whether `W` and package `a.b` get their member through a wildcard `export`. Edits: add or delete a binding, rename a top-level class to or from `Bar`, move a class between packages. Resolution follows each compiler; the rules were probed with `scala-cli` and then checked on every case the harness ran (the client's classfile shows what it resolved to). Zinc's side is the edges its extractors record and the rules of `IncrementalCommon`: an import's edge goes to one class of the file (the first in Scala 2; the *last* in Scala 3, whose `responsibleForImports` keeps the last `TypeDef` it folds over), a package records nothing, an added source invalidates nothing.

`Givens.lean`: the same with an instance found by type (`implicitly`/`summon`). Scala 2 calls any two instances in the lexical scope ambiguous and searches the companion only when there is none; Scala 3 prefers the innermost nesting level, with the file's imports and the client's own package at one level. A changed implicit invalidates every member-ref dependent of its class, so an import's edge to any class of the file is enough; what is left is the scopes with no edge at all.

Fixes, checked on the whole space (`NamesRules.lean`'s `searched_clean`, `names_clean` checks): recording every scope the lookup searched, misses included, or invalidating the users of a name whenever a binding of it is added or removed. Neither touches F4, F5 and F6, which are not about the client's resolution. F6's fix belongs in dotc: decide whether a class calls a trait's initialiser the same way from source and from TASTy (or always call it).

## Harness

retronym/zinc branch `claude/names-conformance` (develop + the harness of retronym/zinc#25): base programs as source files, a probe of the client's constant pool, and two fixes for Scala 3 that the earlier spaces never needed. Scripted's `IncHandler` did not register `TastyFiles` as auxiliary class files (sbt does), so a deleted or restored classfile left its `.tasty` behind and later builds read it ("out of sync with its TASTy file"); and TASTy records source paths relative to the working directory, so the work and clean builds, in different directories, never had equal classfiles. `scripts/select.py` picks bases greedily until every signature (the edit, the model's resolution before and after, the package clause, `first`, and more) has a case.

## Families

Pending scripted tests on retronym/zinc branch `claude/name-resolution-pending` (on top of P9.3's `claude/added-class-inner-package`); each was checked to fail only at its last step (the incremental build succeeds) and its edited sources to fail a clean compile.

| | Family | Lean | Scripted (pending) |
|---|---|---|---|
| F1 | A top-level class added (or renamed to, or moved) into a scope searched earlier: an inner package, a wildcard-imported package, the client's package over `scala._`. Zinc compiles only the added source. | `inner_added_today` (`Added.lean`: `added_today_wrong`) | `added-class-*` (P9.3) |
| F2 | A member added to a package object over an outer binding; in Scala 3 also a top-level `export` gaining a forwarder. The client reached the package object through no symbol. | `pobj_added_today`, `export_added_today` | `added-member-package-object`, `-scala3`, `added-member-top-level-export-scala3` |
| F3 | A member added to a wildcard-imported object, the import charged to another class of the file (Scala 2: the first; Scala 3: the last) that does not use the name. | `wild_first_today` | `added-member-wildcard-import-second-class`, `added-member-wildcard-import-last-class-scala3` |
| F4 | Scala 2 only: a package object member (declared or inherited) beside a class of the same name; scalac's joint compilation leaves the class's mirror without its `ScalaSignature`, the separate one keeps it, and Zinc never recompiles the class's file for an edit of the member. Adding the member: bytes only. Removing it (found with the inherited factor, P10.7): a client that now resolves the class fails to compile incrementally (`not found: value Foo`) where a clean build succeeds; a declared member fails the same way under plain scalac. Not an invalidation Zinc misses: the class's file would have to be recompiled for an edit of another file it does not depend on. | `staleMirror`; `SplitProof.Spec.joint_not_comp` | none (bytes; the removal is reachable only through the inherited factor in this space) |
| F5 | Scala 3 only: a class and a package object member (or top-level export) of one name in one package; the double definition is reported only when both files compile together, and nothing connects them in Zinc (the member is `a.b.package$.Foo`). | `missedClash` | `package-object-member-clashes-with-class-scala3` |
| G1 | An implicit or given added to a package object (Scala 2: `package object a` too), over the companion or making the search ambiguous. | `pobj_added_today_s2` | `added-implicit-package-object`, `added-given-package-object-scala3` |
| G2 | Scala 3: a top-level given added in a new file. | `inner_added_today_s3` | `added-given-top-level-scala3` |
| F6, G3 | Scala 3 only: a client extending a trait whose members are all lazy (`object Foo`, a given alias) compiles without the call to the trait's `$init$` when compiled apart from it (the trait read from TASTy has no initialiser); Zinc recompiles the client in a later round than the trait or without it. In the space the `$init$` is empty, so only bytes differ; but it is a separate compilation bug in dotc: once a client has been compiled apart, a statement later added to the trait (not API, so Zinc recompiles the trait alone) never runs for it, where a clean build runs it. | `Names.separateInit`, `Givens.separateInit` | `trait-initialiser-skipped-scala3` (behavioural: `run` fails) |
| F7 | Scala 3 only, found with the inherited factor (P10.7): `object a.b.Foo` compiled jointly with `package object b extends a.PT`, where `PT` has an `object Foo`, gets a `writeReplace` that serialises `a.PT$Foo$`, the inherited member, instead of `a.b.Foo$`; compiled apart it is right. A dotc bug (the clean build is the wrong one); incremental and clean differ whenever the edit changes which. | `staleModule` | none yet |

## Counts

| Space | Edits | Model unclean (F1/F2/F3/F4/F5 or G) | Harness cases | Model vs harness disagree | Divergences (F1/F2/F3/F4/F5 or G) |
|---|---|---|---|---|---|
| names, 2.13 | 61,812 | 5,892 (3,228/936/864/864/0) | 11,506 | 0 | 1,532 (844/252/260/176/0) |
| names, 3 | 122,528 | 25,312 (6,400/1,008/1,728/0/8,256; F6 7,920) | 3,876 | 0 | 796 (256/42/78/0/270; F6 150) |
| givens, 2.13 | 1,076 | 256 (G1: package object `b` 128, package object `a` 128) | 1,076 | 0 | 256 |
| givens, 3 | 2,355 | 645 (G1 148, G2 208, G3 289) | 2,355 | 0 | 645 |

Model unclean counts are over the whole space; the harness ran every edit of the givens spaces and a greedy selection of bases for the names spaces. These counts predate P10.7's inherited factors and bystanders, which enlarge the spaces. Resolution agreed with the compiler on every case run.

## The cheap fix (retronym/zinc#34)

#34 invalidates, after each cycle, the users of the simple name of every top-level class the cycle added (`invalidateByAddedClasses`). The model's `Mode.cheap` mirrors it: Zinc today, plus the client whenever an edit adds a top-level class named as the client's name (`add`, `unrename` or `move` into `wpkg`, `inner` or `outer`); in `Givens.lean` the only classes added are `Inner$package` and `Outer$package`, which no client names, so the mode is today's (`cheap_is_today`). `cheap_added_clean`: every edit that adds a class is clean under it, but for the divergences beside resolution and the trait initialiser. `lake exe conformance names|givens 2|3 cheap` dumps its verdicts.

The harness ran the same cases as on develop (the same base selection, identical sources) on a scratch branch of retronym/zinc: `claude/names-conformance` with #34 cherry-picked. Model and harness agree on every case, and resolution on every case.

| Space | Family | develop | #34 | Model on the space, today → cheap |
|---|---|---|---|---|
| names, 2.13 | F1 | 844 | 0 | 3,228 → 0 |
| | F2 / F3 / F4 | 252 / 260 / 176 | 252 / 260 / 176 | unchanged |
| names, 3 | F1 | 256 | 0 | 6,400 → 0 |
| | F2 / F3 / F5 | 42 / 78 / 270 | 42 / 78 / 270 | unchanged |
| | F6 | 150 | 450 | 7,920 → 15,672 |
| givens, 2.13 | G1 (both package objects) | 256 | 256 | unchanged |
| givens, 3 | G1 / G2 / G3 | 148 / 208 / 289 | 148 / 208 / 289 | unchanged |

F1 is gone, as predicted; F2, F3, G1 and G2 stay, because none adds a class: the binding is a member of an existing package object, object or `$package` class (G2's added class is `Inner$package`, not a name the client uses). In Scala 3 the fix turns 300 of the harness's F1 cases into F6: a client extending `P`, whose resolution an added class does not change (the inherited member wins), is now recompiled, apart from `P`, and loses the `P.$init$` call (`Client$.class` bytes only; the model counts 7,752 such edits). The revert column moves the same way: names 2.13 988 → 148 (an added class is the revert of a delete, rename or move), names 3 430 → 618 (F6 again).

## Extending #34: a rule per family, as a specification (P10.7, P10.9, P10.10)

Each remaining family gets a rule, run after every cycle as #34's is. `SplitProof.Spec` (names) and `SpecGivens.lean` (implicits) state the rules as keys of the framework's compiler (DESIGN-spec.md) and prove what they guarantee for every program. `Names.lean`/`Givens.lean` check the same rules on the bounded spaces, against the harness, and measure their cost.

The rules:

* **#34** (F1): the users of the simple name of an added top-level class.
* **F2**: the users of a name that a package object (`a.b.package`, Scala 3's `F$package`) gained. On develop the package object's stored API includes inherited members, so diffing each cycle against the merged analysis sees an inherited member appear in the cycle that recompiles the package object.
* **F3**: an import's change is checked against the used names of every class of the importing file, not only the class it is charged to.
* **G** (G1, G2): when a package object or `$package` class gains or loses an implicit (or is a new class with one), invalidate classes. The client never names the instance, so a name cannot narrow it.

Each comes in two reaches. `global` covers every user of the name, or every class for G, which is what #34 does today. `narrowed` covers only the classes of the package where the binding changed and of its nested packages, plus classes that record a wildcard import of that package (`imports`). Recording that import is a bridge change; today the bridge records nothing for a package qualifier.

Two new factors make the binding inherited rather than declared: `package object b extends a.PT` (`pinh`) and `object W extends a.WT` (`winh`). The givens space gets `pinh` and `wpkg` (an instance in `package object q` or a top-level given in `a.q`, imported with `import a.q._` / `import a.q.given`).

### The specification (`SplitProof.Spec`, `SpecGivens.lean`)

Name resolution is one `NCompiler` instance, shared with Phase 13: `SplitProof.Spec`.

- **The client and its scopes.** One client looks the name up in `n` scopes in search order and stops at the first hit. Each scope's binding is a unit, so any program of the slot language is an instance, with any number of bindings.
- **The rules extend it in place.** `Ext` adds three kinds of scope: a package-object member (F2), a wildcard import charged to a class that does not use the name (F3), and a scope reached through a package import. The `rules` design records today's keys, F3's existence keys, and one `rule` key. That key's hash reads the scopes #34 and F2 reach (`global`, or `narrowed`).

Implicit search is `SpecGivens.lean`: the same scopes, as an `XCompiler` (`General.lean`), because the search reads the whole level of its hit and its keys must read the resolved scope from the output.

Because the oracle is arbitrary, the proofs hold for any number of bindings. T3a starts from any state satisfying the invariant, so it covers edit sequences. That answers the bound of the enumeration (at most two bindings, single edits).

| Result | Status |
|---|---|
| `rules_obligations`: the rules meet the obligations whenever every scope is pinned, a `wildOther` import under F3, or reached; so T3a″ (`NCompiler.zinc_sound`) | proved, every lookup |
| `global_obligations`: #34 + F2 + F3, global, for every names lookup (`NamesScopes`) | proved |
| `narrowed_obligations`: the same narrowed, **under the hypothesis** that the bridge records package imports (`imports`, being built for Scala 2 and dotc) | proved |
| `f2_not_obligations` (#34 + F3), `f3_not_obligations` (#34 + F2), `narrowed_without_imports`; Phase 13's `today_not_obligations` (F1, upstream), `cheap_not_obligations` (#34 across subprojects) | proved, one witness each (kernel `decide`/`simp`) |
| Precision: `Necessary`, `Invalidated`, `OverInvalidated` (after an edit `I → I'`); `necessary_invalidated` (sound keys invalidate every necessary unit); `searched_exact` (`searched` invalidates only necessary units); `narrowed_le_global`; `rules_over` (the rules over-invalidate when a scope searched after the hit gains a binding) | proved |
| `joint_not_comp`: F4 (Scala 2's mirror without `ScalaSignature`) and F5 (Scala 3's missed clash) are failures of compositionality, not coverage, so no key fixes them | proved, one witness |
| Givens (`SpecGivens.lean`): `g_global_obligations`, `g_narrowed_obligations` (given recorded imports), `g_searched_obligations`; `g12_today`, `g_narrowed_without_imports`; `g_decls_not_abstraction` (#24 without composition) | proved |
| Resolution per version (Scala 2's precedence, ambiguities, the class-name alias), F6 and F7, the exact recompiled sets, the bystanders of other clients | checked: `Names.lean`/`Givens.lean` on the bounded space and the harness; `Split.check_abstract` checks the slot mapping on the bases |
| Each rule closes its family and nothing else, today's families are F1–F3, the rules together are clean | checked: `NamesRules.lean` `example`s over the bounded spaces |

Precision across clients is not in one client's view. `global` and `narrowed`-with-imports cover the same scopes of this client, but `global` also invalidates every other user of the name. The enumeration's bystanders measure that difference (`User`, `Far` below).

### Cost

Correctness first, but a rule that invalidates the world on common edits is no use. Precision in the spec is tightness: the narrowed rules record only keys a probe of the lookup justifies, so they invalidate a client only when an answer its lookup can read changed (or through inheritance). The global rules record keys on every package. The magnitude comes from the enumeration (`conformance cost`):

* **Client, resolution unchanged**: the client recompiled although what its name (or summon) resolves to did not change.
* **Bystanders**: classes that stand for the rest of a build, recompiled although their lookups never searched the edited scope. `c.User` uses the name elsewhere (`a.Y.Foo`); `a.b.Near`, `a.Mid` and `c.Far` summon nothing.

Every edit in the space touches a binding of the client's name, so these are worst cases, not frequencies.

| Space | Mode | Edits | Wrong | Client, resolution unchanged | `User` | `Near` | `Mid` | `Far` |
|---|---|---|---|---|---|---|---|---|
| names, 2.13 | `today` | 209,552 | 19,008 | 14,432 | 0 | | | |
| | `cheap` (#34) | | 9,712 | 77,368 | 74,792 | | | |
| | `f2` | | 11,904 | 25,088 | 20,464 | | | |
| | `f3` | | 16,400 | 19,120 | 0 | | | |
| | `cheap+f2+f3`, global | | 0 | 92,712 | 95,256 | | | |
| | narrowed | | 6,896 | 65,008 | 0 | | | |
| | narrowed + imports | | 0 | 79,344 | 0 | | | |
| | `searched` | | 0 | 102,808 | 0 | | | |
| | `names` | | 0 | 119,832 | 209,552 | | | |
| | `all+decls` (#24) | | 6,264 | 90,728 | 85,024 | | | |
| names, 3 | `today` | 270,268 | 19,628 | 15,096 | 0 | | | |
| | `cheap` | | 5,208 | 90,160 | 102,948 | | | |
| | `f2` | | 17,444 | 35,688 | 26,296 | | | |
| | `f3` | | 16,604 | 19,472 | 0 | | | |
| | `cheap+f2+f3`, global | | 0 | 115,128 | 129,244 | | | |
| | narrowed | | 11,288 | 82,192 | 0 | | | |
| | narrowed + imports | | 0 | 98,192 | 0 | | | |
| | `searched` | | 0 | 125,176 | 0 | | | |
| | `all+decls` | | 840 | 105,736 | 119,012 | | | |
| givens, 2.13 | `today` | 4,748 | 1,516 | 856 | | 0 | 0 | 0 |
| | `g`, global | | 0 | 856 | | 1,972 | 1,972 | 1,972 |
| | narrowed | | 428 | 856 | | 800 | 624 | 0 |
| | narrowed + imports | | 0 | 856 | | 800 | 624 | 0 |
| | `all+decls` | | 304 | 856 | | 1,572 | 1,572 | 1,572 |
| givens, 3 | `today` | 11,289 | 2,188 | 2,301 | | 0 | 0 | 0 |
| | `g`, global | | 0 | 4,938 | | 6,169 | 6,169 | 6,169 |
| | narrowed | | 468 | 4,571 | | 3,768 | 1,814 | 0 |
| | narrowed + imports | | 0 | 4,938 | | 3,768 | 1,814 | 0 |
| | `all+decls` | | 356 | 4,654 | | 5,409 | 5,409 | 5,409 |

Reading it:

* **Narrowed means exactly the packages the lookup searches** (retronym/zinc#47's `sees`): a class's own package, and the packages its source records as `p._`, a wildcard import when recorded or the outer clause of a chained `package a; package b`. A class of a nested package does not see its parent unless the clause is chained, so a flat `package a.b` client is not reached by `a`'s changes. For Scala 2's implicits, the classes referring to a type under the package are added too, since Scala 2's implicit scope includes the package objects of a type's prefix (Scala 3 dropped this).
* **Narrowing with recorded package imports costs nothing in soundness and removes every bystander outside the searched packages.** `User` and `Far` drop to 0. The client's own count is unchanged, because the client searches those packages.
* **Narrowing without the recorded import is unsound,** exactly on the wildcard-imported package. That is the spec's `narrowed_without_imports`; here it is 6,896 (2.13) and 11,288 (3) wrong edits.
* **F3 is free.**
* **#34 is most of the client's excess.** An added class named like the client's name recompiles it even when an inner scope still wins.
* **G narrowed still reaches a whole package tree.** A tighter G would need the implicit searches each class ran (the type searched), which the bridge does not record.
* **Every extra recompilation grows F6 in Scala 3** (the dotc trait-initialiser bug).
* **The per-cycle baseline is dropped.** Zinc diffs each cycle against the merged analysis, which still holds a not-yet-recompiled package object's old API, so it is sound on develop. With #24's composition, names must be composed against that same analysis.

#### On a real build (Spark 4.0.1 `sql/catalyst`, from retronym/zinc#47)

zinc-develop-names measured the rules on catalyst, 2,527 classes (241 Java), Scala 2.13, with IncBench. These are #47's numbers, quoted.

| Edit | #34 | global | scoped (`sees`) |
|---|---|---|---|
| `util` package object gains `def sql(x: Int)`, a name most classes use | 631 | 2,527 (full) | 831 |
| `expressions` package object gains an implicit class | 664 (unsound) | 2,528 | 2,294 |
| root `catalyst` package object gains an implicit class | 243 (unsound) | 2,528 | 2,477 |

**Blast radius of "the users of `n`".** For each top-level class `p.n`, count the other classes using `n`:
- every class using `n` (#34): p50 2, p90 16, p99 151, max 1,308;
- those that also see `p` (#47): p50 1, p90 8, p99 72, max 979.

The global numbers are skewed by names that recur across packages: 1,187 classes use `Product`, but only 73 of them see `catalyst.expressions.aggregate`.

**Package-object audiences**, in classes, for F2 and G:

| package object | package tree + recorded (the model's old `narrowed`) | `sees`: package + recorded (F2) | + referrers of types under it (G, Scala 2 with package prefixes in the implicit scope) |
|---|---|---|---|
| `catalyst` | 2,137 | 130 | 2,085 |
| `catalyst.expressions` | 1,429 | 1,343 | 1,836 |
| `catalyst.plans` | 503 | 241 | 758 |
| `catalyst.trees` | 14 | 14 | 694 |

Recording chained package clauses is what makes F2 cheap for outer packages: the root package object drops from 2,137 classes to 130. G stays costly only in Scala 2 builds that keep package prefixes in the implicit scope; Scala 3 builds, and Scala 2 without them, get the middle column. #47 proposes the precise key as a follow-up: record, per class, the prefix packages an implicit search consulted. That would bring the root object back to about 130.

### Harness check of the new factors

On the #34 scratch build (`cheap` mode), 60-base subsets weighted to the new factors (names 2.13: 407 cases, names 3: 411, givens 2.13: 257, givens 3: 337). After the fixes below, model and harness agree on every resolution, every verdict, and every recompiled client and bystander set (`analyse.py` now compares those). What the run taught the model:

* Scala 2 treats an inherited package-object member as no package member (`isPackageOwnedInDifferentUnit` looks at the trait). It beats the file's imports, even two binding wildcards, and is ambiguous with a block import. Scala 3 reports no clash between `a.b.Foo` and an inherited member, and the class wins.
* Scala 2's bridge names a class by `fullName`, which skips `package`. To Zinc, the package object's declared `object Foo` and the class `a.b.Foo` are one class name, so a change to either file invalidates the clients of both, and #34 does not see `a.b.Foo` added beside the member (`aliased`).
* F4 is observable (above). F6 also hits `W`, recompiled apart from `WT` (`heirInit`). F7 is new.
* Scala 3 records a dependency on an inherited package-object member that the lookup passed over for `a.b.Foo`.
* Not modelled: under #34, classes that *declare* a member named as the added class (`a.Y`, `a.V`) are recompiled too. Real cost is higher than the `User` column.
* F4 depends on the mode. What decides the mirror is whether the package object has the member when `Inner.scala` is compiled, jointly or apart (probed). The F2 rule recompiles `a.b.Foo` as a user of its own name, which leaves the mirror as a clean build has it for an inherited member, but not for a declared one: there Zinc's `a.b.Foo` is the member, the class-name alias (`innerRecompiled`). zinc-develop-names' run of the narrowed rules (#47, names 2.13, 2,331 cases; givens 2.13, 2,372) agrees with the model on every verdict and recompiled set.
* With exact `sees` (#47's final build, the Scala 2 import record), model and harness agree on every verdict and recompiled client/bystander set: names 2.13 2,331 cases, givens 2.13 2,372.

Case files for the Zinc sessions (develop: `all`, `all+narrowed+imports`; #24: `all+decls`, `all+composed`) are `conformance names|givens 2|3 <mode>` dumps with a greedy base selection. The dumps carry `modelRecompiled`, `modelNecessary`, `modelFamily` and `keys`.

### Coverage: the model's keys against the Analysis

Each edit's `keys` names what the mode needs the client to have recorded before the edit (`Names.clientKeys`, `Givens.clientKeys`), in retronym/zinc#54's grammar:
- the name it uses and the class it resolved to (`uses:Foo`, `ref:a.W.Foo`);
- for each slot of its lookup that the edit changes, the record that carries the change: `inh:a.P`, `ref:a.V`, and `refFile:a.W` / `refFile:a.X` for imports, which are charged to one class of the file;
- for the narrowed rules, `sees:p` for each package scope the lookup searches. The givens rule reads `ref:a.T` instead of `sees:a` for a flat client in Scala 2, where the prefix part of the implicit scope reaches it.

The harness (#54) reads the keys from the Analysis and reports `uncovered`, separately from classfile divergence. Run with `--keys-at both`, before the edit and after the incremental build, on develop + #36 + #54 + #47 (scoped rules, the Scala 2 bridge recording `p._`), mode `all+narrowed+imports`, the overnight base selection:

| space | cases | uncovered | divergences |
|---|---|---|---|
| names 2.13 | 5,905 | 0 | 93, all F4 as the model predicts (83 mirror classfiles, 10 errors in a later compile), plus 73 on the revert |
| givens 2.13 | 4,748 | 0 | 0 |

After the incremental build every key other than the resolution's `ref` is still recorded. That `ref` moves with the resolution, so the after-edit check skips it.

The same keys on a build without #47's bridge records (develop + #36 + #54), on subsets touching the package scopes:
- names 2.13: 144 of 352 cases uncovered, all for `sees:a` (chained clause) or `sees:a.q` (package import). 136 of them build clean: the gap is visible without a divergence. The other 98 divergences are covered; they come from the missing rules.
- givens 2.13: 215 of 351 uncovered, for the same two keys.

What the loop changed in the model: a binding to a library class (`scala.Option`) is a library dependency of the source, not a member-ref, so it has no `ref` key.

## Steps

- [x] P10.1 `Names.lean`: scopes, resolution per version, Zinc's edges, verdict; families as checked examples; `searched_clean`, `names_clean`.
- [x] P10.2 `Givens.lean`: instances by type.
- [x] P10.3 `conformance names|givens 2|3`; harness: source-file bases, a classfile probe, Scala 3's TASTy files and source paths.
- [x] P10.4 Runs on develop, model and harness reconciled (Scala 2's block/explicit ambiguity, the package object searched before the package's classes, Scala 3's last-class import charge, the explicit selector's name charged to the import's class, the missed clash, the trait initialiser).
- [x] P10.5 Pending scripted tests per family.
- [x] P10.6 The cheap fix (retronym/zinc#34) in the model (`Mode.cheap`) and the harness: F1 gone, F6 grows, the rest unchanged.
- [x] P10.7 #34's extensions as rules (F2, F3, G) with theorems per rule and combined; inherited bindings (`pinh`, `winh`); #24's declarations-only API, with and without composition; the cost per mode (`conformance cost`); a harness check of the new factors on #34, model and harness reconciled (Scala 2's inherited package-object member and class-name alias, F4 observable, F6 on `W`, F7).
- [ ] P10.8 Harness runs of the rules: develop (`all`, `all+narrowed+imports`) and #24 (`all+decls`, `all+composed`), by the Zinc sessions.
- [x] P10.9 `NamesSpec.lean`: names and implicit search as `TCompiler` instances; today's keys fail coverage per family; the rules (global, and narrowed given recorded package imports) and `searched` meet the obligations and inherit T3a; #24's declarations-only hash fails abstraction; tightness. Enumerations relabelled as checks; the per-cycle baseline dropped; global vs narrowed rules; the givens `wpkg` slot.
- [x] P10.10 The names rules moved onto the shared instance `SplitProof.Spec` (talks#28): `Ext` kinds, the `rules` design, obligations global and narrowed (under the recorded-import hypothesis), witnesses, precision (`Necessary`, `OverInvalidated`, `searched_exact`, `narrowed_le_global`, `rules_over`), F4/F5 as `joint_not_comp`; givens in `GivensSpec.lean` until the framework merge.
- [ ] Future: a pending scripted test for F7 (and a dotc issue); count the declaring classes the name rules reach; a G that reaches only classes whose implicit search could see the instance (needs the extractor); the `split` layout is Phase 13; members renamed inside a container (the model has add and delete); F5's fix needs the definitions of a name in a package, not its users.
