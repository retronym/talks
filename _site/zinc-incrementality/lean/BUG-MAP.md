# Bug map: the catalogue against the model

Every row of `BUGS-catalogue.md` (145) and every pending or disabled scripted test of `TESTS-catalogue.md` mapped to the phase, Lean file and family or theorem that covers it, or to a gap. Then the gaps clustered into candidate phases, the variants each existing phase predicts that have neither a test nor a bug, and the counts.

Reading the coverage column. `covered`: the named instance's queries and keys express the bug's trace, and the obligation that fails is the one the bug's root cause names (a checked example or a theorem exhibits it). `partially`: the feature is modelled but this mechanism is not instantiated, or only the shape is the same (a different language feature with the same failed obligation). `GAP`: nothing in the model expresses the trace; the cluster code points at the candidate phase in the Gaps section. `n/a`: not a bug, or a harness matter. Compiler bugs (joint and separate compilation differ in the compiler) are `GAP (comp)` unless an instance already has the observable: the model's job for them is to classify the failure as `¬ comp` (`Model.lean`, `Obligations.comp`), as `REVIEW-2026-10-11.md` finding 3 does for F4 and F5.

The predicts column asks whether the instance, had it existed, would have exhibited the failure before the bug was filed: `yes` (a checked example or witness theorem has the trace), `partially` (the family is there, this witness is not), `no` (the instance has the feature but the bug is a precision, implementation or compiler matter the instance does not show), `-` for gaps.

Cluster codes used in the coverage column: K-C1 constructors and synthetic members; K-C2 extraHash lineage and the companion namespace; K-SM stale middle file, alias chains, cyclic inference; K-M1 macro dependency timing; K-MR mirrors and derivation; K-AN annotations; K-N class naming agreement; K-H1 hash stability across forms; K-FI files as units; K-U1 used types' supertypes and structural members; K-L1 local classes and SAM lambdas; K-IC inner and path-dependent classes; K-PL pipelining early-output lifecycle; K-PB phantom binary dependencies; K-EX exports; K-SB snapshot bookkeeping and formats; `comp` compiler joint-vs-separate (the obligation's name, so no prefix). The `K-` prefix keeps cluster codes apart from family IDs such as `Cycles`' C1 and C2. `JavaOrder`'s families are written JO-V1, JO-V2, JO-O1, JO-O2, apart from `InlineOpaque`'s O1 and ROADMAP Track V.

## 1. Catalogued bugs

### Constructors, case classes, default arguments

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| sbt/zinc#97 | abstraction | constructor params | covered: `Synthetic.lean` `over_plain` (one name `<init>` for every class: a constructor change of `C` invalidates a client of `B`'s constructor) | yes | Over-invalidation, on `Synthetic.lean`'s name-level model (not a `Compiler` instance); #288's class-specific names remove it. |
| sbt/zinc#1324 | abstraction | default args | covered: `Synthetic.lean` `over_default` | yes | `<init>$default$N` unmangled: the same key collision one hop further. |
| scala/scala3#12401 | abstraction | constructor params | covered: `Synthetic.lean` `under_12401` (unmangled API against a mangled use) | yes | The under side of #97: a constructor change that moves no name the client used is abstraction failing on the `(C, init)` key. |
| scala/scala3#12898 | abstraction | constructor params | covered: as #12401 | yes | Same as #12401. |
| scala/scala3#19910 (sbt/zinc#1334) | abstraction | constructor params | covered: `Synthetic.lean` `under_of_disagree` (`p;C;init;` against `C;init;`) | yes | Definition side mangled with the package, use side without: K-N's spelling disagreement (`Naming.lean`) one level down, on names instead of classes. |
| sbt/zinc#572 | coverage | case class synthetic companion, default args, package object | covered: `Synthetic.lean` `apply_572` (without the synthetic companion in the API, a change to `apply` invalidates nothing) | yes | Synthetic top-level trees skipped by `API`: the owner's hash has no key for `apply`. `TreeToy.lean` has a synthetic `unapply` only as a query the client asks. |
| sbt/zinc#238 | not a bug | case class synthetic companion | n/a | - | |
| scala/scala3#26231 | coverage, abstraction | pattern matching, case class | covered: `TreeToy.lean` (`pat`, `today` vs `fixed`, `not_obligations_today`; the `_3` sentinel is #26262's `_N+1`) | yes | The coverage half (post-typer `_1`, `_2`) is the checked example. The abstraction half (synthetic `unapply : (C): C`, fixed by hashing `C;init;`) is `Synthetic.lean` `unapply_26231`. |

### Inheritance, traits, companions

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| sbt/zinc#417 | coverage | trait inheritance, same source file | covered: `Files.lean` `Fi.fi_not_covered`, `fi_loop` (the same-file edge dropped: `C`'s key on `B` does not reach `A`); the fix, keeping the edge, proved for every program (`Fi.kept_obligations`, `kept_sound`) | yes | The bridge dropped inheritance edges between classes of one file; Phase 26 made `file u = file v` a predicate of the model. |
| sbt/zinc#542 | abstraction | trait private members | covered: `Flat.lean` P5 fields and private members (`traitPub` ablation: 48,000 unclean without the private channel) | yes | The class mixing a trait in implements its fields and private members; a public-API hash fails abstraction on the `(t, fields)` query. |
| sbt/zinc#662 | compositionality | trait private members across projects | covered: `ExtraHash.lean` `noFold_misses` (a key on the intermediate trait that does not fold the ancestor's private members); also `ImplicitScope.lean` P7.3's ablation, the same shape | yes | The stored-summary design with the `apiHash` fold is #1289's fix in another feature; the `extraHash` lineage itself has no instance (K-C2). |
| sbt/zinc#1794 | abstraction | trait extraHash | covered: `ExtraHash.lean` `coldWarm_spurious` (`HashForms.unstable_spurious` with forms cold and warm); `ImplicitScope.lean` `stored_eq_recomputed` is the consistent case | yes | Parents folded from the previous analysis instead of the current cycle. |
| sbt/zinc#1793 | abstraction | companion object | covered: `ExtraHash.lean` `merged_spurious`, kernel-`decide` example | yes | One `AnalyzedClass` per companion pair, the object's hash merged into the trait's `extraHash`. |
| sbt/zinc#1795 | coverage | companion trait vs object | covered: `ExtraHash.lean` (kernel-`decide` example of `merged_spurious`; `qualified_precise` for per-namespace keys) | yes | `classDependency` on strings: `object B extends A` and `trait B extends A` are one edge. What remains is the namespace on the callback (`AnalysisCallback4`). |
| sbt/zinc#1796 | abstraction | companion members with the same name | covered: `ExtraHash.lean` (kernel-`decide` example of `merged_spurious`; `qualified_sound` states the fix) | yes | `nameHashesForCompanions` merges `class A.x` and `object A.x`. The fix needs the namespace on used names and name hashes (an analysis-format change). |
| sbt/zinc#1798 | coverage | compound type in signature | partially: `Erasure.lean` (intersection `W with Z` in a member type records `(Z, cls)`, not an inheritance key) | no | The bridge recorded an inheritance edge from a `CompoundTypeTree`: sound and imprecise. Precision is not defined in the framework (REVIEW finding 4). |
| sbt/zinc#998 | unknown | inheritance, JDK 11 | GAP (unknown) | - | Not diagnosed. |
| sbt/zinc#1528 | policy | local classes | GAP (K-L1) | - | `memberRef ⊇ inheritance` is an invariant of Zinc's relations, not of the model. `PLAN-sam.md` places it in the files layer (compare every class the round compiled); not stated in `Files.lean` yet. |
| sbt/zinc#830 | coverage | SAM lambda, Java interop | covered: `Sam.lean` `w830_pre` (Scala 2 before #1288: a lambda's walk records only presence); the fix `fix_sound` | yes | A lambda implementing a SAM type is an inheritor with no inheritance key. In the queue (SAM conversion). |
| sbt/zinc#168 | policy | trait compiles to interface (2.12) | partially: `Flat.lean` mixin-forwarder queries, `FlatRules.lean` `traitDirect` | partially | The model says which trait edits a descendant's bytecode reads (forwarders, fields); a narrower inheritance rule is a precision claim, which the framework cannot state. |
| sbt/zinc#1845 | compositionality | implicit scope of ancestors' companions, multi-project | covered: `ImplicitScope.lean` (develop across projects stays wrong; `is_obligations`, `is_sound`; `exhaustive implicit`) | yes | The phase was built from the fix; the instance exhibits the failure independently of it. |
| sbt/zinc#1846 | compositionality | implicit scope of an object's singleton type | covered: `ImplicitScope.lean` P7.6 (`Show[O.type]`, 136 unclean runs of the fix) | yes | Found by the exhaustive check. |
| scala/scala3#18309 | coverage | using-clause on constructor, multi-module | partially: `ImplicitScope.lean` (companion scope across projects), `Givens.lean` (lexical scope) | partially | The resolution site is a constructor's using clause; the model's clients summon directly, and the split layout (Phase 13, `Split.lean`, not in this directory) is where the upstream case lives. |
| scala/scala3#9087 | coverage | multiversal equality `Eql` given, multi-module | partially: `Givens.lean` G1/G2 (a given added in a scope the client has no edge to), one project only | partially | The same family upstream needs the split layout. |
| scala/scala3#9694 | coverage | inner class, separate compilation | covered: `Naming.lean` `spelling_bugs` (`O$I` read, `O` recorded) | yes | `binaryDependency` from `associatedFile` names the top-level classfile for an inner class: the key's unit is the wrong class. The inner-class policy side is K-IC. |

### Type members, aliases, projections, dependent types

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| sbt/zinc#174 | coverage | type members, as-seen-from | covered: `Hier.lean` scenario 2 (`asSeenFrom`: `B extends A[Int] → A[String]`, `A.f : T`; designs `D`, `W`, `Mk`), `Erasure.lean` `asf_of_decl` | yes | The design thread of #174 (inheritance expansion vs name hashing) is Phase 2's three designs. |
| sbt/zinc#269 | coverage | type projection, dealiasing | GAP (K-SM) | - | No instance has type aliases whose dealiasing loses the prefix; `InlineOpaque.lean` reads an alias only inside an inline body. |
| sbt/zinc#476 | coverage | `A.type#B#C` alias chain | GAP (K-SM) | - | The same dealiasing coverage failure, plus the stale middle file. Test `nested-type-params` pending. |
| sbt/zinc#535 | policy | type alias in type projection | GAP (K-SM) | - | The crash: a round compiled against a stale classfile fails instead of producing an output. Rounds cannot fail in the model. |
| sbt/zinc#598 | policy | abstract class to trait | GAP (K-SM) | - | `Flat.lean` has the class/trait kind in the header key, so the invalidation is modelled; the crash in round one (backend asserts on the stale superclass) is not. |
| sbt/zinc#1284 | policy | cyclic deps, initial invalidation | covered: `Cycles.lean` (`zinc_ne_clean`, `two_fixpoints`; #1284's rule as `Mode.mutual`, clean on the space at 48 compilations against the precise rule's 36), `Uniqueness.lean` T3b | yes | The theorems give the reason (a per-unit fixed point is not the clean build on a cycle) and the hypotheses; the stale-middle-file failure that also motivated the rule is K-SM. |
| sbt/zinc#1461 | policy | cyclic deps (unused import) | partially: `Soundness.lean` T3a holds for any over-approximating `Policy.Sound` | no | #1284's rule is sound and imprecise; precision has no definition (REVIEW finding 4). |
| sbt/zinc#1332 | policy | cyclic deps, non-API change | partially: as #1461 | no | |
| sbt/zinc#1420 | policy | Scala 3, initial invalidation | partially: as #1461 | no | |
| sbt/zinc#1417 | policy | generic type as member parameter type | partially: as #1461 | no | |
| sbt/zinc#1780 | policy | bridging classes | partially: `Cycles.lean` `Mode.retry` (clean on the cycle family C2, not on C1; agrees with #1780's branch on the scripted tests) | partially | The retry is modelled on the cycle space; the stale-middle-file crashes it targets (#535, #598) need rounds that fail on stale classfiles (K-SM). |
| sbt/zinc#1561 (scala/scala3#23573) | compiler | dependent type with type-lambda bound | GAP (comp) | - | Classify: unification differs between the unpickled and the source form. |
| scala/scala3#13190 | compiler | opaque type, match type | GAP (comp) | - | Unpickler bug. |
| scala/scala3#12927 | compiler | opaque type, pickling | GAP (comp) | - | Same unpickler bug. |
| scala/scala3#13468 | compiler | opaque type with type parameter | GAP (comp) | - | |
| scala/scala3#17601 | compiler | match type, singleton bound | GAP (comp) | - | |
| scala/scala3#22684 | compiler | match type, given | GAP (comp) | - | Order-dependent typing: the group's output depends on which units are in the group, `¬ comp`. |
| scala/scala3#13121 | compiler | implicit search order | GAP (comp) | - | Clean fails where incremental succeeds: `¬ comp` in the other direction. |
| scala/scala3#20136 | compiler | match type and implicit conversion, separate compilation | GAP (comp) | - | |
| scala/scala3#22456 | coverage | `tracked val`, skolem type | GAP (comp) | - | The extractor crashed: coverage by exception. Classify only. |
| sbt/zinc#1782 | abstraction | type lambda, refinement type parameters | covered: `HashForms.lean` `artefact_bugs` | yes | `tparamID` by `fullName` differs between source and unpickled form: a spurious invalidation (precision). |
| sbt/zinc#88 | abstraction | refinement-typed val | covered: `HashForms.lean` `artefact_bugs` | yes | A spurious `override` flickering between forms. |
| scala/scala3#18080 | abstraction | context bounds | covered: `HashForms.lean` `artefact_bugs` | yes | Synthetic evidence names unstable between compiles. |
| scala/scala3#9133 | abstraction | signatures | covered: `HashForms.lean` `artefact_bugs` | yes | Owner changes before erasure moved full names. |
| scala/bug#2558 | coverage | structural type | GAP (K-U1) | - | Legacy build manager; the use site of a structural type queries the member it names on a type it received, not on a receiver it named. |
| sbt/zinc#87 | coverage | used types, supertypes | covered: `DerivedApi.lean` `usedType_not_coverage` (before #87, the `parents` query on `B.x`'s type has no key); the fix `fix_sound` | yes | `B.x : A1`, `A1`'s parents change, the client of `B.x` names neither `A1` nor its parents. Tests `types-in-used-names-a/b`. |
| sbt/zinc#95 | abstraction | value class | covered: `Toy.lean`/`Examples.lean` (the value-class examples, `repaired_sound`), `Erasure.lean` `dep` (`dep_obligations`, `dep_sound`) | yes | The `underlying` query covered by a key on `V`'s name. |
| sbt/zinc#51 | abstraction | erasure | covered: `Erasure.lean` witness `stored` (erased signature at definition, sbt/zinc#1844's alternative 1) | partially | Hashing pre- and post-erasure signatures is the `stored` witness; superseded by #87/#95, which the model also has (`dep`). |

### Inline and macros

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| sbt/zinc#537 | abstraction | `-opt:l:inline` | covered: `Inline.lean` `not_obligations_today` (sbt/zinc#537 named), `obligations_withBodies` | yes | Also `pipelined_ne_final`: the body is not in an early output. |
| scala/bug#8580 | compiler | `@inline` in empty package, separate compilation | partially: `Inline.lean` `pipelined_ne_final` (Scala 2 inlining reads bytecode the early view lacks) | partially | Classify as `¬ comp`; the "callee not found" is the `final` view missing an answer. |
| scala/scala3#9730 | abstraction | inherited inline def | covered: `HashForms.lean` `artefact_bugs` | yes | An identity hash in `toString` inside the API: `π` not a function of the interface. |
| scala/scala3#11861 | abstraction | nested private inline def | covered: `InlineOpaque.lean` (inline-to-inline chains mix in the referenced symbol's API; private members through `inline$p` accessors) | yes | A `treeHash` without the mix-in fails abstraction on the chain; `dConst_today` is the surviving sibling (constants through a path). |
| scala/scala3#13994 | compiler | inline def, `-sourcepath` | GAP (comp) | - | Crash in the second round. |
| scala/scala3#13085 | coverage | extension method moved between files, inline | partially: `Names.lean` `move` edit, `InlineOpaque.lean` inline callers, `Extensions.lean` (extension scopes) | partially | Extension methods are in the queue; the move of a top-level definition between files of one package is F1's `move` with an inline caller. |
| sbt/zinc#249 | coverage | Scala 2 macros | partially: `MacroDeps.lean` (Scala 3's bridge; the Scala 2 bridge's macro tracking has the same queries) | partially | Meta issue. |
| sbt/zinc#1171 | coverage | Scala 2 macro with type parameter | covered: `Flat.lean` P5 whole-class observation key `(c, all)` (437,696 unclean without macro keys; `macro-type-change`) | yes | `DependencyByMacroExpansion` on type arguments is the `(c, all)` key over the stored linearization. |
| sbt/zinc#1282 | policy | Scala 2 macro implementation change | covered: `MacroDeps.lean` (the `implCode` key exists only inside the macro's project; `crossProject_today`; cost `bytecode_coarse`) | yes | Expansion depends on the implementation's behaviour, a `macroImpl` body query with no instance (K-M1). |
| sbt/zinc#1333 | policy | clients of a macro user | covered: `MacroDeps.lean` `bytecode_coarse` (precision of the transitive bytecode key) | yes | Precision. |
| sbt/zinc#1478 | coverage | Scala 3 macros | covered: `MacroDeps.lean` `crossProject_today` (an implementation in another project: `implCode` uncovered), `fix_sound` | yes | Port request. |
| scala/scala3#23852 (sbt/zinc#1574) | coverage | Scala 3 macro calling a constructor | covered: `MacroDeps.lean` `gen_pre24969` (a generated reference uncovered before the dependency phase moved after `Inlining`), and covered today | yes | The same obligation (coverage of the expansion's references) for an expansion computed by running code; macros are explicitly not modelled (K-M1). |
| scala/scala3#18100 | coverage | Scala 3 macro reached through another method | covered: `MacroDeps.lean` `targ_pre23900` (the type argument read uncovered before `DependencyByMacroExpansion`) | yes | |
| scala/scala3#22178 | coverage | `Mirror` of a nested case class through derivation | GAP (K-MR) | - | Recursive mirror summons: post-typer queries, the `TreeToy` shape for a different phase. |
| scala/scala3#23783 | coverage | macro reading an annotation argument | partially: `Annotations.lean` (the client's `annots` query on a unit reached through a type argument is covered when the client records a key on it; the missing key has no witness), `MacroDeps.lean` | partially |  |
| scala/scala3#22999 | coverage | macro annotation `transform` body change | covered: `MacroDeps.lean` `annot_today` (`implCode transform` uncovered: no `Macro` flag, no transitive bytecode hash), `Annotations.lean` `noBody_not_abstraction` | yes |  |
| scala/scala3#20119 | compositionality | macros with pipelining | GAP (K-PL, comp): not modelled in `MacroDeps.lean` (a compositionality failure of the pipelined group) | - | A spurious cyclic-macro error only under early output: `¬ comp` for the pipelined group. |

### Sealed hierarchies, pattern matching, mirrors

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| scala/scala3#13028 | coverage | `Mirror`, circe derivation | GAP (K-MR) | - | `summon[Decoder[AAA]]` depends on a synthesized `Mirror.Of[AAA]` absent from the tree at extraction. |
| scala/scala3#12634 | coverage | sealed children | covered: `Sealed.lean` (`not_obligations_noChildren`; a hash covering the children meets the obligations) | yes | The Scala 3 port of `sealedDescendants` is the `children` hashing of `JavaSealedSpec.lean`. |
| sbt/zinc#753 | coverage | sealed, `useOptimizedSealed`, 2.13 | partially: `JavaSealedSpec.lean` `cases` keys (scrutinee recorded with `PatMatTarget`) | partially | The scope kind (`Default` vs `PatMat`) and the 2.13 phase order are not modelled; the model's `cases` key is the fixed state. |
| sbt/zinc#1229 | coverage | sealed, `useOptimizedSealed`, 2.13 | partially: as #753 | partially | |
| sbt/zinc#653 | coverage | used-name extraction on 2.13 | GAP (K-SB) | - | Noise and omissions after the phase reorder; no model of the extractor's traversal. |
| scala/scala3#25273 | snapshot | sealed, branch switch | GAP (K-SB) | - | Stale analysis after a branch switch. |
| scala/bug#12414 | compiler | sealed, fruitless type test warning | partially: `Sealed.lean` (the relatedness check reads the hierarchy; a different answer when one side is unpickled is `¬ comp`) | no | Classify. |
| scala/scala3#23817 | compiler | GADT exhaustivity | GAP (comp) | - | |

### Implicits

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| sbt/zinc#945 | coverage | removing `implicit` from a method | partially: `Toy.lean` `implicitScope` key (`πRepaired i implicitScope` = the implicit members), `Examples.lean` `implicitAddition_*` | partially | Addition is the checked example; removal with a name hash that ignores the modifier is the abstraction variant not instantiated. |
| sbt/zinc#616 | compiler | implicit in empty-package package object | GAP (comp) | - | scalac never opens the empty package's package object from `package.class`. Pending test `default-namespace-implicit` is its scripted face. |
| sbt/zinc#1842 | coverage | annotations on definitions | covered: `Annotations.lean` `today_not_coverage` (the definition's `ctor` query to its annotation's class has no key); the fix `obligations_fix`, `fix_sound` | yes | `sym.annotations` visited by neither extractor. |
| sbt/zinc#237 | abstraction | annotations | covered: `HashForms.lean` `masking_237` (annotations dropped in one form mask a change) | yes | Phase travel to the wrong phase: a hash read from the wrong form. |

### Package objects, exports, top-level definitions

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| sbt/zinc#690 | policy | package object extending a trait with an inner class | GAP (K-IC) | - | Invalidation of `package.scala` follows the ancestor, not the ancestor's inner class. Inner classes are in the queue. |
| sbt/zinc#1268 (scala/bug#12887) | policy | deleting a source file, empty package | partially: `Added.lean` `deleted_today_clean` (deletion handled by the key on the resolved class) | no | The model says deletion is covered; the bug was the runner and `invalidateInitial` disagreeing. |
| scala/scala3#11514 | compiler | top-level overloads in different files | covered: `Names.lean` F5 `missedClash` (a double definition reported only when both files compile together), a `¬ comp` witness per REVIEW finding 3 | yes | The F5 shape with two top-level defs instead of a class and a package object member. |
| scala/scala3#10182 | coverage | `export` wildcard | covered: `DerivedApi.lean` `export_not_coverage` (before #10182 the exporter's `baseSig` query has no key); the fix `fix_sound`; also `Names.lean` F2 `export_added_today` | yes | The model has export forwarders as bindings the client reaches through no edge; the pre-#10182 desugaring that dropped every export edge is the extreme of that. |
| scala/scala3#18216 | coverage | `export` forwarder, signature change | partially: `DerivedApi.lean` (sound in one project with #10182's edge, so the failure is on the external path; stated, not proved), `Names.lean` F2 | partially | Two hops: `ModuleB`'s forwarder is derived from `ModuleA.func` across subprojects (K-EX). |
| scala/scala3#11841 | coverage | `export` in a trait | partially: `Names.lean` F2 with `inh` | partially | Not reproducible on 3.2.2. |
| scala/scala3#18767 | compiler | `export` and default arguments | GAP (comp) | - | |
| scala/scala3#4326 | coverage | package references | partially: `Names.lean` ("a package records nothing" is the modelled edge set) | no | Over-invalidation removed; precision. |

### Java interop and mixed compilation

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| sbt/zinc#127 | abstraction (naming) | Java inner classes, expanded names | covered: `Naming.lean` `spelling_bugs` | yes | `A.Inner` vs `A$Inner`: the key's unit spelled differently from the query's. |
| sbt/zinc#192 | coverage | Java anonymous and local classes | covered: `Sam.lean` `w192_pre` (Java before #217: an anonymous class records nothing) | yes |  |
| sbt/zinc#1351 | abstraction (naming) | Java nested classes, Scala 3 pipelining | covered: `Naming.lean` `spelling_bugs` | yes | Two names for one Java nested class, bridge vs `AnalyzingJavaCompiler`. |
| sbt/zinc#1812 (scala/scala3#27134) | coverage (naming) | Java class in the default package, Scala 3 | covered: `Naming.lean` `spelling_bugs`, `default_package_1812` (on `JavaSpec`'s instance) | yes | `<empty>.A` vs `A`: the edge `B -> <empty>.A` never joins `A`'s API; one spelling is the obligation (`coverage_named`). |
| sbt/zinc#1811 | policy | Java interface to abstract class, cycle with Scala implementor | partially: `JavaOrder.lean` `Mixed` group (a Java unit's queries to a Scala unit outside the round are answered from the state) | partially | The model recompiles `B` in round two; Zinc's javac fails in round one against stale `B.class`. Rounds that fail are K-SM. |
| sbt/zinc#867 | policy | Java sources, mixed project | partially: `JavaOrder.lean` (every Java source in every cycle as pipelining's policy) | no | Precision of a policy. |
| sbt/zinc#918 | snapshot | Java sources, pipelining | partially: `JavaOrder.lean` pipelining (Java outputs are source views until the final javac; a Java unit not passed to scalac has no view in the round) | partially | |
| sbt/zinc#1819 | abstraction | Java sources, pipelining | covered: `JavaOrder.lean` `flip_spurious` (stored classfile-view hash against fresh source-view hash), `exclusion_exact` | yes | The pending test `pipelining/java-comment-change` is the same case. |
| sbt/zinc#1311 | policy | mixed Java/Scala edits | GAP (K-SB) | - | `invalidationResults` reused: bookkeeping. |
| sbt/zinc#1182 | policy | transitive invalidation loop | partially: `Termination.lean` (`zinc_some_of_monotoneFrom`: a next round that keeps the previous round terminates), `PingPong.lean` `zinc_diverges` (Zinc's rule without `transitiveStep`) | partially | The fix (include recompiled classes in the next round) is the monotone regime; the exact pre-fix loop is not instantiated. |
| sbt/zinc#1553 | snapshot | Java and Scala class names differing only by case | covered: `Naming.lean` `collision` (two units read through one name cannot be served by any named oracle) | yes | Two units, one file on disk. |
| sbt/zinc#1493 | snapshot | Java compiled outside Zinc | partially: `Classpath.lean` stamp abstraction (equal stamps give equal answers) | partially | An external javac changes the answers under an unchanged stamp: the obligation names it, no witness. |
| sbt/zinc#974 | snapshot | Java sources, 2.13.4 | GAP (K-SB) | - | Concurrency bug. |
| scala/scala3#27133 | coverage | Java sources, `-Xjava-tasty` | partially: `JavaOrder.lean` (under pipelining a Java unit's keys come from the bridge's source view; units dropped before the phase that sends dependencies have none) | partially | A timing failure of coverage (K-M1). |
| sbt/zinc#1789 | policy | `JavaThenScala` with pipelining | covered: `JavaOrder.lean` JO-O2 `javaThenScala_not_comp`; pipelining with `JavaThenScala` rejected in `group` | partially | The model states why the order cannot be honoured; the rejection is the policy. |
| scala/bug#4390 | compiler | Java generic array override | covered: `JavaOrder.lean` JO-V1 `mixed_not_comp` (a Java class whose source and classfile views differ) | partially | Classify as `¬ comp` under `Mixed`; the view difference is abstract in the instance. |
| scala/bug#11569 | compiler | Java inner class, joint compilation | covered: `JavaOrder.lean` JO-V1 `mixed_not_comp` | yes | Exactly the two views: a path-dependent type from source, not from the classfile. |
| scala/bug#2889 | compiler | Java/Scala dependencies, 2.8 build manager | partially: `JavaOrder.lean` JO-V1 | no | Legacy. |

### Pipelining and early output

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| sbt/zinc#1843 | snapshot | pipelining, failed compile | covered: `PipelineLifecycle.lean` `stale_after_revert`, `rollback_preserves`, `rollback_detects` | yes | Proved for every interface and hash: the merged fix is the policy that keeps "published = built". |
| scala/scala3#27125 | policy (protocol) | pipelining, Scala 3.8.3 | covered: `MacroDeps.lean` `early_violates` (the analysis written before `Inlining` sends the dependencies has no keys); the handshake ordering is policy (`PLAN-macros.md`) | yes | Keys arrive after the decision that needs them: a time ordering between `keys` and `invalidated` the model does not have. |
| scala/scala3#27139 | snapshot (race) | pipelining, Java-only run | covered: `PipelineLifecycle.lean` `partial_write` (a cancelled write leaves an early output that never built; rolling it back restores the invariant) | partially | The dropped callbacks are an event order the model does not have. |
| scala/scala3#25520 | snapshot | pipelining, inlined anonymous class from a library | partially: `Classpath.lean` library keys (`(lib, whole)`, every query covered, hash the stamp) | no | A spurious library key is sound and imprecise (K-PB). |
| scala/scala3#26434 | snapshot | `libraryClassName` nondeterminism | partially: as #25520 | no | |
| scala/scala3#21594 | unknown | Scala 3.5.0 | GAP (unknown) | - | |
| sbt/zinc#1396 | policy | large Scala 3 project, local rename | partially: as #1461 (a body-only edit moves no key; the extra recompiles are #1284's rule) | no | Umbrella; precision. |

### Classpath, stamps, products

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| sbt/zinc#981 | snapshot | `-release` flag | GAP (K-PB) | - | A key on a classpath entry (`.sig` in ct.sym) that the next run cannot find: its stamp is "missing", which differs from any stamp. |
| scala/scala3#23689 | snapshot | `import scala.language.adhocExtensions` | GAP (K-PB) | - | A key on a class that does not exist. |
| scala/scala3#11360 | snapshot | constructor proxies | GAP (K-PB, K-C1) | - | A synthetic companion reported as a binary dependency. |
| scala/scala3#25722 | snapshot | annotation class removed from classpath | GAP (K-AN, K-SB) | - | Extractor crash. |
| sbt/zinc#716 | abstraction (naming) | long nested class names | covered: `Naming.lean` `spelling_bugs` | yes | Compactified classfile names vs recorded names. |
| sbt/zinc#1233 (scala/bug#12847) | snapshot | long nested class names | covered: `Naming.lean` `spelling_bugs` | yes | Products named un-compactified; the fix broke local classes. |
| sbt/zinc#449 | snapshot | names containing newlines | GAP (K-SB) | - | Analysis text format. |
| sbt/zinc#1234 | snapshot | stale classfiles, empty analysis | GAP (K-SB) | - | A deleted unit whose product stays on the classpath: `Added.lean`'s `absent` source could express a stale output answering for an absent unit; not done. |
| sbt/zinc#166 | snapshot | shadowing between external and binary deps | partially: `Classpath.lean` (upstream units and libraries as external units with their own keys) | partially | Which classpath entry answers a name is not a query; the model has no resolution order across entries. |
| sbt/zinc#608 | snapshot | reading a V1 analysis file | GAP (K-SB) | - | Format upgrade. |
| sbt/zinc#718 | unknown | whitespace change, Scala.js project | GAP (unknown) | - | |
| scala/scala3#4308 | snapshot | `-scansource` | GAP (K-SB) | - | Legacy. |
| scala/bug#2769 | snapshot | `-make`, empty source | GAP (K-SB) | - | Legacy. |
| scala/bug#354 | policy | ant, adding an abstract method | GAP (K-SB) | - | No dependency tracking at all: every key set empty, coverage fails trivially. Legacy. |

### Binary compatibility under separate compilation (compiler)

| bug | root cause | feature | covered by | predicts | note |
|---|---|---|---|---|---|
| scala/bug#1286 | compiler | trait and companion object in separate files | GAP (comp) | - | |
| scala/bug#1054 | compiler | trait method overridden in class | GAP (comp) | - | |
| scala/bug#1995 | compiler | traits with `-optimise` | GAP (comp) | - | |
| scala/bug#3918 | compiler | intersection type `T1 with T2` | partially: `Erasure.lean` intersection erasure with `kind` (trait vs class of `Z`) | partially | The instance has the exact input the compiler got wrong on an unloaded symbol; the wrong answer is `¬ comp`, which the instance would classify, not exhibit. |
| scala/bug#3038 | compiler | private lazy val | partially: `Flat.lean` P5 (a class parent's private members reach no descendant's bytecode) | no | The bitmap shared down the chain violates the model's assumption; classify. |
| scala/bug#3059 | compiler | lazy val bitmap | partially: as #3038 | no | |
| scala/bug#1105 | compiler | double-nested case class | GAP (comp) | - | |
| scala/bug#1122 | compiler | wrapper class referencing a Java map | GAP (comp) | - | |
| scala/bug#12085 | compiler | private inner class made non-private | GAP (comp) | - | `InnerClasses` flags from the end-of-pipeline view. |
| scala/scala3#26552 | compiler | trait with private inner class | GAP (comp) | - | |
| scala/scala3#26551 | compiler | TASTy sharing, mirrors, anonymous givens | partially: `InlineOpaque.lean`'s pickling artefact (a type prefix pickled differently when an object compiles apart from what it references; TASTy UUID differs, module class identical) | partially | The same kind of artefact, found by the harness and classified by `scripts/inline_opaque.py`. |
| scala/scala3#7661 | compiler | deterministic output | GAP (comp) | - | Umbrella. |
| scala/bug#10256 | compiler | final override of a vararg method | GAP (comp) | - | Order-dependent. |
| scala/bug#9948 | compiler | trait with `private[T] case class` | partially: `Flat.lean` P5 private trait members | no | Classify. |
| scala/scala3#25654 | compiler | covariant override of `private[pkg]` member | partially: `Erasure.lean` bridges (a bridge per overridden declaration whose erasure differs) | partially | A missing bridge under separate compilation is the bridge query answered differently: `¬ comp`. |
| scala/scala3#23863 | compiler | outer accessor of a trait's anonymous class | GAP (comp) | - | |

## 2. Pending and disabled scripted tests

On this branch (16 pending, 3 disabled).

| test | status | covered by | note |
|---|---|---|---|
| source-dependencies/false-error | pending | covered: `Cycles.lean` (inferred types in a cycle, `zinc_ne_clean`), `Uniqueness.lean` T3b, `PingPong.lean` | The intermediate-round failure is K-SM. |
| source-dependencies/new-cyclic | pending | partially: `Model.lean` `comp` (a cyclic-inheritance error only the joint build reports), `Uniqueness.lean` | The new edge is created by the edit; the error needs both files in one group. |
| source-dependencies/replace-test-a | pending | GAP (K-SB) | Products of a renamed top-level object; obsolete build file. |
| source-dependencies/relative-source-error | pending | n/a | sbt-level. |
| source-dependencies/cross-source | pending | n/a | sbt-level. |
| source-dependencies/abstract-class-to-trait | pending | partially: `Flat.lean` P3.6b (the kind in the header key recompiles descendants and moves a client's `invokevirtual`) | The expected failure is the round-one crash against the stale classfile (K-SM). |
| source-dependencies/module-inheritance-extra-hash-213-bin | pending | covered: `ExtraHash.lean` (#1795) | The bridge cannot report `object B` as a term: #1795's namespace on the callback. |
| source-dependencies/changedTypeOfChildOfSealed | pending | partially: `Sealed.lean`, `JavaSealedSpec.lean` `visited` keys | The exhaustiveness check reads the *child's* parents (match on a non-sealed `Base`); the modelled hash covers the parent's children. |
| source-dependencies/default-namespace-implicit | pending | partially: `Givens.lean` G1 (an implicit in a package object the client has no edge to), with the empty package | Plus the compiler side, #616. |
| source-dependencies/package-object-implicit | pending | covered: `Givens.lean` G1 `pobj_added_today_s2` | The package object is an added source here; the family's `added-implicit-package-object` adds the member. |
| source-dependencies/packageobject-and-traits | pending | covered: `Names.lean` F5 `missedClash` (a package object member and a class of one name, reported only jointly), here on Scala 2 | `¬ comp`; no key fixes it (REVIEW finding 3). |
| source-dependencies/import-package | pending | partially: `Names.lean` ("a package records nothing") | The package's own existence is not a query of the instance; adding it is a one-line slot. |
| source-dependencies/nested-type-params | pending | GAP (K-SM) | Alias chain through a projection on a singleton type (#476/#535). |
| source-dependencies/no-type-annotation | pending | covered: `Cycles.lean` `annotated_eq_clean`, `Uniqueness.lean` `fixpoint_unique_of_explicit` (the hypothesis the test violates: an inferred result type) | K-SM for the failing round. |
| source-dependencies/subproject-dependency-b | pending | GAP (K-IC) | An inner class's member across subprojects should not recompile the inheritor: precision of the inheritance key. |
| pipelining/java-comment-change | pending | covered: `JavaOrder.lean` `flip_spurious` | #1819's remaining spurious case; the cheapest fix is named in PLAN-order.md. |
| source-dependencies/binary-3 | disabled | covered: `Classpath.lean` library stamp keys | Disabled for the harness, not the model. |
| source-dependencies/canon | disabled | n/a | Symlinked jar path. |
| source-dependencies/inline | disabled | covered: `Inline.lean` `not_obligations_today` | sbt/zinc#537. |

Pending on side branches, already mapped by their families: name-resolution-pending (F2 `added-member-package-object`, `-scala3`, `added-member-top-level-export-scala3`; F3 `added-member-wildcard-import-second-class`, `-last-class-scala3`; F5 `package-object-member-clashes-with-class-scala3`; G1 `added-implicit-package-object`, `added-given-package-object-scala3`; G2 `added-given-top-level-scala3`; F6 `trait-initialiser-skipped-scala3`) in `Names.lean`/`Givens.lean`; inline-opaque-pending (I1 `inline-constant-path-scala3`, I2 `inline-constvalue-alias-scala3`, I3 `inline-transparent-reference-scala3`, O1 `opaque-type-mixin-forwarder-scala3`) in `InlineOpaque.lean`; java-names-pending (J1 to J4, S2, `java-added-class-inner-package-scala-client`, N1 `classof-used-name`) in `JavaSpec.lean`, `JavaSealedSpec.lean`, `JavaNames.lean`. All covered, except N1, which is checked only.

## 3. Gaps

Each cluster as a candidate phase: the observable as a query, what the bridge records today, the obligation expected to fail, the bugs it would have predicted, the tests it would explain, the size, and the kind of gap. Ranked by bugs explained weighted by recency (newest bug in the cluster); queue status in brackets. Cluster codes carry a `K-` prefix, to keep them apart from family IDs (`Cycles`' C1 and C2, `InlineOpaque`'s O1). Each entry's *Status* records what phases 15 to 28 have since closed; the rest of the entry is the gap as first written.

1. **K-C1 Constructor name mangling and synthetic case-class members.** *Status:* Phase 20 (`Synthetic.lean`) covers #97, #1324, #12401, #12898, #19910, #572 and #26231's abstraction half. 7 bugs, newest 2026: #97, #1324, #12401, #12898, #19910, #572, #26231's abstraction half. [In the queue: case classes and enums; overloads and default args.] Query: `ctor (C, clause list)`, `default (C, m, i)`, `apply`/`unapply`/`copy` of the synthetic companion, with the client's `new C(…)` and `C(…)` as the asking task. Today's keys: `C;init;` (Scala 2 since #288; Scala 3 since #12712, spelled with the package on one side until #19911), `<init>$default$N` (unmangled until #1324), the synthetic companion skipped by `API` until #572, the synthetic `unapply` with signature `(C): C` until #26262. Failing obligation: abstraction on `(C, init)` (all constructors one key: over; a key whose hash ignores a clause: under) and coverage on the spelling of the key's unit (#19910). Tests explained: value-class-underlying, constructors-unrelated(-2), default-params, default-arguments-separate-compilation(-210), case-classes-no-companion, naha-synthetic, nested-case-class, named. Size: small (a `TreeToy`-style instance with one class, two constructors and defaults; `π` with and without mangling; the definition/use spelling as two `keys` functions that must agree). Bridge gap (abstraction, coverage).

2. **K-N Class naming agreement between the bridge and Zinc.** *Status:* Phase 16 (`Naming.lean`) covers all eight (#19910 through Phase 20); #11360 stays with K-PB. 8 bugs, newest 2026: #1812 (`<empty>.A` vs `A`), #1351 (Java nested classes under pipelining), #127 (expanded names), #9694 (inner class `associatedFile`), #716 and #1233 (compactified names), #1553 (case-insensitive filesystems), #19910 (shared with K-C1); #11360 (shared with K-PB). [Not in the queue.] Query: any; the gap is in `Query := CUnit × Q` and `Key := CUnit × K` assuming one spelling of a unit. Today: the bridge spells units one way (`binaryDependency`, `classDependency`, `generatedNonLocalClass`), Zinc another (`ClassToAPI`, `productClassName`, the filesystem). Failing obligation: coverage, `q.1 = k.1` false on spelling, so the key exists and never joins the query. Tests explained: java-inner, malformed-class-name(-with-dollar), compactify, compactify-nested(-class), unexpanded-names, package-object-nested-class, recorded-products, java-name-with-dollars. Size: small (a `spell : Side → CUnit → String` per side in `TCompiler`, the agreement as an obligation, one witness per bug). Bridge gap (coverage).

3. **K-SM Stale middle file, alias chains, cyclic inference.** *Status:* Phase 15 (`Cycles.lean`) covers the inference half (#1284, false-error, no-type-annotation) and #1780's retry on cycles (partially); the alias half and failing rounds remain gaps (#269, #476, #535, #598). 5 gap bugs plus 8 partial, newest 2026: #476, #535, #598, #1780, #269 (gaps); #1284 (covered by T3b), #1461, #1332, #1420, #1417, #1396, #1811, false-error (partial). [In the queue: cyclic inference, REVIEW finding 2 covers the inference half; the alias/dealiasing half and failing rounds are not queued.] Queries: `alias (T)` and `dealias (prefix#T)` for the coverage half (the prefix of a projection is lost after typer, #269/#476); for the policy half the round itself, which today is total: `group` must be allowed to fail when a unit's answers come from a stale interface (#535, #598, #1811), and Zinc's retry (#1780) is a policy on that failure. Today's keys: memberRef on the owner of the dealiased symbol; Zinc's initial invalidation does not include unchanged classes on a path between changed ones (#1284's rule, reverted by #1462). Failing obligations: coverage (alias prefix); T3b uniqueness for the inference cycle (false-error, no-type-annotation), and `comp` read on a partial group whose output is a failure rather than a fixed point. Tests explained: abstract-class-to-trait, false-error, no-type-annotation, nested-type-params, new-cyclic (all five pending), expanded-type-projection, type-alias, typeref-return, check-recompilations, transitive-a. Size: large (a `Task` that can fail, a policy that reads failure, aliases with prefixes in the toy; the inference part is the small phase of the review). Zinc policy gap (the crash and the retry) and bridge gap (dealiasing); the harness would check the predicted T3a-holds-T3-fails case.

4. **K-H1 Hash stability across forms (source, pickle, classfile).** *Status:* Phase 17 (`HashForms.lean`) covers all six; #1794 through Phase 23. 6 gap bugs plus 2 partial, newest 2026: #1782, #88, #18080, #9133, #9730, #237 (gaps); #1794 (partial), #1819 (covered by `JavaOrder.lean` for Java). [Not in the queue.] Observable: none new; `π` must be a function of the interface, and these bugs are cases where `Iface` as the bridge sees it carries a form artefact (a `fullName` through a refinement owner, an identity hash, a synthetic evidence name, a phase-travelled annotation list). Today: the API is extracted from whichever form the compiler has (source in the round, unpickled otherwise), and hashes differ across runs with no edit. Failing obligation: abstraction's converse, as over-invalidation on every run; the framework has no statement of it (REVIEW finding 4's precision). `JavaOrder.lean`'s two-view instance is the shape: generalise `java sv cv` to a Scala unit with a source view and a TASTy/pickle view, and state that `π` must agree across the views the next run compares. Tests explained: abstract-type-override, type-lambda-refinement-owner, unstable-existential-names, trait-extends-trait-extra-round, trait-local-change, fbounded-existentials, pipelining/java-comment-change. Size: small to medium (reuse `JavaOrder`'s structure; one witness per bug; a precision definition to state the over-invalidation). Bridge gap (abstraction).

5. **K-M1 Macro dependency timing and expansion references.** *Status:* #23783 is now partial through Phase 18; #20119 is still a gap. Phase 22 (`MacroDeps.lean`, `PLAN-macros.md`): covered #1478, #22999, #27125, #23852, #18100, #1282, #1333; partially #249 (Scala 2's bridge), #27133 (Java units' dependencies, not modelled); still a gap #20119 (pipelined compositionality) and #23783 (annotation arguments, K-AN). New prediction: a macro that reflects a private member of its type argument is stale under today's `api` key (`private_today`, an abstraction failure); candidate pending test `macro-reflects-private-member-scala3`.

6. **K-C2 extraHash lineage and the companion namespace.** *Status:* Phase 23 (`ExtraHash.lean`) covers #662, #1793, #1794, #1795, #1796 and the pending test; Phase 25 (`Companions.lean`) adds the companion pairs of retronym/zinc#56. 3 gap bugs plus 3 partial, newest 2026: #1793, #1795, #1796 (gaps); #542 (covered by `Flat.lean` P5), #662, #1794 (partial). Pending test module-inheritance-extra-hash-213-bin. [Not in the queue; Phase 9 future names #1796.] Queries: `fields (t)` and `privates (t)` from a class mixing trait `t` in directly (already in `Flat.lean`), now with `t` resolved in the type namespace and its companion in the term namespace. Today's keys: one `extraHash` per `AnalyzedClass` (class and companion merged, #1793), inheritance edges as plain strings (#1795), one name hash per simple name across both sides (#1796). Failing obligation: abstraction (two members or two classes under one hash) and coverage with an over-wide `covers` (the trait half assumed to inherit). Tests explained: trait-private-* (7), module-inheritance-extra-hash(-213-bin), companion-object-extra-hash, trait-extends-trait-extra-round, trait-local-change, empty-modified-names. Size: medium (a term/type tag on `CUnit` in `Flat.lean`'s instance; the `extraHash` as a stored summary with the fold, as `ImplicitScope.lean` already does for implicit scopes; the cold/warm theorem reused). Bridge gap (coverage: `AnalysisCallback4`'s namespace) and Zinc-side key design (the merged hashes).

7. **K-AN Annotations as API and as dependencies.** *Status:* Phase 18 (`Annotations.lean`) covers #1842 and, with `MacroDeps`, #22999; #237 through Phase 17; #23783 partial; #25722 (a crash) is still a gap. 4 gap bugs, newest 2026: #1842, #23783, #22999, #237; #25722 (crash). [Not in the queue.] Queries: `annots (sym)` and `annotArg (sym, i)` asked by a client (a macro, a derivation, `-Xcheckinit`-style behaviour, Java's retention) and by the API of the annotated definition. Today: Scala 2 visits neither in `Dependency` nor `ExtractUsedNames` (annotations live only in `sym.annotations` after typer), and `ExtractAPI` hashes them from the wrong phase (#237). Failing obligation: coverage (no edge to `Ann`, to its constructor's constants, to a Java `@interface`), abstraction (#237). Tests explained: annotations-in-java-sources-a/a2/b, annotations-in-java-params, specialized, annotation-ctor-change-class-3 (pending per the catalogue). Size: small. Bridge gap (coverage, abstraction).

8. **K-PL Pipelining early-output lifecycle.** *Status:* Phase 19 (`PipelineLifecycle.lean`) proves #1843's invariant and covers #27139 (`partial_write`); #27125 through Phase 22; #20119 is still a gap. 3 gap bugs plus 2 partial and 1 covered, newest 2026: #27139, #27125 (shared with K-M1), #20119 (gaps); #918 (partial); #1843 (covered as a checked example on `Snapshot`'s compiler; REVIEW finding 8 asks for it on Phase 14's instance). [Not in the queue beyond P14.4.] Observable: the early output as a second interface with a lifecycle (written, published, rolled back, cancelled) and the callbacks `apiPhaseCompleted`/`dependencyPhaseCompleted` as events the downstream and Zinc wait on. Today: no rollback (#1843), no guarantee the callbacks fire (#27139), the dependency callback before the dependencies (#27125). Failing obligation: the run invariant "published = built" (now `PipelineLifecycle.Published`), and coverage in time. Tests explained: pipelining/* (15), trait-java-parent-pipelining-3. Size: medium (an event order on `round`; the then `Pipelining.lean` facts restated as theorems, done as `PipelineLifecycle.lean`). Snapshot gap.

9. **K-PB Phantom binary dependencies and library attribution.** *Status:* Unchanged. 3 gap bugs plus 2 partial, newest 2026: #981, #23689, #11360 (gaps); #25520, #26434 (partial through `Classpath.lean`'s library keys). [Not in the queue.] Observable: a key on a classpath entry that does not exist (`.sig` under `-release`, `scala.language$adhocExtensions$`, a constructor-proxy companion) or on the wrong entry (an inlined library class attributed to a jar). Today: `binaryDependency` reports whatever file the compiler's symbol table names; Zinc stamps it, finds it missing or in a different jar, and invalidates every run. Failing obligation: stamp abstraction with a "missing" stamp that differs from every stamp; precision for the misattribution. Tests explained: anon-class-dep (`checkNumberOfLibraries`), binary, binary-3. Size: small (`Classpath.lean` with an `absent` library and a key whose owner is not on the classpath). Snapshot gap.

10. **K-L1 Local and anonymous classes, SAM lambdas.** *Status:* Phase 28 (`Sam.lean`) covers #830 and #192; #1528 is still a gap (a statement for the files layer). 3 gap bugs, newest 2025: #1528, #830, #192. [In the queue: SAM conversion.] Queries: the inheritance walk and forwarder queries of `Flat.lean` asked by a local or anonymous class, or by a lambda converted to a SAM type, on behalf of the enclosing class. Today: `LocalDependencyByInheritance`, invalidated but not propagated; no edge for a SAM lambda until #1288; `memberRef ⊇ inheritance` as an invariant of the relations, broken by dropping local dependencies (#1528). Failing obligation: coverage (the lambda's inheritance key), and the policy invariant stated as a hypothesis of `transitiveStep`'s theorem. Tests explained: local-class-inheritance, sam-local-inheritance, sam, anon-java-scala-class, local-class-inheritance-from-java, trait-private-val-local-inheritance, anon-class-java-depends-on-scala, inner-class-java-depends-on-scala. Size: small (`Flat.lean` with a `local` flag on a descendant and a policy that does not propagate through it). Bridge gap (coverage) and Zinc policy gap (#1528).

11. **K-IC Inner and path-dependent classes.** *Status:* #9694's spelling half is covered by Phase 16; #690 and subproject-dependency-b remain. 2 gap bugs plus 1 pending test, newest 2020: #690, #9694 (shared with K-N); subproject-dependency-b; #11569 (covered by `JavaOrder.lean` JO-V1). [In the queue: inner/path-dependent classes.] Queries: a member of an inner class reached through the outer (`O.Inner.m`), the outer's invalidation when the inner is invalidated (#690's package object). Today: inner classes are units of their own with their own name hashes; invalidation of a package object follows its ancestors only. Failing obligation: policy (#690), coverage on the unit's spelling (#9694), precision (subproject-dependency-b). Tests explained: class-based-inheritance, java-inner, package-object-name-inner, type-member-nested-object, as-seen-from-a/b, subproject-dependency-b. Size: small to medium. Zinc policy gap and bridge gap (naming).

12. **K-MR Mirrors and derivation.** *Status:* Unchanged. 2 gap bugs, newest 2024: #13028, #22178. [In the queue as part of case classes and enums.] Query: `mirror (T)` answering `T`'s fields (product) or children (sum), asked by `summon[Mirror.Of[T]]` inside a derivation, recursively for field types (#22178); synthesized after `ExtractDependencies` ran. Today: #18310 records a dependency when the mirror is synthesized; the recursive summons were missed until #24969. Failing obligation: coverage (a post-typer query), the `TreeToy.lean` shape. Tests explained: none (Scala 3 `derives` is untested). Size: small. Bridge gap (coverage).

13. **K-EX Exports as derived API.** *Status:* Phase 21 (`DerivedApi.lean`) covers #10182; #18216 is partial (the cross-subproject path is stated, not proved); #11841 partial; #18767 is `comp`. 1 gap bug plus 3 partial, newest 2023: #18767 (compiler); #10182, #18216, #11841 (partial through `Names.lean` F2). [Not in the queue beyond F2's pending test.] Query: `forwarder (B, f)` whose answer is derived from `A.f`'s signature: a non-local hash on `B` reading `A` (`NonLocal.lean`). Today: the exporting class records inheritance on the exported object (#10182); its forwarders' signatures are its own API, refreshed only when it recompiles. Failing obligation: coverage across the second hop (`ModuleC` reads `B`'s forwarder, `B` not recompiled for `A`'s arity change in another module). Tests explained: added-member-top-level-export-scala3 (pending on a side branch). Size: small (an `NCompiler` instance with `hashDeps B = {A}`). Bridge gap (coverage) or Zinc policy (invalidate exporters as inheritors across projects).

14. **K-U1 Used types' supertypes and structural members.** *Status:* Phase 21 (`DerivedApi.lean`) covers #87; scala/bug#2558 (structural types) is still a gap. 2 gap bugs, newest 2016: #87, #2558. [Not in the queue.] Query: `parents (A1)` and `member (A1, n)` asked about the *type of an answer* (`B.x : A1`) the client received without naming `A1`; and the members a structural type names. Today: #87 added the types in trees to used names, which covers the first hop; a structural type's member names are used names too. Failing obligation: coverage for a query on a unit the trace reached through an answer. Tests explained: types-in-used-names-a/b, struct, struct-usage, struct-projection, variance. Size: small (`Hier.lean` with a client that passes a received value where a supertype is expected). Bridge gap (coverage), mostly closed; worth stating because every later "types in used names" decision rests on it.

15. **K-FI Files as recompilation units.** *Status:* Phase 26 (`Files.lean`) covers #417 and F3; #1268 is partial. 1 gap bug plus the F3 family and 1 partial, newest 2017: #417; F3's pending tests; #1268 (partial). [Not in the queue; REVIEW finding 5.] Observable: none new; `file : CUnit → File`, rounds closed under files, imports charged to one class of the file. Today: Zinc recompiles files, invalidates classes, and charges a top-level import to the first (Scala 2) or last (Scala 3) class. Failing obligation: coverage, when a key is charged to a class of the file that is not the one whose trace has the query (F3); #417's filter dropped same-file inheritance keys. Tests explained: same-source-transitive-invalidation(-trait), class-based-inheritance, class-based-memberRef, trait-private-val-member-ref, same-file-used-names, added-member-wildcard-import-second-class, added-member-wildcard-import-last-class-scala3. Size: medium (a framework layer). Zinc policy gap (file rounds) and bridge gap (charging).

Unclustered. `comp` (compiler joint-vs-separate): 23 bugs with no instance (#1286, #1054, #1995, #1105, #1122, #12085, #26552, #7661, #10256, #23863, #13190, #12927, #13468, #17601, #22684, #13121, #20136, #1561, #13994, #616, #23817, #18767, #22456), 8 classified by an existing instance (#3918, #3038, #3059, #9948, #25654, #26551, #12414, #8580). The model should only classify these; the harness, which compares classfiles, is the tool that finds them, and a phase that enumerates separate-compilation orders over an existing space (every subset of a base as the group) would turn the classification into a prediction. K-SB (snapshot bookkeeping, formats, legacy, unknowns): #653, #25273, #1311, #974, #449, #1234, #608, #4308, #2769, #354, #998, #718, #21594; #1234 is the one worth a witness (`Added.lean`'s `absent` unit with a stale product still answering).

Queue items with no gap row: import renames and given priority, Phase 27 (no catalogued bug; two predicted tests fail on develop, retronym/zinc#58); extensions and implicit classes, Phase 24 (#13085 partial; four predicted tests fail on develop, retronym/zinc#53); cyclic inference, Phase 15 (K-SM above).

## 4. Model feeds back: predicted variants with no test and no bug

For each phase that covers bugs, variants its instance predicts that appear in neither catalogue. One line each: name, edit, expected miss. Checked families that already have a pending test (F1 to F6, G1 to G3, I1 to I3, O1, J1 to J4, S1, S2, N1) are not repeated.

Phase 10, `Names.lean`/`Added.lean` (retronym/zinc#34 and the split layout):
- `added-class-inner-package-upstream`: client in `app`, `package a; package b`, resolves `a.Foo` from `lib`; a new file in `lib` adds `a.b.Foo`. Miss: #34's rule runs over `lib`'s analysis and finds no user; `app`'s external invalidation diffs only recorded classes (DESIGN-spec's failed coverage for the coarse key).
- `renamed-class-into-wildcard-package-upstream`: as above with `a.q.Bar` renamed to `a.q.Foo` behind `import a.q._` in `app`. Miss: same.
- `added-top-level-def-shadows-outer-object-scala3`: client in `package a; package b` calls `Foo()` (object `a.Foo` with `apply`); an existing `a/b/defs.scala` (`b$package`) gains `def Foo(): String`. Miss: F2's mechanism with a plain top-level def in an existing `$package` class, which #34 (top-level classes) and the F2 extension (package objects) both skip.

Phase 2/3/5/6, `Hier.lean`, `Flat.lean`, `Erasure.lean` (forwarders, bridges, erasure inputs):
- `erasure-intersection-mixin-forwarder`: `trait T { def m(x: W with Z): Unit = () }`, `class K extends T`, `Z` a trait made a class. Miss: `T` recompiles (it names `Z`) but its API renders `W with Z` by name; `K`'s mixin forwarder keeps descriptor `(LW;)V` (sbt/zinc#1844's closing comment, the model's 2,176 runs needing `kind` in the class-name hash).
- `erasure-intersection-bridge`: `class K extends T` overriding `m(x: W with Z)` with `Z` made a class. Miss: the bridge pair's descriptors change; `K` is not recompiled.
- `value-class-mixin-forwarder-scala3`: `trait T { def m(v: V): Int = 1 }`, `object K extends T`, `V(u: Int)` becomes `V(u: Long)`. Miss: `K`'s forwarder keeps `(I)I` (P6.5's PoC-only test, no Scala 3 value-class test exists).
- `erasure-bridge-upstream-grandparent-scala2`: `lib`: `class M[T] { def m: T }`, `class A extends M[Int]`; `app`: `class B extends A { override def m: Int }`; edit `A extends M[String]`. Miss: Scala 2's as-seen-from rendering of `B`'s inherited `m` does not move for `app`'s external diff (P6.2's 864 runs).
- `macro-observes-private-member`: a macro reads `c.tpe.decls` of `C` including `private val p: Int`; `p`'s type changes. Miss: no API records a private member; no key covers the observation (P5's PoC finding).
- `macro-observes-asf-type-arg-change`: a macro observes `B.m` as seen from `B` (`B extends A[Int]`, `A.m: T`) and records the name only; edit `A[Long]`. Miss: Scala 3's per-name hashes do not move; the macro did not record `(B, cls)` (P6.4).

Phase 7, `ImplicitScope.lean`:
- `implicit-scope-companion-inherits-scala2-parent-scala3`: `object C extends L` with `L` from a Scala 2 artefact, `L` gains `implicit def sl: Show[C]`; a client summons `Show[C]`. Miss: Scala 3's `ExtractAPI` skips Scala2x ancestors, so the inherited implicit is not in object `C`'s name hashes (`inhNames := false`, P7.7's 120 runs).
- `implicit-scope-ancestor-companion-type-argument-upstream`: `lib`: `A`, `object A { implicit def sa[T <: A]: Show[List[T]] }`, `class B extends A`; `mid`: `class C extends B`; `app`: `implicitly[Show[List[C]]]`; edit adds `object B { implicit def sb[T <: B]: Show[List[T]] }`. Miss: as #1845 through a type argument across three projects (the `W` client, a layout the fix branch's tests do not run).

Phase 11, `InlineOpaque.lean` and `Inline.lean`:
- `inline-reads-java-constant-scala3`: `inline def k = J.K` with `J.java`'s `static final int K`; edit `K`. Miss: the folded constant leaves no name (I1 with a Java owner); with pipelining the source view does not fold it, so pipelined and non-pipelined clients differ (`pipelined_ne_final`).
- `opaque-type-through-alias-mixin-forwarder-scala3`: `object O { opaque type T = Int }`, `object A { type S = O.T }`, `trait Tr { def h(t: A.S): Int = 1 }`, `class K extends Tr`; edit `T = Long`. Miss: O1 through an alias, where `Tr` names `A` not `O`, so even the owner's class-hash route to `Tr` is cut; two hops with no key on either.
- `inline-transparent-given-member-type-scala3`: `transparent inline given g: Show[D] = ...` whose body calls `h`, `h`'s result type changes. Miss: I3 for a given; the probed `inline given` case was clean because the implicit member itself changed, which this edit avoids.

Phase 12/14, `JavaSpec.lean`, `JavaSealedSpec.lean`, `JavaOrder.lean`:
- `java-failed-compile-leaves-classfile`: a Java edit that fails after javac wrote `Bar.class` (a rename in the inner package), then reverted. Miss: the next build compiles nothing and the stale product stays (PLAN-java's "besides", 26 reverts on develop).
- `java-constant-expression-source-view-3`: `static final int K = 1 << 3` read by a Scala client, Scala 3 with pipelining, `Mixed`. Miss: the source view does not fold the constant expression (scala/scala3#27264), so the client compiled in the Java class's batch differs from one compiled alone against the classfile (JO-V1), and from a non-pipelined build (JO-V2).
- `java-object-parent-view-2`: Scala 2 client in a `Mixed` round with a Java class whose parent is typed `ObjectTpeJava` from source (scala/scala#11292); an overload or `==` whose selection depends on it. Miss: JO-V1, bytes differ between the joint round and the lone recompile.
- `java-sealed-nested-permits-pipelining`: S2 with pipelining on. Miss: unchanged with pipelining (`T` in its own file is still not a dependency of the Scala client); the one Java family pipelining does not hide.
- `java-static-import-class-api-change`: Java client with `import static a.X.Foo` using only the method; `X` gains an unrelated member. Expected: no recompile under #43's import edge (a precision check of the fix, not a miss).

Phase 8/9, `TreeToy.lean`, `PingPong.lean`, `Snapshot.lean`:
- `assign-op-member-added`: `x += 1` with `x: A`; `A` gains `def +=`. Miss: the client keeps `x = x + 1` (the failed lookup of `+=` left nothing in the tree).
- `dynamic-select-member-added`: `class D extends Dynamic { def selectDynamic(n: String) }`, client `d.foo`; `D` gains `def foo`. Miss: the tree has `selectDynamic("foo")`, the literal is not a used name.
- `inferred-type-cycle-rounds`: `A.x = B.y`, `B.y = C.z`, `C.z = Some(A.x)`, `transitiveStep = 6`; edit `C`. Expected: pairs rotate for six cycles and the cyclic-inference error appears only at the brute-force round (confirmed on a retronym/zinc branch, not in the corpus).
- `stale-product-after-deleted-source-empty-analysis`: #1234's shape as a scripted test with the model's `absent` unit: delete `B.scala` with an empty previous analysis, `A` uses `B`. Miss: `B.class` stays and `A` compiles.

Phase 1/7 implicits, `Toy.lean`, `Givens.lean`:
- `implicit-modifier-removed-conversion`: `implicit def c(a: A): B` loses `implicit`, the client uses the conversion without naming `c` and names no changed member. Miss: #945's shape with a conversion rather than a value; the model's `implicitScope` key says the client must be invalidated.
- `given-priority-companion-vs-package-level-scala3`: a given in the client's own package (`$package`) and one in `T`'s companion; delete the package-level one. Expected: resolution moves to the companion; the model's levels say the client records nothing for the `$package` binding (G2's deletion direction).

## 5. Summary counts

Counted from the rows above (phases 1 to 28).

Catalogued bugs (145): covered 56, partially 38, GAP 50 (24 tagged `comp`, 11 K-SB, 3 unknown, 12 in other clusters), n/a 1 (sbt/zinc#238). Predicts: `yes` 52, `partially` 26, `no` 16. `yes` is counterfactual (the instance has a witness with the bug's trace); most instances of phases 15 to 28 were built after the bug they cover, so it does not count predictions made before a bug was known.

By root cause (covered / partially / GAP):

| root cause | rows | covered | partially | GAP |
|---|---|---|---|---|
| coverage | 38 | 18 | 13 | 7 |
| compiler | 34 | 3 | 9 | 22 |
| abstraction | 23 | 23 | 0 | 0 |
| policy | 22 | 5 | 11 | 6 |
| snapshot | 20 | 4 | 5 | 11 |
| compositionality | 4 | 3 | 0 | 1 |
| unknown | 3 | 0 | 0 | 3 |
| not a bug | 1 | n/a | | |

By phase (a bug counted once, at the first-named instance of its row; a row that says "as #N" counts with #N's):

| phase | files | covered | partially |
|---|---|---|---|
| 1 core | `Soundness`, `Termination` | 0 | 6 (#1461, #1332, #1420, #1417, #1182, #1396) |
| 1 toy | `Toy` | 1 (#95) | 1 (#945) |
| 2 | `Hier` | 1 (#174) | 0 |
| 3/5 | `Flat` | 2 (#542, #1171) | 4 (#168, #3038, #3059, #9948) |
| 6 | `Erasure` | 1 (#51) | 3 (#1798, #3918, #25654) |
| 7 | `ImplicitScope` | 2 (#1845, #1846) | 1 (#18309) |
| 8 | `Classpath`, `Inline`, `TreeToy` | 2 (#26231, #537) | 5 (#8580, #1493, #25520, #26434, #166) |
| 9 | `Added`, `Sealed` | 1 (#12634) | 2 (#12414, #1268) |
| 10 | `Givens`, `Names` | 1 (#11514) | 4 (#9087, #13085, #11841, #4326) |
| 11 | `InlineOpaque` | 1 (#11861) | 1 (#26551) |
| 12 | `JavaSealedSpec` | 0 | 2 (#753, #1229) |
| 14 | `JavaOrder` | 4 (#1819, #1789, #4390, #11569) | 5 (#1811, #867, #918, #27133, #2889) |
| 15 | `Cycles` | 1 (#1284) | 1 (#1780) |
| 16 | `Naming` | 7 (#9694, #127, #1351, #1812, #1553, #716, #1233) | 0 |
| 17 | `HashForms` | 6 (#1782, #88, #18080, #9133, #9730, #237) | 0 |
| 18 | `Annotations` | 1 (#1842) | 1 (#23783) |
| 19 | `PipelineLifecycle` | 2 (#1843, #27139) | 0 |
| 20 | `Synthetic` | 6 (#97, #1324, #12401, #12898, #19910, #572) | 0 |
| 21 | `DerivedApi` | 2 (#87, #10182) | 1 (#18216) |
| 22 | `MacroDeps` | 7 (#1282, #1333, #1478, #23852, #18100, #22999, #27125) | 1 (#249) |
| 23 | `ExtraHash` | 5 (#662, #1794, #1793, #1795, #1796) | 0 |
| 26 | `Files` | 1 (#417) | 0 |
| 28 | `Sam` | 2 (#830, #192) | 0 |

Pending and disabled tests (19): covered 8 (false-error, module-inheritance-extra-hash-213-bin, package-object-implicit, packageobject-and-traits, no-type-annotation, java-comment-change, binary-3, inline), partially 5 (new-cyclic, abstract-class-to-trait, changedTypeOfChildOfSealed, default-namespace-implicit, import-package), GAP 3 (replace-test-a, nested-type-params, subproject-dependency-b), n/a 3 (relative-source-error, cross-source, canon). The side-branch families are covered, except N1, which is checked only.

Remaining GAP rows by cluster: `comp` 24 (no phase; the model classifies them), K-SB 11 (no phase), K-SM 4 (#269, #476, #535, #598: alias prefixes and failing rounds), K-PB 3, unknown 3, K-MR 2, K-L1 1 (#1528), K-U1 1 (scala/bug#2558), K-IC 1 (#690). Rows with two tags are counted once: #20119 (K-PL, `comp`) under `comp`, #25722 (K-AN, K-SB) under K-SB, #11360 (K-PB, K-C1) under K-PB. Clusters K-C1, K-C2, K-N, K-H1, K-AN, K-PL, K-EX and K-FI have no GAP row left of their own.
