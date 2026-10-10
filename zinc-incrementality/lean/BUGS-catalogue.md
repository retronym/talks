# Catalogue of incremental-compilation bugs

Historical bugs in Zinc, the Scala 2 and Scala 3 compiler bridges, and the compilers themselves that bear on incremental or separate compilation. Collected from sbt/zinc, scala/scala3 and scala/bug issue and PR threads, for a Lean model of Zinc's invalidation.

Columns:

- kind: `under` (undercompilation: stale output, missing error, runtime linkage error), `over` (unnecessary recompilation), `bytes-differ` (joint and separate compilation produce different output), `crash` (the incremental build fails where a clean one succeeds).
- root cause, in model terms:
  - `coverage`: the bridge failed to record a dependency or a used name.
  - `abstraction`: the API hash failed to reflect something a client depends on, or reflects something it should not.
  - `compositionality`: joint and separate compilation differ in the compiler itself.
  - `policy`: Zinc's invalidation or cycle logic dropped (or over-included) something although the recorded facts were right.
  - `snapshot`: the stamp, classpath, product or early-output bookkeeping was wrong.
  - `compiler`: a non-incremental compiler bug that only shows up under incremental or separate compilation.
- fix: the PR that closed it, or `none`.
- test: a Zinc or scala3 scripted test named in the thread.

## Constructors, case classes, default arguments

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| sbt/zinc#97 | 2016 | closed | over | constructor params | abstraction: every constructor is named `<init>`, so any constructor change invalidates every client of the class | sbt/zinc#288 (name becomes `Class;init;`) | value-class-underlying |
| sbt/zinc#1324 | 2024 | merged | over | default args | abstraction: `<init>$default$N` was not mangled with the class name after #288, so unrelated default-argument getters collide | sbt/zinc#1324 | |
| scala/scala3#12401 | 2021 | closed | under | constructor params | abstraction: the Scala 3 bridge did not mangle constructor names, so adding a parameter clause did not change any name the client used; `NoSuchMethodError` at runtime | scala/scala3#12712 | |
| scala/scala3#12898 | 2021 | closed | under | constructor params | abstraction: same as #12401 (adding a parameter) | scala/scala3#12712 | |
| scala/scala3#19910 (sbt/zinc#1334) | 2024 | closed | under | constructor params | abstraction: `zincMangledName` on the definition side included the package, the use side did not, so the hashes never matched; the existing scripted test had no package and passed | scala/scala3#19911 | |
| sbt/zinc#572 | 2018 | merged | under | case class synthetic companion, default args, package object | coverage: `API` skipped synthetic top-level trees, so the synthesized companion's `apply` had no name hash and `A(1)` clients were never invalidated; also fixed package objects introduced in a change | sbt/zinc#572 | packageobject-and-traits |
| sbt/zinc#238 | 2017 | closed | under | case class synthetic companion | not a bug: adding an explicit `private object A` was expected to break `A(1)` but the compiler accepts it | none | naha-synthetic |
| scala/scala3#26231 | 2026 | closed | under | pattern matching, case class | coverage: `ExtractDependencies` runs before `PatternMatcher`, so `_1`, `_2`, `unapply`/`unapplySeq` calls are never used names; abstraction: the synthetic `unapply` has signature `(C): C` whatever the fields, so field changes never move its hash; `NoSuchMethodError` | scala/scala3#26262 | |

Note on #26262: the fix records `C;init;` for synthetic case-class unapplies (the mangled constructor name encodes the whole parameter list), pre-registers both `unapply` and `unapplySeq`, and watches `_N+1` for product extractors.

## Inheritance, traits, companions

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| sbt/zinc#417 | 2017 | closed | under | trait inheritance (cake pattern) | coverage: the bridge filtered inheritance edges between classes in the same source file, a source-level assumption left over from sbt 0.13; with class-level invalidation the transitive chain broke; `AbstractMethodError` | sbt/zinc#424 | |
| sbt/zinc#542 | 2018 | merged | under | trait private members | abstraction: private trait members change the subclass bytecode (fields, accessors) but not the public API hash; introduced `extraHash` and `TraitPrivateMembersModified`, invalidating inheritors only | sbt/zinc#542 | trait-private-val, trait-private-var, trait-private-object |
| sbt/zinc#662 | 2019 | closed | under | trait private members across projects | compositionality: `C extends B extends A` in three projects; `B` is recompiled but its API is unchanged, so `C` in the third project is not; fixed by folding parent `extraHash` into the child's | sbt/zinc#1289 | |
| sbt/zinc#1794 | 2026 | closed | over | trait extraHash | abstraction: the parents folded into `extraHash` came from the previous analysis, so a cold build and the next warm build hashed the same trait differently and a comment edit recompiled inheritors | sbt/zinc#1799 | |
| sbt/zinc#1793 | 2026 | closed | over | companion object | abstraction: one `AnalyzedClass` per companion pair, and `extraHash` merged the object's hash, so adding a member to `object A` recompiled everything extending `trait A` | sbt/zinc#1801 | |
| sbt/zinc#1795 | 2026 | closed | over | companion trait vs object | coverage: `classDependency("A","B",Inheritance)` carries plain strings, so `object B extends A` and `trait B extends A` are indistinguishable and the trait half is assumed to inherit | needs `AnalysisCallback4` (term/type namespace) | |
| sbt/zinc#1796 | 2026 | open | over | companion members with the same name | abstraction: `nameHashesForCompanions` merges the name hashes of class and object, so `class A.x` and `object A.x` share one hash | none | |
| sbt/zinc#1798 | 2026 | closed | over | compound type in signature | coverage: `AnyRef with B` in a member type is a `CompoundTypeTree` wrapping a `Template`, which the Scala 2 traverser recorded as inheritance of `B` | sbt/zinc#1803 | |
| sbt/zinc#998 | 2021 | closed | over | inheritance, JDK 11 | unknown: not diagnosed in the thread; `B` invalidated by transitive inheritance after an unrelated `println` change, only on JDK 11 | none linked | |
| sbt/zinc#1528 | 2025 | merged | under | local classes | policy: local dependencies were dropped from `memberRef`, breaking the invariant `memberRef ⊇ inheritance` that transitive invalidation relies on | sbt/zinc#1528 | |
| sbt/zinc#830 | 2020 | closed | under | SAM lambda, Java interop | coverage: a lambda implementing a SAM type is a subclass of it but no inheritance edge was recorded; changing the Java interface's method type left the lambda alone | sbt/zinc#1288, scala/scala#10617, scala/scala3#16996 | |
| sbt/zinc#168 | 2016 | open | over | trait compiles to interface (2.12) | policy: since 2.12 most trait method changes need no forwarder in subclasses, so inheritance invalidation could be skipped; never implemented | none | |
| sbt/zinc#1845 | 2026 | open | under | implicit scope of ancestors' companions, multi-project | compositionality: in one project `MemberRefInvalidator` reaches clients of inheritors; across projects the downstream only checks the external classes it recorded, and `C`'s API does not include `B`'s companion | sbt/zinc#1845 (open) | |
| sbt/zinc#1846 | 2026 | open | under | implicit scope of an object's singleton type | compositionality: the published implicit-scope summary followed only the class side's parents, not the object side's | sbt/zinc#1846 (open) | implicit-scope-object-singleton-companion |
| scala/scala3#18309 | 2023 | open | under | using-clause on constructor, multi-module | coverage: the implicit chosen for a constructor's using parameter changes in an upstream module and the downstream call site is not invalidated; `NoSuchMethodError` | none | |
| scala/scala3#9087 | 2020 | closed | under | multiversal equality `Eql` given, multi-module | coverage: adding `given Eql[...]` instances in an upstream module makes `EUR == CHF` an error on a clean build, but the downstream file is not recompiled | none linked | |
| scala/scala3#9694 | 2020 | merged | under | inner class, separate compilation | coverage: the binary class name sent via `binaryDependency` was taken from `associatedFile`, which for an inner Scala class is the top-level classfile, so inner-class dependencies were never recorded | scala/scala3#9694 | |

## Type members, aliases, projections, dependent types

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| sbt/zinc#174 | 2016 | closed | under | type members, as-seen-from | coverage: a refinement of `type T` in a subclass changes the effective signature of inherited `foo(x: T)`, but clients only record a use of `foo`; design thread for inheritance expansion vs name hashing | sbt/zinc#239 | |
| sbt/zinc#269 | 2017 | closed | under | type projection, dealiasing | coverage: scalac dealiases the projection after typer so the prefix is lost; fixed by traversing original type trees | sbt/zinc#272 | |
| sbt/zinc#476 | 2018 | open | under | `A.type#B#C` alias chain | coverage: changing `type Operations = A` to `= B` does not invalidate a client that only names `Foo.provide`; recovered only when the middle file is also recompiled | sbt/zinc#1284 (reverted by #1462), sbt/zinc#1780 (open) | nested-type-params |
| sbt/zinc#535 | 2018 | open | crash | type alias in type projection | policy: the invalidated set cannot compile on its own because scalac dealiases aggressively against the stale classfile of an unchanged middle class | sbt/zinc#1780 (open) | nested-type-params |
| sbt/zinc#598 | 2018 | open | crash | abstract class to trait | policy: `Z -> Y -> X`, `X` and `Z` change, `Y` is unchanged; round one compiles `Z` against `Y`'s stale classfile and the backend asserts `Invalid superClass` | sbt/zinc#1284 (reverted by #1462), sbt/zinc#1780 (open) | abstract-class-to-trait |
| sbt/zinc#1284 | 2023 | merged | under | cyclic deps, initial invalidation | policy: also invalidate classes that both depend on and are depended on by an invalidated class, so the stale middle file is recompiled in round one | sbt/zinc#1284 | abstract-class-to-trait, false-error, no-type-annotation, nested-type-params |
| sbt/zinc#1461 | 2024 | closed | over | cyclic deps (unused import) | policy: #1284 recompiled every direct mutual dependency on any change, and only 2-cycles, not longer ones | sbt/zinc#1462 (revert of #1284; four scripted tests moved to pending) | |
| sbt/zinc#1332 | 2024 | closed | over | cyclic deps, non-API change | policy: same as #1461; closed as working as intended at the time | sbt/zinc#1462 | |
| sbt/zinc#1420 | 2024 | closed | over | Scala 3, initial invalidation | policy: an extra cycle on the first compile after a clean build, caused by #1284's mutual-dependency rule | sbt/zinc#1462 | |
| sbt/zinc#1417 | 2024 | closed | over | generic type as member parameter type | policy: comment-only change recompiles a second file on both Scala 2 and 3; closed with #1461/#1420 | sbt/zinc#1462 | |
| sbt/zinc#1780 | 2026 | open | crash | bridging classes | policy: only on failure of the first round, add the unchanged classes on any dependency path between changed classes and retry once | sbt/zinc#1780 (open) | abstract-class-to-trait, false-error, no-type-annotation, nested-type-params |
| sbt/zinc#1561 (scala/scala3#23573) | 2025 | open | crash | dependent type with type-lambda bound | compiler: `m.F[String][Int]` found and required are printed identically but do not unify after a whitespace change to the client | none | |
| scala/scala3#13190 | 2021 | closed | crash | opaque type, match type | compiler: `TreeUnpickler` passed `TypeParamRef`s instead of type parameter symbols to `opaqueToBounds`, so the unpickled opaque type did not reduce | scala/scala3#13206 | |
| scala/scala3#12927 | 2021 | closed | crash | opaque type, pickling | compiler: same unpickler bug as #13190 | scala/scala3#13206 | |
| scala/scala3#13468 | 2021 | closed | crash | opaque type with type parameter | compiler: `Container[Int]` instead of `Container[8]` after uncommenting a line; fixed in the meantime, regression test added | scala/scala3#26309 | |
| scala/scala3#17601 | 2023 | closed | crash | match type, singleton bound | compiler: a meaningless change to the second file makes the compiler loop in `narrowVariances` on the unpickled match type | fixed upstream (2025) | |
| scala/scala3#22684 | 2025 | open | crash | match type, given | compiler: `No given instance` on incremental build only, when the object's parent is a match type; works if the definitions file is recompiled first | none (not reproducible on 3.6.3) | |
| scala/scala3#13121 | 2021 | open | crash | implicit search order (opaque, export, extension, inline) | compiler: clean compile fails to find an implicit that incremental compile finds; depends on typing order | none | |
| scala/scala3#20136 | 2024 | closed | crash | match type and implicit conversion, separate compilation | compiler: regression from #19871; joint compiles, separate does not reduce `ExtractValue[E]` | fixed upstream | |
| scala/scala3#22456 | 2025 | closed | crash | `tracked val`, skolem type | coverage: `ExtractDependencies` threw `Unhandled type` on a `SkolemType` | fixed upstream | |
| sbt/zinc#1782 | 2026 | merged | over | type lambda, refinement type parameters | abstraction: `ExtractAPI.tparamID` named a refinement-owned type parameter by `fullName`, which differs between source (`test.<refinement>.a`) and unpickled form, so every class built on the lambda re-hashed each compile | sbt/zinc#1782 | type-lambda-refinement-siblings |
| sbt/zinc#88 | 2016 | closed | over | refinement-typed val | abstraction: a spurious `override` modifier flickered on refinement members between source and unpickled form (scala/bug#7361); no longer reproduces, regression guard only | sbt/zinc#1720 | |
| scala/scala3#18080 | 2023 | closed | over | context bounds | abstraction: synthetic names of context-bound evidence parameters changed between compiles, so the API of every method with a context bound churned | fixed upstream | |
| scala/scala3#9133 | 2020 | merged | over | signatures | abstraction: phases before erasure can change a definition's owner and thus its full name, so signatures were unstable; always use the initial symbol | scala/scala3#9133 | |
| scala/bug#2558 | 2009 | closed | under | structural type | coverage: the 2.8 build manager did not record a dependency from a structural-type use site to the member it names; won't fix (build manager deprecated) | none | |
| sbt/zinc#87 | 2016 | merged | under | used types, supertypes | coverage: only names in trees were used names; a member whose type's supertypes changed (`B.x: A1`, `A1`'s parents change) did not invalidate the client | sbt/zinc#87 | |
| sbt/zinc#95 | 2016 | merged | under | value class | abstraction: after #87 the erased and unerased signature trick is unnecessary; `extends AnyVal` changes the class's name hash and underlying changes move `<init>` | sbt/zinc#95 | |
| sbt/zinc#51 | 2016 | closed | under | erasure | abstraction: forward-port of sbt/sbt#2261 hashing both pre- and post-erasure signatures; superseded | sbt/zinc#54 | |

## Inline and macros

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| sbt/zinc#537 | 2018 | closed | under | `-opt:l:inline` (Scala 2 optimizer) | abstraction: an inlinable method's body is part of its effective API, but only the signature is hashed; stale inlined code | none (documented; Scala 3 hashes inline bodies) | |
| scala/bug#8580 | 2014 | closed | bytes-differ | `@inline` in empty package, separate compilation | compiler: bytecode of the callee not found under separate compilation, so inlining silently fails | fixed upstream | |
| scala/scala3#9730 | 2020 | merged | over | inherited inline def | abstraction: the API of an inherited inline def included `toString` of a lazy tree reader, which prints an identity hash that changes every run | scala/scala3#9730 | |
| scala/scala3#11861 | 2021 | closed | under | nested private inline def | abstraction: the hash of an inline def did not include the bodies of inline defs it calls, so changing `private inline def foo` did not reach callers of `inline given`; `sbt/zinc#1000` is the same | scala/scala3#12931 | |
| scala/scala3#13994 | 2021 | closed | crash | inline def in object whose file has another name, `-sourcepath` | compiler: inline context not initialised in `lateEnter`, `None.get` in `PrepareInlineable` on the second round | scala/scala3#14050 | |
| scala/scala3#13085 | 2021 | open | under | extension method moved between files, inline | coverage: moving a top-level extension method to another file in the same package leaves an inline caller's client uncompiled, `Not Found` on the next build | none | |
| sbt/zinc#249 | 2017 | open | under | Scala 2 macros | coverage: meta issue for macro-tracker based dependency recording; never merged | none | |
| sbt/zinc#1171 | 2023 | closed | under | Scala 2 macro with type parameter (mainargs) | coverage: a macro inspecting `T` reads members Zinc never records as used; fixed by `DependencyByMacroExpansion` on type arguments of macro calls | sbt/zinc#1316 | macro-type-change-3 (pending: cross-project case) |
| sbt/zinc#1282 | 2023 | merged | under | Scala 2 macro implementation change | policy: invalidate macro classes that transitively depend on any recompiled class, since expansion depends on behaviour, not API; only within one project | sbt/zinc#1282 | |
| sbt/zinc#1333 | 2024 | closed | over | clients of a macro user | policy: #1282 recompiles dependents of any class that merely uses a macro when a non-macro dependency changes | none (accepted cost) | |
| sbt/zinc#1478 | 2024 | open | under | Scala 3 macros | coverage: request to port #1282/#1316 to 2.13 and 3 | partly by scala/scala3#23900, #24969 | |
| scala/scala3#23852 (sbt/zinc#1574) | 2025 | closed | under | Scala 3 macro calling a constructor (macwire) | coverage: `sbt-deps` ran before `Inlining`, so symbols referenced only by the expansion were never recorded; `NoSuchMethodError` | scala/scala3#24969 (move dependency phase after inlining), scala/scala3#23900 (type arguments) | |
| scala/scala3#18100 | 2023 | closed | under | Scala 3 macro reached through another method | coverage: same as #23852 | scala/scala3#24969 | |
| scala/scala3#22178 | 2024 | closed | under | `Mirror` of a nested case class through derivation | coverage: changing `case class Test` did not invalidate `Labels.derived[Deps]` where `Deps` has a `Test` field; the recursive mirror summons were not recorded | scala/scala3#24969 | |
| scala/scala3#23783 | 2025 | open | under | macro reading an annotation argument | coverage: the macro inspects `@MyAnnot("Hello")` on `Foo`; changing the argument changes nothing Zinc tracks for `Foo` (see also sbt/zinc#1842) | none | |
| scala/scala3#22999 | 2025 | open | under | macro annotation `transform` body change | coverage: no dependency from the annotated definition to the annotation's `transform` method | scala/scala3#25128 (open) | |
| scala/scala3#20119 | 2024 | closed | crash | macros with pipelining | compositionality: with early TASTy output a spurious `Cyclic macro dependencies` error between files that compile fine without pipelining | fixed upstream | |

## Sealed hierarchies, pattern matching, mirrors

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| scala/scala3#13028 | 2021 | closed | under | `Mirror`, circe derivation | coverage: `summon[Decoder[AAA]]` depends on the synthesized `Mirror.Of[AAA]`, which is not in the tree at `ExtractDependencies`; changing a field type did not recompile the client | scala/scala3#18310 (record dependencies when the mirror is synthesized) | |
| scala/scala3#12634 | 2021 | closed | under | sealed children | coverage: adding a child to a sealed hierarchy did not invalidate the exhaustive match; port of sbt/zinc#979 (`sealedDescendants`) | scala/scala3#12636 | |
| sbt/zinc#753 | 2020 | closed | under | sealed, `useOptimizedSealed`, 2.13 | coverage: on 2.13 `patmat` runs after `xsbt-api`, so untranslated patterns reach `ExtractUsedNames` and the sealed parent was registered in `Default` scope, not `PatMat` | sbt/zinc#1278 | patMat-scope |
| sbt/zinc#1229 | 2023 | closed | under | sealed, `useOptimizedSealed`, 2.13 | coverage: same as #753; adding a child did not recompile the match | sbt/zinc#1278 | patMat-scope |
| sbt/zinc#653 | 2019 | open | under/over | used-name extraction on 2.13 | coverage: after the patmat phase reorder, `acme.Tupler` no longer records `acme`, and spurious names (`package`, `Class`, `Sealed`) appear | partly by sbt/zinc#1278 | |
| scala/scala3#25273 | 2026 | open | crash | sealed, branch switch | snapshot: stale analysis after switching branches reports `Cannot extend sealed class Either in a different source file` | none | |
| scala/bug#12414 | 2021 | closed | bytes-differ | sealed, fruitless type test warning | compiler: the relatedness check for two sealed traits gave a different answer on an incremental build (one unpickled) than on a clean one; affects `-Xfatal-warnings` | scala/scala#9668 | |
| scala/scala3#23817 | 2025 | closed | bytes-differ | GADT exhaustivity | compiler: `MakeTuple[T <: Tuple]` reported inexhaustive only under separate compilation | scala/scala3#23966 | |

## Implicits

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| sbt/zinc#945 | 2020 | open | under | removing `implicit` from a method | coverage: a client that resolved the implicit records a use of its name, whose hash is unaffected by dropping the modifier; the old implicit keeps being used | none | |
| sbt/zinc#616 | 2018 | closed | crash | implicit in empty-package package object | compiler: scalac never opens an empty-package package object read from `package.class` (scala/bug#10927); Zinc records the dependency correctly | none (fixed in Scala 3) | |
| sbt/zinc#1842 | 2026 | open | under | annotations on definitions | coverage: after typer annotations live only in `sym.annotations`, which neither `Dependency` nor `ExtractUsedNames` visited; `@Ann(1) class S` had no edge to `Ann`, nor to constants used as annotation arguments, nor to Java `@interface`s | sbt/zinc#1842 (open) | annotation-ctor-change-class-3 (pending) |
| sbt/zinc#237 | 2017 | merged | over | annotations | abstraction: `ExtractAPI#annotations` phase-travelled to after typer instead of entering typer, a transcription slip during the class-based name hashing port | sbt/zinc#237 | |

## Package objects, exports, top-level definitions

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| sbt/zinc#690 | 2019 | closed | crash | package object extending a trait with an inner class | policy: Zinc invalidates `package.scala` when an ancestor is invalidated, but not when an inner class of the ancestor is; scalac then reports `Symbol 'type X' is missing from the classpath` | sbt/zinc#983 | package-object-name-inner |
| sbt/zinc#1268 (scala/bug#12887) | 2023 | closed | under | deleting a source file, empty package | policy: the `empty-package` scripted test passes under Zinc's scripted runner but fails in a real sbt project and in scala/scala's runner; a deleted source's dependents were not invalidated | fixed in Zinc 1.10 | empty-package |
| scala/scala3#11514 | 2021 | closed | bytes-differ | top-level overloads in different files | compiler: clashing top-level `def foo` in two files is an error jointly but not separately, so it is only caught after `clean` | fixed upstream | |
| scala/scala3#10182 | 2020 | merged | under | `export` wildcard | coverage: export clauses were desugared before `ExtractDependencies`; kept until `FirstTransform` and recorded as inheritance | scala/scala3#10182 | |
| scala/scala3#18216 | 2023 | open | under | `export` forwarder, signature change | coverage: `ModuleC` imports `func` via `ModuleB`'s `export ModuleA.*`; changing `func`'s arity in `ModuleA` does not recompile `ModuleB`'s forwarders, so `ModuleC` sees the old signature | none | |
| scala/scala3#11841 | 2021 | open | under | `export` in a trait | coverage: adding a method to the exported object and using it through the trait fails with `Not found` until `clean`; not reproducible on 3.2.2 | none | |
| scala/scala3#18767 | 2023 | open | bytes-differ | `export` and default arguments | compiler: default getters of exported methods are not honoured when the exporter is unpickled from another module | none | |
| scala/scala3#4326 | 2018 | merged | over | package references | coverage: packages were recorded as dependencies; now ignored, but package objects kept | scala/scala3#4326 | |

## Java interop and mixed compilation

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| sbt/zinc#127 | 2016 | closed | crash | Java inner classes, expanded names | abstraction (naming): `Failed to find name hashes for A.Inner` because the API used expanded names | sbt/zinc#431 | |
| sbt/zinc#192 | 2016 | closed | under | Java anonymous and local classes | coverage: not handled by class-based name hashing | sbt/zinc#217 | |
| sbt/zinc#1351 | 2024 | closed | crash | Java nested classes, Scala 3 pipelining | abstraction (naming): `ExtractAPI` in Scala 3 and `AnalyzingJavaCompiler` in Zinc named a Java nested class differently, so `Can't find source file for a.A.Inner_sel` | scala/scala3#20279 | pipelining/Yjava-tasty-fromjavaobject, Yjava-tasty-paths, inline-rec-mut, false-error |
| sbt/zinc#1812 (scala/scala3#27134) | 2026 | closed | under | Java class in the default package, Scala 3 | coverage (naming): the bridge named a Java class `<empty>.A` while Zinc registered it as `A`, so `B -> <empty>.A` never joined and adding an abstract method left `B` unrecompiled; `AbstractMethodError` | scala/scala3#27136 | |
| sbt/zinc#1811 | 2026 | open | crash | Java interface to abstract class, cycle with Scala implementor | policy: cycle 1 invalidates only `A.java`, so `compileScala` is a no-op and javac fails against stale `B.class` before cycle 2 can invalidate `B`; originally sbt/sbt#1327 (2014) | none | |
| sbt/zinc#867 | 2020 | closed | over | Java sources, mixed project | policy: every cycle re-invalidated all Java sources (added for `-Ypickle-java` pipelining), triggering a second cycle | sbt/zinc#868, sbt/zinc#899 | |
| sbt/zinc#918 | 2020 | closed | crash | Java sources, pipelining | snapshot: after #912 stopped passing unchanged Java sources to scalac, the second cycle failed with `not found: type ScriptConfig` because the Java symbols were neither in source nor on the classpath | sbt/zinc#920 (revert) | |
| sbt/zinc#1819 | 2026 | closed | over | Java sources, pipelining | abstraction: with pipelining javac runs last, so scalac's view of `J`'s API (from source) is stored and later compared to the classfile-derived API, which never compares equal; every change recompiled all dependents of Java classes | sbt/zinc#1821 (do not compare APIs of unchanged Java sources) | |
| sbt/zinc#1311 | 2023 | closed | over | mixed Java/Scala edits | policy: `invalidationResults` reused to compute the next invalidation after #1182, over-including on mixed edits | sbt/zinc#1312 | |
| sbt/zinc#1182 | 2023 | merged | crash | transitive invalidation loop | policy: an infinite compile loop; fixed by including recompiled classes in the next round's invalidation (sbt/zinc#1120, sbt/sbt#6183) | sbt/zinc#1182 | |
| sbt/zinc#1553 | 2025 | open | crash | Java and Scala class names differing only by case | snapshot: on a case-insensitive filesystem the two classfiles collide, `cannot find symbol` and `Failed to find name hashes`; renaming does not recover without `clean` | none | |
| sbt/zinc#1493 | 2024 | open | under | Java compiled outside Zinc | snapshot: a Java class recompiled by plain `javac` between two Zinc runs in one JVM is not seen as changed; Zinc has no API for externally compiled sources | none | |
| sbt/zinc#974 | 2021 | closed | crash | Java sources, 2.13.4 | snapshot: `ConcurrentModificationException` in `ClassToAPI.process` while reading Java classfiles under 2.13's mutation tracker | fixed | |
| scala/scala3#27133 | 2026 | closed | under | Java sources, `-Xjava-tasty` | coverage: after #24969 dependencies are sent from `Inlining`, but Java units are dropped after `sbt-api`, so a pipelined project's analysis lacks all dependencies of its Java sources | fixed upstream | |
| sbt/zinc#1789 | 2026 | merged | crash | `JavaThenScala` with pipelining | policy: pipelining defers javac, so the order cannot be honoured; now rejected (sbt/sbt#9707) | sbt/zinc#1789 | |
| scala/bug#4390 | 2011 | closed | bytes-differ | Java generic array override | compiler: overriding `T[] create()` needs `Array[T with Object]` under separate but `Array[T]` under joint compilation | fixed upstream | |
| scala/bug#11569 | 2019 | open | bytes-differ | Java inner class, joint compilation | compiler: Scala gives a Java inner class a path-dependent type when the Java source is in the run, not when read from a classfile; found testing Spark with `-Ypickle-java` | none | |
| scala/bug#2889 | 2010 | closed | bytes-differ | Java/Scala dependencies, 2.8 build manager | compiler: `JavaB does not have a constructor` on a clean build, gone after incremental edits | legacy | |

## Pipelining and early output

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| sbt/zinc#1843 | 2026 | open | under | pipelining, failed compile | snapshot: early output (pickle jar and early analysis) is written before the compile is known to succeed and never rolled back on failure; downstream compiles against signatures that never compiled, with no error on 2.12 | sbt/zinc#1843 (open) | |
| scala/scala3#27125 | 2026 | closed | under | pipelining, Scala 3.8.3 | policy (protocol): after #24969 `dependencyPhaseCompleted` fires from the background TASTy writer before `Inlining` sends the dependencies, so Zinc decides what to recompile with none | scala/scala3#27135 | |
| scala/scala3#27139 | 2026 | closed | under | pipelining, Java-only run | snapshot (race): the run can end and cancel the async TASTy write, dropping `apiPhaseCompleted`/`dependencyPhaseCompleted` and some TASTy files; downstream `Not found: type J` | scala/scala3#27141, sbt/zinc#1823 (workaround) | |
| scala/scala3#25520 | 2026 | closed | over | pipelining, inlined anonymous class from a library | snapshot: `Symbol.copy` ignored its compilation-unit argument, so a class inlined from a library was reported as a binary dependency on that jar; Zinc 1.x keeps one class per jar and the order varied, so it was intermittent | scala/scala3#27162 | |
| scala/scala3#26434 | 2026 | closed | over | `libraryClassName` nondeterminism | snapshot: same mechanism as #25520 | scala/scala3#27162 | |
| scala/scala3#21594 | 2024 | closed | over | Scala 3.5.0 | unknown: regression confined to 3.5.0 (not RC7, not 3.5.1); cause not identified in the thread | fixed in 3.5.1 | |
| sbt/zinc#1396 | 2024 | open | over | large Scala 3 project, local rename | policy: umbrella report (>400 files on a local variable rename); follow-ups #1417, #1420 | partly by sbt/zinc#1462 | |

## Classpath, stamps, products

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| sbt/zinc#981 | 2021 | closed | over | `-release` flag | snapshot: binary dependencies recorded as `/8/java/lang/String.sig` from the ct.sym filesystem are not found on the classpath on the next run and are invalidated as modified | fixed | |
| scala/scala3#23689 | 2025 | open | over | `import scala.language.adhocExtensions` | snapshot: `scala.language$adhocExtensions$` is recorded as a binary dependency on scala-library but no such class exists, so the jar is invalidated every build | none | |
| scala/scala3#11360 | 2021 | merged | over | constructor proxies | snapshot: the fake companion holding constructor proxies was reported via `binaryDependency`, Zinc looked for a nonexistent `Namer$.class` and invalidated every run | scala/scala3#11360 | |
| scala/scala3#25722 | 2026 | closed | crash | annotation class removed from classpath | snapshot: `ExtractAPI` crashed on an annotation whose class is no longer on the classpath | scala/scala3#25889 | |
| sbt/zinc#716 | 2019 | closed | over | long nested class names, `-Xmax-classfile-name` | abstraction (naming): compactified classfile names did not match the names Zinc recorded, so the file was always invalidated | sbt/zinc#1259 | |
| sbt/zinc#1233 (scala/bug#12847) | 2023 | closed | crash | long nested class names | snapshot: Zinc reported un-compactified classfile names as products; the first fix phase-travelled to after `flatten` and broke local classes (pekko) | sbt/zinc#1259 | |
| sbt/zinc#449 | 2017 | merged | crash | names containing newlines | snapshot: the analysis text format broke on a used name containing a newline | sbt/zinc#449 | |
| sbt/zinc#1234 | 2023 | closed | crash | stale classfiles, empty analysis | snapshot: with an empty previous analysis stale `.class` files were not deleted and stayed on the classpath | fixed | |
| sbt/zinc#166 | 2016 | closed | under | shadowing between external and binary deps | snapshot: a class added to a project output that shadows the same name in a jar did not invalidate the sources that referenced the jar's class (with `analysisOnlyExtDepLookup`) | sbt/zinc#175, revert of #165 | |
| sbt/zinc#608 | 2018 | closed | crash | reading a V1 analysis file | snapshot: `extraHash` was set to `apiHash` for non-traits when upgrading the format, tripping `different extra api hashes for no traits` | sbt/zinc#581 | |
| sbt/zinc#718 | 2019 | closed | over | whitespace change, Scala.js project | unknown: not minimised; unrelated files recompiled after a newline edit from sbt 1.1.5 on | none linked | |
| scala/scala3#4308 | 2018 | closed | over | `-scansource` | snapshot: `needCompile` compared last-modified times only | legacy | |
| scala/bug#2769 | 2009 | closed | over | `-make`, empty source | snapshot: the 2.8 `-make` build manager recompiled a file that produces no classfiles every time | legacy | |
| scala/bug#354 | 2008 | closed | under | ant, adding an abstract method | policy: pre-Zinc build tools did not track dependencies at all | none | |

## Binary compatibility under separate compilation (compiler)

| id | year | state | kind | feature | root cause | fix | test |
|---|---|---|---|---|---|---|---|
| scala/bug#1286 | 2008 | closed | bytes-differ | trait and companion object in separate files | compiler: `IncompatibleClassChangeError: Implementing class` when the pair is compiled separately | fixed upstream | |
| scala/bug#1054 | 2008 | closed | bytes-differ | trait method overridden in class | compiler: `Found interface Actor, but class was expected` in 2.7.2 trunk | fixed upstream | |
| scala/bug#1995 | 2009 | closed | bytes-differ | traits with `-optimise` | compiler: implementation classes loaded by the front end gave a broken `$init$` signature | fixed upstream | |
| scala/bug#3918 | 2010 | closed | bytes-differ | intersection type `T1 with T2` | compiler: `erasure.intersectionDominator` tested `isTrait` on an unloaded symbol, so the erased return type differed; `NoSuchMethodError` | fixed upstream (r23506) | |
| scala/bug#3038 | 2010 | closed | bytes-differ | private lazy val | compiler: the lazy-val bitmap is shared down the inheritance chain, so adding a private lazy val in a parent breaks separately compiled subclasses | fixed upstream | |
| scala/bug#3059 | 2010 | closed | bytes-differ | lazy val bitmap | compiler: `bitmap$0` is emitted in `A` jointly but reused from `B` separately; caused spurious change notifications | fixed upstream | |
| scala/bug#1105 | 2008 | closed | crash | double-nested case class | compiler: broken classfile on a fresh recompile of the same file | fixed upstream | |
| scala/bug#1122 | 2008 | closed | crash | wrapper class referencing a Java map | compiler: `malformed Scala signature ... refers to nonexisting symbol` on the second file | fixed upstream | |
| scala/bug#12085 | 2020 | closed | bytes-differ | private inner class made non-private | compiler: `InnerClasses` access flag reflected the end-of-pipeline privacy, which differs when the trait is unpickled | scala/scala#9131 | |
| scala/scala3#26552 | 2026 | open | bytes-differ | trait with private inner class | compiler: Scala 3 member order and `InnerClasses` attribute differ for the subclass compiled alone (the Scala 3 counterpart of #12085) | scala/scala3#26572 (closed, unmerged) | |
| scala/scala3#26551 | 2026 | open | bytes-differ | TASTy sharing, mirrors, anonymous givens | compiler: `SHAREDtype` addresses depend on type identity, so TASTy and the embedded UUID differ when `CC` is unpickled; part of #7661 | none | |
| scala/scala3#7661 | 2019 | open | bytes-differ | deterministic output | compiler: umbrella for Scala 3 output stability under reordering and separate compilation (scalac's was scala/scala-dev#405) | partial | |
| scala/bug#10256 | 2017 | open | bytes-differ | final override of a vararg method | compiler: `VerifyError: overrides final method` depending on compilation order | none | |
| scala/bug#9948 | 2016 | open | bytes-differ | trait with `private[T] case class` | compiler: `AbstractMethodError` for the companion accessor when the subclass is compiled separately | none | |
| scala/scala3#25654 | 2026 | closed | bytes-differ | covariant override of `private[pkg]` member | compiler: 3.8.3 regression, no JVM bridge method when the subclass is in another package and compiled separately; `AbstractMethodError` | fixed upstream | |
| scala/scala3#23863 | 2025 | closed | bytes-differ | outer accessor of a trait's anonymous class | compiler: `AbstractMethodError` for `$outer` under separate compilation (reported as a Scalatest/macro incremental problem) | fixed upstream | |

## Patterns

Rows: 145 (sbt/zinc 74, scala/scala3 52, scala/bug 19). States: closed 90, merged 19, open 36.

Root causes, by count:

1. coverage, 38. The bridge did not record a fact. The recurring shapes: trees that exist only after the extraction phase (pattern-match selectors, macro expansions, mirrors, SAM lambdas, exports, annotations in `sym.annotations`), synthetic members (case-class companion, constructor proxies), names that do not match between bridge and Zinc (`<empty>.A`, Java nested classes, compactified names), and dealiased types whose original prefix is gone.
2. compiler (non-incremental bug surfacing under separate compilation), 34. Mostly classfile-level: lazy-val bitmaps, `InnerClasses` attributes, bridges for covariant overrides, erasure of intersections; and typer-level order dependence (match types, opaque types, implicits).
3. abstraction, 23. The hash reflects the wrong thing: constructors all named `<init>`, `extraHash` merged across companions or taken from a stale analysis, inline bodies not hashed, unstable synthetic names (context bounds, refinement type parameters, identity hashes in `toString`), Java APIs compared across source and classfile views, compactified names.
4. policy, 22. Right facts, wrong decision: same-source inheritance ignored, the stale-middle-file problem (#598/#476/#535, fixed by #1284, reverted by #1462, reopened by #1780), Java sources re-invalidated each cycle, javac run alone in cycle 1 (#1811), macro clients over-invalidated by design (#1282/#1333), the pipelining callback protocol (#27125).
5. snapshot, 20. Classpath and product bookkeeping: `.sig` entries from `-release`, nonexistent `$` classes, stale classfiles not deleted, early output not rolled back, intermittent library attribution, case-insensitive filesystems, analysis format edge cases.
6. compositionality, 4 (plus the compiler rows that are joint-vs-separate by nature). Facts that do not cross a project boundary: trait private hashes (#662), implicit scope of ancestors' companions (#1845/#1846), using-clause implicits (#18309), `Eql` givens (#9087).
7. unknown 3, not a bug 1.

Kinds: under 56, over 35, crash 32, bytes-differ 22.

Rows per section: type members, aliases, cycles and name stability 28; Java interop and mixed compilation 18; inheritance, traits and companions 17; inline and macros 17; binary compatibility under separate compilation 16; classpath, stamps and products 14; constructors and case classes 8; sealed and mirrors 8; package objects and exports 8; pipelining 7; implicits 4.

Two clusters account for most of the 2023-2026 activity:

- Scala 3's `ExtractDependencies` running too early. Macro expansions (#23852, #18100, #22178), pattern-match selectors (#26231) and mirrors (#13028) were all invisible at `sbt-deps`. Moving the phase after `Inlining` (#24969) fixed the macro cases but broke the pipelining protocol (#27125, #27133, #27139) and `-Ydump-sbt-inc` (#25125).
- `extraHash` for traits. Introduced for private members (#542), extended across projects by folding in parents (#1289), which then produced cold/warm hash mismatch (#1794) and companion conflation (#1793), fixed by #1799/#1801; #1795 and #1796 remain because the callback cannot tell a term name from a type name.

Still open:

- Undercompilation: sbt/zinc#945 (implicit modifier removed), sbt/zinc#476 (alias chain), sbt/zinc#1811 (Java interface to abstract class in a cycle), sbt/zinc#1493 (Java compiled outside Zinc), sbt/zinc#1845 and #1846 (implicit scope across projects, PRs open), sbt/zinc#1842 (annotations, PR open), sbt/zinc#1843 (early output rollback, PR open), scala/scala3#18309 (using-clause implicits), #13085 (moved extension method), #18216 and #11841 (exports), #23783 and #22999 (macro annotations and annotation arguments), sbt/zinc#249 and #1478 (macro tracking generally).
- Overcompilation: sbt/zinc#1796 (companion name hashes), sbt/zinc#168 (traits as interfaces), sbt/zinc#1396 (umbrella), scala/scala3#23689 (`adhocExtensions` binary dep), sbt/zinc#653 (2.13 used names).
- Crash under incremental build: sbt/zinc#535 and #598 (stale middle file; #1780 open), sbt/zinc#1553 (case-insensitive names), sbt/zinc#1561 (type lambda bound), scala/scala3#22684, #13121, #25273.
- Joint vs separate output: scala/scala3#7661, #26551, #26552, scala/bug#10256, #9948, #11569, scala/scala3#18767.
