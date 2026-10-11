# Zinc scripted test corpus, catalogued for the Lean model

Source: `zinc/src/sbt-test` on `scratch/cheapfix-conformance` (develop plus the conformance harness and the fix "Invalidate the users of an added class's simple name"). 208 tests in the five suites: `source-dependencies` (174), `macros` (9), `pipelining` (15), `general` (5), `apiinfo` (5). Status is `test` (runs), `pending` (a `pending` script records a known failure) or `disabled` (a `disabled` script; not run at all). The repository also has `profiler` (2) and `reporter` (2) suites, which exercise the invalidation profiler and the problem reporter rather than incrementality, and are not catalogued here.

Script vocabulary: `> compile` must succeed, `-> compile` must fail, `> run N` compiles and runs a main class with argument N (so a run assertion is also a "was it recompiled" check), `checkRecompilations n A B` asserts that A and B were last compiled in cycle n (0 is the initial compile), `checkIterations n` asserts n compile cycles in total since the last clean, `checkDependencies A: B C` asserts A's recorded dependencies, `checkProducts` asserts the classfiles recorded for a source. "Error" in the "what must happen" column means the incremental build must report a compile error, which is only possible if the client was recompiled.

Mechanism vocabulary (used in the last column and counted at the end): `memberRef` (a member-reference dependency edge, invalidated by a name hash), `inheritance` (an inheritance edge, invalidated transitively on any API change of the parent), `local inheritance` (inheritance by a local or anonymous class, invalidated but not propagated), `usedNames` (the set of simple names a class uses, including imports and inferred types), `name hashing` (an API change is attributed to the names it modifies; clients that use none of them are skipped), `API hash` (the extracted API and its hash, including stability under irrelevant edits), `extraHash` (the hash of a trait's non-API members and parents, folded into every subclass), `sealed` (children of a sealed parent are part of its API), `implicit` (implicit members and implicit scope), `macro` (macro expansion dependencies), `pipelining` (early output, Java deferred), `Java` (Java sources, javac, the classfile-based API), `classpath-external` (a dependency on a jar or another subproject's output), `deleted source` / `added source` (a source removed or added, as opposed to edited), `products` (classfile naming, recording and restoration), `cycles` (the fixpoint of recompile rounds, transitive invalidation, early stopping), `options` (incOptions or scalac options affecting invalidation), `harness` (the scripted framework itself, nothing incremental).

## Members and signatures (plain member references)

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/added | test | object vals | A gains a reference to B.y during a partial recompile; later B.y changes Int/String | A's new dependency on B is recorded; later change to B.y recompiles A and errors; clean build agrees | memberRef, cycles |
| source-dependencies/check-recompilations | test | object defs, chain B->A, D->C->A | A.foo Int -> String | cycle 1 A, cycle 2 B and C, cycle 3 D (C's inferred result changed) | memberRef, cycles |
| source-dependencies/class-based-memberRef | test | two classes per file | A1.foo removed, A2 untouched, same file | B1 (uses A1 only as a parameter type) and B2 (uses A2.bar) are not recompiled | name hashing, memberRef |
| source-dependencies/transitive-a | test | object vals, inferred types | A.x String -> Int | C (uses B.y.length, B.y inferred from A.x) errors | memberRef, cycles |
| source-dependencies/transitive-early-stopping | test | object vals, inferred types | A.a Int -> String | exactly 4 cycles: A, B, C; D (uses C.c2, whose hash is unchanged) is not recompiled | name hashing, cycles |
| source-dependencies/intermediate-error | test | object def | A.x gets a type error, then is fixed to String | first compile errors; second recompiles B and errors (B.y: Int) | memberRef, cycles |
| source-dependencies/false-error | pending | mutually dependent objects A and B | A.x and A.z change to String together, B.y = A.x | should compile (B's inferred type follows A.x) but Zinc fails on an intermediate round | memberRef, cycles |
| source-dependencies/new-cyclic | pending | trait val, class extends trait | A gains `val x = (new B).y` where B extends A | expected error (new cycle A <-> B) | inheritance, memberRef, cycles |
| source-dependencies/same-source-transitive-invalidation | test | two objects in one file | A.buildNonemptyObjects result Int -> String (and a default-param addition that stays compatible) | with transitiveStep 1 and 3: the compatible change compiles; the breaking change reaches Main through C and B (same file) and errors | memberRef, cycles, options |
| source-dependencies/same-source-transitive-invalidation-trait | test | two traits in one file, inheritance chain | A.buildNonemptyObjects result Int -> String | with transitiveStep 1 and 3: Main (`new C {}`) errors | inheritance, cycles, options |
| source-dependencies/less-inter-inv | test | class chain C<:B<:A, object D uses c.x | A.x Int -> String | 3 cycles: A; B, C (inheritance) and D (memberRef) together; E not recompiled since D's API is unchanged | inheritance, memberRef, cycles |
| source-dependencies/trait-member-modified | test | trait used as a parameter type | trait A gains foo | B(a: A) not recompiled; 2 cycles | name hashing, memberRef |
| source-dependencies/erasure | test | generic result type | A.x List[Int] -> List[String] | B errors | memberRef, API hash |
| source-dependencies/typeref-return | test | type alias as result type | A.I Int -> String | B errors | memberRef, API hash |
| source-dependencies/typeref-only | test | class used only as a type argument | B.scala deleted | A (`def foo: A[B]`) errors | deleted source, memberRef |
| source-dependencies/stability-change | test | stable path import `import A.x.y` | A.x val -> def | B errors (import of an unstable path) | memberRef, API hash |
| source-dependencies/constants | test | `final val` constant | A.x 1 -> 2 | B (asserts on A.x, which javac/scalac inline) recompiled; run 2 passes | memberRef, API hash |
| source-dependencies/qualified-access | test | `private[a]` qualifier | private[a] -> private[b] on A.x | B (in package a) errors | memberRef, API hash |
| source-dependencies/pkg-private-class | test | package-private class | private class A loses foo | B errors | memberRef, API hash |
| source-dependencies/backtick-quoted-names | test | symbolic member name `=` | renamed to asdf | B errors | usedNames, name hashing |
| source-dependencies/empty-modified-names | test | abstract member moved between traits in one file | foo moves from T1 to T2 | compiles (an API change with an empty set of modified names must not crash) | API hash, name hashing |
| source-dependencies/subproject-api-update | test | protected val in another subproject | A.a renamed to A.b | checkNameExistsInClass sees the new name | API hash, classpath-external, harness |
| source-dependencies/check-dependencies | test | class extends two traits | none | checkDependencies A: B C | harness, inheritance |
| source-dependencies/check-dependencies-class-of | test | `classOf[B]` literal | none | checkDependencies A: B | harness, memberRef |
| source-dependencies/check-classes | test | object | none | checkClasses A.scala: A | harness |
| source-dependencies/specify-inc-options | test | none | none | incOptions.properties is honoured (transitiveStep, recompileAllFraction, classfileManagerType, recompileOnMacroDef) | harness, options |
| source-dependencies/scalac-options | test | class | A gains a val and -Xfatal-warnings is removed from scalac options (listed in ignoredScalacOptions) | only A recompiled in cycle 1; the option change does not force a full recompile | options |
| source-dependencies/store-apis-false | test | class inheritance | Bar.scala added with storeApis=false | cycle 1 recompiles only Bar | options, added source |

## Deleted, added and replaced sources; error recovery

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/remove-test-a | test | object with a type error | an erroneous file is added, then deleted | error, then success | added source, deleted source |
| source-dependencies/remove-test-b | test | object member `B.length` | A gains a use of B.length (error, B lacks it); B gains it; B.scala deleted; restored; length removed; B emptied (commented out) | error / ok / error / ok / error / ok / error: every deletion or removal of B.length reaches A | deleted source, memberRef |
| source-dependencies/empty-a | test | object A in package a | A.scala emptied (all commented out), restored, B added and deleted | B errors when A is empty; an empty source with no classes is handled on add, change and delete | deleted source, memberRef |
| source-dependencies/dup-class | test | two files defining `clear.A` | B.scala redefines A, then is fixed | error, then success (duplicate class detected and recovered from) | added source, cycles |
| source-dependencies/restore-classes | test | object vals | A.x Int -> String and class C added; B.y: Int breaks | the failed compile restores A's old classfiles and deletes C.class; reverting A needs no new compile (checkIterations 1) | products, cycles |
| source-dependencies/replace-test-a | pending | top-level object renamed by replacing its source | A.scala defines First, then Second | First.class disappears, Second.class appears (checked by loading classes; old sbt Build.scala, obsolete) | products, harness |
| source-dependencies/relative-source-error | pending | none | scalaSource set to a relative `file("src")` | sbt must reject a relative source directory (sbt-level, not Zinc) | harness |
| source-dependencies/cross-source | pending | sbt cross-version source directories | scalaVersion switched with `++` | sbt-level source selection (obsolete, Scala 2.9/2.10) | harness |

## Inheritance, overriding and traits

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/transitive-inherit | test | trait chain C<:B<:A | A gains def x, C already defines x | C errors (override needed) | inheritance, cycles |
| source-dependencies/transitive-class | test | class chain D<:C<:B<:A, Hello uses D | A gains foo | B, C, D and Hello (same file as D) recompiled in cycle 2 | inheritance, cycles |
| source-dependencies/transitive-b | test | trait chain, inherited val | A.x String -> Int | C (`x.length`) errors | inheritance, cycles |
| source-dependencies/transitive-memberRef | test | class chain D<:C<:B<:A, X uses B as parameter type, Y uses X | A gains foo | B, C, D recompiled in cycle 2; X and Y not recompiled | inheritance, name hashing |
| source-dependencies/parent-change | test | class V extends W, Z extends V, Y calls (new Z).x | V no longer extends W | Y errors ("x is not a member of Z") | inheritance, memberRef |
| source-dependencies/parent-member-change | test | class chain, overloads | A.x(Int) becomes A.x(String), identical to C.x(String) | C errors (override modifier required) | inheritance |
| source-dependencies/override | test | traits with `override def` and `def`, diamond D extends C with B | B's `override def x` loses `override` | D errors | inheritance |
| source-dependencies/abstract-override | test | `abstract override`, stackable traits | C.x becomes `abstract override def x = super.x + 5` | D (extends C with B) errors (no concrete super) | inheritance |
| source-dependencies/linearization | test | stackable traits, super calls, linearization | D extends C with B -> B with C | F recompiled; run 11 instead of 16 | inheritance, cycles |
| source-dependencies/trait-super | test | `abstract override` traits with super calls | super calls added in B then C | X recompiled; run 5 then 21 (super accessors are not in the API) | extraHash, inheritance |
| source-dependencies/abstract-class-to-trait | pending | abstract class becomes trait | A: abstract class -> trait, B extends A, Test does `new B` | both compiles should succeed; B must be recompiled against the trait (stale classfile otherwise) | inheritance, API hash |
| source-dependencies/class-based-inheritance | test | two classes in a file, nested class | A gains nested AA, then AA gains foo | B (extends A2, same file as A) not recompiled; C (extends A) recompiled | inheritance, name hashing |
| source-dependencies/local-class-inheritance | test | local class in a method extends B | A gains abc | B and C (local inheritance) recompiled, D (extends C) not | local inheritance, inheritance |
| source-dependencies/sam-local-inheritance | test | SAM lambda `val f: A = () => 1` | A.foo result Int -> AnyVal | B recompiled (SAM lambda counts as local inheritance), C (extends B) not; 3 cycles | local inheritance, memberRef |
| source-dependencies/compound-type-member-inheritance | test | compound result type `AnyRef with B` | B gains baz | A not recompiled (a compound type in a signature is not an inheritance edge) | inheritance, memberRef, name hashing |
| source-dependencies/trait-extends-trait-extra-round | test | trait chain, class extends trait | comment-only edit to B | D not recompiled, 2 cycles | extraHash, API hash |
| source-dependencies/trait-local-change | test | trait with a concrete method | A.f body "a" -> "b" | B (extends A) not recompiled, 2 cycles | extraHash, API hash |
| source-dependencies/trait-private-val | test | trait private val | Base gains a private val | TestApp (extends Base) recompiled; run passes | extraHash |
| source-dependencies/trait-private-var | test | trait private var and val | A gains a private var, then (after clean) a private val | B recompiled, else AbstractMethodError on the generated accessors | extraHash |
| source-dependencies/trait-private-object | test | trait private object | A gains a private object X used in a val | B recompiled; run passes | extraHash |
| source-dependencies/trait-private-val-member-ref | test | public method made private in a trait; a final class extends it | Base.somePublicMethod becomes private | 2 cycles: Base and BaseClass (same file); TestApp (memberRef on BaseClass) not recompiled | extraHash, name hashing |
| source-dependencies/trait-private-val-local-inheritance | test | `new Base {}` anonymous class | Base.somePublicMethod becomes private | TestApp recompiled (local inheritance); 3 cycles | extraHash, local inheritance |
| source-dependencies/trait-private-val-transitive-inheritance | test | trait chain across three subprojects a, b, c | A's private val renamed | C recompiled through B's extraHash; main runs | extraHash, classpath-external |
| source-dependencies/trait-private-val-mix-transitive-inheritance | test | trait chain, A and B in the same subproject, C in another | A's private val renamed | C recompiled; main runs | extraHash, classpath-external |
| source-dependencies/trait-trait-211 | test | trait chain across packages, Scala 2.11 | A.buildNonemptyObjects gains a parameter and transform's call changes | Foo (extends C extends B extends A) recompiled; run passes (no NoSuchMethodError) | inheritance, extraHash |
| source-dependencies/trait-trait-212 | test | same, Scala 2.12 | same | same | inheritance, extraHash |
| source-dependencies/module-inheritance-extra-hash | test | `trait B; object B extends A` across subprojects, D extends trait B | A's private var renamed | D not recompiled (the companion object's parents are not folded into trait B's extraHash) | extraHash, classpath-external |
| source-dependencies/module-inheritance-extra-hash-213-bin | pending | same, on scala2-sbt-bridge (2.13.y) | same | D should not be recompiled; the bridge does not yet report `object B` as a term | extraHash, classpath-external |
| source-dependencies/lazy-val | test | val overridden by a subclass | A.x val -> lazy val | B (`override val x`) errors | inheritance, API hash |
| source-dependencies/var | test | var vs def pair | A's `def x`/`def x_=` become `var x` | B (`override var x`) errors | inheritance, API hash |
| source-dependencies/trait-java-parent-pipelining-3 | test | Scala 3 trait extends a Java class, across subprojects | none (clean build only) | D not recompiled in a second round: T's extraHash is computed before javac supplies J's API | extraHash, Java, pipelining |
| source-dependencies/trait-jdk-parent-release-3 | test | Scala 3 trait with parent java.lang.Object under -release | none | compile succeeds (JDK parent reported as a project class with no API; extraHash lookup must not fail) | extraHash, API hash |

## Sealed hierarchies and pattern matching

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/sealed | test | sealed trait, exhaustive match | new child E added in A's file | D (matches on A) recompiled; -Xfatal-warnings turns the inexhaustive warning into an error | sealed |
| source-dependencies/sealed-extends-sealed | test | sealed trait extends sealed trait | new child D of A added | App (matches on Z) recompiled; error | sealed |
| source-dependencies/patMat-scope | test | sealed trait, useOptimizedSealed, match vs type-only use | a child changes type; then Sealed gains a parent | child change recompiles only the pattern-match user; the parent change recompiles both users (checked by classfile timestamps) | sealed, usedNames, options |
| source-dependencies/changedTypeOfChildOfSealed | pending | sealed trait, child's parents change, match on a non-sealed parent type | Child2 gains then loses `with Base` | the exhaustiveness warning (as error) must reappear when Child2 stops extending Base | sealed |

## Implicits and implicit scope

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/implicit | test | implicit conversion inherited from a class | A.x loses `implicit` | B (`val x: String = 3`) errors | implicit, memberRef |
| source-dependencies/implicit-params | test | implicit parameter list | A.x's second list loses `implicit` | B errors | implicit, memberRef |
| source-dependencies/implicit-search | test | wildcard imports `import A._, B._`, implicitly[Ordering[Int]] | A gains `val x`, making imported `x` ambiguous so the implicit from B is no longer selected | C recompiled; run now succeeds (the `???` implicit no longer chosen) | usedNames, implicit |
| source-dependencies/implicit-search-companion-scope | test | implicit scope via companion of a parent trait | companion A gains implicit m[A]: M[A] | Test (implicitly[M[B]], B extends A) errors with ambiguity; clean build agrees | implicit, inheritance |
| source-dependencies/implicit-search-higher-kinded | test | same with higher-kinded implicit `m[MM[_], A]` | same | same | implicit, inheritance |
| source-dependencies/companion-object-implicit-scope | test | implicit in companion of a parent trait, across subprojects | an ordinary member added to object A; then the implicit removed | first: D and User not recompiled; second: User errors | implicit, extraHash, classpath-external |
| source-dependencies/companion-object-extra-hash | test | companion object of a parent trait | object A gains def y | D (extends B extends A) not recompiled | extraHash, classpath-external |
| source-dependencies/default-namespace-implicit | pending | package object of the empty package supplying an implicit | Foo.scala touched (no change) | recompiling Foo alone must still find the implicit from the empty-package object | implicit, usedNames |
| source-dependencies/package-object-implicit | pending | package object added with an implicit Int, default implicit parameter | package.scala added | Test must be recompiled (run now throws) | implicit, added source |
| source-dependencies/packageobject-and-traits | pending | package object with implicit val named like a trait | package object foo added with `implicit val Foo` | clean build fails (name clash with trait Foo); incremental build should too | added source, implicit |
| source-dependencies/pkg-self | test | package object extends a class from a subpackage, implicit conversion | A's conversion target C changes body | compile succeeds (classfiles of A deleted while the package object is loaded must not break scalac) | products, cycles |

## Name resolution: imports, packages, package objects, shadowing

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/added-class-in-existing-source | test | nested package clauses `package a; package b`, simple-name lookup | an existing a.b source gains object Foo, shadowing a.Foo | Client recompiled (uses the added simple name); error (v is now String) | added source, usedNames |
| source-dependencies/added-class-inner-package | test | same | a new file adds a.b.Foo | Client recompiled; error | added source, usedNames |
| source-dependencies/added-class-inner-package-scala3 | test | same, Scala 3 | same | same | added source, usedNames |
| source-dependencies/added-class-wildcard-shadows-package | test | `import q._` vs package member | a new file adds q.Foo | Client recompiled; error | added source, usedNames |
| source-dependencies/added-class-wildcard-shadows-package-scala3 | test | same, Scala 3 | same | same | added source, usedNames |
| source-dependencies/added-class-wildcard-shadows-scala | test | `import q._` vs scala.Option | a new file adds q.Option | Client recompiled; error | added source, usedNames |
| source-dependencies/added-class-wildcard-shadows-scala-scala3 | test | same, Scala 3 | same | same | added source, usedNames |
| source-dependencies/import-class | test | `import a.A` of an unused class | class a.A removed from A.scala | B errors (the import is a dependency) | usedNames, memberRef |
| source-dependencies/import-package | pending | `import a.b` of a package | package a.b ceases to exist | B should error; scalac records no dependency on a package | usedNames |
| source-dependencies/empty-package | test | `import pkgName.Test` from a nested package | Test moves from a.pkgName to pkgName; later Define.scala deleted | checkDependencies a.Use: pkgName.Test; deletion errors | usedNames, deleted source |
| source-dependencies/same-file-used-names | test | local `import B._` inside a method, name used in the same file | B gains x, making A.y's `x` ambiguous | A recompiled; error | usedNames |
| source-dependencies/package-object-name | test | `package object b extends A` | A gains foo | 2 cycles (package object recompiled; no spurious extra round from its name) | inheritance, API hash |
| source-dependencies/package-object-name-inner | test | package object extends A, A.Inner uses O.o | O.o String -> Int | 3 cycles | memberRef, cycles |
| source-dependencies/package-object-nested-class | test | objects and classes nested in a package object | none | compiles (class name mapping of package$ nested classes) | products, API hash |
| source-dependencies/resident-package-object | test | package object val | green Int -> String | A errors | memberRef |
| source-dependencies/unexpanded-names | test | `private[X] object` nested in classes and objects | none | compiles (name expansion of private objects) | API hash, products |
| source-dependencies/named | test | named arguments | A.x's parameters swapped (zz, yy) -> (yy, zz) | B recompiled; run 1 (parameter names are part of the API) | memberRef, API hash |

## Abstract types, type members, aliases, path-dependent and structural types

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/abstract-type | test | higher-kinded abstract type member `type S[_]` | S loses its type parameter | B (`type F = S[Int]`) errors | inheritance, API hash |
| source-dependencies/abstract-type-override | test | abstract type, alias and refinement `Inner { type Xyz = Int }` | comment-only edit to Bar | 2 cycles; Impl not recompiled (OVERRIDE flag on the refinement must be stable) | API hash |
| source-dependencies/type-alias | test | type alias | A.X Option[Int] -> Int | B errors | memberRef, API hash |
| source-dependencies/as-seen-from-a | test | abstract type member T fixed in a subclass, nested object method foo(x: T) | B: T = Int -> String | D (`C.X.foo(12)`) errors | memberRef, inheritance, API hash |
| source-dependencies/as-seen-from-b | test | bounded abstract type members T <: S, S refined in subclass | B: S <: Int -> S <: String | D (`val x: Int = C.X.foo`) errors | memberRef, inheritance, API hash |
| source-dependencies/type-member-nested-object | test | singleton type `t.type`, nested object | B.t String -> Int | C (`val proxy: String = t`) errors | memberRef, inheritance |
| source-dependencies/types-in-used-names-a | test | inferred type of a val with a type argument List[B] | B no longer extends A | D (`val lista: List[A] = C.listb`) errors (B appears in D only via a type) | usedNames, memberRef |
| source-dependencies/types-in-used-names-b | test | chained abstract type bounds T <: S <: Int | S's bound Int -> String | B (`val x: Int = (new A).foo`) errors | usedNames, memberRef |
| source-dependencies/nested-type-params | pending | type projection through an object's singleton type `Providers.type#SomeProvider#Operations` | Operations alias A -> B and Bar uses `.b` | incremental compile should succeed like a clean one | memberRef, API hash |
| source-dependencies/expanded-type-projection | test | type-level list via projections, alias `MyFactory = FactoryB :: Nil` | FactoryB -> FactoryA | Usage (`x.foo`) errors; clean build agrees | memberRef, API hash |
| source-dependencies/struct | test | structural type parameter `{ def x: Int }` | A.x Int -> Byte | C (passes A to B.onX) errors | memberRef, API hash |
| source-dependencies/struct-usage | test | structural result type `{ def q: Int }` | q Int -> String | B errors | memberRef, API hash |
| source-dependencies/struct-projection | test | projection on a refinement `({type T <: Int})#T` | bound Int -> String | B errors | memberRef, API hash |
| source-dependencies/type-lambda-refinement-owner | test | type lambda `({ type l[a] = Kleisli[F, R, a] })#l` as a parent's type argument | comment-only edit to Impl | 2 cycles, only Impl recompiled (the refinement's type parameter owner must hash the same from source and from pickles) | API hash, inheritance |
| source-dependencies/type-parameter | test | type parameter on a trait | A[T] -> A | B, C, D error | memberRef, inheritance |
| source-dependencies/variance | test | covariance annotation | A[+T] -> A[T] | C (`val a: A[Any] = new A[Int]`) errors | memberRef, API hash |
| source-dependencies/fbounded-existentials | test | inferred lub of an F-bounded Comparable and String | none | compiles (API extraction of the existential) | API hash |
| source-dependencies/no-type-annotation | pending | class renamed, method without a result type annotation | Before -> After everywhere except Problem.x's inferred type | compile should succeed | usedNames, memberRef |
| apiinfo/unstable-existential-names | test | existential `Box[_]` in a method signature | a private method added to Foo | 2 cycles (existential names must be stable between source and pickle) | API hash |
| apiinfo/circular-structure | test | Scala inner classes extending the outer; Java static nested classes extending the outer | none | compiles (API extraction terminates on the cycle) | API hash, Java |

## Parameters and constructors

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/by-name | test | by-name parameter | `=> String` -> `Function0[String]` | B errors | memberRef, API hash |
| source-dependencies/repeated-parameters | test | varargs `String*` | -> `Seq[String]` | B errors | memberRef, API hash |
| source-dependencies/default-params | test | default argument on an overloaded method | the default moves to the other overload | B (`A.x(5)`) errors (default getter names are part of the API) | memberRef, name hashing |
| source-dependencies/default-arguments-separate-compilation | test | default constructor arguments of a nested class Foo.Bar | Bar gains a second default parameter | test.scala (`new Foo.Bar(1)`) recompiled each time; run passes | memberRef, API hash |
| source-dependencies/default-arguments-separate-compilation-210 | test | same, Scala 2.10 | same | same (bridge must not drop the dependency when associatedFile is null) | memberRef, API hash |
| source-dependencies/constructors-unrelated | test | class constructor vs companion member | A's constructor parameter Int -> String | B (uses only A.x) not recompiled; 2 cycles | name hashing |
| source-dependencies/constructors-unrelated-2 | test | secondary constructors with defaults, memberRef on the companion | B's secondary constructor default type changes; then C's | A not recompiled for B (2 cycles); A errors for C (`new C(1)` uses C's constructor) | name hashing, memberRef |
| source-dependencies/case-classes-no-companion | test | case class without explicit companion, synthetic apply and defaults | A(name) String -> Int; defaults added; default type Char | UseSite errors, then runs after each compatible change, then errors again | memberRef, API hash |
| source-dependencies/naha-synthetic | test | synthetic case-class copy | user-defined private `copy` shadows the synthetic one | B (`a.copy()`) errors | name hashing, memberRef |
| source-dependencies/nested-case-class | test | case class nested in a class, then with a value-class field | A0 then A1 | runs (synthetic companion of a nested case class handled; value class too) | products, API hash |
| source-dependencies/sam | test | SAM conversion of a lambda | A.foo result Int -> String | B errors | memberRef, local inheritance |

## Value classes, specialization, inlining

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/value-class | test | class becomes a value class; used as parameter, as result with no parameter list, as result with two lists | `extends AnyVal` added to A | C errors (null argument) in case 1; C recompiled (run passes, erased signature of B.bar changed) in cases 2 and 3 | memberRef, API hash |
| source-dependencies/value-class-underlying | test | value class underlying type | Int -> Double | B and C recompiled; invalidation log names A, A;init;, x; 3 cycles | name hashing, memberRef |
| source-dependencies/specialized | test | `@specialized` type parameter | annotation added to A.x | B should be recompiled to call the specialized variant (run true; the script notes the check is weak) | API hash |
| source-dependencies/inline | disabled | `@inline` with -opt:l:inline | A.x 1 -> 2 | B must be recompiled because A.x was inlined into it | API hash |

## Java sources and mixed compilation

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/java-basic | test | Java classes across packages, two A.java files | sources added, B made to depend on a.A, a.b.A deleted, a.A deleted, B given a main | dependency on a.A (not a.b.A) recorded; deletion errors; main discovered | Java, added source, deleted source |
| source-dependencies/java-static | test | Scala reads a Java static field | J.x Integer -> String | S errors (static member maps to the companion-less class) | Java, memberRef |
| source-dependencies/java-constants | test | Java `static final int` as a switch label, across subprojects | B.MAX int -> String | A errors (the constant is inlined; the edge must come from javac's AST, not the classfile); clean build agrees | Java, classpath-external, memberRef |
| source-dependencies/java-mixed | test | Java calls a Scala method | S.foo renamed | JJ errors | Java, memberRef |
| source-dependencies/anon-class-java-depends-on-scala | test | Java anonymous class extends a Scala abstract class | S.foo renamed | JJ errors | Java, inheritance |
| source-dependencies/inner-class-java-depends-on-scala | test | Java local class extends a Scala abstract class | S.foo renamed | JJ errors | Java, inheritance |
| source-dependencies/anon-java-scala-class | test | Scala anonymous class `new B {}` of a Java class | A.java gains a method | B and C recompiled, D not | Java, local inheritance |
| source-dependencies/local-class-inheritance-from-java | test | Scala local class extends a Java class | A.java gains a method | B and C recompiled, D not | Java, local inheritance |
| source-dependencies/transitive-inherit-java | test | Java class chain with super call | A loses x() | C (`super.x()`) errors | Java, inheritance |
| source-dependencies/less-inter-inv-java | test | Java class chain, static users | A.x() Integer -> String | 3 cycles; E not recompiled | Java, inheritance, cycles |
| source-dependencies/annotations-in-java-sources-a | test | Java annotation on a class | annotation type gains an element | Foo recompiled in cycle 2 | Java, API hash |
| source-dependencies/annotations-in-java-sources-a2 | test | Java annotation on a class | annotation type's source emptied | Foo recompiled and errors | Java, deleted source |
| source-dependencies/annotations-in-java-sources-b | test | Java annotation, retention policy | @Retention(RUNTIME) added | Foo recompiled in cycle 2 | Java, API hash |
| source-dependencies/annotations-in-java-params | test | Java annotation on a method parameter | annotation type gains an element | Foo recompiled in cycle 2 | Java, API hash |
| source-dependencies/java-inner | test | Java inner (non-static) classes | none | checkProducts A.java: A, A$B; checkDependencies A: A.B; A.B: A D; C: A A.B | Java, products, harness |
| source-dependencies/java-enum | test | Java enum with a constant-specific body | none | compiles (enum constant bodies are anonymous classes) | Java, products |
| source-dependencies/java-anonymous | test | Java anonymous class | none | compiles (no checks, sbt/zinc#83) | Java |
| source-dependencies/java-name-with-dollars | test | Java interface named with `$` | none | compiles | Java, products |
| source-dependencies/java-lambda-typeparams | test | Java lambda in a generic static method, anonymous generic class | none | compiles (generic signatures parsed) | Java, API hash |
| source-dependencies/java-generic-workaround | test | Java nested generic classes (JDK bug 6476261) | none | compiles (unparseable generic signature tolerated) | Java, API hash |
| source-dependencies/java-class-invs | test | Scala object extends a Scala trait from one subproject and a Java interface from another | Std gains x | compiles (invalidation across Java and Scala subprojects) | Java, classpath-external, inheritance |
| source-dependencies/cyclic-dependency | test | Scala class extends Java class whose field is another Scala class (cycle) | both files touched without content change | 2 cycles (no runaway) | Java, inheritance, cycles |
| source-dependencies/mixed-java-invalidations | test | Scala uses a Java class, pipelining off | A gains x; B gains y | exactly one extra cycle each; Java not recompiled | Java, cycles |
| source-dependencies/resident-java | test | JavaThenScala order, Scala reads a Java field | A.x and B's expected type change together | compiles each time | Java, memberRef |
| source-dependencies/new-pkg-dep | test | Scala gains a dependency on a Java class in a new package | A.java added, B references a.A.x | compiles | Java, added source, memberRef |
| source-dependencies/malformed-class-name | test | Java anonymous subclasses of Scala classes whose companions nest objects | BooUser.java added | compiles (nested class names like Boo$Foo$Impl resolved) | Java, products |
| source-dependencies/malformed-class-name-with-dollar | test | Java static nested class named `C$` | A.scala uses B.C$.x | compiles | Java, products |
| source-dependencies/subproject-java | test | Java across subprojects | A.java deleted and replaced by Break.java | checkProducts for A; use errors | Java, classpath-external, deleted source |
| apiinfo/java-basic | test | Java nested and inner classes extending each other, Java reads a Scala val | none | compiles (API extraction of Java nesting) | Java, API hash |
| apiinfo/main-discovery | test | Java and Scala main methods, static inner, instance main (JEP 445 from Java 25) | none | checkMainClasses for Java 24 and 25 | Java, harness |

## Macros

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| macros/macro | test | def macro in another subproject | macro implementation made to throw | Client recompiled and errors; clean build agrees | macro, classpath-external |
| macros/macro-arg-dep | test | macro argument `Foo.str` | Foo.str removed | Foo recompiled first, then Client errors (macro arguments are dependencies) | macro, memberRef |
| macros/macro-arg-dep-nested | test | macro argument that is itself a macro call | Foo.str removed | Client errors | macro, memberRef |
| macros/macro-arg-dep-stackoverflow | test | identity macro on a val | none | compiles without stack overflow in dependency extraction | macro |
| macros/macro-type-change | test | macro inspecting the members of a type argument, same subproject | A gains a val | App recompiled; run true | macro, memberRef |
| macros/macro-type-change-2 | test | same, A in another subproject | same | same | macro, classpath-external |
| macros/macro-type-change-3 | test | macro inspecting base classes of B extends A | A gains a val | App (uses B) recompiled; run true | macro, inheritance |
| macros/macro-type-change-4 | test | macro with a value argument, impl in a nested object, quasiquotes | A gains a val | App recompiled; run true | macro, classpath-external |
| macros/macro-use | test | macro implementation that calls ordinary library code at expansion time | InternalApi.value 1 -> 2 (two calls removed from the macro) | App recompiled; run ABC_2 (a dependency through the macro's runtime, not its signature) | macro, memberRef |

## Pipelining

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| pipelining/subproject-pipelining | test | two subprojects, pipelining on | use edited (no-op for dep); then dep's A removed | compiles; then use errors | pipelining, classpath-external |
| pipelining/subproject-pipelining-3 | test | same, Scala 3 | same | same | pipelining, classpath-external |
| pipelining/subproject-pipelining-optout | test | dep opts out of pipelining, use opts in | same | same | pipelining, classpath-external, options |
| pipelining/subproject-pipelining-mixed | test | Java class in dep, Scala and Java in use, Scala extends Java | dep gains Other.scala; use's B edited | compiles (use needs a pickle for A, which dep did not recompile) | pipelining, Java, classpath-external |
| pipelining/subproject-pipelining-noclobber | test | two Scala files in dep, early output jar | A.x Int -> Long and early/output.jar deleted | compiles (the early jar must contain pickles for A and B, recompiled together) | pipelining, products |
| pipelining/java-then-scala-order | test | JavaThenScala with pipelining | none | mixed subproject is rejected; Scala-only subproject compiles | pipelining, Java, options |
| pipelining/java-comment-change | pending | Java class with a Scala user | comment-only edit to J.java | U should not be recompiled; the scalac-derived and classfile-derived APIs of J never compare equal | pipelining, Java, API hash |
| pipelining/java-parent-body-change | test | Scala trait extends a Java class, pipelining on | T's method body; then J's method renamed | C and U not recompiled for the body change (J is passed to scalac but unchanged); the J change errors | pipelining, Java, extraHash |
| pipelining/java-only-round-3 | test | Scala 3, Java-only change in dep | J.java edited | compiles (a Java-only scalac run never reaches the post-Inlining phase; the early output must still carry J) | pipelining, Java |
| pipelining/java-only-round-downstream-3 | test | Scala 3, Java-only change in dep and a change in use | J.java and U.scala edited | compiles (J.tasty must survive in the early jar when dependencyPhaseCompleted is skipped) | pipelining, Java |
| pipelining/trait-extends-java-interface | test | Scala trait extends a Java interface, across subprojects | T's private var renamed | D not recompiled on the clean build; D recompiled in cycle 1 after the change | pipelining, Java, extraHash |
| pipelining/trait-parent-body-change-3 | test | Scala 3 trait chain, pipelining | B's method body | A and C not recompiled (B's parent A reported in Inlining, after dependencyPhaseCompleted) | pipelining, extraHash |
| pipelining/trait-upstream-parent-body-change-3 | test | Scala 3 trait whose parent is in another subproject | E's method body | F not recompiled | pipelining, extraHash, classpath-external |
| pipelining/trait-parent-downstream-3 | test | Scala 3 trait chain across subprojects | B's method body | D not recompiled (the early analysis must already have B's hash with its parent A) | pipelining, extraHash, classpath-external |
| pipelining/trait-parent-change-downstream-3 | test | Scala 3 trait changes parent, across subprojects | B extends A -> A2; then B's body | D recompiled for the parent change; D recompiled again for the body change only if the early analysis had stale parents (checked by cycle number) | pipelining, extraHash, classpath-external |

## Classpath, binary dependencies and subprojects

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/binary | test | dependency through a packaged jar in use/lib | dep's A removed and the jar repackaged | use errors (jar stamp change invalidates B) | classpath-external |
| source-dependencies/binary-3 | disabled | same, Scala 3 | same | same | classpath-external |
| source-dependencies/subproject-dependency | test | project dependency, pipelining off | dep's A removed | use errors | classpath-external |
| source-dependencies/subproject-dependency-b | pending | inner class of a class in another subproject, B extends A | Inner gains foo | expected no recompilation of use (checkIterations 1) despite the inheritance edge; old sbt build file | classpath-external, inheritance |
| source-dependencies/export-jars | pending | sbt exportJars, constant across projects | A.x 1 -> 2 -> def 3, with and without exportJars | run reflects the new constant (old sbt Build.scala) | classpath-external, harness |
| source-dependencies/canon | disabled | symlinked jar whose canonical path is not a jar | none | scalac must get the non-canonical path; checkIterations 1 on a no-op compile | classpath-external, harness |
| source-dependencies/anon-class-dep | test | anonymous refinement class in the API of a dependency subproject | none | B/checkNumberOfLibraries 1 (the anonymous class in A's output is not misrecorded as a library) | classpath-external, API hash |
| source-dependencies/sourcepath-virtualfile | test | -sourcepath pointing at the project's own sources | B edited, A touched | compiles (sourcepath files resolved as VirtualFiles) | options, harness |
| apiinfo/source-path | test | -sourcepath overriding scala.deprecatedInheritance | none | compiles | options, harness |
| general/classpath-filter | test | runtime classloading of scala.Int | none | run succeeds (classpath filtering for the run classloader) | harness |
| general/bridge-2.12.x | test | none | none | checkBridge zinc | harness |
| general/bridge-2.13.x | test | none | none | checkBridge zinc | harness |
| general/bridge-2.13.y | test | none | none | checkBridge scala2-sbt-bridge | harness |
| general/bridge-3.x | test | none | none | checkBridge scala3-sbt-bridge | harness |

## Products and classfile naming

| test | status | language feature | what changes | what must happen | mechanism |
|---|---|---|---|---|---|
| source-dependencies/check-products | test | object | none | checkProducts A.scala: A.class, A$.class | products, harness |
| source-dependencies/recorded-products | test | default package, nested objects and classes, local and anonymous classes | none | checkProducts for each file, including Container$C$1 and Container$$anon$1 | products |
| source-dependencies/compactify | test | very long package and for-comprehension class names, -Xmax-classfile-name 240 | both sources deleted | compacted classfile names are recorded and deleted with their sources (checkNoClassFiles) | products, deleted source |
| source-dependencies/compactify-nested | test | seven nested classes with long names | none | checkProducts with the compactified name for the deepest class | products |
| source-dependencies/compactify-nested-class | test | anonymous class with a case object inside | none | checkProducts for D$$anon$1$i$ etc. | products |

## Mechanism counts

Each test is counted once per mechanism it is tagged with in the table above (a test tagged with three mechanisms contributes to three counts). 208 tests.

| mechanism | tests |
|---|---|
| memberRef | 63 |
| API hash | 50 |
| inheritance | 39 |
| Java | 39 |
| classpath-external | 27 |
| extraHash | 24 |
| cycles | 21 |
| harness | 20 |
| usedNames | 18 |
| products | 17 |
| pipelining | 16 |
| name hashing | 14 |
| added source | 14 |
| options | 10 |
| deleted source | 9 |
| implicit | 9 |
| macro | 9 |
| local inheritance | 6 |
| sealed | 4 |

By status: 188 `test`, 17 `pending`, 3 `disabled`.

## Features with no test

Compared against the Scala 2 and Scala 3 feature lists, the corpus on this branch has no test at all for the following. Where a pending test exists on a side branch it is named; "none" means nothing at all.

- Extension methods (Scala 3 `extension`, Scala 2 implicit classes): none. The only implicit-conversion tests use `implicit def`.
- Givens and `using` clauses: none on the branch; `added-given-package-object-scala3` and `added-given-top-level-scala3` are pending on origin/claude/name-resolution-pending. `summon` and context functions: none.
- Exports: none on the branch; `added-member-top-level-export-scala3` pending on origin/claude/name-resolution-pending.
- Opaque types: none on the branch; `opaque-type-mixin-forwarder-scala3` pending on origin/claude/inline-opaque-pending.
- Scala 3 `inline` and `transparent inline`: none on the branch (the Scala 2 `@inline` test is disabled); three pending on origin/claude/inline-opaque-pending.
- Scala 3 enums: none (java-enum covers only a Java enum). Scala 3 `derives` and type class derivation: none.
- Match types: none. Union types: none. Intersection types: only the Scala 2 compound type `AnyRef with B` in compound-type-member-inheritance; no Scala 3 `&`.
- Type lambdas: Scala 2 encoding only (type-lambda-refinement-owner, struct-projection); no Scala 3 `[X] =>> F[X]`. Polymorphic function types, dependent function types: none.
- Java records: none. Java sealed interfaces and `permits`: none on the branch; `java-sealed-nested-permits` pending in retronym/zinc#42. Java `default` interface methods: none.
- Java static imports and single-type imports: none on the branch; `java-static-import-member-added`, `java-on-demand-import-ambiguity`, `java-single-type-import-deleted` pending in retronym/zinc#42. Java on-demand (`import a.q.*`) imports with a Java client: none on the branch; `java-added-class-same-package` pending in #42. Scala tests cover package wildcard imports (added-class-wildcard-*, same-file-used-names, implicit-search).
- Scala 3 top-level definitions (vals and defs outside an object, `$package` classes): none on the branch; the given/export pending tests on origin/claude/name-resolution-pending touch them.
- Scala 3 `@main` methods: none (main-discovery covers Scala 2 style mains and Java mains).
- Self types, early initialisers and trait parameters: none. Trait initialisation order: `trait-initialiser-skipped-scala3` pending on origin/claude/name-resolution-pending.
- `Dynamic` (applyDynamic, selectDynamic): none.
- Scala annotations as part of the API (user-defined annotation classes, `@deprecated`, annotation arguments): none; only Java annotations (four tests) and the modifiers `@inline` and `@specialized`. Macro annotations: none.
- String interpolation: only incidental (`s"..."` in bodies); no custom interpolator in an API.
- Implicit classes and implicit conversions through `implicit class`: none.
- Scala 3 given instances in the implicit scope of companions: none (implicit-search-companion-scope is Scala 2 `implicit def`).
- Higher-kinded types: covered only through implicit-search-higher-kinded and abstract-type; no test of an HKT alias change.
- Package-object members shadowing package members, and clashes between a package object member and a class of the package: none on the branch; `added-member-package-object`, `added-member-package-object-scala3`, `added-implicit-package-object`, `package-object-member-clashes-with-class-scala3` pending on origin/claude/name-resolution-pending.
- Which class of a file a top-level import is charged to: none on the branch; `added-member-wildcard-import-second-class` and `added-member-wildcard-import-last-class-scala3` pending on origin/claude/name-resolution-pending.
- `classOf` literals as used names: check-dependencies-class-of records the edge only; `classof-used-name` (the name filter skipping the client) pending in retronym/zinc#42.
- Scala 3 specifics beyond the above: the Scala 3 tests on the branch are the four added-class-*-scala3 name-resolution tests, binary-3 (disabled), trait-java-parent-pipelining-3, trait-jdk-parent-release-3, bridge-3.x and seven pipelining tests. No Scala 3 test covers sealed hierarchies, implicits, macros (Scala 3 macros: none), value classes, structural types or abstract type members.
- Specialization is tested only weakly (specialized: the script says the recompilation of B is not checked). Lazy vals: one test (lazy-val, an override conflict), nothing on the lazy val's own initialisation semantics. Trait fields: well covered by the trait-private-* family. Inner classes: covered (java-inner, class-based-inheritance, subproject-dependency-b pending). Path-dependent types: covered (as-seen-from-a/b, type-member-nested-object). By-name, varargs, default and named arguments: one test each. Structural types: three tests, Scala 2 only.

## Pending tests and their families

On this branch (17 pending, 3 disabled):

- Name resolution and shadowing: import-package (package import not tracked).
- Implicits: default-namespace-implicit (implicit from the empty-package object), package-object-implicit (implicit added through a new package object), packageobject-and-traits (package object member clashes with a trait).
- Inheritance and API: abstract-class-to-trait (class to trait), new-cyclic (new cycle through inheritance), subproject-dependency-b (inner class member across subprojects), module-inheritance-extra-hash-213-bin (extraHash on scala2-sbt-bridge).
- Types: nested-type-params (projection through a singleton type), no-type-annotation (inferred result type after a rename), false-error (mutually dependent objects).
- Sealed: changedTypeOfChildOfSealed (a child's parents change).
- Pipelining and Java: pipelining/java-comment-change (Java API from scalac vs classfile).
- Harness and sbt-level (obsolete): cross-source, export-jars, relative-source-error, replace-test-a.
- Disabled: binary-3 (jar dependency, Scala 3), canon (symlinked jar), inline (Scala 2 `@inline` with the optimiser).

origin/claude/name-resolution-pending adds ten pending tests (it also marks the six added-class-* tests pending, which this branch's fix makes pass). Family: name resolution, where a client reaches a name through a scope that leaves no dependency edge.

- Package object members: added-member-package-object (2.13), added-member-package-object-scala3 (3), added-implicit-package-object (2.13: an implicit added to the package object makes the lexical scope ambiguous), package-object-member-clashes-with-class-scala3 (a package object member with the same name as a class of the package; Scala 3 reports the clash only when both are compiled together).
- Givens and exports (Scala 3): added-given-package-object-scala3, added-given-top-level-scala3 (a given at the import's nesting level makes summon ambiguous), added-member-top-level-export-scala3 (a wildcard export's forwarder shadows a package member).
- Import attribution: added-member-wildcard-import-second-class (Scala 2 charges a top-level import to the first class of the file), added-member-wildcard-import-last-class-scala3 (Scala 3 charges it to the last).
- Trait initialisation (Scala 3): trait-initialiser-skipped-scala3 (a trait with only a lazy val gains a statement; its API is unchanged, so the subclass keeps omitting the `$init$` call).

origin/claude/inline-opaque-pending (retronym/zinc#40) adds four pending tests. Family: Scala 3 inlining and opaque types, where the expansion or erasure in the client depends on something that is not in the inlined definition's API hash and that the client recorded no name for.

- inline-constant-path-scala3 (an inline body reads a constant `D.K` through a path; the inliner folds it before dependencies are collected).
- inline-constvalue-alias-scala3 (an inline body reads a literal type alias through `constValue`; the inline body hash does not hash types).
- inline-transparent-reference-scala3 (a transparent inline expands in typer to a call of `h`; `h`'s result type changes; the expansion's references are not collected).
- opaque-type-mixin-forwarder-scala3 (a mixin forwarder erases an opaque type to its right-hand side; the right-hand side changes; the subclass uses neither the object nor the type).

retronym/zinc#42 (branch claude/java-names-pending) adds seven pending tests, run without pipelining (with pipelining every Java source is recompiled in every cycle and the Java-client cases disappear). Family: Java name resolution and sealed hierarchies, found by the Java spaces of the Lean model (PLAN-java.md).

- J1 java-added-class-same-package: a Java client resolves `Foo` through `import a.q.*`; `a.b.Foo` added to its own package shadows it (the classfile names only a.q.Foo; a Java class records no used names).
- J2 java-static-import-member-added: `import static a.X.Foo` imported only a method; a member class `X.Foo` now shadows the package's Foo (an import leaves nothing in the classfile).
- J3 java-on-demand-import-ambiguity: a member class added behind `import static a.W.*` makes `Foo` ambiguous with `import a.q.*`.
- J4 java-single-type-import-deleted: an unused `import a.q.Bar;` whose class is deleted (javac rejects the import; the classfile does not name Bar; a coverage counterexample from JavaSpec.lean).
- java-added-class-inner-package-scala-client: a Scala client and a Java class added in an inner package (the Scala-source case with a Java binding).
- S2 java-sealed-nested-permits: a leaf added to the `permits` of a sealed T below the scrutinee's S, in its own file; S is not recompiled and the Scala client depends on S, A and B, not T.
- N1 classof-used-name: the Scala 2 bridge records the class of a `classOf` literal as a dependency but registers no used name for it, so the name filter skips the client (not Java-specific).
