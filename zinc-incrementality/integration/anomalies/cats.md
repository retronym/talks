# IncBench anomalies: typelevel/cats

- **Build:** typelevel/cats at `main` (shallow clone, 2026-10-19), Scala 2.13.18, modules `kernelJVM` (95 sources), `coreJVM` (245), `freeJVM` (13). Options as the build sets them: `-Xsource:3`, kind-projector and better-monadic-for plugins, `-release 8`.
- **Run:** `lockstep --verify --profile`, cells `s2-released-released` (bench-1.12.x f7b7642c03), `s2-released-perf` (develop-1.12.x 5615b62e16), `s2-released-merkle` (merkle-1.12.x 556464169f); lockstep's defaults (pipelining off, recompileAllFraction 0.5, `recompileOnMacroDef=true`, confirmed in every cell's generated `incOptions.properties`). The first campaign ran with `false` by mistake; this report replaces it. Clean build ~6.3 s warm. Edit script: `edits/cats.tsv`. Results: `~/code/.integration/campaigns/2026-10-20-cats-macrodef-true`. Timings were taken on a loaded machine and are provisional; counts and verdicts are what this report compares.

## Steps

Cycle figures are sources per cycle in `coreJVM` unless noted; reverts behave like their edits. R = bench (released), P = develop (perf), M = Merkle.

| Step | R / P | M | Verdict |
|---|---|---|---|
| functor-void-body | 1+1+31+**233**, 1,383 cl | same | same |
| functor-add-member | 1+81+84, 709 cl | **1+69+77+233, 1,420 cl** | signature (R, P) / same (M) |
| nel-private-member | 1+1+31+**233**, 1,383 cl | same | same |
| eval-add-case | 1+65+34, 652 cl | 1+64+34 | fresh-mismatch (noise, §4/§5) |
| show-add-implicit | 1+53+34, 545 cl | same | fresh-mismatch (noise) |
| show-implicit-type | 1+53+34, 545 cl | same | fresh-mismatch (noise) |
| package-object-add-alias | 1+1+31+**233**, 1,383 cl | same | same |
| eq-add-member | kernel 2+73, core 22+19+34, 725 cl | kernel 2+70, core 21+12+34, 708 cl | fresh-mismatch (R, P) / **bytecode** (M) |
| semigroup-combinen-body | kernel 1, 14 cl | same | same |

Compared with the first campaign (`false`): the body-only edits `functor-void-body` and `nel-private-member` went from 1+1 (9 and 2 classes) to the whole of `coreJVM` (1,383 classes), `package-object-add-alias` from 1+1 to the same, `eval-add-case`/`show-*` from 1+65+5+233 to 1+65+34 (the type-lambda name flip of §2 still happens but stops after two cycles), and `functor-add-member` is unchanged (709 vs. 705 cl; Merkle 1,420 as before).

## Anomalies

### 1. Merkle under-compiles: anonymous subclasses in a companion miss a new mixin forwarder (correctness, Merkle only)

- **Step:** `eq-add-member` (add `def zincCheck: Int = 1` to `cats.kernel.Eq`).
- **Verdict:** `bytecode` on Merkle, again under `recompileOnMacroDef=true` (335 differing classfiles in the rerun, in `kernelJVM` and the `coreJVM` instances that extend these traits; the setting doesn't touch it). In the first campaign: 312 classfiles in `kernelJVM` that the incremental compile did not write differ from the clean build: every anonymous class in `Order.scala` (125), `PartialOrder.scala` (103) and `Hash.scala` (84). Each lacks `public int zincCheck()`, the mixin forwarder scalac emits in every class that inherits a trait method.
- **Cycles:** kernelJVM 2+70 on Merkle vs. 2+73 on name hashing. The three sources Merkle skips are exactly those files.
- **Cause (from the code):** `filterDescendants` drops the traits `Order`, `PartialOrder`, `Hash`, since no `DescendantRule` says a trait reads an added inherited member. Their companions define `new Hash[A] { ... }` etc., which are concrete classes that need the forwarder. The local-inheritance relation from those anonymous classes to `Hash` is a self-dependency (the companion and the trait share the source class name `cats.kernel.Hash`), so it is dropped from the relations and `invalidateByLocalInheritance` cannot find them either.
- **Minimal repro (confirmed):** `trait A { def a: Int = 0 }` in A.scala; `trait B extends A; object B { def mk: B = new B {} }` in B.scala. Adding `def zincCheck: Int = 1` or `val zincVal: Int = 1` to `A`: name hashing recompiles both files and verifies `same`; Merkle recompiles only A.scala and `B$$anon$1.class` is `bytecode` (stale).
- **Impact:** for a `def`, only a missing forwarder (calls still dispatch to the interface default method). For a `val`, the stale class lacks the field, its accessor and the trait setter, so it fails at run time (`AbstractMethodError` on `zincVal`).
- **Follow-up:** a Merkle descendant rule: a trait descendant must recompile when its own source declares concrete local/anonymous subclasses of it (or: treat a trait descendant whose companion-object classes have local inheritance from it as reading every member change). The repro above makes the scripted test.

### 2. Name hashes of inherited type-lambda members differ between source and classfile parents (over-compilation, all Zincs)

- **Steps:** `eval-add-case`, `show-add-implicit`, `show-implicit-type` (and their reverts) end in a full recompile of `coreJVM` (233 sources in cycle 4) on all three Zincs; it also drives Merkle's `functor-add-member` cascade (anomaly 3).
- **First-cycle API changes:** the edit's own (e.g. `cats.Show: catsShowForZincCheck`), then in cycles 2 and 3 `cats.data.OneAnd`, `OneAndInstances`, `OneAndLowPriority0..3` report changed names `catsDataComonadForNonEmptyStream`, `catsDataComonadForNonEmptyLazyList`. Both are implicits, so `InvalidateUnconditionally` invalidates every member-ref dependent of `OneAnd` (1,108 classes) and `recompileAllFraction` recompiles the module.
- **Cause:** these implicits are declared in `OneAndLowPriority4` (its own file) with types `Comonad[OneAnd[Stream, *]]`. A 3-file repro without cats or kind-projector shows it on plain bench-1.12.x:

  ```scala
  // A.scala
  package p
  trait F[G[_]]
  final case class One[G[_], A](head: A, tail: G[A])
  abstract class A {
    def sameFile: F[({type L[a] = One[List, a]})#L] = null // changes
    def external: F[({type L[a] = Either[Int, a]})#L] = null // stable
    type O[a] = One[List, a]; def aliased: F[O] = null // stable
  }
  // B.scala
  package p
  abstract class B extends A { def b = 1 }
  class C extends B
  ```

  A body edit to `B.scala` after a clean build reports `B` and `C` changed in `sameFile` (and in kind-projector's `F[One[List, *]]`). Further incremental compiles of `B.scala` are stable; the next compile that types `A.scala` from source changes the hash back. So an inherited member whose type is a refinement projection mentioning a class from the parent's own source file hashes differently depending on whether the parent was typed from source or unpickled. In cats `OneAndLowPriority4.scala` is sometimes in the batch and sometimes not, so the hash flips on successive cycles.
- **Merkle:** in the minimal repro Merkle reports no change (it composes inherited names from the parent's stored hashes), but in cats it shows the same names in cycles 3 and 4, presumably when `OneAndLowPriority4.scala` itself is in the batch. Not chased further.
- **Cause and fix:** not `One`'s prefix: the type parameter of the eta-expanded alias `scala.package.List` in `One[List, a]`. Unpickled, the pickler has localised its owner to nothing (`Pickler.localizedOwner`); typed from source on 2.13 its owner is the alias's local dummy (`value <local List>`), so ExtractAPI named it `scala.package.A` from source and `A` from the pickle. rz#77 (develop) and rz#79 (1.x) first named alias-owned parameters by their simple name, which fixed 2.12 (scripted's default) but not 2.13, and renamed refinement lambdas' own parameters, breaking ExtractAPISpecification's sbt/sbt#1079 test. Follow-up commits (rz#79 f42d65ee5, rz#77 e887e3496) keep refinement-relative names and count the local dummy as the alias, with a 2.13 scripted test. On cats with integration/develop-1.12.x plus that commit: `show-add-implicit` 1+53 sources (379 classes, was 1,390), `eval-add-case` 1+65 (632, was 1,402), `functor-add-member` unchanged at 1+81. The Merkle bridge hasher (`tparamIDHashes`) needs the same rule; another session is porting it.

- **Rerun under `recompileOnMacroDef=true`:** the name flip still happens (`OneAndLowPriority0..1` report `catsDataComonadForNonEmptyStream`/`LazyList` on `eval-add-case`, cycles 2 and 3), but ends there, so `eval-add-case` and `show-*` cost 545-652 classes instead of the whole module. The flip is what turns §6's macro cascade into a full-module recompile (1,115 classes invalidated after cycle 3 of `functor-void-body`).

### 3. Merkle cascades on adding a member to `Functor` (over-compilation, Merkle only)

- **Step:** `functor-add-member` (and revert): Merkle 1+69+73+233 sources, 1,420 classes, 10.5 s; name hashing 1+81, 705 classes, 3.7 s.
- **API changes:** cycle 1 `cats.Functor: zincCheck`. From cycle 2 on, Merkle reports 50, then 42, then 16 traits with `TraitPrivateMembersModified` and no names (e.g. `cats.data.Tuple2KApply`, `EitherTFunctor`, `ComposedTraverse`, `StackSafeMonad`), plus anomaly 2's `OneAnd*` implicits in cycles 3 and 4, which make cycle 4 a full recompile.
- **Cause:** a trait's extraHash folds in its trait parents' extraHashes, and a trait's own extraHash covers its whole API, so the public addition to `Functor` changes the extraHash of every trait below it. On Merkle the subtrait's own API is unchanged (`SameAPI` holds), so `findAPIChange` reports `TraitPrivateMembersModified`, and with no `AncestorChange` `filterDescendants` keeps all its descendants. The descendants are invalidated one inheritance level per cycle, recompiling `OneAnd*` along the way, instead of once as name hashing does.
- **Follow-up:** on Merkle, a subtrait whose extraHash moved only because a parent's public API moved should not report a private change (fold only the parents' private-member hashes, not their whole extraHash). Without anomaly 2 the cascade would stop at roughly 1+69+73; with both fixed Merkle should beat name hashing here as it does on scala/scala.

### 4. Specialised forwarders and type-variable names differ with the batch (correctness noise, all Zincs; scalac)

- **Steps:** `eval-add-case`, `show-add-implicit`, `show-implicit-type`, `eq-add-member` and reverts: 22-31 `fresh-mismatch` classes on every cell, all anonymous classes in core instances (`Parallel$$anon$1`, `ChainInstances$$anon$2`, `ConstInstances*$$anon$*`, `EvalInstances$$anon$6`, `Apply$AbstractApply`). The one inspected (`Parallel$$anon$1` on `eval-add-case`) differs by generic signatures with `<A>` vs. `<A$>` and the constant-pool indices that shift with them: §5's family.
- **First campaign's instance:** `eq-add-member` and revert: `SortedMapCommutativeMonoid.class` has different specialised forwarder return types and is missing bridges depending on what else is in the run (27 methods incremental, 31 clean). Not re-examined in the rerun. Needs a plain-scalac repro; if confirmed, a scalac bug that can change dispatch.
- **New under `true`, not new in kind:** `eval-add-case` and `show-*` were `same` in the first campaign only because their 233-source cycle recompiled the module in one batch. Now that they stop at 34 sources, the batch dependence shows. Identical on all three cells, so it is noise rather than a Zinc difference.

### 5. Package object: anonymous class type-parameter names (correctness noise, all Zincs; scalac; first campaign)

- **Rerun:** `package-object-add-alias` is `same` on all cells now: the macro cascade (§6) recompiles the whole module in one batch. The instability is still there in principle (see §4).
- **Step:** `package-object-add-alias` and revert (add `type ZincCheck = Int` to `package object cats`): `cats/package$$anon$1.class` is `fresh-mismatch` on all three. Generic signatures use `<A>` in the incremental build and `<A$>` in the clean one, and that shifts constant-pool indices, so IncBench's signature normalisation doesn't absorb it. Same family as scala#11319 (names that depend on the batch).
- **Follow-up:** IncBench could normalise constant-pool indices (compare javap-level instructions) when the only differences are type-variable names; then this is `signature`.

### 6. The macro rule turns body edits into whole-module recompiles (over-compilation, all Zincs; with recompileOnMacroDef=true)

- **Steps:** `functor-void-body`, `nel-private-member`, `package-object-add-alias`: 1+1+31+233 sources, 1,383 of 1,777 classes, on all three cells, instead of 1+1 (2 to 9 classes) with `false`.
- **Cause:** recompiling anything that `cats.arrow.FunctionK`'s macro (`lift`, in `FunctionKMacroMethods`) depends on makes `IncrementalCommon`'s macro rule invalidate it, and with `true` that is an "API change due to macro definition" for `FunctionKMacroMethods`, which invalidates all of its dependents (49 classes, 31 sources in cycle 3). Those include the `OneAnd*` implicits, so §2's name flip fires (1,115 classes next in line) and cycle 4 recompiles 233 sources, the rest of `coreJVM`.
- **Cost of soundness:** this is the real price of `true` on cats: any edit under `FunctionK`'s dependencies recompiles the module, about 150x the classes of the unsound setting on a body edit. It is the same on name hashing and Merkle. Fixing §2 should end the cascade after cycle 3 (not measured); a macro-impl fingerprint (shapeless §1's follow-up) would avoid it altogether.
- **First campaign:** with `false` this was a harmless extra source in cycle 2, which is how it was first described.

### Performance

- Timings in the rerun are provisional (loaded machine). Merkle's `analysis` phase is higher than the others', but that is not attributable to Merkle: the pinned cells carry a harness bug (IncHandler used an uncached `Locate.definesClass`, fixed in rz#71 4cba55a47) that adds about 100 ms per step to every Merkle cell.
- `analysisWrite` is ~90-100 ms per core step on every Zinc (core's analysis is a few MB), about half of Zinc's own time on body edits.
