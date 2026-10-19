# IncBench anomalies: typelevel/cats

- **Build:** typelevel/cats at `main` (shallow clone, 2026-10-19), Scala 2.13.18, modules `kernelJVM` (95 sources), `coreJVM` (245), `freeJVM` (13). Options as the build sets them: `-Xsource:3`, kind-projector and better-monadic-for plugins, `-release 8`.
- **Run:** `lockstep --verify --profile`, cells `s2-released-released` (bench-1.12.x f7b7642c03), `s2-released-perf` (develop-1.12.x 5615b62e16), `s2-released-merkle` (merkle-1.12.x 556464169f); lockstep's defaults (pipelining off, recompileAllFraction 0.5, recompileOnMacroDef false). Clean build ~6.3 s warm. Edit script: `edits/cats.tsv`. Results: `~/code/.integration/campaigns/2026-10-19-cats`.

## Steps

| Step | released | perf | merkle | Verdict |
|---|---|---|---|---|
| functor-void-body | 1+1 (9 cl) | 1+1 | 1+1 | signature |
| functor-add-member | 1+81, 705 cl | 1+81, 705 cl | **1+69+73+233, 1420 cl** | signature / same |
| nel-private-member | 1+1 | 1+1 | 1+1 | signature |
| eval-add-case | 1+65+5+**233** | same | 1+64+5+**233** | same |
| show-add-implicit | 1+53+5+**233** | same | same | same |
| show-implicit-type | 1+53+5+**233** | same | same | same |
| package-object-add-alias | 1+1 | 1+1 | 1+1 | **fresh-mismatch** (all) |
| eq-add-member | kernel 2+73, core 22+19, 543 cl | same | kernel 2+70, core 21+12, 526 cl | **fresh-mismatch** (all); **bytecode** (merkle) |
| semigroup-combinen-body | 1 | 1 | 1 | same |

Cycle figures are sources per cycle in `coreJVM` unless noted; reverts behave like their edits.

## Anomalies

### 1. Merkle under-compiles: anonymous subclasses in a companion miss a new mixin forwarder (correctness, Merkle only)

- **Step:** `eq-add-member` (add `def zincCheck: Int = 1` to `cats.kernel.Eq`).
- **Verdict:** `bytecode` on Merkle; 312 classfiles in `kernelJVM` that the incremental compile did not write differ from the clean build: every anonymous class in `Order.scala` (125), `PartialOrder.scala` (103) and `Hash.scala` (84). Each lacks `public int zincCheck()`, the mixin forwarder scalac emits in every class that inherits a trait method.
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
- **Cause and fix:** not `One`'s prefix: the type parameter of the eta-expanded alias `scala.package.List` in `One[List, a]`. From source its owner is the alias, so ExtractAPI names it `scala.package.A`; the pickler stores it with owner `nonClassRoot` (`Pickler.localizedOwner`), so unpickled it is `<none>.A`. Fixed in retronym/zinc#77 (a type parameter owned by an alias or abstract type, or by nothing, is named by its simple name), with a scripted test from this repro. The Merkle bridge hasher (rz#24, `tparamIDHashes`) needs the same rule when #77 reaches the Merkle line. Not yet checked end to end on cats.

### 3. Merkle cascades on adding a member to `Functor` (over-compilation, Merkle only)

- **Step:** `functor-add-member` (and revert): Merkle 1+69+73+233 sources, 1,420 classes, 10.5 s; name hashing 1+81, 705 classes, 3.7 s.
- **API changes:** cycle 1 `cats.Functor: zincCheck`. From cycle 2 on, Merkle reports 50, then 42, then 16 traits with `TraitPrivateMembersModified` and no names (e.g. `cats.data.Tuple2KApply`, `EitherTFunctor`, `ComposedTraverse`, `StackSafeMonad`), plus anomaly 2's `OneAnd*` implicits in cycles 3 and 4, which make cycle 4 a full recompile.
- **Cause:** a trait's extraHash folds in its trait parents' extraHashes, and a trait's own extraHash covers its whole API, so the public addition to `Functor` changes the extraHash of every trait below it. On Merkle the subtrait's own API is unchanged (`SameAPI` holds), so `findAPIChange` reports `TraitPrivateMembersModified`, and with no `AncestorChange` `filterDescendants` keeps all its descendants. The descendants are invalidated one inheritance level per cycle, recompiling `OneAnd*` along the way, instead of once as name hashing does.
- **Follow-up:** on Merkle, a subtrait whose extraHash moved only because a parent's public API moved should not report a private change (fold only the parents' private-member hashes, not their whole extraHash). Without anomaly 2 the cascade would stop at roughly 1+69+73; with both fixed Merkle should beat name hashing here as it does on scala/scala.

### 4. Specialised forwarders differ with the batch (correctness noise, all Zincs; scalac)

- **Step:** `eq-add-member` and revert: `coreJVM/cats/instances/SortedMapCommutativeMonoid.class` is `fresh-mismatch` on all three Zincs. In the incremental build, `reverse$mcD$sp()` etc. return `CommutativeSemigroup` and the class has 27 methods; the clean build has them returning `CommutativeMonoid` plus bridges returning `CommutativeSemigroup` (31 methods). The class extends `SortedMapMonoid[K, V] with CommutativeMonoid[...]` (both specialised traits from `kernelJVM`).
- **Follow-up:** reproduce with plain scalac by compiling `sortedMap.scala` alone against core's classfiles vs. the whole module; if confirmed, a scalac issue in specialisation's forwarders/bridges depending on what else is in the run. Missing bridges can change dispatch, so this is more than a verify-normalisation question.

### 5. Package object: anonymous class type-parameter names (correctness noise, all Zincs; scalac)

- **Step:** `package-object-add-alias` and revert (add `type ZincCheck = Int` to `package object cats`): `cats/package$$anon$1.class` is `fresh-mismatch` on all three. Generic signatures use `<A>` in the incremental build and `<A$>` in the clean one, and that shifts constant-pool indices, so IncBench's signature normalisation doesn't absorb it. Same family as scala#11319 (names that depend on the batch).
- **Follow-up:** IncBench could normalise constant-pool indices (compare javap-level instructions) when the only differences are type-variable names; then this is `signature`.

### 6. Macro rule costs a cycle on body edits (minor, all Zincs)

`functor-void-body` and `nel-private-member` recompile a second source with no API change: `IncrementalCommon`'s "macro classes that transitively depend on recompiled classes" rule invalidates `cats.arrow.FunctionK` (its `lift` macro). Cheap here (1 source); see shapeless for where it hurts.

### Performance

- Merkle's `analysis` phase is 1.5-5x the others' on large steps (514 vs. 98 ms on `functor-add-member`; 340 vs. 240 ms on the clean build), and its Zinc-side time on a one-file kernel edit is 137 vs. 87 ms. Consistent with the composition cost fixed in rz#48 9e99fb249 (not yet in integration/merkle-1.12.x).
- `analysisWrite` is ~90-100 ms per core step on every Zinc (core's analysis is a few MB), about half of Zinc's own time on body edits.
