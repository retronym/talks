# Test coverage of the Merkle name-hashing PoC: precision vs soundness

Audited code: `~/code/.integration/integration-merkle` at `f105271a0` (integration/develop + rz#24 + rz#30); the scripted tests and `DescendantRules.scala` are identical at the earlier build `f74915035`. Design doc: `PLAN-merkle-poc.md` (same text as `claude/merkle-stable-hashes`). Nothing was built or run: there is no build set up in the integration checkout, so every expectation below comes from reading the test scripts, `DescendantRules.scala`, `IncrementalNameHashing.scala` and `IncHandler.scala`.

## Summary

- Of the 74 `merkle*` scripted tests (this count includes the 12 `merkle-x-*` and 11 `merkle3-*`), 7 assert a recompiled set with `checkRecompilations` that is smaller than baseline Zinc's. Only 5 of them would fail on baseline: `merkle-member-type`, `merkle-mirror-nested`, `merkle-trait-direct`, `merkle-x-member-type`, `merkle-x-trait-class-ancestor`. The other two, `merkle-subproject` and `merkle-exports-scala2-fbound`, assert only the round-1 set. On baseline the descendants also recompile in round 2, so both tests pass on baseline too.
- Four upstream tests changed by rz#24 also pin precision against a baseline that develop itself pins: `transitive-class`, `transitive-memberRef`, `class-based-inheritance`, `local-class-inheritance`. They run with scripted's default `apiDebug = true`, which forces the TREE path, not the default bridge-hashing (HASHES) path.
- Baseline sets are pinned for two tests only: `merkle-member-type` (`B C X Y`) and `merkle-as-seen-from` (`C X Y Z`, the same as the PoC's). Both pins live only in history, in sbt/zinc commit `719076285` ("Pin today's recompilations for inherited-member edits"). The A side, `claude/merkle-baseline`, has no `merkle*` tests at all. No test uses `descendantRules = all`, `strict` or `none`. The ablation claims in the PLAN and the talk ("`none` fails all of them") come from manual runs and are not encoded anywhere.
- There are no unit tests for `DescendantRule`, `HierarchyView` or `ApiHashCheck`. The Merkle-specific unit tests are `MerkleHashesStabilitySpec`, which checks that hashes are stable across JVMs, and a few `ExtractAPISpecification` cases (one asserts that an internally inherited member is not materialised). No scripted test runs in `apiCheck` (CHECK) mode. `IncBench` and `Conformance` record recompiled sets but assert only correctness (clean equals incremental), not precision.
- Several precision tests assert the positive set of a later round but never pin the descendants at `checkRecompilations 0`. `checkRecompilations k S` checks that S is exactly the set of classes whose *last* compilation was round k. A descendant recompiled in a later round would therefore go unnoticed.

## How a test was categorised

- PRECISION: a `checkRecompilations` line asserts a set strictly smaller than baseline Zinc's for the same edit.
- SOUNDNESS-R: a negative or runtime test that needs a descendant rule. It is expected to undercompile under `descendantRules = none`. Where the PLAN or the talk says so this is stated; otherwise "(inferred)".
- SOUNDNESS-M: needs another part of the PoC (cross-subproject `MerkleHashes` composition, stored-linearization freshness, macro-expansion edges over descendants, package-scope composition, library-ancestor stamps, the bridge storing both companion sides). It does not depend on `descendantRules`.
- REGRESSION: passes with the rules on or off (subsumed by `memberRef` edges, or a stability or bug check), and does not discriminate precision.
- DISCOVERY / OTHER: test discovery, a bridge crash, dependency bookkeeping.

The baseline-pinned column says whether the baseline recompiled set is written down anywhere. For negative tests ("must fail to compile") it is n/a: both sides must fail.

Baseline mechanics used below, from develop's `IncrementalNameHashing`: after round 1 recompiles the edited class, round 2 recompiles every transitive descendant, plus the `memberRef` clients of the class and of every descendant whose used names meet the modified names. For an upstream edit, the downstream descendants and clients are all invalidated in the first downstream cycle. Scripted sets `recompileAllFraction = 1.0`, so small tests never fall back to recompile-all. The pinned baseline `2 B C X Y` of `merkle-member-type` confirms there is no third round in that shape.

## Table of merkle* tests

| test | edit | category | rule or mechanism | baseline set pinned? |
|---|---|---|---|---|
| merkle-abstract | `A.m` concrete to abstract; concrete `B extends A` | SOUNDNESS-R (talk) | abstract | n/a (neg.) |
| merkle-abstract-ancestor | `B` drops its implementation of `A.m`; concrete `C extends B` | SOUNDNESS-R (PLAN, Lean) | abstract, name deferred in any ancestor | n/a |
| merkle-as-seen-from | `B extends A[Int]` to `A[String]` (§10a Edit 2) | REGRESSION: pins `1 B`, `2 C X Y Z`, equal to baseline | header rule + unfiltered memberRef of descendants' clients; class-name hash | yes, `719076285` (history only); same set |
| merkle-bridge-shadowed-inner | none, clean compile | OTHER (bridge crash) | bridge keys extracted classes by name | n/a |
| merkle-companion-class-side | case class `Leaf.m: Int` to `String`; non-descendant client | REGRESSION wrt rules; bridge fix | bridge stores class and module sides | n/a |
| merkle-conflict | `A.m: Int` to `String`; `C extends B with M`, `M.m: Int` | SOUNDNESS-R (talk) | conflicts | n/a |
| merkle-discovery | none; `@Test` in a base class two levels up | DISCOVERY | bridge keeps annotated inherited members | n/a |
| merkle-discovery-added | `Base` gains a `@Test` method; `FooTest extends Mid extends Base` | DISCOVERY, SOUNDNESS-R (inferred) | annotated | n/a |
| merkle-discovery-witness | none | DISCOVERY | erased-signature witness hidden from discovery | n/a |
| merkle-discovery-witness-tree | none, `bridgeHashing = false` | DISCOVERY | same, on the TREE path | n/a |
| merkle-export-inherited-scala3 | trait `Base` gains `object Foo`; `U extends Base`; `export a.U.*` | SOUNDNESS-R (inferred), Scala 3 | exports + package-scope added names | n/a |
| merkle-exports-scala2-fbound | `TreeNode` gains unused `bench1`; `Leaf` case class 3 levels down | PRECISION intended, **weak**: `p/checkRecompilations 1 t.TreeNode` holds on baseline too | exports must not fire when the class side is stored | no |
| merkle-header | `A` becomes `final` | REGRESSION wrt rules (PLAN: no test fails without `header`); fails on develop (HashAPI skips top-level modifiers) | header / class-name hash | pending on baseline (`719076285`) |
| merkle-header-grandchild | `A` gains parent `X` with abstract `y`; concrete `C extends B extends A` | SOUNDNESS-M (inferred: class-name cascade) | header, class-name hash cascade | n/a |
| merkle-implicit | `A.i: Int` to `Long`; `B` uses `implicitly[Int]` | REGRESSION (fallbacks subsumed) | memberRef | n/a |
| merkle-java-static | Java `A.s()` result type; Scala `B extends A` (lib); Java `J` calls `B.s()` (app) | SOUNDNESS-M | cross-subproject composition for a Java client | n/a |
| merkle-java-static-internal | same, all Java, one subproject | REGRESSION | ClassToAPI materialises | n/a |
| merkle-java-static-pure | same, Java lib and Java app | REGRESSION | ClassToAPI | n/a |
| merkle-lib-abstract | `P` drops `next()`, deferred in `Iterator` | SOUNDNESS-R | abstract via library stubs | n/a |
| merkle-lib-abstract-other-path | `P` drops `canEqual`; `D extends P with Product` | SOUNDNESS-R | abstract, library ancestor on another path | n/a |
| merkle-lib-conflict | `P` gains `isEmpty: String`; `D extends P with Seq[Int]` | SOUNDNESS-R | conflicts, externally inherited names | n/a |
| merkle-libjar-java-client | jar `L.m` result type; `D extends L`; downstream Java client | REGRESSION (PLAN: passes under `stubs-only`) | Java client depends on the jar | n/a |
| merkle-libjar-override | jar abstract `L.m` type; `E extends D extends L` declares `m` | SOUNDNESS-M (fails under `libraryAncestors=stubs-only`) | jar-stamp folding + overrides | n/a |
| merkle-member-type | `A.m: Int` to `String` (§10a Edit 1) | PRECISION: `1 A`, `2 X Y` | no rule fires; memberRef to the owner | yes, `2 B C X Y` in `719076285` (history only) |
| merkle-mirror | `A.m` type; top-level `object O extends A`; Java calls `O.m()` | SOUNDNESS-R (talk) | mirror | n/a |
| merkle-mirror-nested | `A` gains `k`; `class G { object N extends A }` | PRECISION: `1 A`, `0 G G.N` | mirror does not fire for a nested object | no (baseline: `G G.N` in round 2) |
| merkle-move-ancestor-downstream | `A` moves lib to app, then `A.m` changes | SOUNDNESS-M | external-to-internal ancestor | n/a |
| merkle-move-ancestor-downstream-macro | same, macro client of `B` | SOUNDNESS-M | macro-expansion edges over descendants (PLAN) | n/a |
| merkle-move-ancestor-upstream | `A` moves app to lib, then changes | SOUNDNESS-M | `MerkleHashes` composition | n/a |
| merkle-move-ancestor-upstream-macro | same, macro client | SOUNDNESS-M | composition for a macro client | n/a |
| merkle-nowarn-separate | comment-only edit of `B` | REGRESSION (stability): `1 B`, `0 A C` | only static annotations make inherited members visible | no (same set expected on baseline) |
| merkle-override | `A.m` type; `C extends B` overrides `m` | SOUNDNESS-R (talk) | overrides | n/a |
| merkle-pipelined-java-self | unrelated `Other.x` edit | OTHER: asserts dependency kind (`checkExternalDependencies`); guards an overcompile | Java-only callback records internal deps | n/a |
| merkle-pobj-inherited-implicit | trait `Base` gains an implicit; `package object b extends Base` | SOUNDNESS-M | package-scope implicits composed over ancestors | n/a |
| merkle-pobj-inherited-libjar | same, `Base` in a jar | SOUNDNESS-M | library ancestors + package scope | n/a |
| merkle-pobj-inherited-member | `Base` gains `object Foo` shadowing `a.Foo` | SOUNDNESS-M | package-scope added names composed | n/a |
| merkle-pobj-inherited-member-scala3 | same, Scala 3 | SOUNDNESS-M | same | n/a |
| merkle-pobj-inherited-subproject | same, `Base` upstream | SOUNDNESS-M | same, across subprojects | n/a |
| merkle-subproject | lib `A.m` type; lib `B extends A`; app `X` uses `(new B).m` | PRECISION intended, **weak**: `lib/checkRecompilations 1 lib.A` holds on baseline too (B is round 2 there) | memberRef to owner across subprojects | no |
| merkle-subproject-class-header | `A` gains parent `X0`; `trait N extends A`; app reads `x` through `N` | SOUNDNESS-M | stored linearization freshness | n/a |
| merkle-subproject-header-cascade | `A extends M[Int]` to `M[String]`; `B`, `C` below; macro client | SOUNDNESS-M | linearization freshness, class-name cascade | n/a |
| merkle-subproject-header-cascade-alias | same, `C` names `B` through an alias | SOUNDNESS-M | same | n/a |
| merkle-subproject-header-cascade-java | same, Java intermediate; then `X0` edit | SOUNDNESS-M | same | n/a |
| merkle-subproject-header-cascade-path | same, path-dependent parent | SOUNDNESS-M | same | n/a |
| merkle-subproject-header-stale-lin | `P` gains parent `X0`, then `X0.x` changes | SOUNDNESS-M | same | n/a |
| merkle-subproject-trait-header | `trait N extends M[Int]` to `M[String]`; `C extends N`; app `Y` | SOUNDNESS-M | composition through a trait header | n/a |
| merkle-trait | `T.m` type; `B extends T` | REGRESSION (PLAN: doesn't discriminate, JVM default methods) | traitDirect | n/a |
| merkle-trait-direct | `T.m` type; `U extends T`, `B extends U`, `C extends B` | PRECISION: `1 T`, `2 B X` | traitDirect vs `trait` | no (baseline: `2 B C U X`) |
| merkle-trait-override | trait `T` gains an override of class `P.m` | SOUNDNESS-R (talk) | traitDirect | n/a |
| merkle-uses | `A.m` type; `B`'s body uses `m` | REGRESSION (uses subsumed) | memberRef | n/a |
| merkle-wildcard-import-inherited | `Base` gains `Foo`; `object W extends Base`; `import w.W._` | SOUNDNESS-M | sibling-class check of added names | n/a |
| merkle-x-abstract | upstream `A.m` becomes abstract | SOUNDNESS-R (PLAN: one of six) | abstract, external | n/a |
| merkle-x-abstract-ancestor | upstream `B` drops `m` | SOUNDNESS-R | abstract, any ancestor | n/a |
| merkle-x-abstract-bridge | app `B` gains `override m`; `C extends B with M` | SOUNDNESS-R (inferred) | conflicts (bridge must go) | n/a |
| merkle-x-conflict | upstream `A.m` type; app `C extends A with M` | SOUNDNESS-R | conflicts, external | n/a |
| merkle-x-header | upstream `A` becomes `final` | REGRESSION wrt rules (inferred) | header via composed top-level header | n/a |
| merkle-x-header-kind | upstream `A` class to trait | REGRESSION wrt rules | class-name hash covers kind | n/a |
| merkle-x-member-type | upstream `A.m` type; app `C extends B extends A`; `X` uses `C.m` | PRECISION: `app/checkRecompilations 1 p.X` | external descendant filter | no (baseline: app round 1 = `B C X`) |
| merkle-x-mirror | upstream `A.m`; app top-level `object O extends A` | SOUNDNESS-R | mirror, external | n/a |
| merkle-x-override | upstream `A.m`; app `C` overrides | SOUNDNESS-R | overrides, external | n/a |
| merkle-x-trait-class-ancestor | upstream class `A.m`; `trait T extends A`; app `B extends T` | PRECISION: `app/checkRecompilations 1 p.X` | traitDirect with forwarder hashes | no (baseline: `B X`) |
| merkle-x-trait-move | `m` moves from trait `Q` to class `A` upstream | SOUNDNESS-R (inferred) | traitDirect forwarder hashes | n/a |
| merkle-x-trait-override | upstream trait `T` gains an override of `P.m` | SOUNDNESS-R | traitDirect, external | n/a |
| merkle3-enum-abstract | trait `P` gains abstract `y`; enum cases | SOUNDNESS-R (PLAN) | abstract | n/a |
| merkle3-export-add | `A` gains `n`; `W` exports `d.*` | SOUNDNESS-R (PLAN) | exports | n/a |
| merkle3-export-change | `A.m` type; exported forwarder | REGRESSION (PLAN) | memberRef | n/a |
| merkle3-given-ambiguous | trait `P` gains a second given | REGRESSION (PLAN) | memberRef (implicit) | n/a |
| merkle3-inline-descendant | inline `P.m` body changes | REGRESSION (PLAN) | inline body in API hash | n/a |
| merkle3-macro-members | `A.x` type; quotes macro reads `B`'s inherited member | REGRESSION (PLAN) | macro-expansion edges | n/a |
| merkle3-mirror | `A.m` type; `object O extends A`, Java client | SOUNDNESS-R (PLAN) | mirror | n/a |
| merkle3-nowarn-separate | comment-only edit of `B` | REGRESSION (stability): `1 B`, `0 A C`; runs with `apiDebug = true` | TASTy annotations | no |
| merkle3-opaque | opaque type representation changes | REGRESSION (PLAN) | memberRef | n/a |
| merkle3-trait-param | trait parameter type changes | REGRESSION (PLAN) | memberRef / constructor | n/a |
| merkle3-transparent-inline | transparent inline body changes | REGRESSION (PLAN) | inline body in API hash | n/a |

Counts: PRECISION 7, of which 5 discriminate. SOUNDNESS-R 22 (several inferred), one of them also DISCOVERY. SOUNDNESS-M 20. REGRESSION 20. DISCOVERY 3. OTHER 2. Total 74.

## Other tests and harnesses

- Upstream scripted tests whose expectations rz#24 changed:
  - `transitive-class`: depth-3 chain; adding an unused member now pins `0 B C D Hello`, `1 A`, where develop pins `2 B C D Hello`.
  - `transitive-memberRef`: same shape plus a client of `B`; pins `0 X Y B C D`, where develop pins `2 B C D`.
  - `class-based-inheritance`: nested class added to `A`; `C extends A` now `0`, previously round 2.
  - `local-class-inheritance`: `B` now `0`, previously round 2.
  These are real precision pins, with the baseline pinned by develop's own copy. All four run with `apiDebug = true`, so on the TREE path.
- Other upstream tests changed by rz#24 (`added-*-package-object*`, `added-member-wildcard-import-*`, `package-object-member-clashes-with-class-scala3`): only the comments changed. Where develop got a correct result by accident through a materialised member, the PoC needed explicit package-scope invalidation. These tests show soundness, not precision.
- `MultiProjectIncrementalSpec` "recompile Java on upstream changes": rz#24 changed the edit from a rename `a` to `a1` into a type change, and made `B` use `a`, so that `B` still recompiles. The old version would have been a cross-subproject precision case (the PoC recompiles only `Z`, develop `B Z`). That case was rewritten away rather than pinned.
- Unit tests:
  - `MerkleHashesStabilitySpec`: composed hashes are identical in a forked JVM.
  - `ExtractAPISpecification`: `Global.Foo` does not materialise the internally inherited `Namer`, while the same class inherited from a library does; an inherited class seen through `A[Int]` vs `A[String]` changes `B`'s API only; inherited Java members are stable whether or not their type was forced.
  - There are no tests of `DescendantRules`, `HierarchyView`, `AncestorChange.headerChanged`, `ApiHashCheck` or `LibraryAncestors`.
- Ablation: `DescendantRules.fromOptions` accepts `all`, `default`, `strict`, `none`, `r1,r2` and `-r1,-r2`. No scripted test sets any of them.
- Check mode: `apiCheck` and `-Dxsbt.api.check=true` are exercised only by manual runs (PLAN: "smoke scripted 76 tests ... 0 disagreements"). No committed test enables them.
- `IncBench`: edits `root-body`, `root-add-member`, `root-add-used-overload`, `mid-add-member`. It records rounds, recompiled counts, wall time and stored sizes. A/B means diffing two JSON outputs; nothing is asserted. `--verify` checks soundness only.
- `Conformance` (rz#25): Lean-generated programs and hand-written spaces (`bin/conformance-spaces.py`). It writes `recompiled` per case to JSON, but its oracle is incremental equals clean. `KeyCheck` checks recorded keys against the model. Neither compares recompiled sets with baseline Zinc or with the model's expected minimal set.

## Gaps and proposed tests

All proposals use `incOptions.properties` = `apiDebug = false`, as the `merkle-*` tests do, so they exercise stored minimized APIs and the HASHES path. Class names in `checkRecompilations` are the analysis names, so `object X` is `X`. Round 0 is the initial compile. `checkRecompilations k S` asserts that S is exactly the set of classes whose last compile was round k, so each proposal also pins the untouched descendants at round 0.

### Gap 0: existing precision assertions that do not discriminate, or are incomplete

Lines to add (expected to pass on the PoC; each `0` line fails on baseline):

- `merkle-subproject`: `> lib/checkRecompilations 0 lib.B` (baseline: `lib.B` in round 2).
- `merkle-exports-scala2-fbound`: `> p/checkRecompilations 0 e.Expression e.UnaryExpression e.Leaf` (baseline: all three in round 2).
- `merkle-member-type`: `> checkRecompilations 0 B C M Z Main` (baseline: `B C` in round 2).
- `merkle-trait-direct`: `> checkRecompilations 0 C U Main` (baseline: `C U` in round 2).
- `merkle-x-member-type`: `> app/checkRecompilations 0 p.B p.C` (baseline: app round 1 = `p.B p.C p.X`).
- `merkle-x-trait-class-ancestor`: `> app/checkRecompilations 0 p.B` (baseline: app round 1 = `p.B p.X`).

### Gap 1: deep hierarchy, member used only by clients, at each depth

`transitive-class` and `transitive-memberRef` pin depth 3, but for an *added unused* member, with no client of the changed name. `merkle-member-type` has a client of the changed name, but only at depth 2. No test changes a member used by clients at every level of a depth-3 chain, and none edits a mid-level class.

`merkle-deep-member-type`:

```scala
// A.scala
abstract class A { def m: Int = 0; def g: Int = 0 }
// B.scala
class B extends A
// C.scala
class C extends B
// D.scala
class D extends C
// XA.scala
object XA { def f(a: A): Any = a.m }
// XB.scala
object XB { def f(b: B): Any = b.m }
// XC.scala
object XC { def f(c: C): Any = c.m }
// XD.scala
object XD { def f(d: D): Any = d.m }
// ZD.scala
object ZD { def f(d: D): Any = d.g }
// changes/A.scala
abstract class A { def m: String = "s"; def g: Int = 0 }
// changes/B.scala
class B extends A { def k: Int = 0 }
```

```
> compile
$ copy-file changes/A.scala A.scala
> compile
> checkRecompilations 1 A
> checkRecompilations 2 XA XB XC XD
# a mid-level class gains a member nobody uses
$ copy-file changes/B.scala B.scala
> compile
> checkRecompilations 3 B
> checkRecompilations 0 C D ZD
```

PoC: no rule fires for `B`, `C` or `D`: none declares `m`, `m` is concrete, there is no other path, and the header is unchanged. Each client records a `memberRef` on the owner `A` with used name `m`. For the `B` edit the modified names are `{k}`; nothing uses it.

Baseline: round 2 = `B C D XA XB XC XD`; round 4 = `C D` after the `B` edit. `ZD` stays on both sides. Confidence: high.

### Gap 2: remove an unused concrete member from an ancestor

`merkle-remove-unused`:

```scala
// A.scala
abstract class A { def m: Int = 0; def gone: Int = 0 }
// B.scala
class B extends A
// C.scala
class C extends B
// X.scala
object X { def f(c: C): Any = c.m }
// changes/A.scala
abstract class A { def m: Int = 0 }
```

```
> compile
$ copy-file changes/A.scala A.scala
> compile
> checkRecompilations 1 A
> checkRecompilations 0 B C X
```

PoC: the modified names are `{gone}`. No client uses it and no rule fires; `exports` does not, because the stored parents of `B` and `C` name `A`.

Baseline: round 2 = `B C`. Confidence: high.

### Gap 3: name filtering through a descendant that uses a different member

`merkle-member-type` already has `Z` (a client of `B` via `g`), but `Z` stays on baseline too, so it shows name filtering, not Merkle. The Merkle-specific contrast is with `merkle-uses`: a descendant whose own body uses a *different* inherited member. On baseline it recompiles; on the PoC its used names do not meet the modified names.

`merkle-uses-other`:

```scala
// A.scala
class A { def m: Int = 0; def g: Int = 0 }
// B.scala
class B extends A { def useG: Int = g }
// X.scala
object X { def f(b: B): Any = b.m }
// Z.scala
object Z { def f(b: B): Any = b.useG }
// changes/A.scala
class A { def m: String = ""; def g: Int = 0 }
```

```
> compile
$ copy-file changes/A.scala A.scala
> compile
> checkRecompilations 1 A
> checkRecompilations 2 X
> checkRecompilations 0 B Z
```

Baseline: round 2 = `B X`. Under `strict` (which adds `uses`) the PoC gives the same result, because `g` is not modified. Confidence: high. Also add the Gap 0 line to `merkle-member-type`.

### Gap 4: an overload added to an ancestor member that clients of a descendant use

IncBench's `root-add-used-overload` shows this at scale (A 1,278, B 768 recompiled), but no scripted test pins it.

`merkle-add-overload`:

```scala
// A.scala
class A { def m(x: Int): Int = x }
// B.scala
class B extends A
// C.scala
class C extends B
// X.scala
object X { def f(c: C): Any = c.m(1) }
// Z.scala
object Z { def f(c: C): Any = c.toString }
// changes/A.scala
class A { def m(x: Int): Int = x; def m(x: String): Int = 0 }
```

```
> compile
$ copy-file changes/A.scala A.scala
> compile
> checkRecompilations 1 A
> checkRecompilations 2 X
> checkRecompilations 0 B C Z
```

PoC: the modified names are `{m}`. `B` and `C` declare only `<init>`. `conflicts` sees no other path declaring `m`, so `X` is the only `m` client.

Baseline: round 2 = `B C X`. Confidence: high.

### Gap 5: trait vs class ancestor in one test

`merkle-trait-direct` (trait chain) and `merkle-x-trait-class-ancestor` (class through a trait, cross-subproject) cover the halves separately. A single-subproject contrast:

`merkle-trait-vs-class`:

```scala
// A.scala
abstract class A { def m: Int = 0 }
// T.scala
trait T { def n: Int = 0 }
// B.scala
class B extends A with T
// C.scala
class C extends B
// X.scala
object X { def f(c: C): Any = c.m }
// Y.scala
object Y { def f(c: C): Any = c.n }
// Main.scala
object Main {
  def main(args: Array[String]): Unit = {
    assert(X.f(new C).toString == args(0), X.f(new C))
    assert(Y.f(new C).toString == args(1), Y.f(new C))
  }
}
// changes/A.scala
abstract class A { def m: String = "s" }
// changes/T.scala
trait T { def n: String = "s" }
```

```
> run 0 0
# class ancestor: no descendant holds anything for m
$ copy-file changes/A.scala A.scala
> run s 0
> checkRecompilations 1 A
> checkRecompilations 2 X
# trait ancestor: B, the first class to mix T in, holds the forwarder for n; C inherits it
$ copy-file changes/T.scala T.scala
> run s s
> checkRecompilations 3 T
> checkRecompilations 4 B Y
> checkRecompilations 0 C Main
```

PoC: for the `A` edit, `traitDirect` needs the changed class to be a trait, so it does not fire. For the `T` edit, `mixesIn(B, T)` holds (no class ancestor of `B` has `T`), while `mixesIn(C, T)` does not, because `B` has `T`.

Baseline: round 2 = `B C X`; round 4 = `B C Y`. Under `strict` (adds `trait`) round 4 would be `B C Y`. Confidence: high for the `A` step; medium-high for `T` (an internal `T` has no forwarder hashes, so `traitDirect` returns "mixes in trait T" without filtering names, which is still just `B`).

A variant with `trait T extends A` and `class B extends T`, editing `A.m`, is the single-subproject twin of `merkle-x-trait-class-ancestor`: the PoC gives `2 X` with `0 T B`, baseline `2 T B X`. It is also the internal form of the catalyst finding about a trait's `extraHash` folding in class parents, which no scripted test pins.

### Gap 6: cross-subproject, ancestor edit upstream, downstream descendants not recompiled

`merkle-x-member-type` covers it, but needs the Gap 0 line. Nothing covers an upstream *intermediate* descendant, where downstream sees the change only through the composed hash of an unrecompiled upstream class.

`merkle-x-member-type-deep`:

```scala
// lib/A.scala
package p
abstract class A { def m: Int = 0; def g: Int = 0 }
// lib/B.scala
package p
class B extends A
// app/C.scala
package p
class C extends B
// app/X.scala
package p
object X {
  def main(args: Array[String]): Unit = {
    val v: Any = (new C).m
    assert(v.toString == args(0), v)
  }
}
// app/Z.scala
package p
object Z { def f(c: C): Any = c.g }
// lib/changes/A.scala
package p
abstract class A { def m: String = "s"; def g: Int = 0 }
```

`build.json`: `lib`, and `app` depending on `lib`. Both have `incOptions.properties` with `apiDebug = false`.

```
> app/run 0
$ copy-file lib/changes/A.scala lib/A.scala
> app/run s
> lib/checkRecompilations 1 p.A
> lib/checkRecompilations 0 p.B
> app/checkRecompilations 1 p.X
> app/checkRecompilations 0 p.C p.Z
```

PoC: `B`'s composed hash for `m` moves through `A` (`MerkleHashes`). `C` is filtered by the external rules. `X` records a `memberRef` on the owner `p.A`.

Baseline: lib round 2 = `p.B`; app round 1 = `p.C p.X`. Confidence: high for lib; medium-high for app (`C`'s exclusion relies on `filterExternalDescendants` with `B` as the changed upstream class).

### Gap 7: private and protected members of an ancestor

Changes to private members are not in either design's API: both recompile only the ancestor, except trait breakers, which the existing `trait-private-*` tests cover. So that is not a precision gap. Protected members are in the API, and no test pins them.

`merkle-protected`:

```scala
// A.scala
class A { protected def p: Int = 0 }
// B.scala
class B extends A { def q: Any = p }
// C.scala
class C extends A
// changes/A.scala
class A { protected def p: String = "" }
```

```
> compile
$ copy-file changes/A.scala A.scala
> compile
> checkRecompilations 1 A
> checkRecompilations 2 B
> checkRecompilations 0 C
```

PoC: `B` uses `p` (memberRef); `C` reads nothing. Baseline: round 2 = `B C`. Confidence: high. A `private[pkg]` variant behaves the same, since it counts as non-private (H2 contract).

### Gap 8: sealed hierarchy and pattern-match client

The direct children of a sealed class share its source, so they recompile with it on both sides. Precision shows only for a non-sealed grandchild in another file.

`merkle-sealed`, with `incOptions.properties` = `apiDebug = false` and `useOptimizedSealed = true`:

```scala
// S.scala
sealed abstract class S { def m: Int = 0 }
final case class K1() extends S
abstract class Open extends S
// KK.scala
class KK extends Open
// Client.scala
object Client { def f(s: S): Int = s match { case K1() => 1; case _: Open => 2 } }
// X.scala
object X { def f(k: KK): Any = k.m }
// changes/S1.scala
sealed abstract class S { def m: String = "s" }
final case class K1() extends S
abstract class Open extends S
// changes/S2.scala
sealed abstract class S { def m: String = "s" }
final case class K1() extends S
final case class K2() extends S
abstract class Open extends S
```

```
> compile
# a member of the sealed root changes: only its client recompiles
$ copy-file changes/S1.scala S.scala
> compile
> checkRecompilations 1 S K1 Open
> checkRecompilations 2 X
# a sealed child is added: the pattern-match client recompiles, the grandchild does not
$ copy-file changes/S2.scala S.scala
> compile
> checkRecompilations 3 S K1 K2 Open
> checkRecompilations 4 Client
> checkRecompilations 0 KK
```

PoC: step 1 is as Gap 1. In step 2 the modified name is `S` in `PatMatTarget`. `headerChanged` does not cover sealed children, and `KK` neither declares nor uses `S` in that scope.

Baseline: round 2 = `KK X`; round 4 = `Client KK`. Confidence: high for step 1. Step 2 needs verifying: that `Client`'s `PatMatTarget` use is recorded (as in `patMat-scope`), and that no added-class rule reaches `KK`.

### Gap 9: §10a Edit 1 with baseline and PoC sets side by side

The baseline `B C X Y` exists only in commit `719076285`, and the A side carries no `merkle*` tests. The in-build A/B is `descendantRules = all`, which keeps every descendant. With the decls-only bridge, `B`'s and `C`'s APIs do not change, so there is no third round, and the set equals develop's.

`merkle-member-type-all`: the sources of `merkle-member-type`, with `incOptions.properties` = `apiDebug = false` and `descendantRules = all`:

```
> run 0
$ copy-file changes/A.scala A.scala
> run s
> checkRecompilations 1 A
> checkRecompilations 2 B C X Y
> checkRecompilations 0 M Z Main
```

Alongside it, `merkle-member-type` with the Gap 0 line pins `2 X Y` and `0 B C M Z Main`. Confidence: high.

Do the same for `merkle-trait-direct-strict`, the sources of `merkle-trait-direct` with `descendantRules = strict`: `checkRecompilations 2 B C U X`, against the default `2 B X`. Also consider porting `merkle-member-type` with baseline expectations to `claude/merkle-baseline`, so that the A side runs it too.

### Gap 10: analysis size and name-hash counts

Nothing is asserted. The PLAN's figures (synthetic 148,233 to 39,633 name hashes; catalyst 212,389 to 94,046) come from IncBench runs. The only structural check is the `ExtractAPISpecification` assertion on `Global.Foo`. `checkNameExistsInClass` exists, but it reads `externalAPI`, and there is no negative form.

Proposal: add two scripted commands to `IncHandler`, `checkNameHash <class> <name>` and `checkNoNameHash <class> <name>`, over `analysis.apis.internalAPI(className).nameHashes`.

`merkle-decls-only`:

```scala
// A.scala
class A { def m: Int = 0; def g: Int = 0 }
// B.scala
class B extends A { def own: Int = 0 }
// L.scala
class L extends scala.collection.AbstractIterator[Int] { def hasNext = false; def next() = 0 }
```

```
> compile
> checkNameHash B own
> checkNoNameHash B m
> checkNoNameHash B g
# library ancestors keep name stubs (libraryAncestors=names)
> checkNameHash L map
```

Baseline: `B` has hashes for `m` and `g`. Exact counts are brittle, because platform stubs (`toString`, `wait`, ...) stay. For size, a ratio check in IncBench (`--expect` thresholds on stored name-hash count per edit) would be the place, rather than scripted.

### Further gaps found

11. §10a Edit 3 shape without a compile error, so that the recompiled set can be pinned. `merkle-conflict` is negative only. `merkle-conflict-precision`:

    ```scala
    // A.scala
    class A { def m: Int = 0 }
    // B.scala
    class B extends A
    // C.scala
    class C extends B with M
    // M.scala
    trait M { def m: Int }
    // changes/A.scala
    class A { final def m: Int = 0 }
    ```

    ```
    > compile
    $ copy-file changes/A.scala A.scala
    > compile
    > checkRecompilations 1 A
    > checkRecompilations 2 C
    > checkRecompilations 0 B M
    ```

    `conflicts` fires for `C` (`M` declares `m` on another path), not for `B`. Baseline: round 2 = `B C`. Confidence: medium-high; it assumes member modifiers are hashed, which the H2 contract states.

12. The `mirror` rule and case-class companions. The catalyst fix ("fired for every case class's companion") has no scripted test. `merkle-case-class-companion`:

    ```scala
    // A.scala
    abstract class A { def m: Int = 0 }
    // K.scala
    case class K(x: Int) extends A
    // X.scala
    object X { def f(k: K): Any = k.m }
    // changes/A.scala
    abstract class A { def m: String = "s" }
    ```

    ```
    > compile
    $ copy-file changes/A.scala A.scala
    > compile
    > checkRecompilations 1 A
    > checkRecompilations 2 X
    > checkRecompilations 0 K
    ```

    Baseline: round 2 = `K X`. Confidence: high (`objectInherits(K, A)` is false for the companion).

13. Header edits are unpinned on both sides. The talk's §15 row "a parent is added: the same" cites `merkle-header` and `merkle-subproject-header-cascade`, which assert only compile failure or runtime values. Catalyst disagrees with "the same": adding `Serializable` to `TreeNode` recompiled 2,304 classes on A and 1,987 on B. A scripted pin of the header path (for example `merkle-as-seen-from` plus a `class P extends Q` parent addition with `checkRecompilations` on both sides) would settle what the talk claims. Name-filtering the header path is on the PLAN's TODO list. A pending test asserting the model's `C X Y` for Edit 2 would document the target.

14. The upstream precision tests run on the TREE path. `transitive-class`, `transitive-memberRef`, `class-based-inheritance`, `local-class-inheritance` and `merkle3-nowarn-separate` have no `apiDebug = false`, so they test stored full APIs and the tree hasher, not the default minimized APIs with bridge hashing.

15. No committed ablation. A per-rule `none` variant would have to assert an undercompile (`> compile` succeeding where a clean build fails), which is awkward as a scripted test. The cheaper encoding is the `all`/`strict` twins of the precision tests (Gap 9). The rule-necessity claims could then be checked by a small script that runs each SOUNDNESS-R test under `descendantRules=-<rule>` and records which fail, kept as a table in the PLAN.

## Implications for the talk's §15 table

- "ancestor member's type changes ... `merkle-member-type`": correct. The baseline set is in history only (`719076285`); add the round-0 pin.
- "same, ancestor in an upstream subproject: every downstream descendant | none downstream": the PoC still recompiles the downstream client `X`. "No downstream descendant" is what `merkle-x-member-type` pins.
- "same, ancestor is a trait: direct mixers only | `merkle-trait`, `merkle-trait-direct`": `merkle-trait` pins no set (runtime only, and per the PLAN it does not discriminate). Only `merkle-trait-direct` pins it.
- "a parent is added (header) | the same | `merkle-header`, `merkle-subproject-header-cascade`": neither test pins a set, and catalyst shows B < A. See gap 13.
- Rule table: the trait rule in `default` is `traitDirect`, not `trait`. "`descendantRules=none` fails all of them" was checked by hand, not by a test.
