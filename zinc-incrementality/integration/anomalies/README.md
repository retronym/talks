# IncBench anomalies across builds

The IncBench campaign tooling (`export-build`, `lockstep --verify --profile`, `lockstep-summary`) run on four more Scala 2.13 builds beyond scala/scala, each with the three Zincs in lockstep (1.12.x, + fixes, + fixes + Merkle; integration commits bench f7b7642c03, develop 5615b62e16, merkle 556464169f). Per-build reports:

- [cats.md](cats.md): typelevel/cats `kernel`, `core`, `free`. Implicits, type classes, kind-projector, specialisation.
- [shapeless.md](shapeless.md): shapeless 2.3 `core` and `examples`. Macro-heavy, with macro users downstream.
- [scala-steward.md](scala-steward.md): scala-steward `core`. Application style, cats-effect/http4s/circe derivation.
- [pekko.md](pekko.md): pekko `actor`, `actor-typed`. Java and Scala mixed, deep hierarchies, cross-file inlining.

Edit scripts are in `../edits/<build>.tsv`, 8-10 edits each (body, public member on a widely inherited type, private member, implicit, sealed case, package object, macro or `@inline`, Java). Raw results are in `~/code/.integration/campaigns/2026-10-19-*`.

## Findings worth their own investigation

In order of how much I'd want them looked at:

1. **Merkle under-compiles anonymous subclasses declared in a trait's companion** (cats §1). Adding a member to a trait doesn't recompile `object B { new B {} }` when `B` is a trait Merkle decides doesn't read the change, because the local-inheritance edge is a self-dependency that Zinc drops. On cats, 312 stale classfiles in `Order`/`PartialOrder`/`Hash`; a 3-line repro misses a mixin forwarder for an added `def` and a field and accessor for an added `val` (an `AbstractMethodError` at run time). The only correctness bug in Zinc itself found here, and Merkle-only. Being fixed in Merkle's descendant rules (session in progress).
2. **Name hashes of inherited type-lambda members depend on whether the parent was typed from source** (cats §2). Plain Zinc, all versions. An inherited member whose type is a refinement projection naming a class from the parent's own file (`F[One[List, *]]`, or written out by hand) hashes differently when the parent comes from the pickle. In cats, because the members are implicits, every edit that recompiles `OneAnd.scala` ends in a full recompile of `core` (233 sources instead of ~60). kind-projector types are everywhere in typelevel code, so this likely hits every cats-style instance-priority chain. Cause: an eta-expanded alias's type parameter (`List`'s `A`) is owned by the alias's local dummy from source and by nothing from the pickle, so it was named `scala.package.A` vs `A`. Fixed in rz#77/rz#79 with follow-up commits for 2.13 (the first version only fixed 2.12); on cats the full recompiles are gone. Merkle's bridge hasher needs the same rule (in progress).
3. **The macro-dependency rule re-invalidates classes it already recompiled** (shapeless §2). `IncrementalCommon`'s third-class invalidation subtracts only the current cycle's classes, so mutually dependent macro-defining sources ping-pong: every body edit in shapeless core costs 1+12+1+13 sources instead of 1+12. Small, self-contained Zinc fix (subtract every class this run already recompiled for this reason).
4. **Merkle's trait-private-member cascade** (cats §3, scala-steward §2). A public addition to a trait changes every subtrait's extraHash, which Merkle reports as `TraitPrivateMembersModified` and handles one inheritance level per cycle. On cats `Functor` it takes Merkle to 1,420 classes against name hashing's 705 (anomaly 2 makes it worse). Fold only the parents' private-member hashes into a trait's extraHash on Merkle.
5. **scalac batch dependence in specialisation** (cats §4). `SortedMapCommutativeMonoid` gets different specialised forwarder return types and is missing bridges depending on what else is in the run. Needs a plain-scalac repro; if confirmed, a scalac bug that can change dispatch.

## The campaign's own defaults

- **recompileOnMacroDef=false makes macro and inlining builds unsound in every cell.** shapeless's macro-expansion edit is `missed-error` (examples not recompiled) and pekko's `@inline` edit leaves stale inlined code. Both are correct with Zinc's default `true`, at the cost of a near-full rebuild on shapeless (1,233 classes). Correctness verdicts on builds with in-project macros or the inliner should be read with that in mind, or such steps run with `true`. A sound and cheap alternative (fingerprint the macro impl, invalidate expansion sites only when it changes) is shapeless §1's follow-up.
- **Verify noise from scalac:** quasiquote fresh-name order (shapeless §3; isolated: `Reifiers.nameMap` is a `HashMap` keyed by `Name`, whose hash is its name-table offset; a scalac fix is proposed as its own session), macro fresh-name counters (shapeless §4), type-variable names shifting constant-pool indices (cats §5), and optimizer inlining that depends on whether Java classes are sources or classfiles in the run (pekko §2). None of these is a Zinc problem, but they make `fresh-mismatch` common on these builds. Two IncBench improvements would remove most of it: normalise constant-pool indices and local-variable names when comparing, and build the per-round reference against all Java as classfiles.

## Performance

- Merkle's `analysis` phase costs 2-6x the others on every build (e.g. 697 vs. 191 ms on shapeless's clean build, ~100 vs. ~10 ms per scala-steward step), which makes Merkle the slowest cell on small steps everywhere. This is the composition cost fixed in rz#48 9e99fb249, which isn't in integration/merkle-1.12.x yet; rerun once it is.
- `analysisWrite` is 30-100 ms per step on these builds, often half of Zinc's own time on a body edit.
- No step where 1.12.x and develop-1.12.x differ by more than noise.

## Merkle vs. name hashing

Merkle recompiled fewer classes on pekko's `ActorRef` (36 vs. 98) and shapeless's `Poly` (351 vs. 417), the same elsewhere, and more on cats's `Functor` (findings 2 and 4). Outside scala/scala, real builds reach most members through implicits and type-level computation rather than inheritance, so Merkle has less to skip.

## Tooling changes

- `export-build` freezes compiler plugins that the checkout builds itself (shapeless) into `<module>/plugins/`.
- `lockstep-summary OUT_DIR` prints per step and cell the verdict, sources per cycle, wall/scalac/Zinc time with Zinc's largest parts, and each cycle's API changes, and flags verify failures and cells that disagree.
