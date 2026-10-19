# IncBench anomalies: milessabin/shapeless

- **Build:** milessabin/shapeless at `main` (shallow clone, 2026-10-19), the 2.3 line, Scala 2.13.18, modules `coreJVM` (83 sources, boilerplate-generated ones included) and `examplesJVM` (52, heavy users of `Generic`, `LabelledGeneric`, `Witness`, `Lazy`, `Poly`). Options as the build sets them, including `-Xfatal-warnings` and shapeless's own compiler plugin (built from the checkout; `export-build` now freezes such plugin jars into the export).
- **Run:** `lockstep --verify --profile`, the three cells as in `cats.md` (bench f7b7642c03, develop 5615b62e16, merkle 556464169f), lockstep's defaults (recompileOnMacroDef false). Clean build ~5.3 s warm. Edit script: `edits/shapeless.tsv`. Results: `~/code/.integration/campaigns/2026-10-19-shapeless`, plus `2026-10-19-shapeless-macrodef` (one step with recompileOnMacroDef true).

## Steps

| Step | released / perf | merkle | Verdict |
|---|---|---|---|
| hcons-tostring-body | core 1+12+1+13 (145 cl) | same | fresh-mismatch (noise, §3) |
| hlist-add-member | core 1+13, examples 14 (263 cl) | same | fresh-mismatch (noise) |
| hlist-add-case | compile error on both sides (exhaustivity warnings are fatal) | | same-fail |
| hlistops-private-member | core 1+13 (153 cl) | same | fresh-mismatch (noise) |
| length-add-implicit | core 1+18, examples 3 (384 cl) | same | fresh-mismatch (noise) |
| package-object-body | core 1+12+1+13 | same | fresh-mismatch (noise) |
| package-object-add-alias | core 1+12+1+13 | same | fresh-mismatch (noise) |
| poly-add-member | core 1+19, examples 12 (417 cl) | core 1+18, examples 12 (351 cl) | fresh-mismatch (noise) |
| generic-macro-impl-body | core 1+12+1+13 | same | fresh-mismatch (noise) |
| generic-macro-expansion | core 1+12+1+13, examples 0 | same | **missed-error** (all) |

## Anomalies

### 1. A macro impl change that alters expansions isn't propagated downstream (correctness, all Zincs, with recompileOnMacroDef=false)

- **Step:** `generic-macro-expansion`: `GenericMacros.mkProductGeneric` wraps its result in `Predef.locally(...)`, which loses the whitebox refinement of `Generic.Aux[T, R]`.
- **Verdict:** `missed-error` on all three. The clean build fails in `examplesJVM` (`could not find implicit value for parameter lgen0: shapeless.LabelledGeneric.Aux[...]` in alacache.scala, alacarte.scala, basecopy.scala, ...); the incremental build succeeds because `examplesJVM` isn't recompiled at all.
- **Cycles:** core 1+12+1+13: the "macro classes depending on recompiled classes" rule recompiles `Generic` and the other macro-defining classes, but their API is unchanged, and with recompileOnMacroDef=false nothing downstream is invalidated.
- **With recompileOnMacroDef=true** (bench Zinc only, same step): `same`, but core recompiles 1+28+66+71+72 sources and examples all 49: 1,233 classes, about the whole build.
- **Reading:** this is the documented price of optimistic macro invalidation, now measured on a real build: either a full rebuild for any edit that touches a macro's dependencies, or silently stale expansions when an impl changes. rz#73's fast-track rule is sound for `macro ???` impls; for real impls in the same build it's this trade-off. Note that the lockstep default puts every campaign on the unsound side; correctness findings in builds with in-project macros should be read with that in mind.
- **Follow-up:** record a fingerprint of a macro's implementation class (its bytecode, or the API+body hash of the impl's source class) in the macro def's analysis, and invalidate expansion sites (the `macroExpansion` relation already exists) only when the impl actually changed. That gives correctness without the cascade.

### 2. The macro-dependency rule recompiles each source twice (over-compilation, all Zincs)

- **Steps:** every body-only edit to a core file that macro-defining classes depend on: `hcons-tostring-body`, `package-object-body`, `generic-macro-impl-body`, and also `package-object-add-alias`: 1+12+1+13 sources with no API change in any cycle (145 classes instead of the ~10 of the edited file).
- **Cause:** `IncrementalCommon.invalidateAfterInternalCompilation`'s third-class invalidation is `(transitiveDeps(recompiledClasses) -- recompiledClasses).filter(hasMacro)`, subtracting only the classes of the current cycle. shapeless's macro-defining classes and `hlists.scala` depend on each other, so cycle 3 re-invalidates `hlists.scala` (recompiled in cycle 1) because cycle 2's macro classes depend on it, and cycle 4 re-invalidates cycle 2's set because they depend on cycle 3's. It stops only when one cycle happens to hold the whole cycle of macro classes.
- **Follow-up:** subtract every class recompiled earlier in this incremental run whose sources haven't changed since. Recompiling a class only because of this rule can't change its behaviour, so it can't be a reason to recompile its macro dependents again. That halves these steps here (and cuts the cats `FunctionK` cycle too). Small, self-contained Zinc change with a scripted test (two mutually dependent files, one defining a macro).

### 3. Quasiquote fresh-name order depends on the batch (correctness noise, scalac)

- **Steps:** almost all: `shapeless/IsHCons1Macros.class` is `fresh-mismatch` whenever it's recompiled in a batch that differs from the clean build's. The only difference is that two locals are swapped (`aload 6`/`aload 7`) in `mkPackUnpack`, whose `q"$cons(_, _)"` reifies two `freshTermName("x$")` vals.
- **Downstream echo:** `examplesJVM/FunctorDemo$*.class` after `hlist-add-member`: the expansion's lambda parameters `x$1`/`x$2` are swapped, because the macro impl itself was compiled with the other order.
- **Isolated:** plain scalac 2.13.18, `scalac Q.scala` vs `scalac P.scala Q.scala` where `Q` holds `q"$cons(_, _)"` and `P` other placeholder quasiquotes: the vals `nn$macro$2`/`nn$macro$3` come out in opposite order. `quasiquotes/Reifiers.scala` keeps `nameMap` in a `mutable.HashMap[Name, ...]` and emits the vals by iterating it; `Name.hashCode` is the name's offset in the run's name table, which depends on what the run interned before. Fix: an insertion-ordered map. Proposed as its own session (scala/scala fix with a DeterminismTest case). Same family as scala#11319.

### 4. Macro fresh-name counters depend on the batch (noise, scalac)

`length-add-implicit`, `poly-add-member`: `examplesJVM/LinearAlgebraExamples$.class` differs only in the names of locals from macro expansions (`x0$3` vs `x0$13`, `_1$macro$4` vs `_1$macro$32`): the counters behind `c.freshName` aren't per compilation unit. Only local variable names, but it makes `--verify` noisy on any build that expands macros; a candidate for IncBench to normalise (LocalVariableTable names) or for scalac to use a per-unit creator.

### Merkle vs. name hashing

- Merkle saves little here: `poly-add-member` 351 vs. 417 classes; the rest are identical. shapeless's members are mostly reached through implicits and type-level computation rather than inheritance, so few descendants can be skipped.
- Merkle reports `$init$` among `HList`'s changed names on `hlist-add-member` (the trait gains its first concrete member). Harmless here.
- Merkle's `analysis` phase costs 2-6x the others' (387 vs. 51 ms on `hlist-add-member`, 697 vs. 191 ms on the clean build), as on cats (composition cost, fixed in rz#48 but not yet in the integration branch).

### Edit-script note

`hlist-add-case` produced the same compile errors on both sides (fatal `match may not be exhaustive` warnings), so it tested nothing. An add-case edit in a build with `-Xfatal-warnings` needs a hierarchy without exhaustive matches.
