# IncBench anomalies: milessabin/shapeless

- **Build:** milessabin/shapeless at `main` (shallow clone, 2026-10-19), the 2.3 line, Scala 2.13.18, modules `coreJVM` (83 sources, boilerplate-generated ones included) and `examplesJVM` (52, heavy users of `Generic`, `LabelledGeneric`, `Witness`, `Lazy`, `Poly`). Options as the build sets them, including `-Xfatal-warnings` and shapeless's own compiler plugin (built from the checkout; `export-build` now freezes such plugin jars into the export).
- **Run:** `lockstep --verify --profile`, the three cells as in `cats.md` (bench f7b7642c03, develop 5615b62e16, merkle 556464169f), with `recompileOnMacroDef=true` (sbt's default; confirmed in every cell's generated `incOptions.properties`). The first campaign ran with `false` by mistake (see the README); this report replaces it. Clean build ~7.5 s warm. Edit script: `edits/shapeless.tsv`. Results: `~/code/.integration/campaigns/2026-10-20-shapeless-macrodef-true`. Timings were taken on a loaded machine and are provisional; this report relies on verdicts and recompile counts.

## Steps

With `recompileOnMacroDef=true` every edit recompiles the whole build, identically on all three Zincs: 1,233 of 1,292 classes (83 core sources over several cycles, then 49 of the 52 examples sources). Previously (with `false`) these steps cost 145-417 classes.

| Step | cycles (core, then examples), all cells | Verdict (all cells) |
|---|---|---|
| hcons-tostring-body | core 1+55+68+72, examples 49 (1,233 cl) | same |
| hlist-add-member | same | fresh-mismatch (noise, §3) |
| hlist-add-case | compile error on both sides (exhaustivity warnings are fatal) | same-fail |
| hlistops-private-member | core 1+13+64+71+72, examples 49 | fresh-mismatch (noise) |
| length-add-implicit | core 1+18+64+71+72, examples 49 | same |
| package-object-body | core 1+38+66+72, examples 49 | same |
| package-object-add-alias | same | fresh-mismatch (noise) |
| poly-add-member | core 1+26+64+71+72, examples 49 | fresh-mismatch (noise) |
| generic-macro-impl-body | core 1+28+66+71+72, examples 49 | same |
| generic-macro-expansion | compile error in `examplesJVM` on both sides | **same-fail** |

Reverts behave like their edits. No `bytecode`, `missed-error` or other correctness verdict in any cell; every `fresh-mismatch` is the same seven classes (`IsHCons1Macros` and `FunctorDemo$*`, §3).

## Anomalies

### 1. A macro impl change that alters expansions is now propagated (resolved; the earlier `missed-error` came from recompileOnMacroDef=false)

- **Step:** `generic-macro-expansion`: `GenericMacros.mkProductGeneric` wraps its result in `Predef.locally(...)`, which loses the whitebox refinement of `Generic.Aux[T, R]`.
- **Verdict:** `same-fail` on all three. The clean build fails in `examplesJVM` (`could not find implicit value for parameter lgen0: shapeless.LabelledGeneric.Aux[...]` in alacache.scala, alacarte.scala, ...) and so does the incremental build, with the same errors. The previous campaign's `missed-error` (examples not recompiled at all) was an artefact of `recompileOnMacroDef=false`, not a Zinc bug in any cell.
- **Cost:** the whole build, 1,233 classes. Soundness here comes from invalidating every dependent of any macro-defining class that gets recompiled ("API change due to macro definition"), not from detecting that an expansion changed, which is why even `hcons-tostring-body` costs the same.
- **Comparison of cells:** none. Merkle and name hashing recompile the identical sources in identical cycles on all 19 steps, and the old differences on `poly-add-member` (351 vs. 417 classes) are gone, because the macro rule dominates.
- **Follow-up:** unchanged from before, and now the main lever for macro-heavy builds: record a fingerprint of a macro's implementation (the impl class's bytecode, or the API+body hash of its source) and invalidate expansion sites (the `macroExpansion` relation already exists) only when the impl changed. That keeps correctness without a whole-build rebuild per edit. rz#73's fast-track covers `macro ???` impls only.

### 2. The macro rule recompiles each source several times (over-compilation, all Zincs; worse with true)

- **Steps:** every step: core is compiled in 4 or 5 cycles (1+55+68+72 sources on `hcons-tostring-body`, 196 source compilations of 83 sources), then examples once. Cycles 2 to 4 each report "API change due to macro definition" for the macro-defining classes (`Generic`, `FromRecordArgs`, `Split1`, `TypeAnnotations`, ...) with 562, 673, 815 classes next to invalidate, although no API changed.
- **Cause:** as before, the third-class invalidation in `IncrementalCommon.invalidateAfterInternalCompilation` subtracts only the current cycle's classes, so mutually dependent macro-defining sources ping-pong. With `recompileOnMacroDef=false` this showed as 1+12+1+13 on body edits; with `true` the macro classes are also invalidated *with their dependents* each time, so the ping-pong runs three to four times over most of core.
- **Follow-up:** the same subtraction fix (do not re-invalidate a class this run already recompiled for this reason and whose source hasn't changed) would cut the 196 source compilations of core to about 83 plus the first cycle; examples is unaffected. It does not remove the whole-build cost of §1.

### 3. Quasiquote fresh-name order depends on the batch (correctness noise, scalac)

- **Steps:** almost all: `shapeless/IsHCons1Macros.class` is `fresh-mismatch` whenever it's recompiled in a batch that differs from the clean build's. The only difference is that two locals are swapped (`aload 6`/`aload 7`) in `mkPackUnpack`, whose `q"$cons(_, _)"` reifies two `freshTermName("x$")` vals.
- **Downstream echo:** `examplesJVM/FunctorDemo$*.class` after `hlist-add-member`: the expansion's lambda parameters `x$1`/`x$2` are swapped, because the macro impl itself was compiled with the other order.
- **Isolated:** plain scalac 2.13.18, `scalac Q.scala` vs `scalac P.scala Q.scala` where `Q` holds `q"$cons(_, _)"` and `P` other placeholder quasiquotes: the vals `nn$macro$2`/`nn$macro$3` come out in opposite order. `quasiquotes/Reifiers.scala` keeps `nameMap` in a `mutable.HashMap[Name, ...]` and emits the vals by iterating it; `Name.hashCode` is the name's offset in the run's name table, which depends on what the run interned before. Fix: an insertion-ordered map. Proposed as its own session (scala/scala fix with a DeterminismTest case). Same family as scala#11319.

### 4. Macro fresh-name counters depend on the batch (noise, scalac; not seen in this rerun)

In the first campaign `length-add-implicit` and `poly-add-member` showed `examplesJVM/LinearAlgebraExamples$.class` differing only in the names of locals from macro expansions (`x0$3` vs `x0$13`), because the counters behind `c.freshName` aren't per compilation unit. With every example recompiled in one cycle the rerun's only fresh-mismatch classes are §3's, and `length-add-implicit` verifies `same`. Still a candidate for IncBench to normalise when examples are recompiled in different batches.

### Merkle vs. name hashing

- Merkle saves nothing here with the real default: every step recompiles the same 1,233 classes in the same cycles as name hashing (previously `poly-add-member` was 351 vs. 417). The macro-dependency rule decides the cost, not the hashing mode.
- Merkle reports `$init$` among `HList`'s changed names on `hlist-add-member` (the trait gains its first concrete member). Harmless here.
- Merkle's `analysis` phase is again several times the others' (about 1.2-1.6 s vs. 0.4-0.7 s per step), but that is not attributable to Merkle: the pinned cells have a harness bug (IncHandler used an uncached `Locate.definesClass`, fixed in rz#71 4cba55a47) that adds about 100 ms per step to every Merkle cell's analysis phase, and these timings come from a loaded machine. Treat all timings as provisional.

### Edit-script note

`hlist-add-case` produced the same compile errors on both sides (fatal `match may not be exhaustive` warnings), so it tested nothing. An add-case edit in a build with `-Xfatal-warnings` needs a hierarchy without exhaustive matches.
