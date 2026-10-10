# The framework, merged

## Problem

The framework exists in four copies:

| Variant | Answers and hash read | Keys from | Extras |
|---|---|---|---|
| `Compiler` (`Model.lean`) | one unit's interface | the trace | |
| `GCompiler` (`NonLocal.lean`) | answers one unit; hash several (`hashDeps`) | the trace | closure keys whose `covers` depends on the interfaces |
| `TCompiler` (`Tree.lean`) | one unit's interface | the output | |
| `NCompiler` (`NonLocalAns.lean`) | several units (`hashDeps`) | the trace and the unit | `locality`; T5 in `Classpath.lean` |

Each restates `envOf`, `override`, `round`, `changed`, `invalidated`, `zinc`, `UpToDate`, `Inv`, and reproves T2 and T3a. `Tree.lean` is `Soundness.lean` with one line changed (REVIEW-2026-10-11, finding 1).

The real cost is that an instance needing two features has nowhere to go. Implicit search needs keys from the output, because the resolved scope is in the output and not the trace's last query. It also needs non-local answers, to live on the shared names instance `SplitProof.Spec` with its `Up`/`S` split. So implicit search sits apart in `GivensSpec.lean`. Phase 14 and the upstream cases will hit the same wall.

## Decision (approved; step 1 built)

**One general structure, `XCompiler` (`General.lean`).** It has `NCompiler`'s fields, except that the extractor also reads the output: `keys : CUnit → Out → List (CUnit × Q) → Finset (CUnit × K)`. `round` records `keys d (out' d) (trace …)`.

The affected units are a decidable predicate, `Affected R s c := c ∈ R ∨ ∃ d ∈ hashDeps c, d ∈ R`, not a `Finset` over `univ`. That way neither the general form nor any variant needs `Fintype CUnit`. `GivensSpec`'s units have none, and `Compiler`'s and `TCompiler`'s theorems never asked for it.

Proved once on `XCompiler`:
- T2 (`round_preserves`) and T3a (`zinc_sound`);
- T4 for monotone policies (`zinc_some_of_monotone`, `zinc_some_of_monotoneFrom`);
- T5 and the snapshot results (`inv_external`, `downstream_sound`, `zinc_out_outside`, `fresh_refreshAll`, `fresh_refreshRef_local`).

The design originally said to change `NCompiler.keys` in place. That would have meant editing the `keys` field and coverage statements of six instances (Erasure, Flat, ImplicitScope, Snapshot, SplitProof, GivensSpec) while instance PRs are open. A new structure that `NCompiler` lifts into, like the others, leaves every instance untouched.

**Every variant lifts into it.** Each lift is `toX`, with `toX_obligations` and an equality lemma: `invalidated_toX`, plus `zinc_toX` for the loop.

| Variant | Lift | Its theorems, now corollaries |
|---|---|---|
| `Compiler` (`Soundness.lean`) | hashes local (`hashDeps _ c = {c}`), keys from the trace | `round_preserves`, `zinc_sound`; `Termination`'s monotone regimes |
| `TCompiler` (`Tree.lean`) | hashes local, keys from the output | `round_preserves`, `zinc_sound` |
| `GCompiler` (`NonLocal.lean`) | answers local, `hashDeps` as given | T2′ `round_preserves`: its `affected` (via `hashRevDeps`, which contains the reverse of `hashDeps`, obligation `rev`) contains the general form's, so its dirty set is larger and its invariant weaker (`invalidated_toX_subset`) |
| `NCompiler` (`NonLocalAns.lean`, `Classpath.lean`) | keys ignore the output; its definitions coincide with the lift's | T2″, T3a″, T5 and the snapshot results |

**T3b and T3 for `TCompiler` instances** (the coordinator's note 1). A per-unit fixed point and the clean build do not mention keys. So `TCompiler.toCompiler`, which forgets the keys, reaches `Uniqueness`'s `fixpoint_unique_of_wf` and `fixpoint_unique_of_explicit` directly. `cleanFrom_fixpoint_of_comp` needs only compositionality. With the `TCompiler`'s own T3a, that gives T3: `TCompiler.zinc_eq_clean_of_explicit` and `TCompiler.zinc_eq_clean_of_wf`, a few lines each. T4's monotone regimes reach `TCompiler` through its lift (`TCompiler.zinc_some_of_monotoneFrom`).

Not moved: T4's explicit-interface and acyclic regimes (`zinc_some_of_explicit`, `zinc_some_of_wf`). They read the round's recorded keys, and no `TCompiler` instance needs them yet. Moving them is the same pattern when one does.

**`Model.lean` stays the first page.** Its docstring introduces the variants and the general form they lift into. DESIGN-spec.md and the README point there first.

**Step 2** (built, stacked on step 1): implicit search on `SplitProof.Spec`'s scopes as an `XCompiler` (`SpecGivens.lean`). Its search asks the whole level of its hit, its keys read the resolved scope from the output, and `GivensSpec.lean` (the separate `TCompiler` over `Pkg × N`) is gone. Names stay on `Spec`'s `NCompiler`: it already lifts into `XCompiler`, and moving it would change only its declaration, against an open PR's file.

## Rejected

- **A sum type of the four.** Every theorem would case on the variant, and nothing would get simpler.
- **Moving every instance to `NCompiler` declarations.** It churns files that work, and conflicts with every open instance PR. The lift gives the same results without touching them.
- **Generalising `Compiler` instead.** `NCompiler` is already the most general in three of the four directions (non-local answers, non-local hash, `locality`), and it is where T5 lives.

## Steps

- [x] 1. `XCompiler` (`General.lean`) with T2, T3a, T4 (monotone), T5 and the snapshot results; lifts and corollaries for `Compiler`, `TCompiler`, `GCompiler` and `NCompiler`; `TCompiler.toCompiler` with T3; `Policy.InS` and `Policy.MonotoneFrom` moved to `Model.lean`. No instance file changed.
- [x] 2. Implicit search on `Spec`'s scopes as an `XCompiler` (`SpecGivens.lean`): a level-wise search and keys read from the output; `GivensSpec.lean` removed. Names stay on `Spec`'s `NCompiler`, which lifts into `XCompiler`: moving it would only change its declaration.
- [ ] Once talks#36 is in: `scripts/Axioms.lean` checks the `XCompiler` theorems too.
