# The framework, merged (design note, for review)

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

## Decision

**One structure: `NCompiler`, with keys that also read the output.** The only change to its fields is `keys : CUnit → Out → List (CUnit × Q) → Finset (CUnit × K)`. `round` records `keys d (out' d) (trace …)`. The proofs of T2″, T3a″ (`NonLocalAns`) and T5 (`Classpath`) use `keys` only through `coverage`, so they carry over with the extra argument threaded through.

**The other three become constructors of it.** Each gets a lift into `NCompiler`, as `Embed.lean` already does for `Compiler`:
- `lift_obligations`: a variant's obligations give the general ones;
- `zinc_lift`: the general loop on the lift is the variant's loop, round for round.

So T2, T3a and T5 hold for every variant through the lift.

- `Compiler.lift`: unchanged from `Embed.lean`, with `keys _ _ tr := C.keys tr`.
- `TCompiler.lift`: `keys _ o _ := C.keysOf o`.
- `GCompiler.lift`: `hashDeps _ c := C.hashDeps c`. Its `hashRevDeps` is the reverse of `hashDeps`; T2′'s `affected` is `NCompiler.affected` on the lift, which needs `hashRevDeps` to be that reverse. That is an extra hypothesis on `lift_obligations`, true of every `GCompiler` instance (`Hier`'s `Mk`).

**Proofs once.** `Soundness.lean`'s, `Tree.lean`'s and `NonLocal.lean`'s `round_preserves` and `zinc_sound` become one-line corollaries through the lift. They keep their names, so PLAN files, the talk and the instances keep citing them. `Uniqueness` (T3b) and `Termination` (T4) stay on `Compiler`, where they were proved, and are not moved.

**Instances do not change**, except where they want the new power. `Hier`, `JavaSpec`, `JavaOrder`, `Cycles`, `Spec`, `InlineOpaque` and the rest keep their variant and get every general result through the lift. `GivensSpec` moves onto `SplitProof.Spec`. Spec's lookup gains levels: every probe of a level is asked, the first level with a hit decides, and `JavaSpec`'s `mem_trace_resolve` is the model. Its keys read the output's resolved scope instead of `trace.getLast?`. Names and givens are then one instance with the `Up`/`S` split, and `GivensSpec.lean` goes.

## Rejected

- **A sum type of the four.** Every theorem would case on the variant, and nothing would get simpler.
- **Moving every instance to `NCompiler` declarations.** It churns files that work, and conflicts with every open instance PR. The lift gives the same results without touching them.
- **Generalising `Compiler` instead.** `NCompiler` is already the most general in three of the four directions (non-local answers, non-local hash, `locality`), and it is where T5 lives.

## Steps, two PRs

1. `NCompiler.keys` reads the output; `TCompiler.lift` and `GCompiler.lift` with `lift_obligations` and `zinc_lift`; the variants' T2/T3a as corollaries; `scripts/Axioms.lean` (talks#36) checks the corollaries.
2. `Spec`'s level-wise lookup and keys from the output; `GivensSpec` ported onto it and removed; PLAN-names and the status table updated.

Timing: after talks#25 (`InlineOpaque` as an instance) merges, which touches the same imports. Neither PR should conflict with an instance file, since instances are not edited in step 1.
