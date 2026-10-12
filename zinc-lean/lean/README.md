# Lean for the talk

Simplified snapshots of the full model, for the slides. The full model was in `zinc-incrementality/lean/` of this repository when they were taken; it is now [retronym/jvm-lang-models](https://github.com/retronym/jvm-lang-models) (`packages/query`, `packages/inc-comp`).

- `Primer.lean`: the primer's code. No Mathlib; `lean Primer.lean` checks it alone.
- `V1/`: Parts V–VI. The abstract model copied from the full model (namespace changed), a typecheck-only toy and its checked examples.
- `V2/`: Part VII. The general model ([`NCompiler`](https://github.com/retronym/jvm-lang-models/blob/4faa126ffd12acc1e45ac41c636751b26b863949/packages/inc-comp/IncComp/NonLocalAns.lean#L32)), `Embed.lean` (V1's model as a special case), the toy with erasure and a mixin forwarder, and the stale-Δ counterexample.

```bash
lake build
```

Lean and Mathlib `v4.34.1`, no `sorry`. To reuse an existing Mathlib build, clone a checkout of jvm-lang-models' `.lake/packages` here (`cp -Rc`); otherwise `lake exe cache get`.
