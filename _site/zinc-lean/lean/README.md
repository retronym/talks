# Lean for the talk

Simplified snapshots of the full model in `../../zinc-incrementality/lean/`, for the slides.

- `Primer.lean`: the primer's code. No Mathlib; `lean Primer.lean` checks it alone.
- `V1/`: Parts V–VI. The abstract model copied from the full model (namespace changed), a typecheck-only toy and its checked examples.
- `V2/`: Part VII. The general model (`NCompiler`), `Embed.lean` (V1's model as a special case), the toy with erasure and a mixin forwarder, and the stale-Δ counterexample.

```bash
lake build
```

Lean and Mathlib `v4.34.1`, no `sorry`. To reuse an existing Mathlib build, clone the full model's `.lake/packages` here (`cp -Rc`); otherwise `lake exe cache get`.
