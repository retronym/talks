# Phase 23 — the extraHash lineage and the companion namespace (`ExtraHash.lean`)

## Question

A class that mixes in a trait implements the trait's fields and private members, so its bytecode reads queries no public API answers. Zinc answers them with `extraHash`, a second hash on a trait's key that covers its private members and, since sbt/zinc#1289, its parents' `extraHash`. And Zinc keys a class by its name, so a companion pair (`trait A` / `object A`, `class A` / `object A`) shares one `AnalyzedClass`, one `extraHash`, one list of parents and one set of name hashes. BUG-MAP's cluster C2, a lineage of fixes: #542 → #662 / #1289 → #1794 / #1793 → #1799 / #1801 → #1795 / #1796 (open).

| Bug | Shape | Obligation |
|---|---|---|
| #542 | a private member of a trait the inheritor implements; no hash covers it | abstraction (missed), fixed by `extraHash` |
| #662 (#1289) | the same through an intermediate trait or across projects: the parent's private members not folded | abstraction (missed), fixed by folding the parents' `extraHash` |
| #1794 | the fold read from the previous analysis: absent on a cold build, present on the next | precision: a cold/warm form difference (`HashForms`) |
| #1793 | `object A`'s members in the pair's `extraHash` | precision: two namespaces under one hash |
| #1795 | `object B extends A` recorded as `trait B`'s parent | precision: an inheritance edge without its namespace |
| #1796 (open) | `class A.x` and `object A.x` under one name hash | precision: names without their namespace |

## Model

Units carry a namespace (type or term), as the companion halves do. Zinc's key is the name alone; its hashes combine both halves. An inheritor's answer reads the type half's private members and those of its trait ancestors. The fix is keys qualified by namespace, and an `extraHash` folded from the current compilation.

## Results (`ExtraHash.lean`)

| Result | Status |
|---|---|
| `merged_spurious`: a key combining the halves moves with the term half while the type half's answers stay | proved, every hash and view |
| `qualified_precise`, `qualified_sound`: per-namespace keys are not moved by the other half, and are sound when each half's hash determines its answers | proved |
| `noFold_misses` (#542, #662): a key on the intermediate trait that does not fold the ancestor's private members misses the ancestor's private change | proved |
| `coldWarm_spurious` (#1794): the fold from the previous analysis, as `HashForms.unstable_spurious` with forms cold and warm | proved |
| #1793, #1795, #1796 as instances of `merged_spurious` / `qualified_precise` | witnesses, kernel `decide` |

So the lineage alternates between the two obligations: #542 and #662 are soundness (abstraction: the key did not cover what the inheritor reads), fixed by adding a hash and then folding it; each fix then over-reached in precision, because the fold read the wrong compilation (#1794) or the key was the name, not the namespace (#1793, #1795, #1796). The remaining one, #1796, needs the namespace on used names and name hashes, the analysis-format change its issue describes; `qualified_sound` is the condition it must meet.

## The cluster's scripted tests

On develop: `trait-private-object`, `-val`, `-val-local-inheritance`, `-val-member-ref`, `-val-mix-transitive-inheritance`, `-val-transitive-inheritance`, `-var` (#542, #662), `module-inheritance-extra-hash`, `companion-object-extra-hash` (#1793, #1795), `trait-extends-trait-extra-round`, `trait-local-change` (#1794), `empty-modified-names` pass. `module-inheritance-extra-hash-213-bin` is pending: scala2-sbt-bridge cannot report `object B` as a term (#1795's namespace on the callback).

## Relevance to the Merkle PoC (retronym/zinc#24)

The Merkle hash composes a class's hash from its declarations and its ancestors': it is `extraHash`'s fold made total. The same two conditions apply: the fold must read the current compilation (`coldWarm_spurious`), and its inputs must carry the namespace (`merged_spurious`), or a companion's change moves every inheritor's hash.

## Steps

- [x] P23.1 `ExtraHash.lean`: the theorems and a witness per bug.
- [x] P23.2 The cluster's scripted tests mapped.
- [ ] Future: the namespace as a tag on `Flat.lean`'s units, so the fold and the namespaced keys run inside a `Compiler` instance with T3a.
