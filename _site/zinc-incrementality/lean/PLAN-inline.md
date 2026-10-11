# Phase 11 — Scala 3 `inline` and opaque types (`InlineOpaque.lean`)

P6.10 left two Scala 3 sources of bytecode that the API renders by name: `inline` bodies (the client's bytecode contains the callee's body) and opaque types (erased to their right-hand side everywhere, though only the defining scope sees it). `Inline.lean` (P8.7) treats an inline body as one hashed value; here the body references other things, and the question is whether an edit to anything the client's expansion reads reaches the client.

### Questions

1. **Inline.** Does an edit to an inline body, or to anything it references (transitively: other inline defs, constants, private members through their accessors, type aliases read at the type level), recompile every client that inlined it, across files and subprojects? And no more than that: an edit to a helper's body, which the expansion only calls, should not recompile the client.
2. **Opaque types.** An edit to the right-hand side changes the erasure of every signature that mentions the type, inside and outside the defining scope (the client's `def f(t: O.T)` is `f(I)` for `T = Int`). Are those clients recompiled, and are descendants whose bytecode erases an *inherited* signature (mixin forwarders, bridges inherited from a trait) recompiled? At what cost: who else is recompiled?
3. **Briefly: `transparent inline`, `inline given`.** Transparent calls are expanded in typer, so the dependency phase sees them expanded; an inline given is an implicit member, which Zinc invalidates by member-ref regardless of used names.

### What dotc and Zinc record (scala3 at `fdc8fb4320`, released as 3.9.0 for the relevant parts)

* `ExtractAPI.apiAnnotations`: an inline method's API carries a marker with `treeHash` of its body. `treeHash` hashes the tree's shape, names and literal constants, not types (its `FIXME`): a `TypeTree` contributes its node kind only, a reference contributes its name. For a reference to another inline symbol (`inline def`, `inline val`, not parameters) it mixes in that symbol's whole API definition, so inline-to-inline chains are transitive. Private members are reached through inline accessors (`inline$p`), public members of the owner and so in its API.
* `ExtractDependencies` runs after typer, before inlining; since scala/scala3 3.8.3 the `Inlining` phase traverses each expansion (`Inlined` trees) and records its references as the client's dependencies and used names. But the inliner has already folded references to constants through a module path (`D.K`, `L.K` with `final val K = 1`), and a type-level read (`constValue[D.N]`, `inline erasedValue[D.N] match`) leaves only its result: no used name for `K` or `N` reaches the client. A constant through `this` (`K` in the owner's own body) survives as a reference and is recorded. A `transparent inline` call is expanded in typer, before `ExtractDependencies`, which records only the call of an `Inlined` tree; the `Inlining` phase does not revisit it.
* Opaque types: the member renders as a type declaration (bounds only); the right-hand side is in the owner's self type (the opaque refinement), which Zinc hashes into the owner's class-name hash. So every user of the owner's name (`O`, or `O$package` for a top-level opaque type, which a client of any top-level definition of that file uses) is recompiled, whether or not it mentions the type.
* Zinc: name-hash invalidation by member ref and used name; inheritance invalidation on any API change; a class with a macro gets a transitive bytecode hash over its internal upstream (`addTransitiveBytecodeHash`), which recompiles the clients of a macro whose implementation changed in the same subproject (only).

### Program space

Source files rendered by the model (package `conf`), Scala 3 only, layouts `single` and `split` (owner files upstream, `Client` and `K` downstream).

* Inline: an inline def `inl` in `object L` or at the top level of `L.scala`, `inline` or `transparent inline`; reached from the client directly, through an inline def `M.w`, or through a plain def `M.w`. Its body is a literal, or references one of: a public helper `h`, a private `val p`, a constant of `L` through `this` or through `L.`, a constant, an `inline val`, a `val` or an `inline def` of another object `D`, or a type alias `D.N` read by `constValue` or by an inline match. Edits: the body literal, a referenced member's value, its type.
* Opaque: `opaque type T` in `object O` or at the top level; right-hand side `Int`, `Long` or `Any`. Clients: a signature mentioning `T`, a call returning it, an extension method on it, an inline def of `O`, an alias `A.S = O.T`; descendants: `K extends Base[O.T]` overriding `g`, `K extends Tr` with `Tr.h(t: O.T)` concrete (mixin forwarder), `K extends Tr2` where `Tr2 extends Base[O.T]` implements `g` (inherited bridge). Edits: every change of the right-hand side.

### Model

A small Zinc loop over keys: each class records the keys it uses (class, name) and inherits; each key covers the facts ("atoms") whose change moves its hash at the class's next compilation; each class's bytecode reads atoms. A run starts from the edited file's classes, invalidates by used name and by inheritance, and is clean iff every class reading a changed atom was recompiled. Modes: Zinc on 3.9.0 (`today`); for inline, `hashConsts` (`treeHash` mixes the constant and the type a reference or `TypeTree` denotes) and `bodyDeps` (the `Inlining` phase records the expansion's references before folding); for opaque, `dep` (a class that erases an inherited signature records the types it reads, P6.8) and `refine` (the right-hand side in `T`'s name hash instead of the owner's class hash).

### Harness

retronym/zinc#36's harness (branch `claude/names-conformance`) as is: `files` bases with `tiers`, `--scala 3.x`, `--layouts single,split`. The model's recompiled set is compared with the harness's (the analysis' compilations since the edit).

### Results

The harness ran every edit of both spaces in both layouts (336 inline cases, 216 opaque, `--scala 3.x` = 3.9.0, Zinc `develop` + #36's harness). Model and harness agree on every verdict and on every recompiled set, but for 12 cases where only a mirror class differs (below). The model's rules were fixed twice against the harness: a transparent expansion records nothing, and an unqualified top-level constant is recorded.

| | Family | Lean | Scripted (pending, retronym/zinc#40) |
|---|---|---|---|
| I1 | Inline body reads a constant through a path (`D.K`, the owner's own `L.K`, `conf.K`); edit the constant. Folded by the inliner, hashed by name. | `check_dConst_today`, `check_pathK_today` | `inline-constant-path-scala3` |
| I2 | Inline body reads a type alias at the type level (`constValue[D.N]`, inline match on `erasedValue[D.N]`); edit the alias. | `check_today_stale` | `inline-constvalue-alias-scala3` |
| I3 | `transparent inline` called directly or from a plain def; edit the type of a member its body calls, or an unqualified constant. Typer's dependency phase records only the call. | `check_today_stale` | `inline-transparent-reference-scala3` (`NoSuchMethodError`) |
| O1 | Opaque type in an inherited signature: `K extends Tr` with `Tr.h(t: O.T)` (mixin forwarder), or `K extends Tr2`, `Tr2 extends Base[O.T]` implementing `g` (forwarder and bridge); edit the right-hand side. The value-class forwarder of P6.5. | `check_fwd_today` | `opaque-type-mixin-forwarder-scala3` |

| Space | Edits | Unclean today (I1/I2/I3 or O1 forwarder/bridge) | Harness divergences per layout | Recompiles today → `hashConsts` / `bodyDeps` or `dep` / `refine` |
|---|---|---|---|---|
| inline | 168 | 64 (24/24/16) | 64 + pickling (4 single, 2 split) | 320 → 416 / 384 |
| opaque | 108 | 24 (12/12) | 24 + pickling (6 single) | 228 → 252 / 216 |

Clean today: plain inline bodies, helpers (a helper's body edit recompiles only `L`: the client is never recompiled for nothing in any mode, `check_precise`), private members through their accessors, unqualified constants, `inline val`, inline-to-inline chains through another file, transparent calls through an inline def; every opaque client that names the type, calls a member returning it, uses an extension, inlines a member, goes through an alias, or overrides with it, in both layouts. The opaque right-hand side is hashed under the owner's name, so every user of the owner recompiles (a client of `O.other` too: `check_other_wasted`); `refine` (the right-hand side in `T`'s hash and in the hashes of the members whose signatures mention `T`) saves those 12 recompiles and is otherwise today's.

Fixes, checked on the space: I1–I3 by `hashConsts` (`treeHash` mixes the constant and the type each reference or `TypeTree` denotes: the owner recompiles anyway, and its API then moves) or `bodyDeps` (record the references of the body before folding, for transparent expansions too: the client is invalidated one cycle earlier and fewer intermediates recompile). O1 by `dep`: a class that erases an inherited signature (forwarder, bridge) records the types the erasure reads, as P6.8 for value classes; a witness of erased signatures in the declarer's hash (P6.9) is the Zinc-side alternative. Costs: +30% / +20% recompiles over today on the inline space, +10% on the opaque space; none of them recompiles a client that reads nothing changed. Write-ups for dotc (not filed): `dotc-inline-opaque-issues.md` in the session notes.

Q3, by probes: an `inline given` (or `transparent inline given`) in `Show`'s companion whose body changes is clean (an implicit member's change invalidates every member-ref dependent), also when its body reads `D.K` inside the anonymous instance (not folded there); `summonInline[Show[D.N]]` with `N` edited from `Int` to `String` is clean. Givens added to scopes are `Givens.lean`'s.

Artefact (dotc, not Zinc): when an object is compiled apart from what it references (Zinc's later cycle), dotc may pickle a type prefix differently (the package's `ThisType` vs its `TermRef`, in the shared types of an extension call or a transparent expansion), so the TASTy UUID in the mirror class's attribute differs from a joint build's; the module class is identical. `scripts/inline_opaque.py` classifies these.

Macros, briefly: a macro implementation edited in the same subproject as the inline def that splices it recompiles the clients (Zinc's transitive bytecode hash of classes with macros); in a separate subproject the harness cannot run it (the macro is loaded from the upstream's early output). Not modelled.

### Proved vs checked

The first round of this phase (`InlineOpaque.lean`) is an executable spec checked by brute force: its `check_` definitions are Booleans evaluated by `native_decide` in `example`s over bounded factor spaces, the verdicts the conformance dump hands the harness. The specification is `InlineOpaqueSpec.lean`, following `DESIGN-spec.md` and `JavaSpec.lean`.

**The instance** (`InlineOpaqueSpec.lean`). A `TCompiler` (`Tree.lean`: `Model.lean`'s `Compiler` with keys read off the output) over any set of units and any program of a slot language: members with primitive or opaque signatures, constants, type aliases read at the type level, `inline` and `transparent inline` defs whose bodies are item lists (literals, calls, constants through `this` or a path, alias reads, signatures, nested inline calls up to a depth), opaque types, trait methods that descendants forward. The unit task is dotc's: an inline call asks `inlineBody` and expands the body in the client, asking inside it what the inliner reads (`constant`, `aliasRhs`, `sig`, nested `inlineBody`); erasing a signature asks `erasure` of an opaque type; a forwarder asks the trait's `meths`, then `erasure` for each opaque type in the inherited signature. The output is the typed tree after inlining, each reference marked by where it ended up: own code, a reference surviving a plain expansion, folded by the inliner, inside a transparent expansion, read only for a forwarder. Today's bridge records the first two (plus the owner's own name for every reference through it), hashes an inline def by its tree, and an opaque right-hand side into the owner (`cls`). `Model.lean` needed no change.

| Result | Proved generally | Lean |
|---|---|---|
| The trace is the tree: a unit asks exactly the queries whose references are in its output | yes | `faithful` |
| Today fails coverage; witnesses I1 (constant through a path), I2 (alias read at the type level), I3 (transparent expansion), O1 (opaque type in an inherited signature) | witness programs (kernel `decide`) | `Ex.I1_today` … `Ex.O1_today` |
| Each fix alone leaves the other family | witness programs | `Ex.O1_inl`, `Ex.I1_opq` |
| Recording folded and transparent references and a forwarder's erased types (`fix`) meets comp, coverage, abstraction; T3a | yes, any program, edit, sound policy | `obligations_fix`, `fix_sound` |
| The same with the right-hand side in `T`'s own name key (`refine`) | yes | `obligations_refine`, `refine_sound` |
| Precision: every name key covers a query asked | yes | `keys_traced` |
| Precision: a name key moves only if an answer it covers changed | yes | `name_exact` |
| Precision: the owner's `cls` key is coarse (a client of `O.other` alone is recompiled on an opaque edit under `fix`, not under `refine`) | witness | `Ex.cls_coarse` |
| Hashing what an inline def's references denote meets the obligations (abstraction restored), T3a″ | yes, `NCompiler` | `InlineOpaqueSound.obligations_denot`, `denot_sound` |
| Per edit: every other unit is invalidated, or its untouched output is already its new compilation | yes, `NCompiler` | `InlineOpaqueSound.recompiles_or_unchanged` |
| Counts, recompiled sets, and agreement of the language's `today` rules with dotc 3.9.0 | checked (bounded spaces, 552 harness cases) | `InlineOpaque.lean` `check_…`, PLAN tables |

**Which obligation I1 breaks.** In the specification all four families are coverage failures: the client asks `D` for `K`, and no recorded key is on `D`. I1 is an abstraction failure only under a stronger covering, which credits the inline def's key with what its body reads (dotc's own justification for hashing bodies). That covering depends on the interface (which body reads what), which `TCompiler`'s `covers` cannot express, so it is stated on the `NCompiler` instance: `InlineOpaqueSound.Ex.I1_abstraction` (the tree hashes of `L.inl` are equal, the read of `D.K` is covered by that key, and its answers differ). Hashing what references denote restores abstraction there (`obligations_denot`).

**The framework.** `Model.lean` is unchanged. The specification is a `TCompiler`. The denotation-hash fix needs a hash over other units' answers and an interface-dependent covering, and both already exist in `NonLocalAns.lean`'s `NCompiler`. As proved, that hash is *fresh* (recomputed from the current interfaces). dotc would *store* it in the owner's API, which is P6.9's stored witness: sound only as a run invariant, so it is not an instance. For the fix dotc would actually ship, the proved soundness is `fix` (recording).

**Assumptions, not derived.** The language abstracts dotc. Two things are inputs from the probes and the harness, not consequences of anything proved: which reads the inliner folds, and which contexts lose their dependencies.

## Steps

- [x] P11.1 Probes (hand-written cases through the harness) to establish the rules above.
- [x] P11.2 `InlineOpaque.lean`: the loop, the two spaces, families as checked examples, the fixes clean on the space.
- [x] P11.3 `conformance inline|opaque [mode]`; harness runs on develop, model and harness reconciled (transparent expansions record nothing; an unqualified top-level constant is recorded; the pickling artefact).
- [x] P11.4 Pending scripted tests per family (retronym/zinc#40, each failing only at its last step, its edited sources passing a clean build); dotc write-ups.
- [x] P11.5 The specification (`InlineOpaqueSpec.lean`, a `TCompiler`): today's coverage failures I1–I3, O1; `fix` and `refine` with obligations and T3a; precision per key. The non-local denotation hash and the per-edit theorem (`InlineOpaqueSound.lean`, `NCompiler`); I1 as an abstraction failure there. `InlineOpaque.lean`'s enumerations are `check_` definitions in `example`s.
- [ ] Future: macros across subprojects (needs the harness to load a macro from final classes); `-Ypickle-java`/Java constants read by inline bodies; the pickling artefact as a dotc reproducibility issue; implementing `bodyDeps` in dotc and re-running the space.
