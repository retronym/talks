# Phase 22 — Scala 3 macro dependencies: what an expansion reads, when it is recorded (`MacroDeps.lean`)

BUG-MAP gap M1: sbt/zinc#249, #1478, scala/scala3#22999, #27125, #20119, partially #23852, #18100, sbt/zinc#1282, #1333, scala/scala3#27133. Phase 11 (`PLAN-inline.md`) specified inline bodies; a macro is an inline def whose body splices a call to an implementation, and the expansion is whatever that implementation *does*. This phase specifies it on the same shape: a `TCompiler` whose task is dotc's, keys read off the tree, a witness per bug, fixes as keys with their cost, and what is left to policy.

## The query: what a macro expansion reads

A call `M.m[T](args)` in a client expands, in the client's compilation, by:

1. `macroBody m` of `M`: which implementation the inline body splices (`${ Impl.f('args) }`); the body's tree, which `M`'s name hash covers (Phase 11);
2. `implCode f` of `Impl`: the implementation's *behaviour*, i.e. its bytecode, run by the compiler's interpreter or classloader. Not its API: a body edit changes the expansion and no signature;
3. what the generated code references: `sig n` of each class the expansion calls (a constructor, a method), its descriptor (scala/scala3#23852);
4. `reflect` of a type argument `T` (and of any type the implementation inspects): its members, *including private ones* (`TypeRepr.of[T].typeSymbol.declarations`), its parents, annotations.

A macro annotation `@annot class C` is the same with the client's own definition as the input: `implCode transform` of the annotation class (scala/scala3#22999).

## What dotc and Zinc record

* dotc's `ExtractDependencies` collects, at the `sbt-deps` phase (after typer): the call `M.m` (member ref, used name), and with `recordInlineCallArgs` each type argument of an inline call as `DependencyByMacroExpansion` (scala/scala3#23900, sbt/zinc's `macroExpansion` relation: invalidate on *any* API change of `T`).
* Since scala/scala3#24969 (3.8.3) the `Inlining` phase traverses each expansion and records its references, so generated references are covered; before, only quoted code's references were (scala/scala3#23852, #18100).
* Since #24969, all dependencies are *sent* to Zinc from `Inlining`. With pipelining, dotc signalled `dependencyPhaseCompleted` from the pickler's background thread, before `Inlining` (scala/scala3#27125, fixed on dotc main by signalling after the send; Zinc's `CompilerPhaseListener.waitForInlining` works around 3.8.3–3.9). Java units under `-Xjava-tasty` are dropped before `Inlining`, so their dependencies are never sent (scala/scala3#27133).
* Zinc: a class with a macro (`hasMacro`, dotc's `Macro` flag on an inline def with a splice) gets a *transitive bytecode hash* over its internal member-ref upstream (sbt/zinc#1282, `addTransitiveBytecodeHash`); a change of it is an `APIChangeDueToMacroDefinition`, which invalidates every dependent of the macro's owner. Only the macro's own subproject is in that upstream: an implementation in another subproject is never in it (sbt/zinc#1478's gap; #1282's description says so).
* A macro annotation's `transform` is not flagged `Macro`, so its owner gets no transitive hash (scala/scala3#22999).

## The model

Units with a static project assignment. A unit declares public members (a signature), macro defs (`macroDef impl f`), implementations (`impl code`: what it generates: literals, references, reads of the type argument), macro annotations (`annot code`), and private members. Its interface is its declarations (the TASTy and classfile view; an implementation's code is in it, as bytecode is). A client's code calls macros (with an optional type argument) and applies annotations.

Queries: `sig n`, `macroBody n`, `implCode n`, `reflect`. The tree after inlining marks each reference: the client's own code (typer); an implementation read for a macro, internal or not to the macro's project; an annotation's implementation; a generated reference; a type argument read.

Keys: `name n` (Zinc's name hash: a member's signature, a macro def's body tree, an implementation's *signature*); `api` (`DependencyByMacroExpansion`: any public API change); `bytecode` (the transitive bytecode hash, here the unit's whole interface). Designs (bridge plus Zinc rule):

| Design | Generated refs | Type args | `implCode` key | Annotation `transform` | Early analysis |
|---|---|---|---|---|---|
| `pre24969` (≤ 3.8.2) | no | `api` | internal only | no | full |
| `pre23900` | no | no | internal only | no | full |
| `today` (3.9, Zinc develop) | yes | `api` (public) | internal only | no | full |
| `early` (3.8.3–3.9 without the workaround) | – | – | – | – | none sent |
| `fix` | yes | `api` with private members | every project | yes | full |

## Obligations per bug

| Bug | Query not covered, or covered with a hash that misses it | Obligation |
|---|---|---|
| scala/scala3#23852, #18100 (before #24969) | `sig` of a generated reference | coverage |
| type argument before #23900 (sbt/zinc#1171's Scala 3 face) | `reflect T` | coverage |
| a private member the macro reflects (macro-observes-private-member) | `reflect T` under `api`, whose hash is public | abstraction |
| scala/scala3#22999 | `implCode transform` of an annotation | coverage |
| sbt/zinc#1478, #1282's limit | `implCode f` of an implementation in another project | coverage |
| scala/scala3#27125 (handshake before `Inlining`) | every query: the early analysis has no keys | coverage of the analysis Zinc hands on |
| scala/scala3#27133 | the dependencies of a Java unit under `-Xjava-tasty` | coverage (Java units; masked in one project by recompiling every Java source on a Scala change) |
| scala/scala3#20119 | a spurious cyclic-macro error under early output | compositionality of the pipelined group; not modelled here |

## Fixes as keys, and their cost

* Record generated references after inlining (#24969, done).
* Type arguments as `api` keys (#23900, done); with private members in the hash, abstraction holds for reflection; cost: any private edit of `T` recompiles every macro call over `T`.
* The implementation's bytecode as a key wherever the implementation lives: across projects Zinc would need the upstream's bytecode hashes in the analysis it reads (it has them in the upstream's analysis). Cost: as #1282, any bytecode change of the implementation's class recompiles every call site; a per-method key would be finer but unsound unless transitive over what the implementation calls.
* Macro annotations' `transform` treated as a macro (the `Macro` flag or Zinc recognising `MacroAnnotation` subclasses).

## Policy, not keys

The early-output handshake is not a key: T3a is about the state at the end of the loop, and the obligation is on *which* state Zinc writes as early analysis. It must be read from the complete tree (after `Inlining`). dotc's fix (signal after sending) and Zinc's `waitForInlining` both enforce that ordering; it cannot be stated as a covering relation. Likewise the recompile-all-Java policy that masks #27133 in one project, and #1282's choice to recompile the macro's owner (and so all its dependents) rather than the call sites only (sbt/zinc#1333).

## Proved vs checked

Proved, for every program, project assignment and edit (`MacroDeps.lean`, a `TCompiler`, kernel `decide` for witnesses, standard axioms only): `faithful` (a unit asks exactly the references in its tree); `obligations_fix`, `fix_sound` (T3a); one witness per bug, naming the failed obligation (`gen_pre24969`, `targ_pre23900` and `annot_today`, `crossProject_today`, `early_violates`: coverage; `private_today`: abstraction); `today` covers the generated reference and the type argument (two `example`s); cost witnesses `bytecode_coarse`, `private_coarse`.

Checked only against sources, not the harness: that the designs are dotc's and Zinc's (the `today` row: dotc 3.9 `ExtractDependencies`/`Inlining`/`Pickler`, Zinc `develop`'s `addTransitiveBytecodeHash`, `macroExpansion` relation and `CompilerPhaseListener`). Not modelled: #20119 (compositionality of the pipelined group), #27133 (Java units), #23783 (annotation arguments), macro *definitions'* suspension within a run.

Prediction for the harness or a pending scripted test: `private_today`, a macro that reflects a private member of its type argument (`macro-reflects-private-member-scala3`); untested.

## Steps

- [x] P22.1 `MacroDeps.lean`: the language, the task, the tree, `faithful`.
- [x] P22.2 Witnesses per bug (kernel `decide`), designs `pre24969`, `pre23900`, `today`, `early`.
- [x] P22.3 `fix`: obligations, T3a; precision witnesses (the bytecode key, private members).
- [x] P22.4 PLAN status row, BUG-MAP M1 entries.
