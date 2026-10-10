# Phase 18 — annotations as API and as dependencies (`Annotations.lean`)

## Question

A definition `@Ann(arg) class S` asks things about `Ann` when it compiles: that its constructor takes the arguments, whether it is a static annotation (so whether it is pickled and seen by separate compilation), and for a macro annotation its `transform` body, which rewrites `S`. An argument may name a constant of another class (`@SerialVersionUID(Consts.Uid)`). A client of `S` may read `S`'s annotations (a macro, a derivation, Java's retention). Which keys does Zinc record for these queries, and does the hash move when the answers do? BUG-MAP's cluster AN: sbt/zinc#1842 (the user's open PR), #237, scala/scala3#22999, #23783.

## What the bridges do, read off the code

* Scala 2 (`ExtractAPI.annotations`): the API of a definition includes its static annotations (`staticAnnotations`), read at typer (#237 restored the phase travel), with arguments printed. `Dependency` and `ExtractUsedNames` do not visit `sym.annotations`, so `S` records no edge to `Ann` or to the classes its arguments name (#1842).
* Zinc core: a changed source that declares an annotation class invalidates its member-ref dependents unconditionally (`APIChangeDueToAnnotationDefinition`), but with no edge from `S` there is nothing to invalidate.
* Scala 3 (`ExtractDependencies`): the same gap as Scala 2 before #1842 (#1842's pending Scala 3 tests).
* A macro annotation's `transform` body is a method body; no class's API hash covers it (#22999).

## Model

Units: annotation classes (static or not, constructor arity, `transform` body), constant holders, annotated definitions `defn a arg` (one annotation, a literal or a constant reference as argument), clients reading a definition's annotations. Queries: `ctor`, `static`, `transform`, `const`, `annots`. Keys: a class key per unit. Bridges: `today` (the definition records nothing on `a` or the constant's holder), `rec1842` (it records both). Hashes: `noBody` (an annotation class hashed without its `transform` body) or `withBody`.

## Results (`Annotations.lean`)

| Result | Status |
|---|---|
| `obligations_comp`: the two-stage joint compile (definitions against the round's classes, clients against the round's definitions) is a fixed point | proved, every program |
| `obligations_fix`, `fix_sound`: #1842's keys (the annotation's class, a constant argument's holder) with a macro annotation's `transform` body in its hash meet the obligations, so T3a | proved, every program |
| `today_not_coverage` (#1842): the definition's `ctor` query to its annotation's class has no key, whatever the hashing | proved, one witness |
| `noBody_not_abstraction` (scala/scala3#22999): two macro annotations differing in `transform` hash alike, whatever the keys | proved, one witness |
| #237 | `HashForms.masking_237` (annotations read at a phase that drops them) |
| scala/scala3#23783 (a macro reading a type argument's annotations) | the client's `annots` query on a unit reached through a type argument: covered when the client records a key on that unit, as `client d` does here; the bug is the missing key |

So #1842 as a key: a class key, from the annotated definition, on the annotation's class and on the holders of constants in its arguments. It fixes coverage; it does not fix #22999, which is abstraction: the key exists and its hash leaves out the body the expansion read. Hashing a macro annotation's `transform` body (as `InlineOpaque.lean` hashes inline bodies) closes it; its cost is invalidating the annotated definitions on any body edit of a macro annotation, which is what a macro's users need anyway. A non-static annotation is absent from the pickle, so leaving it out of the API is consistent across forms (`HashForms` stability), not a masking.

## The cluster's scripted tests

On develop: `annotations-in-java-sources-a`, `-a2`, `-b`, `annotations-in-java-params` and `specialized` pass (annotations in the API of Java sources and of specialised members). #1842 adds `annotation-ctor-change-class`, `annotation-ctor-change-param`, `annotation-class-signature-change`, `annotation-constant-arg`, `annotation-java-interface` (each an instance of `today_not_coverage`, fixed by `obligations_fix`'s keys), with the Scala 3 and scala2-sbt-bridge variants pending (the same gap in those bridges).

## Steps

- [x] P18.1 `Annotations.lean`: the instance, obligations for the fix, counterexamples per bug.
- [x] P18.2 The cluster's scripted tests mapped.
- [ ] Future: several annotations per definition and Java retention; the macro-annotation body hash in the Scala 3 bridge.
