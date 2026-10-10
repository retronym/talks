# Phase 17 — hash stability across forms: source, pickle, classfile (`HashForms.lean`)

## Question

The bridge extracts a unit's API from whichever form the compiler holds: the typed tree when the unit is in the round, the unpickled (or TASTy, or classfile) symbols when it is read from the classpath. Zinc compares the hash stored in one run with the hash computed in the next, often from a different form. `Model.lean` assumes `π : Iface → K → Hash`, a function of the interface; these bugs are cases where the bridge's view of the interface carries an artefact of the form, so `π` is not a function of the interface. BUG-MAP's cluster H1: 6 bugs, newest 2026.

| Bug | Artefact | Forms that differ |
|---|---|---|
| sbt/zinc#1782 | a type parameter's id from `fullName` through a refinement owner | source vs unpickled |
| sbt/zinc#88 | a spurious `override` flag | source vs unpickled |
| scala/scala3#18080 | synthetic context-bound evidence names (`evidence$1`, `evidence$2`) | one compile vs the next |
| scala/scala3#9133 | full names moved by owner changes before erasure | before vs after the owner change |
| scala/scala3#9730 | an identity hash in a `toString` inside the API | one run vs the next |
| sbt/zinc#237 | annotations read at the wrong phase (phase travel) | the phase that drops them vs the one that keeps them |

`JavaOrder.lean`'s `flip_spurious` is the two-form Java case (classfile view stored, source view fresh).

## Model

Forms `F`; a unit's interface `i`; the bridge sees `view f i` and hashes it, `π f i = h (view f i)`. The formed compiler's interface is the pair `(f, i)`: answers depend on `i` only, hashes on both.

* **Form stability**: `h (view f i) = h (view f' i)` for all forms. Without it, an unchanged interface read through another form reports a change: a spurious invalidation (precision).
* **No masking**: `h (view f i) = h (view f' i') → answers of i and i' agree`. Without it, a real change hides behind a form that drops the detail (#237): abstraction, so soundness.

## Results (`HashForms.lean`)

| Result | Status |
|---|---|
| `abstraction_formed_iff`: abstraction for the formed interface `(f, i)` holds exactly when no form masks a difference | proved |
| `stable_precise`, `stable_not_spurious`: with form stability a change reported across forms means the interface changed | proved |
| `unstable_spurious`: without it some unchanged interface reports a change (`Spurious`, precision as a definition) | proved |
| `canonical_stable`, `canonical_noMasking`: hashing a canonical form through a normalisation of each view is stable and inherits abstraction from the canonical view | proved |
| `skip_unsound`, `conservative_sound`, `conservative_spurious`: with the form in the key, skipping a cross-form comparison misses a real change; reporting it is sound and spurious whenever the interface did not change | proved |
| `artefact_bugs`: #1782, #88, scala3#18080, #9133, #9730, each a form artefact, each a spurious invalidation | proved, kernel `decide` |
| `masking_237`: annotations dropped in one form mask an annotation change, so abstraction fails | proved |

So the cluster splits by obligation: five bugs are precision (an artefact makes an unchanged interface report a change, every run the forms alternate), and #237 is soundness (a form drops a detail, masking a change). The fix is the same shape for both: hash a canonical form, i.e. normalise each view before hashing (the fixes of #1782 and scala3#18080 did this for one artefact each: ids not from `fullName`, stable synthetic names). Carrying the form in the key is not a fix: it turns every cross-form comparison into a conservative invalidation.

## The cluster's scripted tests

On develop: `abstract-type-override`, `type-lambda-refinement-owner`, `unstable-existential-names` (apiinfo), `trait-extends-trait-extra-round`, `trait-local-change`, `fbounded-existentials` pass, each a regression test of one artefact normalised (`canonical_stable` for that artefact). `pipelining/java-comment-change` is pending: the Java instance of `unstable_spurious` (`JavaOrder.flip_spurious`).

## Steps

- [x] P17.1 `HashForms.lean`: the formed interface, the obligations across forms, precision as a definition, witnesses.
- [x] P17.2 The cluster's scripted tests mapped (above).
- [ ] Future: `Spurious` lifted into `Model.lean` as the precision definition (REVIEW finding 4), and the formed interface as a `TCompiler` construction like `Naming.lean`'s.
