# Phase 28 — SAM conversion and local classes (BUG-MAP gap L1)

## Question

A lambda converted to a SAM type, and a local or anonymous class, are classes in the output with no Zinc class of their own: Zinc attributes their dependencies to the enclosing top-level class. Their lowering reads the target type's members through its whole ancestry: which abstract methods remain after defaults, so whether the type is functional and which method the lambda implements, and whether the target is an interface, so `invokedynamic` + `LambdaMetafactory` or a class at compile time. The question is whether the keys the bridges record for the enclosing class cover those reads, for Scala 2, Scala 3 and Java clients.

Bugs: sbt/zinc#830 (a lambda to a Java SAM type is not recompiled when the SAM's method changes; fixed by sbt/zinc#1288 and scala/scala#10617 for Scala 2, scala/scala3#16996 for Scala 3), sbt/zinc#192 (Java anonymous and local classes; fixed by sbt/zinc#217), sbt/zinc#1528 (same-source dependencies and the `memberRef ⊇ inheritance` invariant; merged 2025).

## The observable, as queries

For a class `t`, one query `info`: is `t` an interface, its parents, its declared methods (name, parameter types, result, abstract or not). A client's lowering asks it for every class of the walk from the target up its parents. From the answers:

* **Functional.** The members merged up the walk (the first declaration of a name wins, so a default overrides an inherited abstract method); the type is functional if exactly one merged member is abstract, and a lambda of arity `n` converts if that member takes `n` parameters.
* **Which method.** That member: its name and descriptor are what the lambda's output encodes (the `LambdaMetafactory` call site's `samMethodType`, or the anonymous class's override).
* **`invokedynamic` or a class.** Every class of the walk an interface: `invokedynamic`; otherwise (a Scala SAM class) a class at compile time. Java requires an interface.
* **An anonymous or local class** must implement the merged abstract members, so its output reads the same walk.
* **A lambda in argument position** `o.m(() => …)` first asks `o` for its alternatives named `m`, then the walk of each alternative's parameter type, and converts to the one alternative whose parameter type is functional at that arity: none is an error, two are an ambiguity.

The enclosing top-level class is the Zinc class that records all of it: in the model a client unit is a top-level class whose uses are lambdas, anonymous and local classes, and its keys are read off its output.

## What the bridges record today

| Use | Scala 2 before #1288 | Scala 2.12.19+/2.13.13+ (#1288, scala/scala#10617) | Scala 3 (#16996) | Java (`JavaAnalyze`, after #217) |
|---|---|---|---|---|
| lambda, target `t` named by the client | `memberRef` on `t`, used name `t` | + `LocalDependencyByInheritance` on `t` (the `SAMFunction` attachment) | `LocalDependencyByInheritance` on the `Closure`'s `tpt` class | `memberRef` on `t` when `t` is a `Class` constant or in a declared descriptor |
| anonymous or local class extending `t` | `LocalDependencyByInheritance` on `t` | same | same | `LocalDependencyByInheritance` on `t`, the local class mapped to its top-level class (#217; before it, nothing) |
| lambda as the argument of `o.m` | `memberRef` on `o`, name `m` | + local inheritance on the **chosen** alternative's parameter type | same | `memberRef` on `o` (the `Methodref`'s class); the parameter types are only in descriptor strings, which `ClassFile.types` does not read |

What an edge stands for: `invalidateClassesInternally` invalidates, for a class `p` whose API changed, the transitive inheritors of `p`, the local inheritors of each, and the member-ref dependents of each (by name for Scala, all for Java). So an inheritance or local-inheritance edge on `t` covers every class of `t`'s walk with its whole API, and a Java member-ref edge on `t` does too (`t` is recompiled when an ancestor changes, and its API includes inherited members). In the model that is the key `(x, api)` for every `x` of the walk. A Scala member-ref edge with used name `t` covers no member of `t`: the key `(t, present)`.

## Predicted failed obligations

| Bug or prediction | Use | Failed obligation | Witness |
|---|---|---|---|
| sbt/zinc#830 (Scala 2 before #1288) | lambda | coverage: the walk of `t` has only `(t, present)` | `w830_pre` |
| sbt/zinc#192 (Java before #217) | anonymous class | coverage: no key at all | `w192_pre` |
| **P1** (Java today): a lambda passed to `O.run(F)`, `F`'s abstract method changes | lambda argument | coverage: `F`'s walk has no key; `J`'s constant pool names `O` and `J` only (checked with javac 21; clean v1: "incompatible parameter types in lambda expression") | `p1_today` |
| **P2** (Scala 2.13, Scala 3, Java today): `run(F1)` and `run(F2)`, `F1` not functional; `F1` gains a default and becomes functional | lambda argument | coverage: the unchosen alternative's parameter type is walked with no key (checked: v0 compiles, v1 ambiguous on scalac 2.13.16, Scala 3.7.3 and javac 21) | `p2_today` |
| sbt/zinc#1528 | same-source classes | not coverage: a policy obligation of the files layer. Zinc drops same-source `memberRef` edges and relies on recompiling the whole source, so every class of a recompiled source must be compared after the round (the fix adds `invalidatedSources`' classes to `recompiledClasses`). With a class compiled but not compared, `changed` misses its change and its dependents | stated for `Files.lean` (the files layer, coded in parallel); not in `Sam.lean` |

## The fix, as keys with cost

`fix`: for a lambda in argument position, a local-inheritance edge (the walk's `api` keys) on the parameter type of **every** alternative considered, not only the chosen one; Java's extractor reads the SAM types from the `invokedynamic` and `Methodref` descriptors (or javac's tree) and records the same. Cost: one edge per SAM-typed parameter of each alternative of each overloaded method called with a lambda; nothing outside lambdas in argument position (`fix_eq_today` there). Precision: the edge has the whole API as hash, so any change to an alternative's parameter type recompiles the client, as today's edge on the chosen type does.

## Results (`Zinc/Sam.lean`)

A `TCompiler` over an arbitrary finite set of names, for top-level clients whose bodies hold lambdas (target named, or in argument position) and anonymous or local classes; types declare interface-ness, parents and methods. Keys per design are read off the output (`recKeys`).

| Result | Status |
|---|---|
| `obligations_fix`, `fix_sound`: the fix meets `comp`, coverage and abstraction, and T3a holds | proved, every program |
| `obligations_today_argFree`, `today_sound_argFree`: today's bridges (Scala 2.13.13+, Scala 3, Java after #217) meet the obligations on the sources without a lambda in argument position | proved, every program |
| `today_sub_fix`, `fix_eq_today`: the fix records everything today does, and exactly that on outputs without a lambda in argument position | proved, every output |
| `w830_pre` (sbt/zinc#830): Scala 2 before #1288, a lambda's walk has only `(t, present)`; the lowering changes with the SAM's result (`example`) | proved, one witness |
| `w192_pre` (sbt/zinc#192): Java before #217, an anonymous class records nothing | proved, one witness |
| **P1** `p1_today`: Java today, `O.run(() -> 1)`, the SAM type has no key | proved, one witness; checked with javac 21 (constant pool, clean v1 fails) |
| **P2** `p2_today`: Scala today, the unchosen alternative `run(F1)` has no key; making `F1` functional makes the call ambiguous (`example`) | proved, one witness; checked with scalac 2.13.16, Scala 3.7.3 and javac 21 |

Proved for every program: the four obligations-and-soundness results and the cost. Checked: the witnesses (kernel `decide` on one program each) and the compiler behaviour behind P1 and P2 (javac, scalac, dotc on the probes in this file's table). Not checked against Zinc: P1 and P2 are predictions until the pending tests below run.

Simplifications: one lambda arity and no parameter types for the lambda; members merge by name, the first declaration on a depth-first walk winning (JLS §9.4.1.3 and Scala's linearisation agree with it on the programs here); overload resolution picks the single applicable alternative, with no most-specific step; the walk is bounded by `fuel`.

### Pending tests (predicted misses)

- `sam-java-lambda-argument` (Java client): `F.java` `interface F { int apply(); }`, `O.java` `class O { static void run(F f) {} }`, `J.java` `class J { void go() { O.run(() -> 1); } }`; change `F.apply` to take an `int`. Expected: `J` fails to compile. Predicted with Zinc today: `J` is not recompiled (`p1_today`).
- `sam-overload-becomes-functional` (Scala client, and a Java variant): `trait F1 { def apply(): Int; def other(): Int }`, `trait F2 { def apply(): Int }`, `object P { def run(f: F1) = (); def run(f: F2) = () }`, `class K { def go = P.run(() => 1) }`; give `F1.other` a default. Expected: ambiguity error. Predicted with Zinc today: `K` is not recompiled (`p2_today`).

### sbt/zinc#1528

A policy of the files layer, not a coverage failure here: Zinc records no `memberRef` between classes of one source and relies on compiling the whole source, so its change detection must compare every class the round compiled; the merged fix adds `invalidatedSources`' classes to `recompiledClasses`. The statement belongs with `Files.lean` (coded in parallel by the files-layer session): a loop that compiles the closure of `R` under sources but compares only `R` misses a co-compiled class's change, and comparing the closure is an instance of the generic loop.

## Steps

- [x] P28.1 This design.
- [x] P28.2 `Zinc/Sam.lean`: the task, today's keys per bridge, witnesses by kernel `decide`, the fix's `Obligations` and T3a, today's obligations without lambdas in argument position, the fix's cost.
- [ ] P28.3 The pending tests above in retronym/zinc, and #1528's statement in the files layer.
