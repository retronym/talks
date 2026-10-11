# Phase 16 — class-name agreement between the bridge and Zinc (`Naming.lean`)

## Question

`Query := CUnit × Q` and `Key := CUnit × K` assume one spelling of a unit. In Zinc there are at least two. The compiler reads a class through the name its output carries: the classfile on disk, the class name Zinc analysed (`productClassName`, `ClassToAPI`, `generatedNonLocalClass`). The bridge records dependencies under the name it computes from symbols (`classDependency`, `binaryDependency`, `associatedFile`). When the two spellings of one class differ, the recorded key names a unit Zinc never compiles, and the class it should name never invalidates its dependent. When two classes share one spelling (one file on disk), their hashes merge. BUG-MAP's cluster N: 8 bugs, newest 2026.

| Bug | Spelling of the read (product) | Spelling of the key (bridge) |
|---|---|---|
| sbt/zinc#1812, scala/scala3#27134 | `A` (Java class in the default package) | `<empty>.A` |
| sbt/zinc#127 | `A$Inner` (expanded) | `A.Inner` |
| sbt/zinc#1351 | `A.Inner` (`AnalyzingJavaCompiler`) | `A$Inner` (bridge, Scala 3 pipelining) |
| scala/scala3#9694 | `O$I` (inner class) | `O` (`associatedFile` of the top-level classfile) |
| sbt/zinc#716, #1233 | compactified classfile name | full name |
| sbt/zinc#1553 | one file for `A` and `a` (case-insensitive filesystem) | two classes |

## Model

A construction over any `TCompiler` (`Tree.lean`) with two spellings of its units into names: `read : CUnit → Name` (how the compiler reaches a unit's output: its product) and `rec : CUnit → Name` (how the bridge records a key on it). The named compiler's units are names; its task asks `(read u, q)` where the underlying one asks `(u, q)`, and its keys are `(rec u, k)` where the underlying ones are `(u, k)`. Coverage asks `q.1 = k.1`, i.e. `read u = rec u` for every unit a trace reaches.

## Results (`Naming.lean`)

| Result | Status |
|---|---|
| `run_rename`, `trace_rename`: a renamed task runs as the original against the pulled-back oracle, and traces the renamed queries | proved, every task |
| `coverage_named`: with one spelling (`read = rec`), the named compiler's coverage is the underlying one's | proved, every `TCompiler` |
| `not_coverage_named`: a traced unit whose read spelling no covering key carries breaks coverage | proved, every `TCompiler` |
| `collision`: two units read through one name cannot be served by any named oracle when their answers differ (#1553) | proved |
| `spelling_bugs`: #1812, #127, #1351, #9694, #716/#1233, each as a pair of spellings on a minimal client | proved, kernel `decide` |
| `default_package_1812`: on `JavaSpec`'s instance (fix keys, obligations proved), a default-package client resolving `A` asks for `A` and records `<empty>.A`; with one spelling its coverage carries over | proved, kernel `decide` |

The construction proves coverage only; comp and abstraction carry over when `read` is injective (a bijection between units and names), which `collision` shows is itself an obligation.

## The cluster's scripted tests

All pass on develop, each the regression test of a spelling fixed by making the two sides agree: `java-inner` (#127), `malformed-class-name`, `malformed-class-name-with-dollar`, `java-name-with-dollars` (canonical names of Java and `$`-named classes), `compactify`, `compactify-nested`, `compactify-nested-class` (#716), `unexpanded-names`, `package-object-nested-class`, `recorded-products` (#1233). Each is an instance of `coverage_named`'s hypothesis on one spelling pair. #1812 (Scala 3, Java class in the default package) and #1351 (Java nested classes under Scala 3 pipelining) have no test on develop; both are fixes on the dotty side (scala/scala3#27134 for #1812).

## Policy

The fix is one spelling, not more keys: a canonical name function shared by the bridge and Zinc (the binary name of the classfile, as `productClassName` has it), or a normalisation at the callback boundary. Recording both spellings would satisfy coverage, but it hides the disagreement: a test should assert agreement.

## Steps

- [x] P16.1 `Naming.lean`: the construction, `coverage_named`, `not_coverage_named`, `collision`, witnesses.
- [x] P16.2 The cluster's scripted tests mapped (above).
- [ ] Future: comp and abstraction for the named compiler under an injective `read`; pending tests for #1812 and #1351 once the Scala 3 version scripted uses has a bridge to test against.
