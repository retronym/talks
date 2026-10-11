# Track B — binary compatibility (`BinCompat/`)

## Problem

Zinc asks whether a client must be *recompiled*; MiMa asks whether its old classfile still *links*. With JVM linkage written as a `Task` (Track J), both are questions about a trace against an edited environment, so the Zinc framework's vocabulary (keys, coverage, abstraction) should describe MiMa too. Two questions follow:
- Is MiMa sound, and where it isn't, why? MiMa had never been checked against a model of the JVM.
- How do Zinc and binary compatibility relate? The expectation: Zinc-clean implies binary-compatible for a client, and the converse fails exactly where MiMa is needed.

## What was built

- **`probes/mima/Mima.scala`** runs `mima-core` 1.2.1 (pinned, via scala-cli) on class directories: the `v0`/`v1` that `probes/jvm` renders, and, for Scala, `probes/mima/scala.sh` compiles each `Scala/Catalogue.lean` case with scalac 2.13.18.
- **`BinCompat/Mima.lean`, a model of MiMa's checker** (`Analyzer`, `TemplateChecker`, `FieldChecker`, `MethodChecker`), read from its sources.
- **`BinCompat/Edits.lean`, an edit space:** every well-formed single edit of two base libraries, changing one class's header (abstract, final, interface, public, superclass, interfaces) or setting one member slot (`m()V`, `m()I`, field `m`) to absent or any combination of flags. 302 edits. The client space `spaceB` is `Jvm.Clients.space3` plus `X implements J`, `X implements I, J` and `m()I` sites.
- **`BinCompat/Keys.lean`, MiMa as a bridge design** in `DESIGN-spec.md`'s terms. `mima o n` is `(keys o).flatMap (check o n)`, with keys per class public in the old library (`template c`, `field c n d`, `method c n d`, `newMethods c`) and `covers` saying which class-table entries each key's comparison reads. The obligation: if no key reports, every client that linked against the old library still links. MiMa compares by a relation, not equality (an added method is a changed answer, and fine), so abstraction here means "strong enough for linking".
- **`BinCompat/Fixed.lean`, a corrected rule set,** and `BinCompat/Sound.lean`, its check on the space.
- **`BinCompat/ZincBridge*.lean`, the Zinc ⇒ binary-compatible theorem** (Track B4) and its variants.

Steps:
- Track B1: MiMa against the catalogue and the edit space. Done.
- Track B2: MiMa as keys; its gaps; corrected rules checked on the space. Done; a proof for all libraries is open.
- Track B3: source-level spaces. Started; open.
- Track B4: Zinc-clean implies binary-compatible. Done.

## Results

### The model of MiMa agrees with MiMa (Track B1)

As a multiset of problems per library, on all 35 `Jvm` catalogue cases of Tracks J1–J3 and all 302 edits (`probes/mima/compare.py`). On the catalogue the first problem MiMa reports is each case's `mima` field, checked against the model by kernel `decide`; two expected names were wrong before (`defaultRemoved` gets `DirectAbstractMethodProblem`, `superCallAbstract` gets `AbstractClassProblem`).

Per edit, MiMa's report against `breaksSomeClient`:

| MiMa | some client breaks | only changes behaviour | neither |
|---|---|---|---|
| reports | 140 | 0 | 17 |
| silent | **40** | 4 | 101 |

- **The 40 false negatives** all break on HotSpot 21, 25 and 27 (each edit's breaking client, run by `probes/jvm`). They fall into four gaps, below.
- **The 17 reported edits that break no client** are all `ReversedMissingMethodProblem` (a new abstract method). It is reachable only through library code calling it on a client's subclass, and the model has no library method bodies (Track J4), so they are outside the client space, not false positives.
- **The 4 silent edits that change behaviour** (a new override in `B`, a field in `B` hiding `A`'s) are outside MiMa's scope.

### Why MiMa misses: coverage and abstraction gaps (Track B2)

`miss_changes_footprint` (from `link_congr`): a client that stops linking has a footprint query whose answer changed. So every miss is either a **coverage gap** (no key covers the changed query) or an **abstraction gap** (a key covers it and passes). Each gap has a witness in `BinCompat/Keys.lean` (library edit, client, changed query) by kernel `decide`, confirmed on HotSpot, with MiMa silent.

| Gap | Witness | Edit | Client failure | Kind |
|---|---|---|---|---|
| MiMa-F1, final fields | `finalField` | a public field becomes `final` | `putfield`/`putstatic`: `IllegalAccessError` | abstraction: the field key covers it, and `final` is not compared |
| MiMa-M1, shadowing through a subclass | `shadowStatic`, `shadowField`, `overridePrivate` | `B extends A` gains a member named like an inherited one, with any access and any of `static`/`final`; or `B`'s override becomes private | `invokevirtual B.m` / `getfield B.m`: ICCE, `IllegalAccessError`, or a final override at load | coverage: MiMa checks only members a class declares. When `B` declared it, abstraction instead: MiMa's parser drops private members and its lookup finds `A.m` |
| MiMa-F2, interface fields first | `ifaceField` | an interface gains a field | `X extends A implements I` resolves `X.m` to `I.m` (superinterfaces before superclass) | coverage: MiMa's field lookup never reads interfaces |
| MiMa-D1, conflicting defaults | `defaultConflict` | an interface gains a default another public interface has | `invokeinterface`: ICCE | coverage: `checkNew` reads only abstract methods |
| MiMa-P1, protected members | `protectedRemoved` | a protected method is removed | a subclass client's call: `NoSuchMethodError` | coverage: only `ACC_PUBLIC` members get keys |

MiMa-P1 is outside the edit space (the bases have no protected member), hence its own witness. Scala's `protected` is public in bytecode, so it affects Java-defined libraries.

**The corrected rules** (`BinCompat/Fixed.lean`) are MiMa plus: the member a reference *through* each public class resolves to, by JVM resolution with private members and superinterfaces, compared by access rank, `static`, `abstract` and `final`, for methods and fields (MiMa-M1, MiMa-F1); an interface that newly sees a field (MiMa-F2); a new default that an unrelated public interface also has (MiMa-D1). On the space they report all 40 false negatives and nothing that breaks no client beyond MiMa's own 17. `BinCompat/Sound.lean` checks by kernel `decide` that every unreported edit leaves every client of `spaceB` linking: 105 edits against the full client space, about 30 minutes and 7 GB, so it is built on demand (`lake build BinCompat.Sound`).

Not proved: soundness of the corrected rules for all libraries (`ROADMAP.md`). The equality design (every query a key, compared by equality) is sound for all libraries by `link_congr`, but reports every edit.

### Source-level spaces, started (Track B3)

The Scala catalogue cases of Tracks S1–S3, compiled by scalac 2.13.18 and run through MiMa: MiMa reports exactly the cases where the old client fails against `v1`.
- `abstractAddedToTrait`, `valAddedToTrait`: `ReversedMissingMethodProblem` (for the `val`, the getter and the mangled setter).
- `classBecomesTrait`: `IncompatibleTemplateDefProblem`.
- `paramWithDefaultAdded`: `DirectMissingMethodProblem`.
- `widenedToValueClass`: `FinalClassProblem`, `DirectMissingMethodProblem` (the constructor), `IncompatibleMethTypeProblem`.
- Silent on `concreteAddedToTrait` (compatible) and `traitOverrideAdded` (links, but runs `B.m` where a fresh build runs `T.m`; outside MiMa's scope).

### Zinc-clean implies binary-compatible (Track B4)

**The front end.** Scala lowering is an `XCompiler` (`General.lean`): a unit is a source unit, its task is `lowerSrc` with queries renamed to `(unit, side)`, its output the unit's declarations plus its classfiles. The interface is the declaration, so it is source-determined. Every query is answered as if in the same run (`inRun = true`), faithful for Scala 2.12 and 2.13. A key per traced query, hashed by the declaration it read, meets the obligations (`searched_obligations`).

**`XCompiler.untouched_eq_clean`** (`BinCompat/ZincBridge.lean`). After an edit, if Zinc's loop stops and a unit was in none of its rounds, its old output equals its output in the clean build of the new sources. Hypotheses: the framework's `Obligations`; source-determined interfaces (the explicit-interface case of T3b); a `Sound` policy inside `S`; the dirty set in the first round; the old build up to date except at the edit (`inv_of_edit`). `must_recompile` is the contrapositive. For lowering, `after_eq_fresh`: the client's old classfiles with the new library give the same `Jvm.outcome` as a fresh build, and `compatible_of_untouched`: `Jvm.Compatible` holds whenever the fresh build links.

**The converse fails** (`gap_witness`). Adding a concrete method to a trait leaves the old `X extends T` linking (it selects the default method), so the edit is binary compatible; but a fresh build adds a mixin forwarder, so `X`'s classfile changes and every sound bridge recompiles it. That gap is what MiMa does not report.

**Scala 3, compiled separately** (`BinCompat/ZincBridgeScala3.lean`). A round reads the rest from TASTy, so the faithful compiler answers `inRun := v ∈ G`. Under F6 the obligation that fails is `comp`: `C extends T`, `T` holding only a `lazy val`, gets different classfiles in `{T, C}` and `{C}` over the same interfaces (`f6_witness`), so no per-unit task makes `comp` hold, whatever the keys (`not_comp`). With retronym/scala3#10 (the TASTy reader computes `NoInits` as the namer does) the faithful joint compilation is Track B4's (`group3Fix_eq`), and Track B4 holds for Scala 3 (`after_eq_fresh_fix`). We take the fix over restricting to programs without the F6 shape: that restriction covers every trait the client reads, library traits included, and excludes common code.

**Zinc's actual keys** (`BinCompat/ZincBridgeKeys.lean`): inheritance on each parent hashed over its ancestors, member-ref name keys on every class the source names, and the unit itself. **Coverage fails** (`coverage_fails`): for `T { def f(v: V): Int }` and `object O extends T`, lowering `O` erases `f` for its forwarders and so asks for `V`, which `O`'s source never names and which is not an ancestor. **The conclusion fails too** (`loop_witness`): `V` becomes a value class, Zinc recompiles `V` then `T`, `T`'s API is unchanged, the loop stops with `O` untouched, and a fresh `invokestatic O.f(I)I` gets `NoSuchMethodError`. The fixes: keys on value classes in inherited signatures (what `searched` does), or hashing a value-class reference by its underlying type. A JVM-linkage theorem predicted a Zinc bug; the pending scripted tests in retronym/zinc#57 reproduce it.

**Library JARs** (`BinCompat/ZincBridgeLibs.lean`). A library has no Analysis, so each query on a library unit is covered by the unit's stamp key, hashed by its whole interface (`stamp_covers`); the bridge meets the obligations (`obligations`). `library_client` is T5a (`inv_external`) followed by `untouched_eq_clean`: a client the loop never recompiled links against the edited JAR as a fresh build does, given a disjoint library, an up-to-date old build, stored stamps that are the old library's interfaces (`fresh_of_stamps`), and a sound policy.

Not done: a restricted Scala 3 theorem without the fix. `XCompiler` subsumes the `NCompiler` statement first planned (through `NCompiler.toX`).

## Issues to file

Drafts against MiMa, one per gap, not yet filed. Each needs a reproducer from the edit space (`lake exe bincompat witness <edit>`) in MiMa's functional-test layout.

1. **A field that becomes `final` is not reported** (MiMa-F1). `FieldChecker` compares access, type and `static`, not `final`. A client's `putfield`/`putstatic` fails with `IllegalAccessError`. Suggested: a `FinalFieldProblem` when the old field is not final and the new one is.
2. **A member a subclass adds can hide an inherited one, and is not reported** (MiMa-M1). `B extends A`, `A.m()` public. If `B` adds a static, private, package-private or protected `m()`, or a field `m` with incompatible flags, a client's `invokevirtual B.m` or `getfield B.m` resolves to the new member and fails; a public final `m()` breaks a client's override at load. MiMa checks only the members `B` declared in the old version. Changing an override `B.m` from public to private is the same failure, also unreported, because the class file parser drops private methods and the lookup finds `A.m`. Suggested: for each class, check the resolution of every inherited public or protected member through that class, with private members in the new version's lookup.
3. **An interface field that field resolution now reaches first is not reported** (MiMa-F2). Field resolution searches superinterfaces before the superclass (JVMS §5.4.3.2). If `I` gains a field `m`, a client `class X extends A implements I` that read `A.m` as `X.m` now gets `I.m`, which is static and final. `FieldChecker` looks only in the class and its superclasses.
4. **A default method that conflicts with another interface's is not reported** (MiMa-D1). If `J` gains a default `m()` that an unrelated `I` has, a client implementing both gets `IncompatibleClassChangeError`. Clients can declare their own interfaces, so any new default can conflict, and MiMa treats new defaults as compatible by design; at least a conflict between two of the library's own interfaces can be reported.
5. **Protected members are not checked** (MiMa-P1). `nonAccessible` is `!isBytecodePublic`, so a protected method a client's subclass calls can be removed without a report (`protectedRemoved`: `NoSuchMethodError` on HotSpot). Affects Java-defined libraries.

## PRs

- retronym/talks#64: MiMa against the `Jvm` model, the gaps, the corrected rules (Tracks B1, B2).
- retronym/talks#59: Zinc-clean implies binary-compatible, and the converse fails (Track B4).
- retronym/talks#62: Track B4 for Scala 3 separate compilation, Zinc's actual keys, and library JARs.
