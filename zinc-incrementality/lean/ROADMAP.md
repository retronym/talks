# From a Zinc model to a model of Scala, Java and the JVM

## Why

The Lean model was built to answer one question: is Zinc's invalidation sound, relative to obligations on the compiler bridge? To answer it, each feature file (`Erasure`, `Hier`, `Flat`, `Inline`, `Names`, …) has its own toy language, sized to what Zinc hashes. That paid off: the toys found real bugs, and the program spaces generated from them were checked against real Zinc.

Those toys are private to one consumer. The same knowledge would answer other questions if it were factored out:

- **Binary compatibility.** Zinc asks whether a client must be *recompiled*; MiMa asks whether its old classfile still *links*. Both are questions about a task's trace against an edited environment. `Jvm/Link.lean` writes JVM linkage as a `Task`, so T1 applies unchanged (`link_congr`).
- **IDE type systems.** The TCK (`retronym/scala-type-system-tck`) already checks IntelliJ against an `asSeenFrom` model that overlaps `Hier`.
- **Scala 2 → 3 migration.** The name-resolution calibration in talks#21 is already a list of differences between the two compilers.

"5×" means five dimensions, each improved by about that factor. It does not mean five times the lines.

| Dimension | Today | Target |
|---|---|---|
| Consumers | Zinc | Zinc, binary compatibility (MiMa), the TCK; migration as a stretch goal |
| Oracles the model is calibrated against | scalac 2/3 through the Zinc harness | adds HotSpot, javac, MiMa, and scalac/javac classfile shapes |
| Shared language layers | none: one toy per Zinc feature | `Jvm`, `Java`, `Scala`, each used by at least two consumers |
| JVM semantics | erasure and forwarders, inside Zinc toys | linkage: methods, fields, access, constants, which method runs |
| People | Jason plus agents | outside contributors, through the tiers in the contributor proposal |

## Relation to `DESIGN-spec.md` and `REVIEW-2026-10-11.md`

This roadmap follows the specification framing of `DESIGN-spec.md`:
- every observable is a query, and a unit's task is the compiler's own algorithm;
- a design is a `keys`/`π`/`covers` triple with an `Obligations` proof;
- enumeration is for testing, and is labelled as such.

`Jvm/Link.lean` already has that shape. Linking is the JVM's own resolution and selection algorithm, written as a `Task`, and its trace is the linkage footprint.

Three of the review's findings apply to these tracks:
- **Finding 1.** The Zinc ⇒ binary-compatible theorem (B4) waits for the framework merge, which unifies four near-copies of the compiler framework into one structure.
- **Finding 7.** Witnesses use kernel `decide`, never `native_decide`, wherever it terminates.
- **Finding 8.** The new layers live beside `Zinc/` (`Jvm/`, `Scala/`), not in it.

The tracks use letters (J, S, V, B), not phase numbers, so they don't collide with `PLAN.md`'s phases.

## Architecture

```
Core      Task (query trees, T1), program spaces, JSON dumps        (today: Zinc.Task)
Jvm       classfiles, linkage, selection, behaviour                 (Jvm/Link.lean)
Java      a javac subset: source → Jvm.World; JLS §13 statements
Scala     a scalac subset: resolution, linearization, asSeenFrom, implicits; lowering → Jvm.World, Scala 2 and 3
consumers Zinc (exists), BinCompat (MiMa), TCK, Migration
```

**Contract: `Jvm.World`, `Jvm.Program` and `Jvm.Site`.** A front end turns sources into a `World` (the classfiles) and a `Program` (what a client loads and executes). A consumer reads a `World`. Only the JVM track changes these types, and only by adding to them.

**Front ends are compilers in Zinc's sense.** Lowering a class reads other classes' interfaces, which is a `Task` like any other. A front end is an `NCompiler` whose output contains classfiles. That gives the one theorem tying the consumers together:

> For a front end that meets Zinc's obligations: if Zinc does not invalidate a client `c` after a library edit, then `c`'s old classfile equals the recompiled one, and so it links against the new library exactly as a fresh build would.

So Zinc-clean implies binary-compatible for that client. The converse fails, and the gap is precisely what MiMa reports. Adding a method is the standard example: it is binary-compatible, yet Zinc must recompile the clients that use the name.

## Tracks

Each track:
- owns one directory and one `lean_lib`;
- works on its own branch off `claude/bincompat-lean`;
- edits only its own section of this file.

No track edits `Zinc/`; talks#21 and the PRs stacked on it own that directory. Integration happens on `claude/bincompat-lean`, which is based on talks#21's branch.

### J — JVM (`Jvm/`)

- **J1. Calibrate the catalogue on HotSpot.** DONE.
  - `lake exe jvmcases` dumps the catalogue as JSON lines. `probes/jvm` renders each case's `v0`, `v1` and client with the Classfile API (classfile version 65), runs the client against both, and compares the `Throwable` and the method that ran with the model. Run it with `probes/jvm/probe.sh "" -- $JAVA_HOME...`; `OUT=dir` keeps the classfiles for MiMa (B1), and `lake exe jvmcases space` gives the client spaces.
  - The probe's sites are what javac emits: `C c = new R(); c.m()` is `new R; invokespecial R.<init>; invokevirtual C.m`. So the verifier's upcast check, instantiation and load-on-reference are part of the model, as `Site` semantics. The model's `LinkError` type gained `verify`, `illegalAccess` and `noSuchField`.
  - Calibrated on Temurin 21.0.12, 25.0.4 and 27. Every case agrees on all three, apart from one known HotSpot bug.
  - `LinkError` → JVM class: `noClassDef` → `NoClassDefFoundError`, `incompatibleClassChange` → `IncompatibleClassChangeError`, `noSuchMethod` → `NoSuchMethodError`, `noSuchField` → `NoSuchFieldError`, `abstractMethod` → `AbstractMethodError`, `instantiation` → `InstantiationError`, `illegalAccess` → `IllegalAccessError`, `verify` → `VerifyError`, and **`finalSuper`, `finalOverride` → `IncompatibleClassChangeError`** (not `VerifyError`) on all three JDKs.
  - **JDK 21 deviates on `defaultConflict`.** `invokeinterface` on a receiver with two maximally-specific defaults throws `AbstractMethodError`, where JVMS §6.5 says `IncompatibleClassChangeError`. This is [JDK-8356942](https://bugs.openjdk.org/browse/JDK-8356942): it regressed in JDK 10 and was fixed in 25. The model follows the JVMS, and the probe reports the JDK 21 result as a known deviation.
- **Finding 7.** DONE. No `native_decide` remains in `Jvm/`. The catalogue's witnesses use plain `decide`. The client-space verdicts use `decide +kernel`, because the elaborator's `decide` hits its recursion limit on them. Both run in the kernel, and none needed `native_decide`.
- **J2. Client spaces.** DONE. `Jvm/Clients.lean` defines `breaksSomeClient k`: some client in a bounded space links on `v0` and fails on `v1`. It also defines `changesSomeClient k`: some client links on both and runs a different method. Clients must be well-typed against `v0`.
  - `space`, for the original 12 cases: an optional client class `X` (superclass, interfaces, `m()V`/`m()I`) and one call site of any kind, owner, descriptor and receiver. 15,652 programs.
  - `space3`, for the J3 cases: adds fields, `invokespecial`, interface statics, and sites run from inside `X`. 44,144 programs.
  - **The probe agrees with the model on every program in both spaces, before and after, on JDK 21, 25 and 27.** The only exceptions are on JDK 21: the JDK-8356942 cases, and the JDK-8350029 cases below.
- **J3. More linkage.** Done for most of it: fields, `invokespecial`, private methods, static and private interface methods, access control, and the verifier's protected check. 23 catalogue cases.
  - Calibrating the space found three things the model lacked. All are now modelled:
    - Loading a class checks that its superclass and superinterfaces are accessible (`IllegalAccessError`).
    - The verifier's `invokespecial` rule turns on whether the referenced class is an interface, not on the constant's tag. An `InterfaceMethodref` to a class passes the verifier and fails in resolution with ICCE. A reference to an interface that is not a direct superinterface is a `VerifyError`. This is the rule on JDK 25 and later. JDK 21 checks the constant's tag instead, so it gives `VerifyError` where 25 gives ICCE, and the reverse. This was [JDK-8350029](https://bugs.openjdk.org/browse/JDK-8350029), fixed in 25. It affects 56 space programs, all in forms javac never emits, and the probe reports them on JDK 21 as a known deviation.
    - The protected-receiver check (§4.10.1.8), predicted by `methodBecomesProtectedOther`.
  - TODO: nestmates. Private access is same-class only. A nest change can only break a client through a library method's own calls, which needs method bodies (J4).
  - TODO: `Object`'s methods in interface resolution; transitive overriding through an intermediate package-private method (§5.4.5); clients in the library's package; a space over two client classes.
- **J4. Behaviour.** TODO. Constants folded into the client. Method bodies, so that a library method's own calls link too. Which method runs is already observed by the probe and is part of the outcome; `changesSomeClient` is the first form of the "links, but runs different code" verdict.

The catalogue on HotSpot, with the J2 verdicts. "MiMa" is the problem MiMa is expected to report, to be confirmed by track B. "HotSpot" is the result on `v1`; "same" means it links and runs the method the model predicts. The breaks and changes columns are counts over the clients that link on `v0`.

| Case | MiMa | Model on `v1` | HotSpot | Breaks some client | Changes some client |
|---|---|---|---|---|---|
| `methodRemoved` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (12/29) | no |
| `resultTypeChanged` | IncompatibleResultTypeProblem | `noSuchMethod` | `NoSuchMethodError` | yes (12/29) | no |
| `classBecomesInterface` | IncompatibleTemplateDefProblem | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (49/78) | no |
| `becomesStatic` | VirtualStaticMemberProblem | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (12/29) | no |
| `becomesAbstract` | AbstractClassProblem | `instantiation` | `InstantiationError` | yes (7/17) | no |
| `becomesFinal` | FinalClassProblem | `finalSuper` | `IncompatibleClassChangeError` | yes (8/17) | no |
| `methodBecomesFinal` | FinalMethodProblem | `finalOverride` | `IncompatibleClassChangeError` | yes (5/29) | no |
| `superclassRemoved` | MissingTypesProblem | `noSuchMethod` | `NoSuchMethodError` | yes (28/78) | no |
| `defaultRemoved` | ReversedMissingMethodProblem | `abstractMethod` | `AbstractMethodError` | yes (4/15) | no |
| `defaultConflict` | — | `incompatibleClassChange` | `IncompatibleClassChangeError` (21: `AbstractMethodError`, JDK-8356942) | yes (4/30) | no |
| `overrideAdded` | — | links, runs `B` | same | no | yes (26/78) |
| `pulledUp` | — | links, runs `A` | same | no | yes (14/50) |
| `methodBecomesPrivate` | DirectMissingMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (18/41) | no |
| `methodBecomesPackagePrivate` | InaccessibleMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (18/41) | no |
| `classBecomesPackagePrivate` | InaccessibleClassProblem | `illegalAccess` | `IllegalAccessError` | yes (16/23) | no |
| `methodBecomesProtected` | InaccessibleMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (12/41) | no |
| `methodBecomesProtectedSub` | InaccessibleMethodProblem | links, runs `p1.A` | same | yes (12/41) | no |
| `methodBecomesProtectedOther` | InaccessibleMethodProblem | `verify` | `VerifyError` | yes (12/41) | no |
| `overrideCutByPackage` | InaccessibleMethodProblem | links, runs `p1.A` | same | yes (18/41) | no |
| `overrideBecomesPrivate` | — | links, runs `A` | same | yes (22/110) | yes (15/110) |
| `superCallPulledUp` | — | links, runs `A` | same | no | yes (20/69) |
| `superCallRemoved` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (22/69) | no |
| `superCallAbstract` | DirectAbstractMethodProblem | `abstractMethod` | `AbstractMethodError` | yes (25/41) | no |
| `defaultSuperCallAbstract` | DirectAbstractMethodProblem | `abstractMethod` | `AbstractMethodError` | yes (7/23) | no |
| `staticIfaceMethodRemoved` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (9/23) | no |
| `staticMovedToIface` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (11/34) | no |
| `defaultBecomesStatic` | VirtualStaticMemberProblem | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (9/23) | no |
| `defaultBecomesPrivate` | DirectMissingMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (9/23) | no |
| `fieldRemoved` | MissingFieldProblem | `noSuchField` | `NoSuchFieldError` | yes (34/57) | no |
| `fieldBecomesStatic` | VirtualStaticMemberProblem | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (34/57) | no |
| `fieldBecomesFinal` | — | `illegalAccess` | `IllegalAccessError` | yes (17/57) | no |
| `fieldBecomesPrivate` | MissingFieldProblem | `illegalAccess` | `IllegalAccessError` | yes (34/57) | no |
| `fieldShadowed` | — | links, runs `B` | same | no | yes (42/165) |
| `fieldIfaceBeforeSuper` | — | links, runs `I` | same | yes (37/224) | yes (37/224) |
| `putstaticBecomesFinal` | — | `illegalAccess` | `IllegalAccessError` | yes (13/49) | no |

For track B, three cases are candidate MiMa false negatives:
- `defaultConflict` (no problem expected).
- `overrideBecomesPrivate`: `B.m` becomes private while `A.m` is still inherited, so a client calling `B.m` gets `IllegalAccessError`, because resolution finds the private method first.
- `fieldIfaceBeforeSuper`: an interface of `B` gains a static field. Field resolution searches superinterfaces before the superclass, so `putstatic B.m` now hits a final interface field and gets `IllegalAccessError`.

`fieldBecomesFinal` and `putstaticBecomesFinal` may be further false negatives if MiMa has no final-field rule.

### S — Scala (`Scala/`)

- [x] **S1. Lowering for Scala 2.12+** to `Jvm.World` (`Scala/Lower.lean`), as a `Task` over other definitions' interfaces, with `lower_congr` (T1 for lowering):
  - classes;
  - traits: default methods, `$init$`, static `m$` impl methods, trait fields (abstract getter and setter);
  - mixin forwarders (2.12 and 2.13 agree on the space: forwarders for every concrete trait method the class mixes in itself);
  - objects: `MODULE$`, static forwarders on the companion or mirror class;
  - bridges;
  - value classes: extension methods, erased signatures.
- [x] **S2. Scala 3 deltas.** Trait initialisers including F6 (separate compilation), `@static`, extension methods, `Serializable` objects. Enums and `inline`: TODO.
- [x] **S3. Calibrate against scalac's own classfiles** (`probes/scala/probe.py`). Agreement below.
- [ ] **S4. Shared `AsSeenFrom` and linearization,** one model used by the TCK and later by `Zinc/Hier`. `Scala.lin` and `Scala.lookup` are a start.
- [x] **Source-level edit catalogue** (`Scala/Catalogue.lean`), the bridge to B3.

#### S design

**Source.** A typed, already-resolved AST, since lowering runs after the typer: top-level definitions (class, abstract class, final class, trait, object, value class) with a superclass, mixed-in traits, at most one type parameter and parents applied to type arguments. Members are `def`s with parameters and a result type, abstract or concrete, `final` or not, and `val`s in traits and classes. Types are `Int`, `Unit`, `String`, `Object`, the type parameter, and other definitions by name. A class and its companion object are one unit, as in a source file. Bodies are opaque: lowering only needs to know a member is concrete.

**Lowering is a `Task`.** Its queries are other definitions' interfaces (`decl d`: kind, parents, members with signatures; no bodies), which is what scalac reads from pickles or TASTy. Lowering a unit asks for its own declaration, its ancestors' (linearization, mixin forwarders, bridges, which parent is a trait), each value class it mentions in a signature (erasure), and its companion (static forwarders). Its output is a list of classfiles: the `Jvm.Classfile` the JVM links against, plus what `Jvm` does not model yet (fields, access, `ACC_BRIDGE`, and for synthesized methods the invoke instructions of their bodies: a forwarder's `invokestatic T.m$`, a constructor's `T.$init$` calls). So a unit's lowering has a trace, and T1 says an edit to a definition outside that trace leaves its classfiles unchanged. That is the hook to `NCompiler` and to B4.

**Scala 2.12, 2.13 and 3 are one parameter,** `Dialect`, read only where the compilers differ. The differences are found by the calibration probe, not assumed.

**Calibration (S3).** A Lean exe enumerates a bounded space of programs, prints each as Scala source and as the model's classfiles. A script compiles them with scalac 2.12, 2.13 and 3 (one package per program, one compiler run per dialect, two runs for the separate-compilation cases), parses the classfiles directly (header, fields, methods with access and flags, and the invokes in synthesized methods), and diffs. Enumeration here is testing, per `DESIGN-spec.md`.

**Out of scope** for S1–S3: method bodies and their call sites in user code, overloading, nested and local classes, inner-class attributes and generic `Signature` attributes, how a class implements a `lazy val`, `var`, `private[this]` and qualified access, specialization, case classes (catalogue only), Java-defined parents, Scala 3 `inline`, opaque types and given instances. Type checking is limited to what the space needs to stay well-typed (abstract members implemented, conflicting inherited members overridden).


#### S4 design

**Problem.** Three copies of "a member's type as seen from a prefix" exist: the TCK's (`scala-type-system-tck/lean/AsSeenFrom`: this-types along owner chains, against IntelliJ's substitutor chain), `Zinc/Hier.lean` and `Zinc/Erasure.lean` (type arguments along parents, private toys), and `Scala/Lower.lean` (an ad hoc `Ty.subst` in `lin`). They answer one question and can't be compared.

**One map, generic in the type language.** `Scala/AsSeenFrom.lean` defines scalac's `asSeenFrom(pre, clazz)` once, over any type language with substitutable *leaves*: this-types `D.this` and class type parameters `D#i`, each anchored at a class given as its owner path. A type language provides `leaf`, `bind` (substitute every leaf) and `leaves`, with the monad laws; `asf pre c t` is `bind t` of the anchored walk (`thisTypeAsSeen` and `classParameterAsSeen` are one walk with two outcomes). The environment is the TCK's `World` plus `bargs` (a base type's arguments). The composition law and "a chain is one `asSeenFrom`" are proved once, from lockstep (the map commutes with `bpre`, `hasBase`, `bargs`). The file imports only Lean core, so a project without Mathlib can use it.

**Consumers.**
- `Scala/Lower.lean`: base types along the linearization become `asf` of the parent's arguments (scalac's `baseType`), and bridges pair an override with an overridden member only when their types match as seen from the class (`memberType`). The probe must still agree with scalac.
- The TCK: its `Ty` is an instance (this-leaves only, no class parameters), and its `Scalac.asf` is proved equal to the shared map, so its `Chain` theorems follow from the shared ones. How the TCK depends on the file (vendored copy, or a Mathlib-free lake package in this repo that it `require`s by `subDir`) is a decision for Jason, prototyped below.
- `Zinc/Hier` and `Zinc/Erasure`: not touched (other sessions own `Zinc/`); they can move to the shared map in the later single-writer port.

**Out of scope:** existential capture of unstable prefixes, refinement classes, `baseType` itself (an input, as in the TCK).

#### S status

**Calibration.** `python3 probes/scala/probe.py OUT` (about a minute). Every program agrees with scalac on header, fields, methods with their flags, and the invokes of synthesized bodies:

| scalac | programs | of which |
|---|---|---|
| 2.12.21 | 1320/1320 | mixin 1280, generic 24, value class 4, trait companion 2, misc 4, `$init$` joint 3 and separate 3 |
| 2.13.18 | 1320/1320 | the same |
| 3.9.0 | 1326/1326 | the same, plus `@static` and extension methods 4, `$init$` of a trait with an extension method, joint and separate |

The model started from the textbook rules; the probe corrected it in these places, each now a rule in `Lower.lean`:

- **Interfaces are minimised.** A direct trait parent that another direct parent already extends is not in the classfile's interface list (`class C extends B with T with U`, `U extends T`: `implements U`). All three versions.
- **`$init$` is not universal.** Scala 2 omits it for a trait with no concrete member, and a subclass's constructor calls only the `$init$`s that exist. Scala 3 emits it only for a trait with initialisers (a concrete `val`); see F6 below.
- **Objects changed in 2.13.** 2.12: instance fields, a non-final `MODULE$`, `$init$` calls in the constructor, trait-field implementations `final`. 2.13 and 3: static fields, `final MODULE$`, `$init$` calls in `<clinit>`, trait-field implementations not final.
- **Static forwarders include inherited members,** not only the methods in the module class (an object extending a class gets forwarders for the class's methods).
- **Scala 3 forwards more:** trait setters (Scala 2 skips them), and a bridge when the first member of that erased signature along the linearization is concrete. So `object O extends B with T` with an overriding `m(): String` gets a static `m()Object` forwarder when `B.m(): Object` is concrete and `T` does not declare `m`, but not when an abstract `T.m(): Object` comes first.
- **Scala 3 objects** implement `java.io.Serializable` and have a private `writeReplace`; an object implementing a `lazy val` has a private `<clinit>`.
- **Trait setter names carry the trait's full name,** with the package mangled: `p1$T$_setter_$v_$eq`. The model omits packages; the probe strips them.
- A mixin forwarder for a `final` trait method is `final`. A Scala 3 `@static val` becomes a public static final field of the companion class, initialised in a private `<clinit>`, with no accessor.

**F6, extended.** A Scala 3 trait whose only initialisers are a `lazy val`, *or which has any extension method* (even an abstract one), has an `$init$`. A subclass compiled in the same run calls it; one compiled against the trait's TASTy does not (the TASTy says `NoInits`). The extension-method case is new; it is likely the more common one (syntax traits for type classes). In the model, lowering depends on `View.inRun`, so this is a compositionality failure (review finding 3), witnessed by kernel `decide` in `Scala/Facts.lean`; the probe confirms both runs.

**Catalogue.** Seven source edits, each linked before, after (old client classfiles, new library) and fresh (client recompiled), by kernel `decide`. Two show the gaps between Zinc and binary compatibility:
- `traitOverrideAdded`: a trait gains a concrete override of a method the client's superclass has. The old client has no forwarder, so the JVM selects the superclass's method; a fresh build runs the trait's. Links either way, MiMa has nothing to say, Zinc must recompile. Confirmed on HotSpot with 2.13.18 (prints 1, fresh prints 2).
- `widenedToValueClass`: `V` becomes a value class, and `W`'s classfile changes although `W`'s source did not; `W`'s lowering trace contains `V`.

`valAddedToTrait` fails earlier on HotSpot than in the model: `new Y` already throws `AbstractMethodError`, since `$init$` calls the missing setter. The model needs static interface methods (J3) to see that.

**TODO (future work)**
- Enums. Observed (3.9.0): `enum Color { case Red, Green }` is an abstract class implementing `scala.reflect.Enum` with forwarders for `scala.Product`'s methods and static `values`/`valueOf`/`fromOrdinal`; the cases are public static final fields of `Color$` without accessors or static forwarders; simple cases are instances of one anonymous class. Needs library traits (`Product`, `Mirror`) in the environment.
- Case classes, constructor parameters (and `Jvm` constructor sites), default getters, `lazy val` implementation in classes, `var`, overloading, nested classes, Java-defined parents.
- Check the catalogue against MiMa and HotSpot for every case (B3), and add a client-space enumeration over source edits.
- Lowering as an `NCompiler` instance, for B4; after the framework merge (review finding 1).
- S4.

### V — Java (`Java/`), deferred

Not launched yet. Java name resolution, sealed hierarchies and compile order are already Phases 12 and 14 (`PLAN-java.md`, `PLAN-order.md`). Lowering javac's output to `Jvm.World` comes after J and S, and reuses those phases' probes.

- **V1. Lowering for a javac subset:**
  - classes and interfaces;
  - default, static and private interface methods;
  - bridges for generics and covariant returns;
  - `static final` constants (folded, ConstantValue);
  - enums, records, sealed / `permits`.
- **V2. JLS ch. 13 as checked statements against `Jvm` linkage.** One example per rule. The theorem `compatible_of_footprint` applies where it can.
- **V3. Calibrate against javac.**

### B — Binary compatibility (`BinCompat/`, plus a scala-cli harness outside Lean)

- **B1. MiMa against the catalogue, at the JVM level.** MiMa reads classfiles, so J1's rendered jars are enough to start; it needs no front end. Per case, compare MiMa's problems with the model's verdict.
- **B2. MiMa as a bridge design, in `DESIGN-spec.md`'s terms.** MiMa compares a set of facts per library class; those facts are its keys. Its check is sound if every linkage query any client can ask is covered by a compared key (coverage), and if equal facts give equal answers (abstraction). Prove this for a corrected rule set; for MiMa's actual rules, give a counterexample trace for each gap. Then check it on a space, as `FlatRules` checked the PoC's rules, to measure false negatives and false positives. `defaultConflict` is a candidate false negative to confirm.
- **B3. Source-level spaces.** Once S1 and V1 exist: Scala and Java edits, lowered, linked, and checked against MiMa and HotSpot.
- **B4. The Zinc ⇒ binary-compatible theorem above,** stated over `NCompiler`. It needs S1 or V1 to be a compiler instance.

### Later, single writer, after talks#21 merges

- Move `Task` to `Core`. Port `Erasure`, `Flat` and `Inline` off their private toys onto `Scala`/`Java` lowering, so Zinc becomes one consumer among several.
- The contributor-facing repo (see the separate proposal).

## Order and dependencies

```
J1 ──► B1 ──► B2
J2 ──┘
S1 ──► S3, S4 ──► B3, B4
V1 ──► V2, V3 ──► B3
```

J, S and V can start at once; they share only the `Jvm` types. B1 can start as soon as J1 has rendered jars. The first milestone is B1 + B2 on the 12 catalogue cases: MiMa checked against a JVM model, with every disagreement explained.

## Done so far

- `Jvm/Link.lean`:
  - resolution (§5.4.3.3, §5.4.3.4) and selection (§5.4.6) as a `Task` over the class table;
  - loading checks;
  - `link_congr` (T1 for linkage), `Compatible`, `compatible_of_footprint`.
- `Jvm/Catalogue.lean`: 35 edits, each with MiMa's expected problem name, checked before and after by kernel `decide` and on HotSpot (§J).
- `Jvm/Clients.lean`: the J2 verdicts over two client spaces, checked on HotSpot (§J).
