# Track J — JVM linkage (`Jvm/`)

## Problem

Zinc asks whether a client must be *recompiled*; binary compatibility asks whether its old classfile still *links*, and runs the same code, against an edited library. Both are questions about a task's trace against an edited environment. The Zinc toys model erasure and forwarders inside each feature file, but nothing modelled linkage itself, so there was no ground truth to check MiMa against (Track B) and nothing for the Scala and Java front ends (Tracks S and V) to lower to.

## What was built

- **`Jvm/Link.lean`.** Linking as a `Task` over the class table: loading checks, resolution (JVMS §5.4.3.2–4), selection (§5.4.6) and access (§5.4.4, plus the verifier's receiver, `invokespecial` and protected rules). Its trace is the client's *linkage footprint*, so T1 applies unchanged: `link_congr`. `Compatible` and `compatible_of_footprint` state binary compatibility and prove it where the edit misses the footprint.
- **The contract.** `Jvm.World` (classfiles), `Jvm.Program` (what a client loads and executes) and `Jvm.Site`. Front ends produce a `World`; consumers read one. These types were changed only additively.
- **Sites as javac emits them.** `C c = new R(); c.m()` is `new R; invokespecial R.<init>; invokevirtual C.m`, so the verifier's upcast check, instantiation and load-on-reference are part of `Site` semantics. `Site.construct c n d` is `new c(…)`.
- **`Jvm/Catalogue.lean`.** 45 library edits, each with MiMa's expected problem, linked before and after by kernel `decide`.
- **`Jvm/Clients.lean`.** `breaksSomeClient k`: some client in a bounded space links on `v0` and fails on `v1`. `changesSomeClient k`: some client links on both and runs a different method (the first form of "links, but runs different code"). Clients must be well-typed against `v0`. Three spaces: `space` (15,652 programs; an optional client class `X` and one call site of any kind), `space3` (44,144; adds fields, `invokespecial`, interface statics, sites inside `X`), `space5` (14,256; constructors and `new`).
- **The HotSpot probe.** `lake exe jvmcases` dumps the catalogue and spaces as JSON lines; `probes/jvm` renders each case's `v0`, `v1` and client with the Classfile API (version 65), runs the client against both, and compares the `Throwable` and the method that ran. `OUT=dir` keeps the classfiles for MiMa.
- **No `native_decide`** (review finding 7). Catalogue witnesses use `decide`; client-space verdicts use `decide +kernel`, since the elaborator's `decide` hits its recursion limit.

Steps:
- Track J1: calibrate the catalogue on HotSpot. Done.
- Track J2: client spaces and verdicts. Done.
- Track J3: fields, `invokespecial`, private methods, static and private interface methods, access control, the protected check. Done, except nestmates and the smaller items in `ROADMAP.md`.
- Track J5: sealed classes (`PermittedSubclasses`) and constructor calls. Done.
- Track J4: behaviour (constants, method bodies). Open, see `ROADMAP.md`.

## Results

**Calibration.** On Temurin 21.0.12, 25.0.4 and 27, the probe agrees with the model on every catalogue case and on every program of `space`, `space3` and `space5` (58,400 programs in the full run), apart from two known HotSpot bugs on JDK 21, below.

**`LinkError` to the JVM's exceptions**, the same on all three JDKs: `noClassDef` → `NoClassDefFoundError`, `incompatibleClassChange` → `IncompatibleClassChangeError`, `noSuchMethod` → `NoSuchMethodError`, `noSuchField` → `NoSuchFieldError`, `abstractMethod` → `AbstractMethodError`, `instantiation` → `InstantiationError`, `illegalAccess` → `IllegalAccessError`, `verify` → `VerifyError`. `finalSuper` and `finalOverride` are `IncompatibleClassChangeError`, not `VerifyError`.

**What calibration added to the model.** Each of these was a disagreement first, and is now a rule:
- Loading a class checks that its superclass and superinterfaces are accessible (`IllegalAccessError`).
- The verifier's `invokespecial` rule turns on whether the referenced class is an interface, not on the constant's tag. An `InterfaceMethodref` to a class passes the verifier and fails resolution with ICCE; a reference to an interface that is not a direct superinterface is a `VerifyError`.
- The protected-receiver check (§4.10.1.8), predicted by `methodBecomesProtectedOther`.
- `PermittedSubclasses` (JVMS §5.3.5) is checked after the final-superclass check and before the access check, as HotSpot's class file parser does: the class must be listed and, unless public, in the sealed type's run-time package.
- A constructor resolves like any method, walking superclasses with an access check, but HotSpot then requires it to be declared by `c` itself, so an inherited match is `noSuchMethod` (`ctorPulledUp`).

**Known JDK bugs hit by the probe**, both fixed in JDK 25. The model follows the JVMS; the probe reports the JDK 21 results as known deviations.
- [JDK-8356942](https://bugs.openjdk.org/browse/JDK-8356942): `invokeinterface` on a receiver with two maximally-specific defaults throws `AbstractMethodError` instead of ICCE (`defaultConflict`). Regressed in JDK 10.
- [JDK-8350029](https://bugs.openjdk.org/browse/JDK-8350029): JDK 21's `invokespecial` verification checks the constant's tag, so it gives `VerifyError` where 25 gives ICCE, and the reverse. 56 programs of `space3` and 4 of `space5`, all in forms javac never emits.

**The catalogue on HotSpot.** "MiMa" is the first problem MiMa 1.2.1 reports (Track B). "HotSpot" is the result on `v1`; "same" means it links and runs the method the model predicts. Breaks and changes are counts over the clients that link on `v0`.

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
| `defaultRemoved` | DirectAbstractMethodProblem | `abstractMethod` | `AbstractMethodError` | yes (4/15) | no |
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
| `superCallAbstract` | AbstractClassProblem | `abstractMethod` | `AbstractMethodError` | yes (25/41) | no |
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
| `classBecomesSealed` | — | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (15/32) | no |
| `classBecomesSealedPermitting` | — | links | same | no | no |
| `ifaceBecomesSealed` | — | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (7/14) | no |
| `sealedPermitsNonPublicElsewhere` | — | `incompatibleClassChange` | `IncompatibleClassChangeError` | no (0/32) | no |
| `sealedPermitsPublicElsewhere` | — | links | same | no | no |
| `ctorRemoved` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (9/41) | no |
| `ctorBecomesPrivate` | DirectMissingMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (9/41) | no |
| `ctorBecomesPackagePrivate` | InaccessibleMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (9/41) | no |
| `ctorPulledUp` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (13/86) | no |
| `ctorClassBecomesAbstract` | AbstractClassProblem | `instantiation` | `InstantiationError` | yes (27/41) | no |

MiMa 1.2.1 is silent on five cases that break some client: `defaultConflict`, `overrideBecomesPrivate`, `fieldIfaceBeforeSuper`, `fieldBecomesFinal` and `putstaticBecomesFinal`. Track B explains each as a gap.

## Not modelled

Nestmates (private access is same-class only); method bodies, so a library method's own calls and constants folded into the client (Track J4); `Object`'s methods in interface resolution; transitive overriding through an intermediate package-private method (§5.4.5); clients in the library's package; spaces over two client classes; protected constructors and constructor chaining between library classes; signature-polymorphic methods, loader constraints, class initialisation, modules. The open ones are in `ROADMAP.md`.

## PRs

- retronym/talks#50: HotSpot calibration, client spaces, fields, access and `invokespecial` (Tracks J1–J3).
- retronym/talks#63: sealed classes and constructor call sites (Track J5).
