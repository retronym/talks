# Track V — the Java layer (`Java/`)

## Problem

Java name resolution, sealed hierarchies and compile order are already Phases 12 and 14 (`PLAN-java.md`, `PLAN-order.md`), but nothing said what javac emits. Binary compatibility in Java is mostly JLS chapter 13, written as prose; with a Java front end lowering to `Jvm.World` (Track J), each of its rules becomes a checked statement, and Track B gets Java library edits to judge MiMa on. Java-defined libraries are also where MiMa's protected-member gap (MiMa-P1) bites.

## What was built

**Source.** A typed, already-attributed subset, since javac's back end (`Lower`, `TransTypes`, `Gen`) runs after attribution: top-level types in one package, each a class (abstract, final, sealed, non-sealed), an interface, an enum or a record; at most one type parameter; methods (abstract, concrete, static, final, default and private in interfaces, narrowed results), fields (instance, static, `static final` constants over literals and other types' constants), enum constants and record components. Bodies are opaque except for the constants they read and whether a field's initialiser is a constant expression.

**Lowering is a `Task` over other types' interfaces** (`Java/Lower.lean`), as `Scala/Lower.lean` is: it asks for the declarations of its supertypes (bridges, enum and record supertypes) and of every type whose constant it reads, which is what javac reads from other classfiles' `ConstantValue` attributes. The output is `Java.ClassOut`, a `Jvm.Classfile` plus `ConstantValue`, `ACC_BRIDGE`/`ACC_SYNTHETIC`/`ACC_ENUM`, `PermittedSubclasses`, `Record`, and the invokes of synthesised bodies. `lower_congr` is T1 for it. In particular a client's classfile depends on the *values* of the constants it reads, so a constant edit changes the client's classfile although no signature changed (JLS §13.4.9).

**javac's release** was to be a parameter, read where the probe found a difference. It found none, so lowering does not take one.

Steps:
- Track V1: lowering for the subset. Done.
- Track V2: JLS chapter 13 as checked statements against `Jvm` linkage (`Java/Jls13.lean`, over `Java/Catalogue.lean`). Done.
- Track V3: calibration against javac (`probes/java/probe.py`, `Java/Space.lean`). Done.

## Results

**Calibration.** 99 programs in six families, compiled by javac 17.0.20, 21.0.12 and 25.0.4 (Temurin, `--release` matching). Compared: class flags, superclass, interfaces, `PermittedSubclasses`, `Record`; fields' access, flags and `ConstantValue`; methods' access and flags; per method the `getstatic`s and invokes on non-`java/` classes and the `int` and `String` constants pushed (where folded constants show up).

| family | programs | agree (17 / 21 / 25) |
|---|---|---|
| interfaces: abstract, default, static, private methods, a constant | 32 | 32 / 32 / 32 |
| bridges: class or interface supertype, generic or not, narrowed result, substituted parameter, a third level | 30 | 30 / 30 / 30 |
| constants: literal, `1 << 3`, string concatenation, non-constant; through an interface; folded into a client | 8 | 8 / 8 / 8 |
| enums: 0–2 constants, an interface, a constant | 12 | 12 / 12 / 12 |
| records: 0–2 components, an interface the accessor implements | 5 | 5 / 5 / 5 |
| sealed: interface or abstract class, `permits` explicit or inferred, final, non-sealed, record and sealed subtypes | 12 | 12 / 12 / 12 |

The three javacs agree on everything compared. What the probe and hand-compiled samples corrected:
- The implicit canonical constructor of a package-private record takes the record's access (JLS §8.10.4); the model had it public.
- An interface that narrows a generic interface method gets a *default* bridge.
- An enum gets a private static synthetic `$values()` called from `<clinit>`, and a private `(String, int)` constructor.
- A record's `toString`/`hashCode`/`equals` are `final` and `invokedynamic` to `ObjectMethods`.
- An interface constant whose initialiser reads a non-constant gives the interface a `<clinit>`.

**JLS chapter 13** (`Java/Jls13.lean`, 20 examples over the 17 cases of `Java/Catalogue.lean`, by kernel `decide`):
- **Constants (§13.1, §13.4.9).** A changed constant links before and after, by `compatible_of_footprint` (the client never touches `A`), yet the client's classfile changes and its lowering trace has `decl A`, also through an interface constant that folds `A.K`. A deleted constant still links (the client has its copy) and no longer compiles; a deleted non-constant field gives `NoSuchFieldError`.
- **Generics (§13.4.15).** Removing a narrowing override breaks a call through the subclass but not one through the superclass (it selected the bridge, now the inherited method); adding one moves selection to the new bridge.
- **Interfaces (§13.5.3, §13.5.6).** An abstract method added gives `AbstractMethodError`; a default added links; a private one is compatible by footprint.
- **Enums (§13.4.26) and records (§13.4.27).** Adding a constant or component is compatible by footprint; removing one gives `NoSuchFieldError` / `NoSuchMethodError`. A component added breaks `new R(1)` compiled before it (`recordComponentAddedNew`), while the old accessors still link.
- **Sealed.** Making a class `sealed` without permitting an existing subclass gives `IncompatibleClassChangeError` at load (`classBecomesSealed`).

The last two needed `PermittedSubclasses` and `Site.construct` in `Jvm`, added by Track J5.

## Not covered

Nested, local and anonymous classes (so no nestmates; Track J3's open item), overloading beyond bridges, varargs, annotations, `Signature` and `InnerClasses`, lambdas, switch on enums or patterns, `module-info`. Not compared by the probe: the rest of the bytecode, `MethodParameters`, `invokedynamic` bootstrap arguments. Java catalogue cases are not yet run through MiMa (Track B3, `ROADMAP.md`).

## PRs

- retronym/talks#60: lowering, javac calibration and JLS chapter 13 (Tracks V1–V3).
- retronym/talks#63: sealed classes and constructor sites in `Jvm`, and the Java cases that use them.
