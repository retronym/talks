# Track S — the Scala layer (`Scala/`)

## Problem

Each Zinc feature file has its own toy Scala, sized to what Zinc hashes, and none of them says what classfiles scalac actually emits. Binary compatibility (Track B) needs exactly that: a library edit in Scala source, lowered to classfiles, linked by `Jvm`. And three copies of "a member's type as seen from a prefix" (the TCK's, `Zinc/Hier`/`Zinc/Erasure`, and lowering's own substitution) answered one question in three incomparable ways.

## What was built

**Lowering is a `Task`** (`Scala/Lower.lean`). Its queries are other definitions' interfaces (`decl d`: kind, parents, members with signatures, no bodies), which is what scalac reads from pickles or TASTy. Lowering a unit asks for its own declaration, its ancestors' (linearization, mixin forwarders, bridges), each value class in a signature (erasure) and its companion (static forwarders). Its output is `ClassOut`: a `Jvm.Classfile` plus what `Jvm` does not model (fields' flags, `ACC_BRIDGE`, `InnerClasses`, the invokes of synthesized bodies). So lowering has a trace, and `lower_congr` is T1 for it: an edit outside a unit's trace leaves its classfiles unchanged. That is the hook to `XCompiler` and Track B4.

**Scala 2.12, 2.13 and 3 are one parameter,** `Dialect`, read only where the probe found the compilers differ.

**Calibration is by probe, not by reading the spec.** A Lean exe enumerates a bounded space, prints each program as Scala source and as the model's classfiles; `probes/scala/probe.py` compiles them with each scalac (one run per dialect, two for separate-compilation cases), parses the classfiles and diffs. Enumeration is testing, per `DESIGN-spec.md`.

Steps:
- Track S1: lowering for Scala 2.12+: classes, traits (defaults, `$init$`, static `m$`, trait fields), mixin forwarders, objects (`MODULE$`, static forwarders), bridges, value classes.
- Track S2: Scala 3 deltas: trait initialisers under separate compilation (F6), `@static`, extension methods, `Serializable` objects.
- Track S3: the calibration probe.
- Track S4: one `asSeenFrom`, shared with the TCK (`Scala/AsSeenFrom.lean`).
- Track S5: membership and overriding as refchecks (`Scala/Members.lean`).
- Track S6: case classes, enums, inline and opaque, nested classes, by desugaring (`Scala/Desugar.lean`).
- A source-level edit catalogue (`Scala/Catalogue.lean`), the input to Track B3.

All done.

## Results

### Lowering (Tracks S1–S3)

The probe agrees with scalac on header, fields, methods with flags, `InnerClasses`, and the invokes of synthesized bodies, on every program: 1348/1348 on 2.12.21 and 2.13.18, 1363/1363 on 3.9.0. Families: mixin 1280, generic 24, `asf` 10, value class 4, trait companion 2, `$init$` joint and separate 3+3, misc 4; on Scala 3 also `@static` and extension methods; and the Track S6 families below.

The model started from the textbook rules. The probe corrected it here, each now a rule in `Lower.lean`:
- **Interfaces are minimised.** A direct trait parent that another direct parent already extends is not in the interface list. All three versions.
- **`$init$` is not universal.** Scala 2 omits it for a trait with no concrete member; Scala 3 emits it only for a trait with initialisers.
- **Objects changed in 2.13.** 2.12: instance fields, non-final `MODULE$`, `$init$` calls in the constructor, trait-field implementations `final`. 2.13 and 3: static fields, `final MODULE$`, `$init$` calls in `<clinit>`, trait-field implementations not final.
- **Static forwarders include inherited members.**
- **Scala 3 forwards more:** trait setters, and a bridge when the first member of that erased signature along the linearization is concrete.
- **Scala 3 objects** are `Serializable` with a private `writeReplace`; an object implementing a `lazy val` has a private `<clinit>`.
- **Trait setter names carry the trait's full name,** package mangled: `p1$T$_setter_$v_$eq`.
- A mixin forwarder for a `final` trait method is `final`. A Scala 3 `@static val` is a public static final field of the companion class, with no accessor.

**F6, extended.** A Scala 3 trait whose only initialiser is a `lazy val`, *or which has any extension method*, has an `$init$`. A subclass compiled in the same run calls it; one compiled against the trait's TASTy does not (the TASTy says `NoInits`). The extension-method case is new and likely the common one (syntax traits for type classes). In the model lowering depends on `View.inRun`, a compositionality failure witnessed by kernel `decide` in `Scala/Facts.lean` (`ctorInits`); the probe confirms both runs. Track B4 shows what it costs and that retronym/scala3#10 fixes it.

### One `asSeenFrom` (Track S4)

`Scala/AsSeenFrom.lean` defines scalac's `asSeenFrom(pre, clazz)` once, generic in the type language: any language with substitutable leaves (this-types and class type parameters, anchored at their owner) and a lawful `bind`. `leafAsSeen` is the walk; `asf` is `bind` of it. `compose` and `chain_is_single` are proved once, from lockstep. It imports only Lean core, so a Mathlib-free project can use it.

Consumers:
- **Lowering.** `lin` computes each base type's arguments as `asSeenFrom(C.this, P)` (scalac's `baseType`), replacing an ad hoc substitution; members are grouped by `memberType` (`sigGroups`), and bridges and forwarders work per group. The new `asf` probe family found two corrections: a bridge to an override at a value class unboxes and boxes, and an overload next to an inherited generic method is not an override (name-only lookup had dropped a mixin forwarder).
- **The TCK.** On retronym/scala-type-system-tck branch `claude/shared-asf`, `lean/AsSeenFrom/Shared.lean` is a vendored copy, and `Port.lean` makes the TCK's `Ty` an instance and proves its `Scalac.asf` *is* the shared map (`asf_eq` in that file). `Chain.compose` now follows from the shared `compose`; the other TCK results build unchanged.
- **`Zinc/Hier`, `Zinc/Erasure`:** not yet; see `ROADMAP.md`.

### Membership and overriding (Track S5)

`Scala/Members.lean` is refchecks as a `Task` over interfaces, on the shared `asSeenFrom`: for a class, either the errors scalac or dotc reports, or per signature the member a selection runs. Calibrated by `probes/scala/members.py` on 4704 hierarchies (`T`, `U`, `B`, `C`, each declaring `m` one of eleven ways), **rejected programs included**: errors are compared per class and kind, and for accepted programs a `main` checks which owner's `m` runs.

| compiler | agree | accepted |
|---|---|---|
| 2.12.21 | 4700/4704 | 772 |
| 2.13.18 | 4700/4704 | 772 |
| 3.9.0 | 4704/4704 | 672 |

The rules the probe forced, beyond the textbook:
- **One error per member,** in the order access, `final`, missing `override`, accidental override, `def` over `val`, lazy against strict, result type.
- **Which pairs.** A pair a parent has was checked there; **2.13 checks it again** in each subclass (2.12 and 3 don't).
- **Private.** A private member isn't inherited and implements nothing. Scala 2 stops at it; Scala 3 also checks the inherited member it fails to hide. `override private` is a refchecks error in Scala 2 and an earlier-phase error in Scala 3, which hides every other program's refchecks errors, so the probe recompiles in rounds.
- **Accidental override needs a real override;** otherwise it is "inherits conflicting members".
- **Re-abstraction.** An abstract member of a *class* re-abstracts the concrete one it extends; one in a *trait* does not. Scala 3 forms a pair there; Scala 2 doesn't.

**A scalac 2 bug, found by the runtime check** (the 4 disagreements). `trait T { val m = "T" }; abstract class B extends T { def m: String }; class C extends B with T { override val m = "C" }` compiles with 2.12.21 and 2.13.18, and `new C` throws `AbstractMethodError`: `T.$init$` calls the trait setter, which `C` does not implement. Scala 3 runs it. Nearest report: scala/bug#12456. Not yet filed (`ROADMAP.md`).

**Java's rules (JLS 8.4.8), the spec Track V diffs against:**
- **Order.** No linearization: a class method always beats an interface default; among interfaces the maximally specific default wins, and two unrelated defaults are an error unless the class declares the method.
- **Same member** by subsignature (a raw method overrides a generic one); same erasure without override is a clash. Scala matches by `memberType` and uses erasure only for bridges.
- **No `override` keyword**, so no "needs `override`", "conflicting members" or third-member rule.
- **Access and statics.** A package-private method is not overridden from another package, and the JVM's selection agrees (Track J3). Statics hide, they don't override.
- **Re-abstraction** is allowed in both; Java also checks `throws`.

### Case classes, enums, inline and opaque, nested classes (Track S6)

**Desugaring plus a library prelude, not new lowering rules.** Each feature is a desugaring into the existing AST. What the compiler inherits from the library (`Product`, `Equals`, `AbstractFunctionN`, `Mirror`, `scala.reflect.Enum`) enters as declarations in a prelude, read through `Q.decl` like any parent. The calibrated forwarder and bridge rules do the rest, so the probe tests the desugaring and the prelude together.

| family | 2.12.21 | 2.13.18 | 3.9.0 |
|---|---|---|---|
| `case` | 14/14 | 14/14 | 14/14 |
| `nest` | 3/3 | 3/3 | 3/3 |
| `sealed` | 1/1 | 1/1 | 1/1 |
| `enum` | | | 4/4 |
| `inline` (and opaque) | | | 5/5 |

What the probe corrected:
- **Case classes.** Synthesized `copy`, `toString`, `hashCode`, `equals`, `canEqual` are skipped when a *superclass* defines one concretely (a trait's doesn't count); `productPrefix` is always synthesized. With a superclass's `copy`, Scala 3 keeps `copy$default$N`, Scala 2 drops it. Only a synthesized companion extends `AbstractFunctionN` and overrides `toString`. Serializable objects get `readResolve` in 2.12, `writeReplace` in 2.13; Scala 3 makes every object `Serializable`.
- **Nesting.** A nested object gets no mirror class; its module class has a public constructor, final only in Scala 3, where the enclosing module class also gets a static field for it. `InnerClasses` names the mirror or companion as outer; a nested class and its companion list each other.
- **Enums.** `values`, `valueOf`, `$values` exist only when every case is a singleton; `$new` is private with no static forwarder.
- **Inline.** An `inline def` is in the classfile only when it implements or overrides a member.

### The source-level catalogue

`Scala/Catalogue.lean`: library edits in Scala source, each lowered and linked `before`, `after` (old client classfiles, new library) and `fresh` (client recompiled) by kernel `decide`. Two show the gaps between Zinc and binary compatibility:
- `traitOverrideAdded`: the old client has no forwarder, so the JVM selects the superclass's method; a fresh build runs the trait's. Links either way, MiMa is silent, Zinc must recompile. Confirmed on HotSpot with 2.13.18.
- `widenedToValueClass`: `W`'s classfile changes although `W`'s source did not, because its lowering trace contains `V`.

And from Track S6: `caseFieldAdded` (accessor links; constructor, `apply`, `copy` don't), `nestedClassMoved` (`NoClassDefFoundError`), `enumCaseAdded` (links), `enumCaseRemoved` (`NoSuchFieldError`), and `inlineBodyChanged`: the library's classfiles are *equal* before and after while every client holds the old body. Binary compatibility can't see it; Phase 11's `InlineOpaqueSpec` gives Zinc the keys for it.

`valAddedToTrait` fails earlier on HotSpot than in the model: `new Y` already throws `AbstractMethodError`, since `$init$` calls the missing setter. The catalogue leaves out sites through `invokestatic T.m$` and `T.$init$`.

## Out of scope

Method bodies and call sites in user code; overloading in general; generic `Signature` attributes; `lazy val` and `var` implementation in classes; `private[this]` and qualified access; specialization; Java-defined parents; given instances; case classes with type parameters, several parameter lists or private constructors; enums with type parameters; local classes; macros. The open items are in `ROADMAP.md`.

## PRs

- retronym/talks#39: lowering, calibration against 2.12/2.13/3 (Tracks S1–S3) and the catalogue.
- retronym/talks#56: the shared `asSeenFrom` (Track S4).
- retronym/talks#58: membership and overriding (Track S5).
- retronym/talks#65: case classes, enums, inline and opaque, nested classes (Track S6).
