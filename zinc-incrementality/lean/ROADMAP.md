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

Each track owns one directory and one `lean_lib`, works on its own branch off `claude/bincompat-lean`, and edits only its own section of this file. Tracks never edit `Zinc/` (talks#21 is open on it). Integration happens on `claude/bincompat-lean`.

### J — JVM (`Jvm/`)

- **J1. Calibrate the catalogue on HotSpot.** Render each `Catalogue` case to classfiles (Classfile API on JDK 24+, or ASM) for `v0`, `v1` and the client. Run the client against `v1` and record the `Throwable`'s class. Map `LinkError` to JVM classes. In particular: is `finalSuper` a `VerifyError` or an `IncompatibleClassChangeError` on JDK 21 and 25?
- **J2. Client spaces.** Enumerate the bounded clients a library edit could break, to answer "∃ a client that links on `v0` and fails on `v1`". This is the model's verdict for a MiMa problem.
- **J3. More linkage.**
  - fields (`get`/`put`, static ↔ instance);
  - `invokespecial`, private methods and nestmates;
  - static and private interface methods;
  - `Object`'s methods in interface resolution;
  - access control, especially package-private across packages and `protected`.
- **J4. Behaviour.** Constants folded into the client, and which method runs. This makes "links, but runs different code" a first-class verdict (`overrideAdded`, `pulledUp`, constants).

### S — Scala (`Scala/`)

- **S1. Lowering for Scala 2.12+** to `Jvm.World`:
  - classes;
  - traits: default methods, `$init$`, static `m$` impl methods;
  - mixin forwarders, under the 2.12 vs 2.13 forwarder rules;
  - objects: `MODULE$` and static forwarders;
  - bridges;
  - value classes: extension methods, erased signatures.
- **S2. Scala 3 deltas.** Trait initialisers, which ties into F6 in talks#21. Also `@static`, enums, `inline`, and extension methods.
- **S3. Calibrate against scalac's own classfiles.** For each source in a bounded space, compile with scalac 2.13 and 3, read the classfiles (`javap`, or the Classfile API), and diff the model's `World` against them.
- **S4. Shared `AsSeenFrom` and linearization,** one model used by the TCK and later by `Zinc/Hier`.

### V — Java (`Java/`)

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
- **B2. MiMa's rules as a policy.** Like `FlatRules` checked the PoC's rules: false negatives (the model breaks a client and MiMa is silent) and false positives. `defaultConflict` is a candidate false negative to confirm.
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
- `Jvm/Catalogue.lean`: 12 edits, each with MiMa's problem name, checked before and after by evaluation.
  - Two are compatible but change the footprint (`overrideAdded`, `pulledUp`).
  - One has no MiMa problem named (`defaultConflict`).
