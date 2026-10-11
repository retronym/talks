# From a Zinc model to a model of Scala, Java and the JVM

## Why

The Lean model was built to answer one question: is Zinc's invalidation sound, relative to obligations on the compiler bridge? To answer it, each feature file (`Erasure`, `Hier`, `Flat`, `Inline`, `Names`, …) has its own toy language, sized to what Zinc hashes. The toys found real bugs, but they are private to one consumer. Factored out, the same knowledge answers other questions:

- **Binary compatibility.** Zinc asks whether a client must be *recompiled*; MiMa asks whether its old classfile still *links*. Both are questions about a task's trace against an edited environment, so T1 applies to linkage unchanged (`link_congr`).
- **IDE type systems.** The TCK (`retronym/scala-type-system-tck`) checks IntelliJ against an `asSeenFrom` model that now shares its core with the Scala layer.
- **Scala 2 → 3 migration.** The name-resolution calibration in talks#21 is already a list of differences between the two compilers.

## Architecture

```
Core      Task (query trees, T1), program spaces, JSON dumps        (today: Zinc.Task)
Jvm       classfiles, linkage, selection, behaviour                 (Jvm/)
Java      a javac subset: source → Jvm.World; JLS §13 statements    (Java/)
Scala     resolution, linearization, asSeenFrom, membership; lowering → Jvm.World, Scala 2 and 3   (Scala/)
consumers Zinc (Zinc/), binary compatibility (BinCompat/), the TCK; migration as a stretch goal
```

`Jvm.World`, `Jvm.Program` and `Jvm.Site` are the contract: a front end turns sources into classfiles and a client program; a consumer reads them. Each layer is calibrated against its real tool (HotSpot, scalac, javac, MiMa) before claims are built on it. Front ends are compilers in Zinc's sense, so for a front end meeting Zinc's obligations, a client Zinc does not recompile links against the new library exactly as a fresh build would (Track B4, `XCompiler.untouched_eq_clean`). The converse fails, and the gap is what MiMa reports.

## Done

Each track's results, calibration numbers and PRs are in its own file:

| Track | Layer | Results |
|---|---|---|
| Tracks J1–J3, J5 | JVM linkage, calibrated on HotSpot 21/25/27 over ~58k client programs | `PLAN-track-j.md` |
| Tracks S1–S6 | Scala lowering (2.12, 2.13, 3), shared `asSeenFrom`, membership; calibrated on scalac | `PLAN-track-s.md` |
| Tracks V1–V3 | Java lowering, JLS chapter 13; calibrated on javac 17/21/25 | `PLAN-track-java.md` |
| Tracks B1, B2, B4 | MiMa modelled, five gaps (MiMa-F1, MiMa-M1, MiMa-F2, MiMa-D1, MiMa-P1), corrected rules; Zinc-clean ⇒ binary-compatible | `PLAN-track-b.md` |

## Open

### Track J4: behaviour

**Why.** The JVM model links but runs no code. A library method's own calls are invisible, so MiMa's 17 `ReversedMissingMethodProblem` reports that break no client in the model are unjudged, and nestmates can't be modelled usefully (a nest change breaks a client only through a library method's own calls). Constants folded into the client are part of the same gap.

**Done looks like.** Method bodies as a list of sites linked when the method runs; constants folded at the client; `changesSomeClient` generalised to "links, but runs different code"; the 17 reports classified on HotSpot. Track: `PLAN-track-j.md`.

### Track J3 remainder: nestmates and smaller linkage gaps

**Why.** These are what `Jvm/Link.lean` still says it doesn't model, and each can hide a MiMa gap.

**Done looks like.** Nestmates (`NestHost`/`NestMembers`, private access between members; after Track J4); `Object`'s methods in interface resolution; transitive overriding through an intermediate package-private method (§5.4.5); clients in the library's package; a space over two client classes; protected constructors and constructor chaining between library classes. Each calibrated on HotSpot like the rest. Track: `PLAN-track-j.md`.

### Track B3: source-level spaces

**Why.** MiMa's users edit source, not classfiles. The JVM edit space found MiMa's gaps; a source edit space would find which ones real Scala and Java edits reach, and where scalac's encoding (forwarders, `$init$`, value classes) makes a source-compatible-looking edit break.

**Done looks like.** A space of source edits, Scala and Java, lowered, linked against a client space and checked against MiMa and HotSpot, as the JVM edit space was. Today only the Scala catalogue's first cases have been run through MiMa, and the Java catalogue not at all. Track: `PLAN-track-b.md`.

### A general proof for the corrected MiMa rules

**Why.** `BinCompat/Sound.lean` checks the corrected rules on the edit space only. Upstreaming them to MiMa is stronger with a proof that they are sound for every library.

**Done looks like.** A theorem that if `Fixed` reports nothing, every client that linked on the old library links on the new one, for all libraries. It needs a monotonicity argument about resolution and selection over the whole `Jvm` model. Track: `PLAN-track-b.md`.

### Port `Hier`, `Erasure`, `Flat` and `ImplicitScope` onto the shared Scala layer

**Why.** These four `Zinc/` files each have their own toy Scala, their own `asSeenFrom` and their own query plumbing. No `Zinc/` file imports `Scala/AsSeenFrom.lean` or `Scala/Lower.lean`. Until they do, Zinc's bridge instances, Track B4 and the MiMa model don't share one Scala semantics, and Track B4's key model (`ZincBridgeKeys.lean`) stays separate from the Zinc one.

**Done looks like.** The four files restated over `Scala/AsSeenFrom` and `Scala/Lower`, with their theorems kept; `Task` moved out of `Zinc` into a core library; the explicit-interface T3 that Track B4 restates in `BinCompat/ZincBridge.lean` moved into `General.lean`. Single-writer work, since it touches `Zinc/`. Track: `PLAN-track-s.md`.

### The TCK's dependency on `Scala/AsSeenFrom.lean`

**Why.** The TCK uses a vendored copy (retronym/scala-type-system-tck, branch `claude/shared-asf`), which can drift.

**Done looks like.** A decision for Jason. Either keep the vendored copy with a CI diff against a pinned talks commit, or move the file into a Mathlib-free lake package in this repo (say `lean_lib AsSeenFromCore`) that the TCK `require`s by `git … subDir`. Recommendation: vendored until the TCK branch reaches `master`, then the package. Track: `PLAN-track-s.md`.

### Scala and Java layer remainders

**Why.** Each widens what Track B3's source spaces can express.

**Done looks like.** Membership: type members, `var`, `protected` and qualified access, `abstract override`, objects as overriders, and a probe of the Java rules. Lowering: case classes with type parameters or several parameter lists, enums with type parameters, objects nested in classes, local classes, constructor parameters of plain classes, `lazy val` and `var` in classes, overloading, Java-defined parents. Tracks: `PLAN-track-s.md`, `PLAN-track-java.md`.

### Upstream reports

**Why.** Findings help no one until filed.

**Done looks like.** The five MiMa issues (drafts in `PLAN-track-b.md`, "Issues to file") and the scalac 2 trait-setter `AbstractMethodError` (`PLAN-track-s.md`) filed.

### The contributor repository

**Why.** The model has one author plus agents. The layers are now separable enough for outside contributors, through the tiers in the contributor proposal.

**Done looks like.** A contributor-facing repository with the layers, the probes and a first set of tiered tasks, per the separate proposal.
