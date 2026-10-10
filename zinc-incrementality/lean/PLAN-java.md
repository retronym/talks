# Phase 12 — Java in mixed builds: name resolution and sealed hierarchies (`JavaNames.lean`, `JavaSealed.lean`)

Phase 10 of `PLAN.md` covered Scala clients over Scala bindings. Java sources take another path through Zinc: javac compiles them, and `JavaAnalyze` reads the products back. The question is the same (does an edit change what a client resolved, or what it may assume about a sealed hierarchy, without Zinc invalidating the client?), but Java's rules and Zinc's Java-side edges differ.

## Question

1. A Java class added to a package, or as a member class, that shadows a name a Scala or Java client resolved. Does Zinc's Java dependency extraction record enough, and does retronym/zinc#34's added-class rule fire for Java-added classes and for Java clients?
2. Java's own scoping (JLS 6.4.1, 7.5): single-type and single-static imports shadow the package's types, which shadow on-demand imports (`import a.q.*`, `import static a.W.*`, `java.lang.*`), and two on-demand imports supplying one name are an ambiguity error, not a shadowing.
3. Java `sealed … permits` (P8.6, retronym/zinc#21: the API omitted the children), and exhaustivity of a Scala match or a Java pattern `switch` against a Java sealed hierarchy, one and two levels deep.

## What Zinc does with Java, read off the code (develop)

* **Edges.** `JavaAnalyze` records a member-ref edge from a class to every class in its classfile's constant pool, plus (sbt/zinc#148) the transitive ancestors of each, and an inheritance edge to each parent (`ClassToAPI`). Imports leave nothing in a classfile, so a Java import records no edge at all, not even a static import of a class. A member class that the client resolved shows up twice: `a/X$Foo`, and `a/X` as its outer class in the `InnerClasses` attribute.
* **No used names.** A Java class records none. `MemberRefInvalidator` therefore invalidates a Java dependent on any API change of a class it depends on (no name filter), and retronym/zinc#34, which invalidates the users of an added class's simple name, never reaches a Java client.
* **API.** `ClassToAPI` (reflection plus the classfile's `InnerClasses`) includes member classes, so adding `X.Foo` changes `X`'s name hash for `Foo`; top-level Java classes are `topLevel`, so #34 sees a Java class as added. Sealed children only for enums (fixed by #21).
* **Pipelining.** With `pipelining` on (scripted's default, not sbt's), Zinc hands every Java source to every cycle (`IncrementalCommon`, "we currently always invalidate all java sources"), and a Java class's API comes from scalac's view of the Java source (`-Ypickle-java`). That hides every Java-client miss, and #21's. The harness runs the Java spaces with `pipelining=false`, sbt's default, unless noted.

## Probed rules (javac 21, scalac 2.13.16 and 3.3.6)

* Java: member types of the class and its supertypes, then single(-static) imports, then the package's types, then the on-demand imports together with `java.lang`; two on-demand bindings are ambiguous (`q.*` against `W.*`, `q.*` or `W.*` against `java.lang.Process`). A single-static import of a name with no type (`X` has only a method `Foo`) compiles and binds nothing.
* Scala over Java bindings: as Phase 10, with Java statics as companion members (`import a.W._` sees `W.Foo`); a member class of a Java interface is *not* inherited (`object Client extends a.P` does not see `P.Foo`); an explicit import of a name that is only a method binds no type, and the lookup goes on outward; a wildcard import over `java.lang` shadows it (no ambiguity, unlike Java).
* Both compilers read `sealed`/`permits` from Java sources (explicit or inferred from the compilation unit) and check exhaustivity against it: Java's switch without `default` is an error, Scala's match a warning (`-Werror` makes it observable).

## Model

`JavaNames.lean`: the client is Java or Scala (2 or 3), in package `a.b` or `a`, with optional `implements a.P`, `import static a.X.Foo` (Scala `import a.X.Foo`; `X` always has a static method `Foo`, so the import compiles), `import static a.W.*` (Scala `import a.W._`), `import a.q.*`, and the name `Foo` or `Process` (then `java.lang.Process` is the last resort). Slots: `inh` (member class of `P`, Java only), `expl`, `wild` (static member classes of `X`, `W`), `wpkg` (`a.q.Foo`), `inner` (`a.b.Foo`), `outer` (`a.Foo`), `lib`. Every binding is a Java source; the client uses the name as a class literal, so its classfile shows what it resolved to. Edits as in `Names.lean`. Zinc's edges: the Java client's as above; the Scala client's as Phase 10.

`JavaSealed.lean`: a Java hierarchy `S permits A, B` (or `S permits A, T`, `T permits B`), with `permits` explicit (one file per class) or inferred (all in `S.java`), and a pure Scala hierarchy as a control; a client (Java `switch` without `default`, or a Scala match under `-Werror`) whose cases are the leaves. Edits: add a leaf `C` under `S` or `T`, delete it. The verdict depends on `pipelining`, #21, and whether the client has an edge to the parent that changed (a Scala client's type patterns record `B`, not `B`'s sealed parent `T`; a Java client gets `T` through sbt/zinc#148's ancestors).

Modes: `today`; for names `cheap` (#34) and `fix` (#34 with a Java class's used names, the simple names from the attributed tree that sbt/zinc#145's listener already walks, and an edge from a static import to its class); for sealed `permits` (#21), `desc` (#21 listing the transitive permitted subclasses, as the Scala bridge's `sealedDescendants` does) and `fix` (#21, and a change to a sealed class's children also invalidates the `PatMatTarget` users of its sealed ancestors). Each takes `pipe`.

## Harness

The harness needed no code for Java: a source-file base may hold `.java` files under `src/main/java/…` (a public class's file beside its package), and the runs pass `--inc-option pipelining=false`. Two commits on retronym/zinc#36's branch: the scaladoc says so, and the JSON results escape control characters (Scala 3's coloured messages broke the JSON lines). `scripts/jselect.py` picks bases until every signature (the edit, the resolution before and after, the package, the name, `implements`) has an edit; `scripts/janalyse.py` reads the client's classfile for its resolution and compares verdicts and recompilation.

## Families

| | Family | Lean | Scripted (pending, retronym/zinc branch `claude/java-names-pending`) |
|---|---|---|---|
| J1 | A Java class added to a Java client's package (or moved, or renamed to the name) over an on-demand import or `java.lang`. The client's classfile names only what it resolved, and it records no used names, so #34 does not reach it. A Scala client over a Java-added class is #34's F1: fixed. | `j1_today`, `j1_cheap` | `java-added-class-same-package`; `java-added-class-inner-package-scala-client` (fixed by #34) |
| J2 | A member class added behind a single-static import (`import static a.X.Foo`, `X` had only a method `Foo`) shadows the package's or an on-demand `Foo`. An import leaves no trace in a classfile. | `j2` | `java-static-import-member-added` |
| J3 | A second on-demand binding (`import static a.W.*` gains `W.Foo`, or `a.q.Foo`/`a.q.Process` appears beside another on-demand `Foo` or `java.lang.Process`): javac's ambiguity error, missed. | `j3`, `j3_lib` | `java-on-demand-import-ambiguity` |
| N1 | Scala 2's bridge registers no used name for the type of a `classOf` literal (`Dependency` records the class; `ExtractUsedNames` skips the literal), so a name-filtered invalidation skips the client: `W.Foo` deleted from a wildcard-imported object, and #34. Not Java-specific; Scala 3 records it. | `n1` | `classof-used-name` |
| S1 | A leaf added to a Java `permits`, no pipelining: `ClassToAPI` lists no children (retronym/zinc#21's case). | `s1`, `s1_pipe` | `java-sealed-permits-exhaustivity` (retronym/zinc#14, fixed by #21) |
| S2 | A leaf added under a nested sealed `T` declared in a file of its own. `S` is not recompiled, and a Scala client depends on `S` and its patterns' classes, not `T`: missed with #21, and with pipelining. A Java client gets `T` through sbt/zinc#148's ancestors. With `T` in `S`'s file (inferred `permits`, or any Scala hierarchy) the descendants in `S`'s hash catch it, so #21 should list descendants too. | `s2` | `java-sealed-nested-permits` |

With pipelining (scripted's default, not sbt's) every Java source is compiled in every cycle and J1–J3 and S1 vanish (`j1_pipe`, `s1_pipe`); S2 stays.

## Counts

Model counts are over the whole space; the harness ran a greedy selection of the names bases (Java 124 bases / 808 edits, Scala 62 / 382 each) and every sealed base. Model and harness agree on every case of every run, and resolution agrees with the compiler on every case.

| Space | Edits | Model unclean: today → #34 → fix | Harness divergences: develop → #34 → #34+fix |
|---|---|---|---|
| names, Java client | 12,376 | 1,632 (J1 616, J2 488, J3 528) → 1,632 → 0 | 100 → 100 → 0 |
| names, Scala 2 client | 4,664 | 752 (F1 584, N1 168) → 476 (F1 308 where the client names `Foo` only in `classOf`, N1 168) → 476 | 54 → 30 → (not run) |
| names, Scala 3 client | 4,664 | 552 (F1) → 0 → 0 | 46 → 0 → 0 |

| Sealed | Edits | Model unclean: today / pipelining / #21 / #21+desc / fix | Harness: develop, develop pipelining, #21, #21 pipelining |
|---|---|---|---|
| Java client | 12 | 6 / 0 / 0 / 0 / 0 | 6, 0, 0, 0 |
| Scala 2 client | 18 | 6 / 1 / 2 / 1 / 0 | 6, 1, 2, 1 |
| Scala 3 client | 18 | 6 / 1 / 2 / 1 / 0 | 6, 1, 2, 1 |

Besides: after a Java client's compile fails (an edit the incremental build rightly rejects), reverting the edit leaves a classfile javac wrote before the error (`a/b/Bar.class` after `rename inner`): the next build sees the sources of the last successful analysis and compiles nothing. Present on develop (26 of the Java reverts), with `useCustomizedFileManager` on or off. Not a resolution question; noted for a scripted test.

## Answers

1. Zinc's Java extraction records only the classes a classfile names, so it misses every change of what a Java client's name resolves to that adds a binding (J1, J2, J3). #34 fires for Java-added classes (they are `topLevel` in `ClassToAPI`), which fixes Scala clients (Scala 3: 46 → 0), but never reaches a Java client, which has no used names.
2. Java's static imports are the other half: an import is not in the classfile, so a member added behind `import static` is invisible (J2), and so is a second on-demand binding, which Java makes an error (J3).
3. #21 fixes the one-level case for every client. A nested sealed level in its own file (S2) still misses Scala clients; Java clients are saved by sbt/zinc#148's ancestor edges.

The fix for 1 and 2 (retronym/zinc branch `claude/java-used-names`, on #34): the listener that recovers inlined constants from javac's attributed AST gains a sibling that records each class's simple names (identifiers) and an edge to the class of each static import. Pragmatically: the names cost what Scala's do, #34 invalidates Java users of an added class's simple name as it does Scala ones, and the static-import edges invalidate a Java importer on an API change of the imported class (Java dependents are not name-filtered), which a Java class using any member of it already had. For S2: invalidate the `PatMatTarget` users of a sealed class's sealed ancestors when its children change (rare edits, so cheap); listing descendants in #21 catches only the same-file case.

## Steps

- [x] P12.1 `JavaNames.lean`, `JavaSealed.lean`: rules (probed with javac 21, scalac 2.13.16 and 3.3.6), Zinc's Java edges, verdicts, families as checked examples; `fix_clean` (names, Java and Scala 3 clients), `cheap_clean_scala`, `JavaSealed.fix_clean`.
- [x] P12.2 `lake exe jconformance names|sealed java|2|3 [cheap|fix|permits|desc] [pipe]`; harness: Java files under `src/main/java`, `pipelining=false`, JSON escaping.
- [x] P12.3 Runs on develop, develop+#34 and develop+#34+fix (names), develop and develop+#21, with and without pipelining (sealed); model and harness reconciled (Scala 2's `classOf`; the Scala bridge's descendants; pipelining's unchanged Java sources keep their API).
- [x] P12.4 Pending scripted tests per family (`claude/java-names-pending`); the Java fix with its tests (`claude/java-used-names`).
- [ ] Future: the S2 fix; N1 in the Scala 2 bridge; the stale javac classfile after a failed compile; Java clients of Scala bindings (package objects are invisible to Java, but Scala `object` members are static forwarders); the `split` layout.
