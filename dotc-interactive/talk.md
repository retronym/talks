# dotc, from batch to interactive: targeting, a session, cancellation that unwinds, and several readers over one symbol table

**Audience:** people who work on scalac, dotc, Metals, the IntelliJ Scala plugin or another compiler that also has to serve an editor.

**What this is:** a visual guide to a stream of work on Scala 3's presentation compiler (23–24 October 2026, the draft [retronym/scala3#84][PR] on top of [retronym/scala3#68][PR68]). It takes the driver from one whole-file run per request to a targeted, resumable, cancellable session, and then to several concurrent readers over one symbol table, following Kotlin K2's lazy resolve and IntelliJ's read and write actions.

<!-- break -->

**Arc:**

1. The batch compiler as it was, and why scalac's presentation compiler was hard to get right.
2. Targeting: type only the path to the request.
3. The session: one run serves many requests.
4. Cancellation that unwinds.
5. Several readers: K2's rules, and completion as lazy resolve.
6. The races the suites found, each as a before and after.
7. Readers side by side, as lanes over one symbol table.
8. Edits that keep the run, range requests, diagnostics by provenance.
9. The measurements.
10. Prior art.

Every number is from the design notes, cited by section: [session §n][S] is `interactive-session.md`, [readers §n][M] is `interactive-multi-reader.md`, [Track I §n][TI] is the model. `§n` alone is a card of this talk.

---

## Part I — The batch compiler as it was

### 1. One thread, one run

```mermaid
flowchart TB
  subgraph R["Run n, one thread"]
    direction LR
    P[parser] --> N[namer] --> T[typer] --> X["… → backend"]
  end
  U["compilation units: trees"] --- R
  R -- "reads and writes" --> CB["ContextBase, lives across runs:<br/>symbol table (denotations, scopes),<br/>uniques, names, caches"]
```

- A `Run` takes a set of units through the phases, on one thread. The symbol table, uniques and caches live on the `ContextBase` and outlive the run.
- `ContextBase.checkSingleThreaded`, asserted at the start of a run, records the assumption. Parallel pickling and `-Ybackend-parallelism` keep every symbol-table access on the main thread and hand workers only context-free work ([readers §3][M]).
- Nothing in the typer polled for cancellation. The check was at unit and subphase boundaries, and the presentation compiler's callback consumed the interrupt bit ([Track I §2][TI]).

### 2. Trees: typed values, untyped trees consumed

```mermaid
flowchart LR
  U["untyped DefDef<br/>attachments: SymOfTree,<br/>TypedAhead, ExpandedTree"] -- "typer removes<br/>the attachments" --> T["typed DefDef<br/>(a value)"]
  U -. "type it again?" .-> X["no symbol, no expansion:<br/>cannot be typed twice (I8)"]
```

- A typed tree is a value: once built, nothing else in the run changes it (with a few exceptions: `withTypeUnchecked` assigns in place, `span_=`).
- The untyped tree is consumed. `retrieveSym` takes `SymOfTree`, `typedUnadapted` takes `TypedAhead`, `traverse` takes `ExpandedTree`, the Namer's `setMods` rewrites modifiers ([readers §3][M], kind E).
- In batch that is free: each tree is typed once. For an editor it is finding I8, and it comes back in §11.

### 3. Completers: lazy facts with a one-bit black hole

```mermaid
stateDiagram-v2
  direction TB
  [*] --> Lazy: Namer enters the symbol
  Lazy --> Touched: completeFrom sets Touched,<br/>runs the completer
  Touched --> Completed: info set,<br/>Touched cleared
  Touched --> Cyclic: re-entered while Touched
  Cyclic: CyclicReference
  Touched --> Leaked: completer throws
  Leaked: Touched left set
  Leaked --> Cyclic: next access in the run
```

- The Namer enters one symbol per definition, its info a `LazyType`. `SymDenotation.completeFrom` sets `Touched`, runs the completer, and stores the info.
- `Touched` is the only recursion guard. Meeting it set is a `CyclicReference`. In batch that is right: a true cycle is an error, and `Namer` and `Typer` catch it where an alternative exists.
- It was not reset if the completer threw. In batch the run ends anyway; in a long-lived session every later request sees a spurious cycle ([session §6][S], [Track I §2][TI]).

### 4. Periods and denotations

<figure class="fig anim">
<svg viewBox="0 0 720 210" role="img" aria-label="A symbol's denotations as a ring, each valid for a period of one run">
  <text x="0" y="16" class="h">phases of run 3</text>
  <g class="a-in" style="--d:.1s">
    <rect x="120" y="28" width="60" height="22" rx="4" class="box"/><text x="150" y="43" text-anchor="middle">parser</text>
    <rect x="184" y="28" width="60" height="22" rx="4" class="box"/><text x="214" y="43" text-anchor="middle">typer</text>
    <rect x="248" y="28" width="70" height="22" rx="4" class="box"/><text x="283" y="43" text-anchor="middle">pickler</text>
    <rect x="322" y="28" width="56" height="22" rx="4" class="box"/><text x="350" y="43" text-anchor="middle">…</text>
    <rect x="382" y="28" width="70" height="22" rx="4" class="box"/><text x="417" y="43" text-anchor="middle">erasure</text>
    <rect x="456" y="28" width="56" height="22" rx="4" class="box"/><text x="484" y="43" text-anchor="middle">…</text>
    <rect x="516" y="28" width="70" height="22" rx="4" class="box"/><text x="551" y="43" text-anchor="middle">backend</text>
  </g>
  <text x="0" y="88" class="b">symbol f</text>
  <text x="0" y="104" class="m">lastDenot</text>
  <rect x="184" y="68" width="194" height="42" rx="6" class="typed a-grow-x" style="--d:.5s"/>
  <text x="194" y="85" class="mono a-in" style="--d:.9s">d1: (x: Int): List[T]</text>
  <text x="194" y="101" class="mono a-in" style="--d:.9s">Period(3, typer..pickler)</text>
  <rect x="382" y="68" width="204" height="42" rx="6" class="pub a-grow-x" style="--d:1.1s"/>
  <text x="392" y="85" class="mono a-in" style="--d:1.5s">d2: (x: Int): List</text>
  <text x="392" y="101" class="mono a-in" style="--d:1.5s">Period(3, erasure..backend)</text>
  <path d="M 586 96 C 650 100, 640 140, 380 140 C 130 140, 120 110, 180 100" class="mut dash a-in" style="--d:1.7s" marker-end="url(#arr4)"/>
  <text x="400" y="158" class="m a-in" style="--d:1.8s">nextInRun: the ring of one symbol's denotations</text>
  <text x="0" y="186" class="b a-in" style="--d:2.2s">run 4:</text>
  <text x="50" y="186" class="mono a-in" style="--d:2.2s">d1.current</text>
  <text x="140" y="186" class="a-in" style="--d:2.4s">brings d1 forward to run 4 (a write on the first read in the run), or finds it stale</text>
  <defs><marker id="arr4" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="f-mut"/></marker></defs>
</svg>
<figcaption>Martin Odersky's design for dotc: a fact is valid for a period, a run id and a range of phases ([periods.md][periods]).</figcaption>
</figure>

- A `Period` is a run id and a phase interval; a `SymDenotation` is a symbol's meaning over one period, and the denotations of one symbol form a ring.
- Reading a denotation in a later run is a write: `Denotation.current` validates it, or brings it forward and links it into the ring ([readers §3][M], kind B).
- The run id is 16 bits, and nothing guarded it: a long-lived driver overflows it into the phase bits (I10, [session §9][S]). A livelock later ran it past 65,535 to 0 (I43).

### 5. scalac's presentation compiler: requests nested inside the type check

<figure class="fig anim">
<svg viewBox="0 0 720 200" role="img" aria-label="scalac services a request at a safepoint inside the background type check">
  <text x="0" y="16" class="h">compiler thread</text>
  <rect x="0" y="34" width="700" height="34" rx="6" class="box a-grow-x" style="--d:.1s"/>
  <text x="10" y="56" class="a-in" style="--d:.3s">backgroundCompile: typing unit A</text>
  <g class="a-in" style="--d:.6s">
    <line x1="240" y1="30" x2="240" y2="72" class="mut"/><line x1="290" y1="30" x2="290" y2="72" class="mut"/>
    <line x1="340" y1="30" x2="340" y2="72" class="mut"/><line x1="390" y1="30" x2="390" y2="72" class="mut"/>
    <line x1="440" y1="30" x2="440" y2="72" class="mut"/><line x1="490" y1="30" x2="490" y2="72" class="mut"/>
    <line x1="540" y1="30" x2="540" y2="72" class="mut"/><line x1="590" y1="30" x2="590" y2="72" class="mut"/>
    <text x="415" y="24" class="m" text-anchor="middle">signalDone after every tree: a safepoint</text>
  </g>
  <g class="a-drop" style="--d:1.1s">
    <rect x="300" y="96" width="180" height="40" rx="6" class="own"/>
    <text x="390" y="114" text-anchor="middle" class="b">askTypeAt(pos)</text>
    <text x="390" y="129" text-anchor="middle" class="m">same trees, same symbols</text>
  </g>
  <path d="M 390 96 L 390 72" class="s-own a-in" style="--d:1.5s" marker-end="url(#arr5)"/>
  <text x="0" y="168" class="a-in" style="--d:1.9s">the background resumes from whatever the request left: synthetics, scopes, caches, the half-typed unit</text>
  <text x="0" y="188" class="b c-bad a-in" style="--d:2.4s">so every invariant over mutable state must hold at every safepoint</text>
  <defs><marker id="arr5" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="f-own"/></marker></defs>
</svg>
<figcaption>Nested servicing ([Track I §1–2][TI]). Requests run only when no completer is in progress (<code>lockedCount == 0</code>) and no speculative typing is buffered.</figcaption>
</figure>

- The typer calls `signalDone` after each tree; there `pollForWork` runs the requests that arrived, inside the type check, on the same thread.
- The property needed is not thread safety (nothing runs at the same time, and a lock is either reentrant and lets the request in, or deadlocks). It is the discipline of async-signal safety ([Track I][TI] summary).

### 6. The bugs that discipline produces: scala/scala#11328

| commit in [scala/scala#11328][11328] | state that is not a fact | broken at a safepoint |
|---|---|---|
| `uninterruptible(addSyntheticMethods)` | a member set grown in a burst | a nested retype saw part of the burst, skipped the rest |
| `consumeSynthetic` | `unit.synthetics`, consumed | a targeted check took the trees and was abandoned |
| keep the implicit factory | a symbol's identity | the implicit cache held the replaced symbol |
| suspend a targeted check's warnings | `suppressionsKnown`, a completeness claim | made by a check that stopped early |

- Track I's toy injects one request at every safepoint of a scalac-shaped kernel. Before the PR the four scenarios modelled on its tests diverge at 8–13 of 14–18 safepoints; after it, at none ([Track I §4][TI]).
- Each fix is local to one shape, and the harness is the only way to know there is no fifth. One remains: a nested `askType(source)` still diverges at 16 of 16 (findings I1 and I2, confirmed against the PR's branch).
- dotc under Metals diverges nowhere, because it never interrupts: a request waits, then pays a fresh whole-file run.

### 7. dotc under Metals, before this work

```mermaid
flowchart TB
  E["editor request"] --> Q["CompilerJobQueue<br/>one thread, LIFO"]
  Q --> D["InteractiveDriver.run<br/>fresh Run per request"]
  D --> W["parse, index,<br/>type the whole file"]
  W --> A["answer read off<br/>the typed tree"]
  C["cancel token"] -. "cancels the future,<br/>not the work" .-> Q
```

- Every request made a new `Run` and typed every statement of the file. `CachingDriver` skipped the run when the file and its text were the last ones ([session §1][S]).
- After an edit, the first request is a whole-file run: 0.4 to 1.6 s on `Types.scala`, 7,000 lines ([session §1][S]).
- A run could not be stopped: the cancellation hook consumed the interrupt bit and the typer never polled. A completion made obsolete by the next keystroke ran to the end, and the next one queued behind it ([session §4][S]).
- Failure was all or nothing: a `CyclicReference` anywhere, or a stack overflow, emptied the answer, and a leaked `Touched` poisoned later requests.

---

## Part II — Targeting

### 8. Type only the path

<figure class="fig anim">
<svg viewBox="0 0 720 300" role="img" aria-label="A targeted run types the statements on the path to the request and records the others with their contexts">
  <text x="0" y="14" class="h">A.scala, 60 objects</text>
  <rect x="0" y="24" width="300" height="20" rx="4" class="typed a-in" style="--d:.3s"/><text x="8" y="38" class="mono">import scala.collection.mutable</text>
  <rect x="0" y="48" width="300" height="20" rx="4" class="skip a-in" style="--d:1.8s"/><text x="8" y="62" class="mono">object O1 { … }</text>
  <rect x="0" y="72" width="300" height="20" rx="4" class="skip a-in" style="--d:1.85s"/><text x="8" y="86" class="mono">object O2 { … }</text>
  <rect x="0" y="96" width="300" height="20" rx="4" class="skip a-in" style="--d:1.9s"/><text x="8" y="110" class="mono">…  object O9 { … }</text>
  <rect x="0" y="120" width="300" height="88" rx="4" class="typed a-in" style="--d:.7s"/><text x="8" y="134" class="mono">object O10 {</text>
  <rect x="16" y="142" width="276" height="20" rx="4" class="skip a-in" style="--d:1.95s"/><text x="24" y="156" class="mono">def method10(x: Int): Int = …</text>
  <rect x="16" y="166" width="276" height="20" rx="4" class="typed a-in" style="--d:1.1s"/><text x="24" y="180" class="mono">val r = method10(1).@@</text>
  <text x="8" y="202" class="mono">}</text>
  <rect x="0" y="212" width="300" height="20" rx="4" class="skip a-in" style="--d:2.0s"/><text x="8" y="226" class="mono">object O11 { … }</text>
  <rect x="0" y="236" width="300" height="20" rx="4" class="skip a-in" style="--d:2.05s"/><text x="8" y="250" class="mono">…  object O60 { … }</text>
  <circle cx="232" cy="176" r="5" class="f-own a-pop" style="--d:.1s"/>
  <path d="M 320 176 L 300 176" class="s-own a-in" style="--d:.2s"/>
  <text x="326" y="180" class="c-own b a-in" style="--d:.2s">target</text>
  <g class="a-in" style="--d:2.3s">
    <text x="390" y="62" class="b">skipped: recorded, not typed</text>
    <text x="390" y="80" class="mono">SkippedStat(stat, ctx, owner)</text>
    <text x="390" y="98" class="m">the untyped tree, the context it would</text>
    <text x="390" y="114" class="m">have been typed in, and its owner</text>
  </g>
  <g class="a-in" style="--d:2.7s">
    <text x="390" y="160" class="b">completion in object 10</text>
    <text x="390" y="180">before: 11 statements, 791 trees</text>
    <text x="390" y="198" class="c-typed b">after: 1 statement, 43 trees</text>
    <text x="390" y="222" class="m">400-object file: 2 top-level trees, not 22</text>
  </g>
</svg>
<div class="legend"><span><i class="typed"></i>typed</span><span><i class="skip"></i>skipped, context recorded</span></div>
<figcaption>The x-ray's 60-object file ([session][S] summary, §2, §3).</figcaption>
</figure>

- `Typer.typedStats` types a package's or a template's statements in order, so the decision is made there. Of each list on the way down, only the statement containing the target is typed.
- A skipped statement's symbols are as usable as a typed one's: the Namer entered them before any statement was typed, with completers that compute signatures on demand. What it lacks is its typed tree.
- The first version typed a *prefix*, everything up to the target. The x-ray showed `method1`…`method6` typed for a completion in object 7. The prefix was never the point; the typed *set* is ([session §2][S]).

### 9. Where the rule bends

- **Never skipped:** imports and exports (they shape the context of what follows), nested package clauses, synthetic trees with no span of their own.
- **A point between statements** types only the next one. scalac's rule types the whole list there; on `class JavaParser`'s header that was 10,000 trees for one hover.
- **Blocks** are targeted too, but statements the target's statement names, transitively, are typed in order (200 dependent vals overflowed the stack through their completers), and a skipped local leaves a typed stub so the block's scope still has `x` in `locally { val x = 1; x@@ }`.
- **Typed whole:** a tree that outlives the request as a value. A body typed ahead by an overload resolution (I21), a refinement's synthetic class (I25), an inline method's body (I28), and blocks under speculative typer states such as `tryEither` (I24) ([session §2][S]).

---

## Part III — The session

### 10. One run, many requests

```mermaid
flowchart TB
  Q["request on (uri, content, target)"] --> S{"same content<br/>as the session?"}
  S -- no --> F["Fresh: new targeted run"]
  S -- yes --> K{"target inside a<br/>skipped statement?"}
  K -- no --> SV["Served: nothing typed"]
  K -- yes --> RS["Resumed: type that statement<br/>in its recorded context,<br/>splice it into the tree"]
```

| request ([session §3][S], x-ray, warm JVM) | typed | trees | ms |
|---|---|---|---|
| fresh completion in object 10 | 1 statement | 43 | 12–60 |
| resume into object 40 | +1 statement | 41 | 7 |
| served from what is typed | 0 | 8 | 1–3 |
| whole file, for comparison | 60 statements | 12,097 | 357 |

The run's denotations, completers and caches stay valid throughout: it is the same `Run`. An edit starts a fresh run, which is now cheap.

### 11. Resume and splice

<figure class="fig anim">
<svg viewBox="0 0 720 230" role="img" aria-label="A skipped statement is typed in its recorded context and spliced into the typed tree">
  <text x="0" y="14" class="h">typed tree (tpdTree)</text>
  <rect x="0" y="24" width="250" height="24" rx="5" class="typed"/><text x="10" y="40" class="mono">PackageDef p</text>
  <rect x="20" y="54" width="230" height="22" rx="5" class="typed"/><text x="30" y="69" class="mono">Import …</text>
  <rect x="20" y="80" width="230" height="22" rx="5" class="typed"/><text x="30" y="95" class="mono">ModuleDef O10 (r typed)</text>
  <rect x="20" y="106" width="230" height="22" rx="5" class="typed a-pop" style="--d:2.2s"/><text x="30" y="121" class="mono a-in" style="--d:2.3s">ModuleDef O40</text>
  <text x="440" y="14" class="h">skipped statements</text>
  <rect x="440" y="24" width="200" height="22" rx="5" class="skip"/><text x="450" y="39" class="mono">O1 … O9, O11 … O39</text>
  <rect x="440" y="50" width="200" height="22" rx="5" class="skip a-out" style="--d:1.0s;--o:.15"/><text x="450" y="65" class="mono a-out" style="--d:1.0s;--o:.15">O40  (ctx, owner)</text>
  <rect x="440" y="76" width="200" height="22" rx="5" class="skip"/><text x="450" y="91" class="mono">O41 … O60</text>
  <circle cx="610" cy="61" r="5" class="f-own a-pop" style="--d:.2s"/>
  <text x="560" y="128" class="c-own a-in" style="--d:.3s">hover lands in O40</text>
  <g class="a-in" style="--d:.8s">
    <rect x="300" y="150" width="200" height="40" rx="6" class="own"/>
    <text x="400" y="166" text-anchor="middle" class="mono">typedStats(O40 :: Nil, owner)</text>
    <text x="400" y="182" text-anchor="middle" class="m">in its recorded context</text>
  </g>
  <path d="M 520 72 C 520 120, 470 140, 440 150" class="s-own a-draw" pathLength="1" style="--d:.6s"/>
  <path d="M 300 170 C 270 170, 270 117, 252 117" class="s-typed a-draw" pathLength="1" style="--d:1.7s"/>
  <text x="0" y="215" class="m a-in" style="--d:2.6s">the splice is a TreeMap that copies only the path to the owner; SetRootTree re-run; new skipped members join the list</text>
</svg>
<figcaption>Statements can be typed in any order: object 200 after object 10, then object 5 ([session §3][S]).</figcaption>
</figure>

- Why the recorded context is enough: a statement's context in `typedStats` is the template's plus the imports before it, and nothing typing an earlier sibling adds.
- A whole-file request on the same content completes the session instead of replacing it: every still-skipped statement typed and spliced in one pass. Document highlight asks for one on every cursor move; in one VS Code session 136 of 142 whole-file runs came from it ([session §7][S]).

### 12. Poisoned statements (I8)

<figure class="fig pair">
<svg viewBox="0 0 340 150" role="img" aria-label="Before: a statement whose typing was cancelled cannot be typed again">
  <text x="0" y="14" class="h">before</text>
  <rect x="0" y="26" width="320" height="26" rx="5" class="bad"/><text x="10" y="43" class="mono">object O59 { def giant = … }</text>
  <text x="0" y="74">typing unwound by a cancellation:</text>
  <text x="0" y="92" class="mono">SymOfTree, TypedAhead, ExpandedTree</text>
  <text x="0" y="110">already taken off the untyped tree</text>
  <text x="0" y="134" class="c-bad b">resume: no symbols, nothing to type</text>
</svg>
<svg viewBox="0 0 340 150" role="img" aria-label="After: the statement is re-parsed, re-indexed in its recorded context and skipped again">
  <text x="0" y="14" class="h">after</text>
  <rect x="0" y="26" width="320" height="26" rx="5" class="skip"/><text x="10" y="43" class="mono">object O59 { def giant = … }</text>
  <text x="0" y="74">re-parse the file, find the statement</text>
  <text x="0" y="92">with the same span and class, unlink its</text>
  <text x="0" y="110">symbols, index the fresh tree, skip it</text>
  <text x="0" y="134" class="c-typed b">a later resume types it as new</text>
</svg>
<figcaption>Only definitions are replaceable. An aborted expression statement or a companion pair (I22: a case class's synthetics live in its object's tree) poisons the session, and every later request starts fresh (I23) ([session §3][S]).</figcaption>
</figure>

### 13. Leaving a file (I17)

```mermaid
sequenceDiagram
  participant A as Applications.scala (run 5)
  participant Q as QuotesAndSplices.scala (run 6)
  Note over A: targeted run:<br/>typedApply skipped,<br/>its completer pending
  A->>Q: next request is on another file
  Q->>A: needs typedApply's signature
  Note over A,Q: A Namer completer of run 5<br/>refuses to run in run 6:<br/>"Not found: typedApply"
  Note over A: fix: completeSymbolsOf(A)<br/>before leaving, signatures<br/>only, in run 5
```

- A whole-file run never exposed this: it completed every member while typing the bodies ([session §3][S]).
- The rule, honestly stated: a run's lazy facts must be forced or discarded before the run is left, until completers become functions of node and owner (stage 3 of the cancellation design).

---

## Part IV — Cancellation that unwinds

### 14. Cancelling the future, not the work

<figure class="fig pair">
<svg viewBox="0 0 340 170" role="img" aria-label="Before: the cancel token cancels the future; the typer runs on">
  <text x="0" y="14" class="h">before</text>
  <text x="0" y="40">lsp4j cancels the request's future</text>
  <text x="0" y="60">callback: <tspan class="mono">isCancelled = Thread.interrupted()</tspan></text>
  <text x="0" y="80">the bit is consumed by the first check</text>
  <rect x="0" y="96" width="320" height="22" rx="5" class="own"/><text x="10" y="111">typer runs to the end of the file</text>
  <rect x="0" y="124" width="200" height="22" rx="5" class="wait"/><text x="10" y="139">next request queued behind</text>
</svg>
<svg viewBox="0 0 340 170" role="img" aria-label="After: a sticky flag polled every 1,024 typed trees; the typer unwinds">
  <text x="0" y="14" class="h">after</text>
  <text x="0" y="40">token.onCancel() is the driver's checker</text>
  <text x="0" y="60">a sticky flag, polled every 1,024 typed trees</text>
  <text x="0" y="80"><tspan class="mono">CancelledCompilation</tspan> (a ControlThrowable)</text>
  <rect x="0" y="96" width="90" height="22" rx="5" class="own"/><text x="8" y="111">typer</text>
  <path d="M 92 107 L 112 107" class="s-bad"/><text x="116" y="111" class="c-bad">unwinds</text>
  <rect x="0" y="124" width="200" height="22" rx="5" class="typed"/><text x="10" y="139">next request runs at once</text>
</svg>
<figcaption>[session §4][S]. The exception's cause is a <code>CancellationException</code>, so mtags classifies it as a cancellation and keeps the driver.</figcaption>
</figure>

### 15. The token path

<figure class="fig anim">
<svg viewBox="0 0 720 150" role="img" aria-label="The cancellation token's path from the editor to the typer's checkpoint">
  <defs><marker id="m15" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="f-mut"/></marker></defs>
  <g class="a-in" style="--d:.1s"><rect x="0" y="10" width="200" height="44" rx="6" class="box"/><text x="100" y="29" text-anchor="middle" class="b">VS Code</text><text x="100" y="45" text-anchor="middle" class="mono">&#36;/cancelRequest</text></g>
  <path d="M 202 32 L 254 32" class="mut a-draw" pathLength="1" style="--d:.4s" marker-end="url(#m15)"/>
  <g class="a-in" style="--d:.5s"><rect x="260" y="10" width="200" height="44" rx="6" class="box"/><text x="360" y="29" text-anchor="middle" class="b">lsp4j</text><text x="360" y="45" text-anchor="middle">the future is cancelled</text></g>
  <path d="M 462 32 L 514 32" class="mut a-draw" pathLength="1" style="--d:.8s" marker-end="url(#m15)"/>
  <g class="a-in" style="--d:.9s"><rect x="520" y="10" width="200" height="44" rx="6" class="box"/><text x="620" y="29" text-anchor="middle" class="b">Metals CancelTokens</text><text x="620" y="45" text-anchor="middle" class="mono">CancelToken</text></g>
  <path d="M 620 56 C 620 80, 100 70, 100 92" class="mut a-draw" pathLength="1" style="--d:1.2s" marker-end="url(#m15)"/>
  <g class="a-in" style="--d:1.4s"><rect x="0" y="96" width="200" height="44" rx="6" class="box"/><text x="100" y="115" text-anchor="middle" class="b">mtags CompilerAccess</text><text x="100" y="131" text-anchor="middle" class="mono">withInterruptableCompiler</text></g>
  <path d="M 202 118 L 254 118" class="mut a-draw" pathLength="1" style="--d:1.7s" marker-end="url(#m15)"/>
  <g class="a-in" style="--d:1.8s"><rect x="260" y="96" width="200" height="44" rx="6" class="own"/><text x="360" y="115" text-anchor="middle" class="b">Scala3CompilerAccess</text><text x="360" y="131" text-anchor="middle">token.onCancel() as checker</text></g>
  <path d="M 462 118 L 514 118" class="s-own a-draw" pathLength="1" style="--d:2.1s" marker-end="url(#m15)"/>
  <g class="a-pop" style="--d:2.2s"><rect x="520" y="96" width="200" height="44" rx="6" class="bad"/><text x="620" y="115" text-anchor="middle" class="b">Typer.typed</text><text x="620" y="131" text-anchor="middle">checkpoint every 1,024 trees</text></g>
</svg>
</figure>

- `CompletionAbortSuite.abort-via-token` is this path without the editor: a token cancelled 20 ms after submission, the request answers its default, the driver is kept (the next run id is exactly one more) ([session §4][S]).
- Not built on thread interrupts: the bit is unsticky and consumed, `ClosedByInterruptException` in a loader becomes a symbol marked absent, and catch-alls swallowed it.

### 16. The unwind, frame by frame

<figure class="fig anim">
<svg viewBox="0 0 720 360" role="img" aria-label="A cancellation unwinds the stack; each completeFrom frame clears Touched on its way out">
  <text x="0" y="14" class="h">the request's thread, innermost frame on top</text>
  <g class="a-pop" style="--d:.2s"><rect x="490" y="30" width="150" height="24" rx="12" class="bad"/><text x="565" y="46" text-anchor="middle" class="c-bad b">cancel(): flag set</text></g>
  <rect x="0" y="28" width="460" height="28" rx="5" class="bad a-out" style="--d:1.1s"/><text x="10" y="46" class="mono a-out" style="--d:1.1s">checkCancelledTyping  →  throw CancelledCompilation</text>
  <rect x="0" y="60" width="460" height="28" rx="5" class="box a-out" style="--d:1.4s"/><text x="10" y="78" class="mono a-out" style="--d:1.4s">Typer.typed(…)  inside B's body</text>
  <rect x="0" y="92" width="460" height="28" rx="5" class="own a-out" style="--d:1.7s"/><text x="10" y="110" class="mono a-out" style="--d:1.7s">completeFrom(B)</text>
  <g class="a-out" style="--d:1.7s;--o:0"><rect x="490" y="96" width="74" height="20" rx="10" class="own"/><text x="527" y="110" text-anchor="middle" class="c-own">Touched</text></g>
  <g class="a-pop" style="--d:1.9s"><rect x="490" y="96" width="128" height="20" rx="10" class="skip"/><text x="554" y="110" text-anchor="middle">B: LazyType again</text></g>
  <rect x="0" y="124" width="460" height="28" rx="5" class="box a-out" style="--d:2.0s"/><text x="10" y="142" class="mono a-out" style="--d:2.0s">Namer completer of A: types A's body ahead</text>
  <rect x="0" y="156" width="460" height="28" rx="5" class="own a-out" style="--d:2.3s"/><text x="10" y="174" class="mono a-out" style="--d:2.3s">completeFrom(A)</text>
  <g class="a-out" style="--d:2.3s;--o:0"><rect x="490" y="160" width="74" height="20" rx="10" class="own"/><text x="527" y="174" text-anchor="middle" class="c-own">Touched</text></g>
  <g class="a-pop" style="--d:2.5s"><rect x="490" y="160" width="128" height="20" rx="10" class="skip"/><text x="554" y="174" text-anchor="middle">A: LazyType again</text></g>
  <rect x="0" y="188" width="460" height="28" rx="5" class="box a-out" style="--d:2.6s"/><text x="10" y="206" class="mono a-out" style="--d:2.6s">typedStats(O59 :: Nil)  a resume</text>
  <g class="a-pop" style="--d:2.8s"><rect x="490" y="192" width="200" height="20" rx="10" class="skip"/><text x="590" y="206" text-anchor="middle">O59 re-parsed, skipped again</text></g>
  <rect x="0" y="220" width="460" height="28" rx="5" class="box a-out" style="--d:2.9s"/><text x="10" y="238" class="mono a-out" style="--d:2.9s">Run.compileSources</text>
  <rect x="0" y="252" width="460" height="28" rx="5" class="box a-out" style="--d:3.1s"/><text x="10" y="270" class="mono a-out" style="--d:3.1s">InteractiveDriver.runUpTo, CachingDriver.run</text>
  <rect x="0" y="284" width="460" height="28" rx="5" class="typed"/><text x="10" y="302" class="mono">CompilerAccess.withSharedCompiler</text>
  <g class="a-pop" style="--d:3.4s"><rect x="490" y="288" width="232" height="20" rx="10" class="typed"/><text x="606" y="302" text-anchor="middle" class="c-typed">answers the default, keeps the driver</text></g>
  <path d="M 462 42 C 482 42, 482 298, 462 298" class="s-bad a-draw" pathLength="1" style="--d:1.1s"/>
  <text x="0" y="340" class="m a-in" style="--d:3.6s">kept: every statement typed before the abort, the run's facts that completed, the aborted run's context (I14)</text>
</svg>
<figcaption>Each frame restores what it set on the way out: <code>completeFrom</code> clears <code>Touched</code>, a <code>LazyAnnotation</code> keeps its thunk, a <code>SymbolLoader</code> leaves its root loadable ([session §4][S]). The Lean model's <code>forceA_unlock_touched</code> against <code>touched_stays_cyclic</code> is this difference ([Track I §5][TI]).</figcaption>
</figure>

### 17. What survives an abort

| kind of state | after a cancellation ([session §4][S]) |
|---|---|
| facts (denotations) | written only on completion; an unwound completion leaves the lazy type |
| trees and units | the aborted run's partial tree is garbage; the previous run's stay current |
| the run's context | the *aborted* run's: it brought classpath denotations forward to its run id, and the clock does not roll back (I14) |
| unit-scope state, diagnostics | per run, dropped with it |
| the session | statements typed before the abort kept; the one being typed re-parsed (§12) |

The soak suite (`CompletionSoakSuite`) is a seeded random walk of 300 requests, cancellations at random checkpoints and edits on one driver: every completion must equal a fresh whole-file run's, and no symbol of the file may be left `Touched`. It found I14 on its first run.

### 18. Degrade instead of failing

- `Touched` is cleared on every unwinding exception in interactive mode, not only cancellation; a flag found set on a symbol not in this reader's `completing` set is healed, not reported as a cycle.
- A cycle costs one symbol for one request. Only an exception of unknown effect taints the run (the next request starts fresh). That is IntelliJ's `RecursionManager` discipline mapped onto `completeFrom` ([session §6][S]).
- Sized by measurement: one cycle in 1,074 targeted completions over `Typer.scala` and `Namer.scala`; 223 preventions over the whole suite, nearly all in the provider's own type-ahead of implicit conversions ([session §6][S]).
- `a-true-cycle-costs-the-cyclic-members-only`: `def pBeta = pGamma; def pGamma = pBeta` lists as `pBeta: Any, pGamma: Any` beside the whole `pAlpha` and `pDelta`.

---

## Part V — Several readers: K2's rules

### 19. What a second reader is for

- With targeting, a hover queued behind a hover waits milliseconds. Step 0 replayed a recorded VS Code session (814 presentation-compiler events) with Metals' job queue instrumented: 89 to 93 percent of all queueing was behind whole-file work, the first `run` after an edit and the providers that walk the whole typed tree ([readers §0][M], §42).
- So what a second reader buys is a *background pass* (diagnostics, semantic tokens, the session completed) beside foreground hovers that stay fast, and later several open files over one classpath symbol table ([readers §1][M]).
- The measurement also warned: a targeted reader spends 65 to 79 percent of its CPU inside completers, 5 to 20 percent typing bodies (§43). A lock around completions would serialise most of it.

### 20. Read actions and write actions

<figure class="fig anim">
<svg viewBox="0 0 720 190" role="img" aria-label="Readers run together; a writer raises the sticky flag, waits for readers to unwind, and runs alone">
  <text x="0" y="40" class="b">reader 1</text>
  <text x="0" y="80" class="b">reader 2</text>
  <text x="0" y="120" class="b">writer</text>
  <rect x="80" y="26" width="300" height="22" rx="5" class="typed a-grow-x" style="--d:.1s"/><text x="90" y="41" class="a-in" style="--d:.4s">hover: readUpTo</text>
  <rect x="140" y="66" width="250" height="22" rx="5" class="typed a-grow-x" style="--d:.3s"/><text x="150" y="81" class="a-in" style="--d:.6s">background pass: readAll</text>
  <line x1="330" y1="10" x2="330" y2="160" class="s-bad dash a-in" style="--d:1.0s"/>
  <text x="336" y="160" class="c-bad a-in" style="--d:1.0s">new content: writerPending</text>
  <rect x="380" y="26" width="6" height="22" class="f-bad a-pop" style="--d:1.3s"/>
  <rect x="390" y="66" width="6" height="22" class="f-bad a-pop" style="--d:1.4s"/>
  <text x="400" y="41" class="m a-in" style="--d:1.4s">next checkpoint: unwind</text>
  <rect x="400" y="106" width="150" height="22" rx="5" class="own a-grow-x" style="--d:1.7s"/><text x="410" y="121" class="a-in" style="--d:2.0s">fresh run, alone</text>
  <rect x="556" y="26" width="120" height="22" rx="5" class="typed a-grow-x" style="--d:2.4s"/><text x="566" y="41" class="a-in" style="--d:2.6s">retried</text>
  <rect x="556" y="66" width="120" height="22" rx="5" class="typed a-grow-x" style="--d:2.5s"/><text x="566" y="81" class="a-in" style="--d:2.7s">retried</text>
</svg>
<figcaption>IntelliJ's pending write action cancelling read actions at <code>checkCanceled</code>, with the typer's checkpoint as <code>checkCanceled</code> ([readers §2][M], §8 step 3).</figcaption>
</figure>

- Not snapshots. Roslyn's compilations are immutable, so an old reader finishes against the old world. dotc cannot do that while a run brings shared classpath denotations forward to its own run id: two runs cannot be read at once (I14). Snapshot readers need facts that outlive a run (stage 3) ([readers §2][M]).

### 21. What a reader may write: K2's four rules

| rule | stated for dotc ([readers §3][M]) |
|---|---|
| 1. disposable | everything a reader writes is thrown away or re-validated by the next writer; a run already is |
| 2. published once, consistent | another reader sees "not computed" or the finished value, never a partial one |
| 3. idempotent | any reader computing it would write the same value, so a race to publish needs only safe publication |
| 4. cancellation leaves it unpublished | a reader unwound midway leaves the fact as it found it; the next reader recomputes |

Kotlin's low-level FIR resolves declarations in place under these rules (§48). dotc's typer broke all four: trees mutated in place, nothing published a completion, nothing recorded what content a type was computed against, and a cancelled typer left half-typed trees ([PR][PR]).

### 22. Five kinds of state

```mermaid
flowchart LR
  A["A · per-request scratch<br/>comparers, context pools,<br/>targeting slots, cancel checker"] -->|"move to a<br/>thread-confined Reader"| A2["one per thread"]
  B["B · lazy facts with a black hole<br/>completeFrom's Touched,<br/>InheritedCache.locked, loaders"] -->|"owner + barrier<br/>per root"| B2["lazy resolve"]
  C["C · pure caches<br/>lastDenot/checkedPeriod,<br/>member and base-type caches"] -->|"one-field publication,<br/>concurrent maps"| C2["safe publication"]
  D["D · interning, counters<br/>Uniques, _nextSymId"] -->|"concurrent interner,<br/>atomic counter"| D2["linearizable"]
  E["E · trees<br/>consumed attachments,<br/>the session's splice"] -->|"skipped statements as facts,<br/>a persistent typed tree"| E2["step 5, not built"]
```

- dotc had no precedent for concurrent readers of symbols or types ([readers §3][M]).
- A *root* is the unit a completion is claimed by: whatever one completion writes together. A symbol loader completes a class and its module at once, and the TASTy completers of one file share one unpickler's address maps, so the claim is per pair or per file, not per symbol ([readers §3.1][M]). §24 lists the roots.
- The `Reader` (kind A) found its own bug: it cannot be a field of the context, because contexts are captured (completer creation contexts, import contexts, skipped statements' contexts) and run later under another request. It is bound to the thread ([readers §8][M] step 2).

### 23. Step 3: one coarse lock, and why it was not enough

- Every completion, bring-forward, inherited-cache computation and lazy TASTy read under one reentrant lock; concurrency in body typing only, as K2 started.
- The two-reader suites found fourteen races (I34 to I47), each fixed. Then I48: a completer publishes intermediate infos (a `TempClassInfo`, `TypeBounds.empty` while a TASTy type is read) that a reader outside the lock takes as complete.

| hover beside a background pass, `Types.scala` ([readers §8][M]) | median | p90 | right? |
|---|---|---|---|
| reads outside the lock | 1.0 ms | 7.9 ms | no (I48) |
| reads under the lock (serialised) | 141 ms | 457 ms | yes |

The premise did not hold: body typing reads what completions are in the middle of writing. A serialised hover waits for whatever statement the pass is typing, and the statement's size does not predict it: a 95-character statement held the lock for 368 ms through the completions it forced.

### 24. Completion as lazy resolve

```mermaid
stateDiagram-v2
  direction TB
  [*] --> Idle
  Idle: Idle, info is a LazyType
  Idle --> InProgress: acquire(R)
  InProgress: InProgress, owner R, latch
  InProgress --> Done: release(R), latch opens
  InProgress --> Idle: R unwinds, LazyType restored, latch opens
  Done: Done, info published
  Done --> [*]
```

- One claim per root (§22): a loader's class and module together, a TASTy file, a Namer symbol by itself, and as roots of their own the inherited caches (base data, member names), the lazy TASTy reads, `LazyRef` computations and, under one key, every bring-forward to a new run ([readers §8][M] step 4).
- While it runs, the symbol's info is an `InProgress`, a lazy type only the owner sees through. Every other reader meets a lazy type and takes the existing slow path of `Denotation.info`, which waits on the root. The hot test, `myInfo.isInstanceOf[LazyType]`, is unchanged.
- A Namer completion runs in a committable typer state of its own and reports to the namer's reporter, so a hover that forces a signature does not swallow its diagnostics.
- Behind `-Yinteractive-readers`; batch never allocates an `InProgress`.

### 25. Two readers, one inferred signature

```mermaid
sequenceDiagram
    participant R1 as Reader R1 (hover on f)
    participant F as f (root)
    participant G as g (root)
    participant R2 as Reader R2 (completion needs g)
    R2->>G: acquire(R2): Idle → InProgress(R2, latch)
    activate G
    Note over G: R2 runs g's completer<br/>fresh TyperState, StoreReporter
    R1->>F: acquire(R1): Idle → InProgress(R1, latch)
    activate F
    Note over F: R1 types f's body ahead
    R1->>G: acquire(R1): InProgress(R2)
    Note over R1,G: wouldDeadlock? owner R2, R2.waitingOn = null → no
    R1-->>G: R1.waitingOn = G, then latch.await()
    alt R2 publishes
        Note over G: g.info = T_g, fully defined
        R2->>G: release(R2): InProgress → Done, latch.open()
        G-->>R1: Waited (g.isCompleted)
        R1->>G: read g.info
    else R2 is cancelled or unwinds inside g
        Note over G: g.info restored to its LazyType,<br/>TyperState discarded, nothing published
        R2->>G: release(R2, unwound = true): InProgress → Idle, latch.open()
        G-->>R1: retry acquire(R1): Idle → InProgress(R1)
        Note over R1,G: R1 completes g itself (rule 4)
        R1->>G: release(R1): Done
    end
    deactivate G
    Note over F: f.info = T_f (needs only T_g)
    R1->>F: release(R1): InProgress → Done
    deactivate F
    R1->>R1: answer the hover from f.info
```

`def f = g + 1` and `def g = …`, both with inferred result types ([readers §3.1][M]). Part VII draws both branches as lanes.

### 26. What the model says

Before the compiler work, two forcers over one lazy store in Lean (`Query/Concurrent.lean`) and a two-reader kernel in the Java toy ([Track I, two readers][TC], [readers §7][M]):

| statement | theorem | consequence |
|---|---|---|
| with holes owned and a barrier, every value either forcer stores or answers is the fixed point's, under every schedule | `run_agree` | the barrier is the whole correctness argument; no ranking, no fairness needed |
| under a ranked fixed point no schedule reports a cycle | `run_ranked_no_cyc` | a wait that closes a wait-for cycle reports a real cycle; which reader names it varies (15 of 81 interleavings in the toy) |
| a peek at the other forcer's hole races; at one's own, it does not | `peek_any_races`, `peek_own_agrees` | `isCompleting` must mean "on this reader" (toy: 24 of 63 interleavings race) |
| an aborted owner's waiter takes over if the hole is released; stuck if `Touched` stays | `abort_waiter_takes_over`, `abort_keep_hole_waiter_stuck` | the reset belongs in the owner's unwind path |

Left to `decide` rather than proved: progress.

---

## Part VI — The races, before and after

### 27. A peek at another reader's completion (I41)

<figure class="fig pair">
<svg viewBox="0 0 340 190" role="img" aria-label="Before: a peek sees another reader's completion and skips the import">
  <text x="0" y="14" class="h">before</text>
  <text x="40" y="36" class="b" text-anchor="middle">R1</text><text x="290" y="36" class="b" text-anchor="middle">R2</text>
  <line x1="40" y1="44" x2="40" y2="180" class="ln"/><line x1="290" y1="44" x2="290" y2="180" class="ln"/>
  <rect x="115" y="60" width="110" height="34" rx="6" class="own"/><text x="170" y="75" text-anchor="middle" class="mono">import Ops._</text><text x="170" y="89" text-anchor="middle" class="m">Touched by R1</text>
  <path d="M 40 77 L 113 77" class="s-own"/>
  <path d="M 290 120 C 250 120, 240 100, 226 90" class="s-bad dash"/>
  <text x="290" y="138" text-anchor="end" class="mono">isCompleting?</text>
  <text x="290" y="154" text-anchor="end">yes: skip the import</text>
  <text x="290" y="172" text-anchor="end" class="c-bad">"foo is not a member of T"</text>
</svg>
<svg viewBox="0 0 340 190" role="img" aria-label="After: isCompleting means on this reader; another reader's completion is waited for">
  <text x="0" y="14" class="h">after</text>
  <text x="40" y="36" class="b" text-anchor="middle">R1</text><text x="290" y="36" class="b" text-anchor="middle">R2</text>
  <line x1="40" y1="44" x2="40" y2="180" class="ln"/><line x1="290" y1="44" x2="290" y2="180" class="ln"/>
  <rect x="115" y="60" width="110" height="34" rx="6" class="typed"/><text x="170" y="75" text-anchor="middle" class="mono">import Ops._</text><text x="170" y="89" text-anchor="middle" class="m">published by R1</text>
  <path d="M 40 77 L 113 77" class="s-typed"/>
  <path d="M 290 120 C 250 120, 240 100, 226 90" class="s-wait"/>
  <text x="290" y="138" text-anchor="end" class="mono">isCompleting on R2?</text>
  <text x="290" y="154" text-anchor="end">no: wait, look again</text>
  <text x="290" y="172" text-anchor="end" class="c-typed">foo found through Ops</text>
</svg>
<figcaption>Thirteen sites peek at <code>isCompleting</code> and take another path rather than force ([readers §4.1][M]). The model predicted it (<code>peek_any_races</code>); the two-reader suites found it ([readers §8][M], I41).</figcaption>
</figure>

### 28. A wait-for cycle, or a lock order (I54)

<figure class="fig pair">
<svg viewBox="0 0 340 190" role="img" aria-label="Before: two roots taken in different orders raise a false CyclicReference">
  <text x="0" y="14" class="h">before: raise CyclicReference</text>
  <rect x="20" y="40" width="110" height="30" rx="6" class="own"/><text x="75" y="60" text-anchor="middle">R1 holds X.tasty</text>
  <rect x="210" y="40" width="110" height="30" rx="6" class="own"/><text x="265" y="60" text-anchor="middle">R2 holds Y.tasty</text>
  <path d="M 130 50 C 170 40, 180 40, 208 50" class="s-wait"/><text x="170" y="34" text-anchor="middle" class="c-wait">waits</text>
  <path d="M 210 64 C 170 76, 170 76, 132 64" class="s-wait"/><text x="170" y="92" text-anchor="middle" class="c-wait">waits</text>
  <text x="0" y="124">roots are coarser than facts:</text>
  <text x="0" y="142">two files taken in two orders,</text>
  <text x="0" y="160">not a dependency cycle</text>
  <text x="0" y="180" class="c-bad">a false "Cyclic reference"</text>
</svg>
<svg viewBox="0 0 340 190" role="img" aria-label="After: the reader that would close the cycle backs off and is retried">
  <text x="0" y="14" class="h">after: back off and retry</text>
  <rect x="20" y="40" width="110" height="30" rx="6" class="own"/><text x="75" y="60" text-anchor="middle">R1 holds X.tasty</text>
  <rect x="210" y="40" width="110" height="30" rx="6" class="skip"/><text x="265" y="60" text-anchor="middle">R2 released Y</text>
  <path d="M 130 50 C 170 40, 180 40, 208 50" class="s-typed"/><text x="170" y="34" text-anchor="middle" class="c-typed">takes Y, proceeds</text>
  <text x="0" y="124">R2 is pre-empted, as by a writer:</text>
  <text x="0" y="142">unwinds, releases its roots; the</text>
  <text x="0" y="160">driver retries its request</text>
  <text x="0" y="180" class="c-typed">counted; more than 20 fails a test</text>
</svg>
<figcaption>A true dependency cycle then shows in the other reader alone, where a single reader would report it. The cross-thread cycle test gives the single-reader answer in all 30 rounds, backing off 19–25 times ([readers §8][M] step 4).</figcaption>
</figure>

### 29. The base-type cache's sentinel (I34)

<figure class="fig pair">
<svg viewBox="0 0 340 170" role="img" aria-label="Before: the in-progress mark in the shared cache looks like a cycle to the other reader">
  <text x="0" y="14" class="h">before</text>
  <text x="0" y="38" class="mono">baseTypeOf(C, Any)</text>
  <rect x="0" y="50" width="320" height="30" rx="6" class="own"/><text x="10" y="70" class="mono">myBaseTypeCache(Any) = NoPrefix</text>
  <text x="0" y="100">R1's in-progress mark, in the shared cache</text>
  <text x="0" y="120">R2 reads it as "already in progress here"</text>
  <text x="0" y="146" class="c-bad">"Cyclic reference involving class Any"</text>
</svg>
<svg viewBox="0 0 340 170" role="img" aria-label="After: the in-progress mark lives on the reader">
  <text x="0" y="14" class="h">after</text>
  <text x="0" y="38" class="mono">baseTypeOf(C, Any)</text>
  <rect x="0" y="50" width="320" height="30" rx="6" class="typed"/><text x="10" y="70" class="mono">Reader.pendingBaseTypes  (identity set)</text>
  <text x="0" y="100">the mark is R1's own; R2 computes the</text>
  <text x="0" y="120">same value (rule 3); cleared on every unwind</text>
  <text x="0" y="146" class="m">identity: a structural set made equal types cyclic</text>
</svg>
<figcaption>A second black hole hiding in a cache ([readers §8][M] step 3). The cache version also leaked the mark on cancellation.</figcaption>
</figure>

### 30. The period published before the denotation (I36)

<figure class="fig pair">
<svg viewBox="0 0 340 180" role="img" aria-label="Before: the period is stored first; a reader sees a current period and a null symbol">
  <text x="0" y="14" class="h">before</text>
  <text x="0" y="40" class="mono">writer:  checkedPeriod = now</text>
  <text x="59" y="58" class="mono">lastSymbol = sym</text>
  <text x="0" y="90" class="mono">reader:  if checkedPeriod == now</text>
  <text x="73" y="108" class="mono">use lastSymbol</text>
  <rect x="0" y="124" width="320" height="26" rx="6" class="bad"/><text x="10" y="141">current period, null lastSymbol</text>
  <text x="0" y="170" class="m">NamedType.stableInRunSymbol</text>
</svg>
<svg viewBox="0 0 340 180" role="img" aria-label="After: fields first, then the period with a release store, read with an acquire load">
  <text x="0" y="14" class="h">after</text>
  <text x="0" y="40" class="mono">writer:  lastSymbol = sym</text>
  <text x="59" y="58" class="mono">setRelease(checkedPeriod, now)</text>
  <text x="0" y="90" class="mono">reader:  if getAcquire(checkedPeriod)</text>
  <text x="86" y="108" class="mono">== now: use lastSymbol</text>
  <rect x="0" y="124" width="320" height="26" rx="6" class="typed"/><text x="10" y="141">the period publishes the fields</text>
  <text x="0" y="170" class="m">util.Publish: static final VarHandles</text>
</svg>
<figcaption>The one cost that cannot be chosen per mode: a field is a field in batch too. Plain moves on x86, <code>stlr</code>/<code>ldar</code> on Apple silicon; measured with perflab in §47 ([readers §8][M], [PR][PR]).</figcaption>
</figure>

### 31. The typer state dropped with its variable (I62)

<figure class="fig pair">
<svg viewBox="0 0 340 180" role="img" aria-label="Before: a completion's own typer state is dropped with an uninstantiated type variable">
  <text x="0" y="14" class="h">before</text>
  <text x="0" y="38" class="mono">val retractedVars = Set.empty[A] …</text>
  <rect x="0" y="50" width="200" height="40" rx="6" class="own"/><text x="10" y="67">completion's TyperState</text><text x="10" y="83" class="mono">A: uninstantiated</text>
  <path d="M 200 70 L 240 70" class="s-bad"/><text x="246" y="74" class="c-bad">dropped</text>
  <text x="0" y="116" class="mono">retractedVars: Set[A | TermRef]</text>
  <text x="0" y="134">A belongs to no live state</text>
  <text x="0" y="160" class="c-bad mono">Found: Set[A | TermRef]</text>
  <text x="0" y="176" class="c-bad mono">Required: Set[TermRef]</text>
</svg>
<svg viewBox="0 0 340 180" role="img" aria-label="After: variables are instantiated when the completion ends, then made permanent">
  <text x="0" y="14" class="h">after</text>
  <text x="0" y="38" class="mono">val retractedVars = Set.empty[A] …</text>
  <rect x="0" y="50" width="200" height="40" rx="6" class="typed"/><text x="10" y="67">completion ends:</text><text x="10" y="83">instantiate, then gc</text>
  <text x="0" y="116" class="mono">retractedVars: Set[TermRef]</text>
  <text x="0" y="134">as fullyDefinedType would</text>
  <text x="0" y="160" class="c-typed">1,441 identifiers of Nullables.scala</text>
  <text x="0" y="176" class="c-typed">match a whole-file run</text>
</svg>
<figcaption>In the serialised mode the variable stayed in the namer's state and the enclosing statement instantiated it. In a state of its own it was dropped ([readers §8][M] step 4).</figcaption>
</figure>

### 32. The leaked claim that wedged the x-ray (I61)

<figure class="fig pair">
<svg viewBox="0 0 340 180" role="img" aria-label="Before: a claim is released only on cancellation; another exception leaks it">
  <text x="0" y="14" class="h">before</text>
  <rect x="0" y="30" width="190" height="28" rx="6" class="own"/><text x="10" y="48">claim: statement s, R1</text>
  <text x="200" y="48" class="c-bad">assertion escapes</text>
  <text x="0" y="82">released only on cancellation</text>
  <rect x="0" y="96" width="320" height="28" rx="6" class="wait"/><text x="10" y="114">R2 waits for s, holding the session monitor</text>
  <text x="0" y="146">forever: the x-ray's handlers ran on</text>
  <text x="0" y="164" class="c-bad">the HTTP dispatcher, and the page froze</text>
</svg>
<svg viewBox="0 0 340 180" role="img" aria-label="After: released on any exception, the session poisoned, waits bounded">
  <text x="0" y="14" class="h">after</text>
  <rect x="0" y="30" width="190" height="28" rx="6" class="skip"/><text x="10" y="48">claim released</text>
  <text x="200" y="48" class="c-typed">session poisoned</text>
  <text x="0" y="82">on any exception; the next request is fresh</text>
  <rect x="0" y="96" width="320" height="28" rx="6" class="typed"/><text x="10" y="114">a claim records its owner thread</text>
  <text x="0" y="146">a wait gives up if the owner is gone,</text>
  <text x="0" y="164">or after 60 s, and retries</text>
</svg>
<figcaption>Any mode, not only with several readers ([readers §8][M] step 4). The x-ray now handles each request on a thread of its own and reports one that takes more than 30 s.</figcaption>
</figure>

### 33. The rest of the register

| | finding ([readers §8][M]) |
|---|---|
| I35 | the unpickler's address maps filled under the lock and read outside it: `key not found: Addr(417)` |
| I42 | a completer's constraints and a resume's commit in one typer state: a looping `OrderingConstraint` until the heap ran out |
| I43 | two fresh runs replacing each other for ever, run ids past 65,535 to 0: a fresh run and the read of its result are one write action |
| I44 | a completer captured before the wait, stale after it: `UnsupportedOperationException: complete` |
| I45 | `cleanup` erroring out a classpath symbol another reader was loading |
| I52, I55, I57 | a read action in the run's root typer state; a shared implicit `SearchRoot`; a `LazyRef` in progress taken for a cycle |
| I63–I67 | found by the throughput runs: a false self-type cycle, explicit nulls' flow facts, committed creation states, a class's caches read twice |
| I60 | two-reader soak failures under heavy load, a different symptom each time: an import's selector facts, now published as one value |
| I68 | with four or eight readers, now and then one file's errors differ from the whole-set run: the hunt in §33a–§33c |
| I70, I72, I73, I75 | found by that hunt: a completion typed in the run's shared state without the lock; three more peeks at another reader's `InProgress` (`ensureCompletions`, `typeParams`, the self type); a cached empty list computed while another reader's completion started |


### 33a. The shapes of race in shared caches (I68)

Types are hash-consed, and symbols, denotations, scopes, annotations and import infos are reached by every reader, so every plain `var` that typing fills lazily is shared. The hunt for I68 found the same four shapes again and again ([readers §4.4][M]):

| shape | where it was found | cure |
|---|---|---|
| a cache in several fields, written one after the other | `PreDenotation.asSeenFrom`, `NamedType.denot`, `AppliedType.superType`, `MatchType.reduced` | one immutable value, one release store; or the period read first with acquire |
| a sentinel during a computation | `packageObjsCache = Nil`, a lazy annotation's `myTree = null`, `myTypeParams` set early | a claim keyed by the object, as `LazyRef` has since I57: the owner meets the sentinel, others wait |
| a field read twice | `ImportInfo.featureImported`, `SourceFile.offsetToLine` | read once into a local, return what was computed |
| a structure published while it is filled | `MutableScope.toList` (I77), `ImportInfo.SelectorInfo` (I60) | build in a local and publish once, or a synchronised map in a concurrent base |

- Each fix is taken only on a concurrent base where it costs anything on the batch path; most cost nothing (a local instead of a field, the order of two stores).
- The races hide in the 484-file loop, about one divergent file a round, and show in a small one: `ShownSoak` types conversions to the compiler's `Formatting.Shown` with eight readers every round, and diverged in ten of seventeen files a round before the fixes.
- After them, 20 rounds of 484 files at k=8: no failed cell, 7 divergent files, all from §33c's raised cycles ([readers §8][M] step 4).

### 33b. A statement's typer state is private (I76)

<figure class="fig pair">
<svg viewBox="0 0 340 200" role="img" aria-label="Before: readers commit statements into the run's shared typer state and fork from it">
  <text x="0" y="14" class="h">before</text>
  <rect x="80" y="26" width="180" height="40" rx="6" class="bad"/><text x="170" y="43" text-anchor="middle" class="b">the run's TyperState</text><text x="170" y="58" text-anchor="middle" class="m">shared, committed into</text>
  <rect x="0" y="100" width="130" height="30" rx="6" class="own"/><text x="65" y="120" text-anchor="middle">R1's statement</text>
  <rect x="210" y="100" width="130" height="30" rx="6" class="own"/><text x="275" y="120" text-anchor="middle">R2's statement</text>
  <path d="M 65 100 L 120 68" class="s-bad"/><text x="40" y="88" class="c-bad">commit</text>
  <path d="M 220 68 L 275 100" class="s-wait"/><text x="262" y="88" class="c-wait">fork</text>
  <text x="0" y="156">the given's [A], bound by R1's commit,</text>
  <text x="0" y="172">met by R2's typing</text>
  <text x="0" y="192" class="c-bad">conversion to Shown rejected; an NPE</text>
</svg>
<svg viewBox="0 0 340 200" role="img" aria-label="After: a statement's typer state is settled when it ends and dropped; the run's state is read-only">
  <text x="0" y="14" class="h">after</text>
  <rect x="80" y="26" width="180" height="40" rx="6" class="typed"/><text x="170" y="43" text-anchor="middle" class="b">the run's TyperState</text><text x="170" y="58" text-anchor="middle" class="m">read-only once the run opens</text>
  <rect x="0" y="100" width="130" height="30" rx="6" class="own"/><text x="65" y="120" text-anchor="middle">R1's statement</text>
  <rect x="210" y="100" width="130" height="30" rx="6" class="own"/><text x="275" y="120" text-anchor="middle">R2's statement</text>
  <path d="M 120 68 L 65 100" class="s-typed"/><path d="M 220 68 L 275 100" class="s-typed"/>
  <text x="0" y="156">each settled when it ends (variables</text>
  <text x="0" y="172">instantiated), then dropped, never committed</text>
  <text x="0" y="192" class="c-typed">an assertion in commit keeps it so</text>
</svg>
<figcaption>The rule I66 made for locals, applied to statements; lazy annotation arguments and inline bodies, typed by whichever reader forces them, get a private child state too ([readers §8][M] step 4). A change to how a session keeps constraints, not a race fix.</figcaption>
</figure>

### 33c. Who backs off: victim selection (I74)

<figure class="fig pair">
<svg viewBox="0 0 340 200" role="img" aria-label="Before: a reader inside a Namer completion backs off and leaves it unwound for the rest of the run">
  <text x="0" y="14" class="h">before: whoever closes the cycle</text>
  <rect x="0" y="30" width="150" height="40" rx="6" class="own"/><text x="10" y="47">R1 inside a Namer</text><text x="10" y="62">completion of s</text>
  <rect x="190" y="30" width="150" height="40" rx="6" class="own"/><text x="200" y="47">R2 typing</text><text x="200" y="62">a body</text>
  <text x="0" y="96">R1 closes a wait-for cycle and backs off</text>
  <rect x="0" y="108" width="320" height="26" rx="6" class="bad"/><text x="10" y="125">s: UnwoundCompletion (cannot run twice, I53)</text>
  <text x="0" y="156">pre-empts every reader that reaches it</text>
  <text x="0" y="172">until a fresh run: with every file in one</text>
  <text x="0" y="188" class="c-bad">run, 4 of 20 cells at k=8 never recovered</text>
</svg>
<svg viewBox="0 0 340 200" role="img" aria-label="After: the body-typing reader backs off; a reader inside a Namer completion never does">
  <text x="0" y="14" class="h">after: a victim with no Namer completion</text>
  <rect x="0" y="30" width="150" height="40" rx="6" class="typed"/><text x="10" y="47">R1 finishes s</text><text x="10" y="62">and publishes</text>
  <rect x="190" y="30" width="150" height="40" rx="6" class="skip"/><text x="200" y="47">R2 backs off,</text><text x="200" y="62">its request restarts</text>
  <text x="0" y="96">all parties inside Namer completions,</text>
  <text x="0" y="112">every root a symbol: one raises</text>
  <text x="0" y="128">CyclicReference, the single-reader answer;</text>
  <text x="0" y="144">through a coarse root it waits, bounded</text>
  <text x="0" y="172" class="m">a raised cycle no sequential order has:</text>
  <text x="0" y="188" class="m">7 divergent files in 20 rounds (Setting)</text>
</svg>
<figcaption>The backoff of §28, made to choose its victim ([readers §8][M] step 4). The remaining divergences are two readers completing <code>Settings.Setting</code>'s members in opposite orders. The fix is a Namer completion that can run again (non-destructive attachments, I8), out of scope here.</figcaption>
</figure>

---

## Part VII — Readers side by side

Each panel is lanes over time, running down: readers at the edges, the roots they claim in the middle. A root's lane shows its state: idle, in progress with an owner, done.

<div class="legend"><span><i class="own"></i>in progress, owned (and the owner's work)</span><span><i class="wait"></i>waiting on a barrier</span><span><i class="typed"></i>published, done</span><span><i class="skip"></i>idle: a lazy type</span><span><i class="bad"></i>cancelled</span></div>

### 34. A claim, a wait, a publication

<figure class="fig anim">
<svg viewBox="0 0 720 360" role="img" aria-label="R2 owns g; R1 owns f and waits on g's barrier; R2 publishes g; R1 completes f and answers">
  <defs><marker id="m34" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="f-mut"/></marker></defs>
  <text x="90" y="20" class="b" text-anchor="middle">R1 · hover on f</text><text x="290" y="20" class="b" text-anchor="middle">root f</text><text x="430" y="20" class="b" text-anchor="middle">root g</text><text x="630" y="20" class="b" text-anchor="middle">R2 · completion</text>
  <line x1="90" y1="30" x2="90" y2="340" class="ln"/><line x1="290" y1="30" x2="290" y2="340" class="ln"/><line x1="430" y1="30" x2="430" y2="340" class="ln"/><line x1="630" y1="30" x2="630" y2="340" class="ln"/>
  <rect x="250" y="34" width="80" height="56" rx="4" class="skip"/><text x="290" y="66" text-anchor="middle" class="m">idle</text>
  <rect x="390" y="34" width="80" height="26" rx="4" class="skip"/><text x="430" y="51" text-anchor="middle" class="m">idle</text>
  <rect x="390" y="60" width="80" height="110" rx="4" class="own a-grow-d" style="--d:.31s"/><text x="430" y="104" text-anchor="middle" class="b a-in" style="--d:.5s">InProgress</text><text x="430" y="120" text-anchor="middle" class="a-in" style="--d:.5s">owner R2</text>
  <rect x="570" y="60" width="120" height="110" rx="4" class="own a-grow-d" style="--d:.31s"/><text x="580" y="80" class="a-in" style="--d:.5s">runs g's completer</text><text x="580" y="96" class="m a-in" style="--d:.5s">own TyperState</text>
  <path d="M 568 64 L 474 64" class="mut a-in" style="--d:.31s" marker-end="url(#m34)"/><text x="520" y="58" text-anchor="middle" class="m a-in" style="--d:.31s">acquire</text>
  <rect x="250" y="90" width="80" height="160" rx="4" class="own a-grow-d" style="--d:.78s"/><text x="290" y="160" text-anchor="middle" class="b a-in" style="--d:1s">InProgress</text><text x="290" y="176" text-anchor="middle" class="a-in" style="--d:1s">owner R1</text>
  <rect x="30" y="90" width="120" height="40" rx="4" class="own a-grow-d" style="--d:.78s"/><text x="40" y="108" class="a-in" style="--d:.9s">types f's body</text><text x="40" y="122" class="m a-in" style="--d:.9s">ahead</text>
  <path d="M 152 94 L 246 94" class="mut a-in" style="--d:.78s" marker-end="url(#m34)"/><text x="200" y="88" text-anchor="middle" class="m a-in" style="--d:.78s">acquire</text>
  <path d="M 152 134 L 386 134" class="s-wait a-draw" pathLength="1" style="--d:1.4s"/><text x="200" y="128" text-anchor="middle" class="c-wait a-in" style="--d:1.4s">needs g</text>
  <g class="a-in" style="--d:1.5s"><rect x="30" y="130" width="120" height="40" rx="4" class="wait a-blink" style="--d:1.7s"/></g><text x="40" y="148" class="a-in" style="--d:1.5s">waits on g's</text><text x="40" y="162" class="a-in" style="--d:1.5s">barrier</text>
  <text x="200" y="152" text-anchor="middle" class="m a-in" style="--d:1.5s">no cycle</text>
  <rect x="390" y="170" width="80" height="160" rx="4" class="typed a-grow-d" style="--d:2s"/><text x="430" y="200" text-anchor="middle" class="b a-in" style="--d:2.1s">Done</text><text x="430" y="216" text-anchor="middle" class="mono a-in" style="--d:2.1s">T_g</text>
  <path d="M 388 178 L 154 178" class="s-pub a-draw" pathLength="1" style="--d:2s"/><text x="200" y="192" text-anchor="middle" class="c-pub a-in" style="--d:2.1s">latch opens</text>
  <rect x="570" y="170" width="120" height="30" rx="4" class="typed a-grow-d" style="--d:2s"/><text x="580" y="190" class="a-in" style="--d:2.1s">publishes, goes on</text>
  <rect x="30" y="182" width="120" height="66" rx="4" class="own a-grow-d" style="--d:2.2s"/><text x="40" y="200" class="a-in" style="--d:2.3s">reads g.info,</text><text x="40" y="216" class="a-in" style="--d:2.3s">finishes f</text>
  <rect x="250" y="250" width="80" height="80" rx="4" class="typed a-grow-d" style="--d:3.26s"/><text x="290" y="280" text-anchor="middle" class="b a-in" style="--d:3.35s">Done</text><text x="290" y="296" text-anchor="middle" class="mono a-in" style="--d:3.35s">T_f</text>
  <rect x="30" y="256" width="120" height="30" rx="4" class="typed a-grow-d" style="--d:3.41s"/><text x="40" y="276" class="a-in" style="--d:3.5s">answers the hover</text>
  <line x1="20" y1="40" x2="700" y2="40" class="mut dash a-sweep" style="--ty:296px;--t:4.6s"/>
</svg>
<figcaption>Rule 2 is the barrier: nobody but the owner sees <code>f</code> or <code>g</code> half-completed. Rule 3: whoever completes <code>g</code> writes the same <code>T_g</code> ([readers §3.1][M]).</figcaption>
</figure>

### 35. A cancelled owner hands over

<figure class="fig anim">
<svg viewBox="0 0 720 360" role="img" aria-label="R2 owns g and is cancelled; it unwinds, restores the lazy type and opens the latch; R1 takes over and completes g">
  <defs><marker id="m35" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="f-mut"/></marker></defs>
  <text x="100" y="20" class="b" text-anchor="middle">R1 · needs g</text><text x="360" y="20" class="b" text-anchor="middle">root g</text><text x="620" y="20" class="b" text-anchor="middle">R2 · owner</text>
  <line x1="100" y1="30" x2="100" y2="340" class="ln"/><line x1="360" y1="30" x2="360" y2="340" class="ln"/><line x1="620" y1="30" x2="620" y2="340" class="ln"/>
  <rect x="310" y="34" width="100" height="26" rx="4" class="skip"/><text x="360" y="51" text-anchor="middle" class="m">idle</text>
  <rect x="310" y="60" width="100" height="110" rx="4" class="own a-grow-d" style="--d:.31s"/><text x="360" y="100" text-anchor="middle" class="b a-in" style="--d:.5s">InProgress</text><text x="360" y="116" text-anchor="middle" class="a-in" style="--d:.5s">owner R2</text>
  <rect x="550" y="60" width="140" height="110" rx="4" class="own a-grow-d" style="--d:.31s"/><text x="560" y="80" class="a-in" style="--d:.5s">runs g's completer</text>
  <path d="M 548 64 L 414 64" class="mut a-in" style="--d:.31s" marker-end="url(#m35)"/><text x="480" y="58" text-anchor="middle" class="m a-in" style="--d:.31s">acquire</text>
  <path d="M 172 104 L 306 104" class="s-wait a-draw" pathLength="1" style="--d:.95s"/><text x="240" y="98" text-anchor="middle" class="c-wait a-in" style="--d:.95s">acquire: owner R2</text>
  <g class="a-in" style="--d:1s"><rect x="30" y="100" width="140" height="90" rx="4" class="wait a-blink" style="--d:1.2s;--n:4"/></g><text x="40" y="120" class="a-in" style="--d:1s">waits on g's barrier</text>
  <g class="a-pop" style="--d:1.7s"><rect x="560" y="130" width="120" height="24" rx="12" class="bad"/><text x="620" y="146" text-anchor="middle" class="c-bad b">cancelled</text></g>
  <rect x="550" y="170" width="140" height="8" class="f-bad a-pop" style="--d:2s"/><text x="560" y="196" class="c-bad a-in" style="--d:2s">unwinds: TyperState</text><text x="560" y="212" class="c-bad a-in" style="--d:2s">discarded, nothing</text><text x="560" y="228" class="c-bad a-in" style="--d:2s">published</text>
  <rect x="310" y="170" width="100" height="24" rx="4" class="skip a-grow-d" style="--d:2s"/><text x="360" y="186" text-anchor="middle" class="a-in" style="--d:2.1s">idle again</text>
  <path d="M 306 182 L 174 182" class="s-pub a-draw" pathLength="1" style="--d:2.1s"/><text x="240" y="176" text-anchor="middle" class="c-pub a-in" style="--d:2.1s">latch opens</text>
  <rect x="310" y="194" width="100" height="86" rx="4" class="own a-grow-d" style="--d:2.4s"/><text x="360" y="230" text-anchor="middle" class="b a-in" style="--d:2.5s">InProgress</text><text x="360" y="246" text-anchor="middle" class="a-in" style="--d:2.5s">owner R1</text>
  <rect x="30" y="194" width="140" height="86" rx="4" class="own a-grow-d" style="--d:2.4s"/><text x="40" y="214" class="a-in" style="--d:2.5s">retries acquire,</text><text x="40" y="230" class="a-in" style="--d:2.5s">completes g itself</text>
  <path d="M 172 198 L 306 198" class="mut a-in" style="--d:2.4s" marker-end="url(#m35)"/>
  <rect x="310" y="280" width="100" height="50" rx="4" class="typed a-grow-d" style="--d:3.6s"/><text x="360" y="304" text-anchor="middle" class="b a-in" style="--d:3.7s">Done</text><text x="360" y="320" text-anchor="middle" class="mono a-in" style="--d:3.7s">T_g</text>
  <rect x="30" y="284" width="140" height="30" rx="4" class="typed a-grow-d" style="--d:3.7s"/><text x="40" y="304" class="a-in" style="--d:3.8s">goes on with T_g</text>
  <line x1="20" y1="40" x2="700" y2="40" class="mut dash a-sweep" style="--ty:296px;--t:4.6s"/>
</svg>
<figcaption>Rule 4, and the model's <code>abort_waiter_takes_over</code>. With dotc's old discipline (<code>Touched</code> left set) the barrier is owned by a reader that no longer exists and R1 waits for the rest of the run (<code>abort_keep_hole_waiter_stuck</code>). So the owner resets the root in its own unwind path, before releasing it ([Track I, two readers][TC]). A waiter cancelled by a writer is cancelled too; hand-over is for an owner's own failure ([readers §9][M]).</figcaption>
</figure>

### 36. A background pass beside hovers

<figure class="fig anim">
<svg viewBox="0 0 720 380" role="img" aria-label="A background pass claims and types one skipped statement at a time; hovers on another reader are served, wait for the claimed statement, or claim one the pass has not reached">
  <defs><marker id="m36" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="f-mut"/></marker></defs>
  <text x="100" y="20" class="b" text-anchor="middle">R1 · background pass</text><text x="360" y="20" class="b" text-anchor="middle">skipped statements</text><text x="620" y="20" class="b" text-anchor="middle">R2 · hovers</text>
  <line x1="100" y1="30" x2="100" y2="360" class="ln"/><line x1="620" y1="30" x2="620" y2="360" class="ln"/>
  <rect x="300" y="36" width="120" height="22" rx="4" class="skip"/><text x="360" y="51" text-anchor="middle" class="mono">s1 … s4</text>
  <rect x="30" y="60" width="140" height="60" rx="4" class="own a-grow-d" style="--d:.3s"/><text x="40" y="80" class="a-in" style="--d:.4s">visible lines first</text><text x="40" y="96" class="m a-in" style="--d:.4s">a range target</text>
  <rect x="300" y="122" width="120" height="22" rx="4" class="own a-pop" style="--d:1.1s"/><text x="360" y="137" text-anchor="middle" class="mono a-in" style="--d:1.1s">s1 claimed by R1</text>
  <rect x="30" y="122" width="140" height="56" rx="4" class="own a-grow-d" style="--d:1.1s"/><text x="40" y="142" class="a-in" style="--d:1.2s">types s1</text>
  <circle cx="620" cy="80" r="6" class="f-typed a-pop" style="--d:.5s"/><text x="608" y="84" text-anchor="end" class="a-in" style="--d:.5s">served, 1 ms</text>
  <circle cx="620" cy="104" r="6" class="f-typed a-pop" style="--d:.8s"/><text x="608" y="108" text-anchor="end" class="a-in" style="--d:.8s">served</text>
  <circle cx="620" cy="128" r="6" class="f-typed a-pop" style="--d:1.1s"/><text x="608" y="132" text-anchor="end" class="a-in" style="--d:1.1s">served</text>
  <path d="M 548 156 L 424 140" class="s-wait a-draw" pathLength="1" style="--d:1.45s"/><text x="490" y="166" text-anchor="middle" class="c-wait a-in" style="--d:1.45s">lands in s1</text>
  <g class="a-in" style="--d:1.5s"><rect x="560" y="152" width="120" height="26" rx="4" class="wait a-blink" style="--d:1.6s;--n:2"/></g><text x="570" y="169" class="a-in" style="--d:1.5s">waits for s1</text>
  <rect x="300" y="180" width="120" height="22" rx="4" class="typed a-pop" style="--d:2s"/><text x="360" y="195" text-anchor="middle" class="mono a-in" style="--d:2s">s1 spliced</text>
  <path d="M 424 191 L 556 186" class="s-pub a-draw" pathLength="1" style="--d:2s"/>
  <circle cx="620" cy="196" r="6" class="f-typed a-pop" style="--d:2.1s"/><text x="608" y="200" text-anchor="end" class="a-in" style="--d:2.1s">answered</text>
  <rect x="300" y="210" width="120" height="22" rx="4" class="own a-pop" style="--d:2.3s"/><text x="360" y="225" text-anchor="middle" class="mono a-in" style="--d:2.3s">s2 claimed by R1</text>
  <rect x="30" y="210" width="140" height="56" rx="4" class="own a-grow-d" style="--d:2.3s"/><text x="40" y="230" class="a-in" style="--d:2.4s">types s2</text>
  <rect x="300" y="240" width="120" height="22" rx="4" class="own a-pop" style="--d:2.7s"/><text x="360" y="255" text-anchor="middle" class="mono a-in" style="--d:2.7s">s4 claimed by R2</text>
  <rect x="560" y="240" width="120" height="40" rx="4" class="own a-grow-d" style="--d:2.7s"/><text x="570" y="258" class="a-in" style="--d:2.8s">types s4 itself</text><text x="570" y="272" class="m a-in" style="--d:2.8s">a resume</text>
  <rect x="300" y="270" width="120" height="22" rx="4" class="typed a-pop" style="--d:3.1s"/><text x="360" y="285" text-anchor="middle" class="mono a-in" style="--d:3.1s">s2, s4 spliced</text>
  <rect x="30" y="296" width="140" height="40" rx="4" class="own a-grow-d" style="--d:3.4s"/><text x="40" y="314" class="a-in" style="--d:3.5s">types s3; s4 is</text><text x="40" y="328" class="m a-in" style="--d:3.5s">already typed</text>
  <circle cx="620" cy="300" r="6" class="f-typed a-pop" style="--d:3.4s"/><text x="608" y="304" text-anchor="end" class="a-in" style="--d:3.4s">served</text>
  <circle cx="620" cy="324" r="6" class="f-typed a-pop" style="--d:3.7s"/><text x="608" y="328" text-anchor="end" class="a-in" style="--d:3.7s">served</text>
  <line x1="20" y1="40" x2="700" y2="40" class="mut dash a-sweep" style="--ty:310px;--t:4.4s"/>
</svg>
<figcaption>The x-ray's background pass. On a quiet machine with <code>-Yinteractive-readers</code>, the pass types <code>Types.scala</code> in 560–850 ms with 27–53 hovers served beside it at about 1 ms median; serialised, 3–6 hovers at 17–490 ms median. Its diagnostics equal a whole-file run's ([readers §8][M] step 4).</figcaption>
</figure>

---

## Part VIII — Edits that keep the run, ranges, diagnostics

### 37. Classifying an edit

```mermaid
flowchart TB
  N["new content"] --> R["edit region, from the common<br/>prefix and suffix; offset map"]
  R --> P["parse it"]
  P --> C{"vs the pristine<br/>parse"}
  C -- "no difference" --> L["layout edit: keep the run,<br/>shift spans"]
  C -- "only inside one member's<br/>right-hand side D" --> E{"D eligible?"}
  E -- "declared result type,<br/>not inline, not a constructor" --> B["body edit: keep the run, shift spans,<br/>re-index D with its old symbols, skip it"]
  E -- "otherwise" --> F["fresh run"]
  C -- "anything else" --> F
```

- IntelliJ's `BlockModificationTracker` is the rule: an edit inside a body whose definition has a declared type bumps that body's count only ([session §12][S]).
- The comparison is with a pristine parse kept on the session, not the unit's tree: the Namer mutates the trees it indexes (`setMods`), and comparing against those would take false fresh runs.
- The re-index refines D's old symbols (same identity, so every typed reference stays valid) and checks that the new info is `=:=` the old: the Lean toy's backdating (`tier1_body_edit`). Behind `-Yinteractive-body-edits`.

### 38. Shifting the spans

<figure class="fig anim">
<svg viewBox="0 0 740 230" role="img" aria-label="After an edit inside method10, spans after the edit move by delta; spans containing it grow; method10 is re-indexed and skipped">
  <text x="0" y="14" class="h">spans of A.scala, offset →</text>
  <rect x="300" y="28" width="40" height="106" class="pub a-in" style="--d:.2s;opacity:.45"/>
  <text x="346" y="24" class="c-pub a-in" style="--d:.2s">the edit: delta characters</text>
  <rect x="10" y="40" width="720" height="22" rx="4" class="typed"/><text x="18" y="55" class="mono">PackageDef</text>
  <rect x="20" y="72" width="160" height="22" rx="4" class="typed"/><text x="28" y="87" class="mono">O9</text>
  <rect x="190" y="72" width="320" height="22" rx="4" class="typed"/><text x="198" y="87" class="mono">O10 (contains the edit: grows)</text>
  <g class="a-slide" style="--dx:-40px;--d:.6s"><rect x="520" y="72" width="200" height="22" rx="4" class="typed"/><text x="528" y="87" class="mono">O11 (moves by delta)</text></g>
  <rect x="200" y="104" width="80" height="22" rx="4" class="typed"/><text x="208" y="119" class="mono">method9</text>
  <rect x="290" y="104" width="130" height="22" rx="4" class="skip a-in" style="--d:1.4s"/><text x="298" y="119" class="mono">D = method10</text>
  <g class="a-slide" style="--dx:-40px;--d:.75s"><rect x="430" y="104" width="70" height="22" rx="4" class="typed"/><text x="438" y="119" class="mono">val r</text></g>
  <g class="a-slide" style="--dx:-40px;--d:.9s"><rect x="530" y="104" width="80" height="22" rx="4" class="typed"/><text x="538" y="119" class="mono">def a</text><rect x="620" y="104" width="90" height="22" rx="4" class="typed"/><text x="628" y="119" class="mono">def b</text></g>
  <g class="a-in" style="--d:1.6s">
    <text x="20" y="156" class="b">on Types.scala, the edit costs:</text>
    <text x="20" y="176">parse 9–15 ms · compare 3–6 ms · shift 43,000 trees and 5,400 symbols 10–20 ms · re-index 1–2 ms</text>
    <text x="20" y="198" class="m">D becomes a skipped statement; the next request decides whether it is typed</text>
  </g>
</svg>
<figcaption>Eager, in place: every tree the session holds, every symbol's coordinate, the diagnostics, and the <code>SourceFile</code> itself, so identity checks need no rewriting. A copying <code>TreeMap</code> would leave <code>defTree</code>, root trees and caches in the old frame ([session §12][S]).</figcaption>
</figure>

### 39. 382 ms to 6 ms

<figure class="fig anim">
<svg viewBox="0 0 720 200" role="img" aria-label="The whole-file run after a keystroke, with and without body edits, median ms">
  <text x="0" y="14" class="h">whole-file run after a keystroke in a body, median ms</text>
  <text x="0" y="46" class="b">Types.scala</text>
  <rect x="150" y="32" width="478" height="16" rx="3" class="own a-grow-x" style="--d:.1s"/><text x="634" y="45" class="a-in" style="--d:.6s">382 (p90 607)</text>
  <rect x="150" y="52" width="7" height="16" rx="2" class="typed a-grow-x" style="--d:.3s"/><text x="163" y="65" class="c-typed b a-in" style="--d:.6s">5.9 (p90 25)</text>
  <text x="0" y="104" class="b">TypeComparer.scala</text>
  <rect x="150" y="90" width="181" height="16" rx="3" class="own a-grow-x" style="--d:.2s"/><text x="337" y="103" class="a-in" style="--d:.7s">145</text>
  <rect x="150" y="110" width="10" height="16" rx="2" class="typed a-grow-x" style="--d:.4s"/><text x="166" y="123" class="c-typed b a-in" style="--d:.7s">7.9</text>
  <text x="0" y="162" class="b">Contexts.scala</text>
  <rect x="150" y="148" width="40" height="16" rx="3" class="own a-grow-x" style="--d:.3s"/><text x="196" y="161" class="a-in" style="--d:.8s">32.1</text>
  <rect x="150" y="168" width="2" height="16" rx="1" class="typed a-grow-x" style="--d:.5s"/><text x="158" y="181" class="c-typed b a-in" style="--d:.8s">0.8</text>
</svg>
<div class="legend"><span><i class="own"></i>flag off: the edit is a fresh run</span><span><i class="typed"></i><code>-Yinteractive-body-edits</code></span></div>
<figcaption>45 rounds per file: a digit added inside a method body, a hover elsewhere, then a whole-file run as document highlight or semantic tokens ask; first five rounds dropped ([session §12][S], Measured). The hover right after the edit is unchanged (31.5 / 32.4 ms on Types.scala): it pays the edit itself, mostly the shift.</figcaption>
</figure>

Of the 45 edits, 43, 40 and 39 were body edits; the rest (an inline method, a method with an inferred result type) took a fresh run, as designed. Step 0 found about 90 percent of the queueing behind exactly this whole-file request (§42).

### 40. Range requests

<figure class="fig anim">
<svg viewBox="0 0 720 210" role="img" aria-label="A range target types the statements that touch the visible window and skips the rest">
  <text x="0" y="14" class="h">Types.scala, 7,000 lines</text>
  <rect x="0" y="24" width="40" height="176" rx="4" class="skip"/>
  <rect x="0" y="94" width="40" height="22" rx="2" class="own a-pop" style="--d:.2s"/>
  <text x="50" y="110" class="c-own b a-in" style="--d:.3s">the visible 60 lines</text>
  <g class="a-in" style="--d:.7s">
    <rect x="200" y="24" width="200" height="20" rx="4" class="skip"/><text x="208" y="38" class="mono">statements before</text>
    <rect x="200" y="86" width="200" height="20" rx="4" class="typed"/><text x="208" y="100" class="mono">touches the window</text>
    <rect x="200" y="110" width="200" height="20" rx="4" class="typed"/><text x="208" y="124" class="mono">touches the window</text>
    <rect x="200" y="172" width="200" height="20" rx="4" class="skip"/><text x="208" y="186" class="mono">statements after</text>
  </g>
  <g class="a-in" style="--d:1.2s">
    <text x="430" y="70" class="b">a 60-line window</text>
    <text x="430" y="90" class="c-typed b">637–969 trees, 26–38 ms</text>
    <text x="430" y="122" class="b">the whole file</text>
    <text x="430" y="142">41,123 trees, 307–328 ms</text>
    <text x="430" y="174" class="m">semantic tokens for the window</text>
    <text x="430" y="192" class="m">after the hints: 0–1 ms (vs 68–72 ms)</text>
  </g>
</svg>
<figcaption><code>Run.typingTarget</code> may be a range: at each statement list, a statement is typed if its span touches it ([session §7][S], Range requests).</figcaption>
</figure>

- Inlay hints always carry a range; semantic tokens have a `range` form. The compiler half is done and checked against whole-file answers; Metals still sends the whole-file forms. `RangeParams` already extends `VirtualFileParams`, so Metals can pass one to the existing method.
- Document highlight stays whole-file: its question is a point, its answer is every occurrence in the file.

### 41. Diagnostics by provenance (I69)

<figure class="fig pair">
<svg viewBox="0 0 340 210" role="img" aria-label="Before: after a body edit, diagnostics are kept or dropped by position">
  <text x="0" y="14" class="h">before: keyed by position</text>
  <rect x="0" y="26" width="320" height="24" rx="5" class="box"/><text x="10" y="42" class="mono">inline def helper = … error …</text>
  <rect x="0" y="56" width="320" height="56" rx="5" class="own"/><text x="10" y="72" class="mono">def D: Int = helper   (edited)</text>
  <text x="10" y="90" class="m">drop what is positioned in D's span</text>
  <text x="10" y="104" class="m">keep the rest, shifted</text>
  <text x="0" y="134" class="c-bad">D's inlined error, positioned in helper: kept, stale</text>
  <text x="0" y="152" class="c-bad">the class's check positioned at D: dropped</text>
  <text x="0" y="170" class="c-bad">a @nowarn removed from D: still in force</text>
  <text x="0" y="198" class="m">span-based: 4 of 13 SessionEditSuite cases fail</text>
</svg>
<svg viewBox="0 0 340 210" role="img" aria-label="After: each diagnostic is tagged with the fact whose computation reported it">
  <text x="0" y="14" class="h">after: keyed by provenance</text>
  <rect x="0" y="26" width="104" height="24" rx="5" class="pub"/><text x="52" y="42" text-anchor="middle" class="mono">Stat(sym)</text>
  <rect x="110" y="26" width="128" height="24" rx="5" class="pub"/><text x="174" y="42" text-anchor="middle" class="mono">Completion(sym)</text>
  <rect x="244" y="26" width="40" height="24" rx="5" class="pub"/><text x="264" y="42" text-anchor="middle" class="mono">run</text>
  <rect x="290" y="26" width="46" height="24" rx="5" class="pub"/><text x="313" y="42" text-anchor="middle" class="mono">Parse</text>
  <text x="0" y="74">tagged where a reporter first issues it,</text>
  <text x="0" y="90">carried through typer-state buffers</text>
  <text x="0" y="116">an edit of D drops Stat and Completion of</text>
  <text x="0" y="132">D's symbols and their suppressions; keeps</text>
  <text x="0" y="148">the rest, shifted; D's old ones shown stale</text>
  <text x="0" y="164">until D is typed again</text>
  <text x="0" y="198" class="c-typed">all 13 pass; the whole suite, 2,072 tests</text>
</svg>
<figcaption>[session §12][S], Diagnostics, on the branch <code>claude/diag-provenance-2d3c5e</code>. Found by the x-ray's replay: a body edit kept a stale diagnostic (I69).</figcaption>
</figure>

- The invariant: after every edit, the completed session's diagnostics equal a fresh whole-file run's as a multiset of level, position and message, not a count. The body-edit soaks and oracles check it before each edit and at the end.
- Not a buffer per fact: step 4 tried a `StoreReporter` per Namer completion and dropped it (I59), because completers created inside it report into it after it has been flushed. A tag has no flush.
- This is IntelliJ's rule, highlighting kept by the pass that made it, and the answer to [readers §4.3][M]: a side effect of forcing is stored with the fact, whichever reader forced it.
- Cost: 0.2 ms median per edit on `Types.scala` (55 diagnostics), against 4–15 ms for the span shift.

---

## Part IX — The measurements

### 42. Where the queueing went

<figure class="fig anim">
<svg viewBox="0 0 720 200" role="img" aria-label="Share of queueing delay by what ran in between, four replays">
  <text x="0" y="14" class="h">waiting time, by what the jobs in between did</text>
  <text x="0" y="45" class="b">burst</text>
  <g class="a-grow-x" style="--d:.1s"><rect x="80" y="32" width="280" height="18" class="own"/><rect x="360" y="32" width="224" height="18" class="pub"/><rect x="584" y="32" width="17" height="18" class="wait"/><rect x="601" y="32" width="6" height="18" class="typed"/><rect x="607" y="32" width="11" height="18" class="skip"/></g>
  <text x="0" y="81" class="b">spread</text>
  <g class="a-grow-x" style="--d:.25s"><rect x="80" y="68" width="280" height="18" class="own"/><rect x="360" y="68" width="185" height="18" class="pub"/><rect x="545" y="68" width="28" height="18" class="wait"/><rect x="573" y="68" width="39" height="18" class="typed"/><rect x="612" y="68" width="6" height="18" class="skip"/></g>
  <text x="0" y="117" class="b">jars</text>
  <g class="a-grow-x" style="--d:.4s"><rect x="80" y="104" width="213" height="18" class="own"/><rect x="293" y="104" width="168" height="18" class="pub"/><rect x="461" y="104" width="84" height="18" class="wait"/><rect x="545" y="104" width="39" height="18" class="typed"/><rect x="584" y="104" width="17" height="18" class="skip"/></g>
  <text x="0" y="153" class="b">Metals</text>
  <g class="a-grow-x" style="--d:.55s"><rect x="80" y="140" width="258" height="18" class="own"/><rect x="338" y="140" width="196" height="18" class="pub"/><rect x="534" y="140" width="45" height="18" class="wait"/><rect x="579" y="140" width="34" height="18" class="typed"/><rect x="613" y="140" width="28" height="18" class="skip"/></g>
  <text x="90" y="46" class="a-in" style="--d:.9s">50%</text><text x="370" y="46" class="a-in" style="--d:.9s">40%</text>
  <text x="90" y="154" class="a-in" style="--d:.9s">46%</text><text x="348" y="154" class="a-in" style="--d:.9s">35%</text>
  <text x="80" y="188" class="m a-in" style="--d:1.1s">89–93% behind whole-file work; a hover behind a hover waits a frame</text>
</svg>
<div class="legend"><span><i class="own"></i>a whole-file run</span><span><i class="pub"></i>a provider over a cached whole-file run</span><span><i class="wait"></i>completing the session</span><span><i class="typed"></i>targeted, fresh or resumed</span><span><i class="skip"></i>targeted, served</span></div>
<figcaption>814 events of a recorded VS Code session on the compiler's own sources, replayed four ways ([readers §0][M]). Hover wait median 6–7 ms in the burst, jars and Metals replays, p90 142–533 ms; the hover's own driver time 0.1 ms.</figcaption>
</figure>

The verdict at the time: concurrency would overlap the fifth of a reader that is body typing; the cheaper moves (a session that survives an edit, range requests) come first. That is the order the work then took.

### 43. Where a reader's CPU goes

<figure class="fig anim">
<svg viewBox="0 0 720 170" role="img" aria-label="Share of a reader's CPU inside completers, body typing and other work">
  <text x="0" y="14" class="h">async-profiler, CPU samples by stack</text>
  <text x="0" y="45" class="b">targeted reader, jars</text>
  <g class="a-grow-x" style="--d:.1s"><rect x="170" y="32" width="403" height="18" class="own"/><rect x="573" y="32" width="31" height="18" class="typed"/><rect x="604" y="32" width="76" height="18" class="skip"/></g>
  <text x="180" y="46" class="a-in" style="--d:.7s">completers 79%</text><text x="578" y="46" class="a-in" style="--d:.7s">6</text>
  <text x="0" y="81" class="b">whole-file run, jars</text>
  <g class="a-grow-x" style="--d:.25s"><rect x="170" y="68" width="326" height="18" class="own"/><rect x="496" y="68" width="153" height="18" class="typed"/><rect x="649" y="68" width="31" height="18" class="skip"/></g>
  <text x="180" y="82" class="a-in" style="--d:.8s">64%</text><text x="506" y="82" class="a-in" style="--d:.8s">body typing 30%</text>
  <text x="0" y="117" class="b">targeted, oracle (cold)</text>
  <g class="a-grow-x" style="--d:.4s"><rect x="170" y="104" width="331" height="18" class="own"/><rect x="501" y="104" width="102" height="18" class="typed"/><rect x="603" y="104" width="77" height="18" class="skip"/></g>
  <text x="180" y="118" class="a-in" style="--d:.9s">65%</text><text x="511" y="118" class="a-in" style="--d:.9s">20%</text>
  <text x="170" y="152" class="m a-in" style="--d:1.1s">of the completers' share, a fifth to two fifths is classpath IO under the loaders</text>
</svg>
<div class="legend"><span><i class="own"></i>inside a completion</span><span><i class="typed"></i>body typing</span><span><i class="skip"></i>parse, index, splice, providers</span></div>
<figcaption>[readers §0][M]. A coarse completion lock would serialise four fifths of a reader. Step 3's lock did; step 4 replaced it with a claim per root (§24).</figcaption>
</figure>

### 44. Hovers beside a background pass

<figure class="fig anim">
<svg viewBox="0 0 720 190" role="img" aria-label="Hover wall time beside a background pass on Types.scala, median and p90, log scale">
  <text x="0" y="14" class="h">hover beside a pass, Types.scala, ms (log scale)</text>
  <line x1="171" y1="150" x2="680" y2="150" class="ln"/>
  <line x1="171" y1="30" x2="171" y2="150" class="ln"/><text x="171" y="166" text-anchor="middle" class="m">1</text>
  <line x1="341" y1="30" x2="341" y2="150" class="ln"/><text x="341" y="166" text-anchor="middle" class="m">10</text>
  <line x1="510" y1="30" x2="510" y2="150" class="ln"/><text x="510" y="166" text-anchor="middle" class="m">100</text>
  <line x1="680" y1="30" x2="680" y2="150" class="ln"/><text x="680" y="166" text-anchor="middle" class="m">1,000</text>
  <text x="0" y="52" class="b">coarse lock</text><text x="0" y="66" class="m">reads outside</text>
  <path d="M 171 56 L 323 56" class="s-bad a-draw" pathLength="1" style="--d:.3s" stroke-width="2"/><circle cx="171" cy="56" r="6" class="f-bad a-pop" style="--d:.2s"/><text x="330" y="60" class="c-bad a-in" style="--d:.6s">1.0 / 7.9, wrong answers (I48)</text>
  <text x="0" y="92" class="b">serialised</text><text x="0" y="106" class="m">reads under it</text>
  <path d="M 536 96 L 622 96" class="s-own a-draw" pathLength="1" style="--d:.6s" stroke-width="2"/><circle cx="536" cy="96" r="6" class="f-own a-pop" style="--d:.5s"/><text x="530" y="82" class="c-own a-in" style="--d:.9s">141 / 457</text>
  <text x="0" y="132" class="b">lazy resolve</text><text x="0" y="146" class="m">-Yinteractive-readers</text>
  <path d="M 184 136 L 328 136" class="s-typed a-draw" pathLength="1" style="--d:.9s" stroke-width="2"/><circle cx="184" cy="136" r="6" class="f-typed a-pop" style="--d:.8s"/><text x="336" y="140" class="c-typed b a-in" style="--d:1.2s">1.2 / 8.4, right answers</text>
</svg>
<figcaption>Dot: median; line to the p90. <code>Typer.scala</code>: 0.7 / 11.5, 158 / 279 and 0.7 / 15.5 ms. In the lazy-resolve runs 3 of 412 hovers waited on a root ([readers §8][M], steps 3 and 4).</figcaption>
</figure>

### 45. The replay ties, and why

<figure class="fig anim">
<svg viewBox="0 0 720 170" role="img" aria-label="Replay latency median and p90 for three modes: they tie">
  <text x="0" y="14" class="h">120 requests, Typer.scala edited 15 times, ms</text>
  <text x="0" y="48" class="b">Metals today</text><text x="0" y="62" class="m">no targeting + CachingDriver</text>
  <rect x="200" y="36" width="25" height="12" rx="2" class="skip a-grow-x" style="--d:.1s"/><rect x="200" y="50" width="403" height="12" rx="2" class="pub a-grow-x" style="--d:.2s"/><text x="610" y="60" class="a-in" style="--d:.7s">10.0 / 161</text>
  <text x="0" y="96" class="b">targeted session</text><text x="0" y="110" class="m">default</text>
  <rect x="200" y="84" width="28" height="12" rx="2" class="skip a-grow-x" style="--d:.2s"/><rect x="200" y="98" width="403" height="12" rx="2" class="pub a-grow-x" style="--d:.3s"/><text x="610" y="108" class="a-in" style="--d:.8s">11.0 / 161</text>
  <text x="0" y="144" class="b">lazy resolve</text><text x="0" y="158" class="m">-Yinteractive-readers</text>
  <rect x="200" y="132" width="26" height="12" rx="2" class="skip a-grow-x" style="--d:.3s"/><rect x="200" y="146" width="405" height="12" rx="2" class="pub a-grow-x" style="--d:.4s"/><text x="610" y="156" class="a-in" style="--d:.9s">10.4 / 162</text>
</svg>
<div class="legend"><span><i class="skip"></i>median</span><span><i class="pub"></i>p90</span></div>
<figcaption>Every answer and every diagnostics count agrees with the baseline; 17–18 whole-file runs in each mode ([readers §8][M] step 4, the replay).</figcaption>
</figure>

```mermaid
sequenceDiagram
  participant E as editor
  participant D as driver
  E->>D: didChange (an edit)
  E->>D: inlay hints for the visible range
  Note over D: on Metals' whole-file form:<br/>run types the whole file
  E->>D: hover, definition, highlight …
  Note over D: all served: nothing left to skip,<br/>and one request at a time leaves<br/>nothing for a second reader to overlap
```

The modes tie because the first request after each edit types the whole file. What changes an editing session is the body-edit flag (§39) and range requests on the Metals side (§40); what the readers buy is the background pass beside hovers (§36, §44). An earlier table had the targeted modes at 231–296 ms median: I58, a whole-file run that left no session, hidden in the baseline by `CachingDriver`.

### 46. Several readers over one run

<figure class="fig anim">
<svg viewBox="0 0 720 336" role="img" aria-label="Wall time and worker CPU typing 484 compiler files with 1, 2, 4 and 8 readers">
  <text x="0" y="14" class="h">484 files of compiler/src/dotty/tools/dotc, seconds</text>
  <line x1="60" y1="280" x2="680" y2="280" class="ln"/>
  <line x1="60" y1="30" x2="60" y2="280" class="ln"/>
  <text x="52" y="284" text-anchor="end" class="m">0</text><line x1="56" y1="166" x2="680" y2="166" class="ln dash"/><text x="52" y="170" text-anchor="end" class="m">5</text><line x1="56" y1="53" x2="680" y2="53" class="ln dash"/><text x="52" y="57" text-anchor="end" class="m">10</text>
  <text x="100" y="300" text-anchor="middle">k = 1</text><text x="280" y="300" text-anchor="middle">2</text><text x="460" y="300" text-anchor="middle">4</text><text x="640" y="300" text-anchor="middle">8</text>
  <line x1="60" y1="187" x2="680" y2="187" class="s-wait dash a-in" style="--d:.1s"/><text x="676" y="181" text-anchor="end" class="c-wait a-in" style="--d:.1s">batch compiler up to the typer: 4.1 s</text>
  <path d="M 100 150 L 280 215 L 460 248 L 640 264" class="mut dash a-draw" pathLength="1" style="--d:.3s"/><text x="648" y="272" class="m a-in" style="--d:.9s">linear</text>
  <path d="M 100 162 L 280 137 L 460 110 L 640 48" class="s-own a-draw" pathLength="1" style="--d:.5s" stroke-width="2"/>
  <circle cx="100" cy="162" r="4" class="f-own a-pop" style="--d:.5s"/><circle cx="280" cy="137" r="4" class="f-own a-pop" style="--d:.7s"/><circle cx="460" cy="110" r="4" class="f-own a-pop" style="--d:.9s"/><circle cx="640" cy="48" r="4" class="f-own a-pop" style="--d:1.1s"/>
  <text x="640" y="38" text-anchor="middle" class="c-own a-in" style="--d:1.2s">worker CPU 10.2 s</text><text x="90" y="178" text-anchor="end" class="c-own a-in" style="--d:.6s">5.2</text>
  <path d="M 100 150 L 280 191 L 460 216 L 640 232" class="s-typed a-draw" pathLength="1" style="--d:1.0s" stroke-width="2.5"/>
  <circle cx="100" cy="150" r="5" class="f-typed a-pop" style="--d:1.0s"/><circle cx="280" cy="191" r="5" class="f-typed a-pop" style="--d:1.2s"/><circle cx="460" cy="216" r="5" class="f-typed a-pop" style="--d:1.4s"/><circle cx="640" cy="232" r="5" class="f-typed a-pop" style="--d:1.6s"/>
  <text x="100" y="138" text-anchor="middle" class="c-typed b a-in" style="--d:1.1s">5.7</text><text x="280" y="210" text-anchor="middle" class="c-typed b a-in" style="--d:1.3s">3.9</text><text x="460" y="235" text-anchor="middle" class="c-typed b a-in" style="--d:1.5s">2.8</text><text x="640" y="252" text-anchor="middle" class="c-typed b a-in" style="--d:1.7s">wall 2.1 s</text>
  <text x="0" y="326" class="m a-in" style="--d:1.9s">root waits</text><text x="100" y="326" text-anchor="middle" class="m a-in" style="--d:1.9s">0</text><text x="280" y="326" text-anchor="middle" class="m a-in" style="--d:1.9s">&lt;1 ms</text><text x="460" y="326" text-anchor="middle" class="m a-in" style="--d:2.0s">&lt;3 ms</text><text x="640" y="326" text-anchor="middle" class="m a-in" style="--d:2.1s">&lt;4 ms</text>
</svg>
<div class="legend"><span><i class="typed"></i>wall time, round-robin</span><span><i class="own"></i>worker CPU</span><span><i class="wait"></i>batch typer</span></div>
<figcaption>Every top-level statement of every file skipped in one run, then k reader threads type their files (visible lines, then the rest), with work stealing; JDK 21, 18 cores (6 performance), medians of 3 rounds, including the single-threaded open of 0.5 s ([readers §8][M] step 4, Throughput).</figcaption>
</figure>

- Eight readers are 2.7 times one and twice the batch typer. Batching files into islands, or warming shared roots first, changes nothing beyond round noise: contention on the symbol table is not the limit.
- What is: the CPU each file costs as k grows (efficiency cores, the memory system) and the serial open. Per file, about 1.4 times the batch typer's CPU, from resuming statement by statement and splicing.
- Getting these numbers took six more race fixes (I60, I63–I67). The I68 hunt that followed (§33a–§33c) brought 20 rounds at k=8 to no failed cell and 7 divergent files, all from raised cycles.

### 47. The batch compiler pays nothing it can measure

| corpus | build | ms/op, median of 5 rounds | Δ | instructions/op | Δ |
|---|---|---|---|---|---|
| dottyUtil | base | 140.9 | | 1.900G | |
| dottyUtil | step 2 (the `Reader`) | 141.4 | +0.4% | 1.895G | −0.3% |
| dottyUtil | step 3 (structures per base, lock, publication) | 141.3 | +0.3% | 1.919G | +1.0% |
| re2s | base | 240.4 | | 4.793G | |
| re2s | step 2 | 237.5 | −1.2% | 4.711G | −1.7% |
| re2s | step 3 | 237.6 | −1.2% | 4.744G | −1.0% |

- The pattern: pay at construction and along existing seams. A `ContextBase` decides once whether it is concurrent; batch answers false and the concurrent classes are never loaded. The reader is a field read in batch, a `ThreadLocal` in the interactive subclass. `InProgress` lives on the existing slow path ([PR][PR]).
- The round-to-round spread of one build is 1–2 percent, as large as the differences: nothing above about 2 percent is paid, nothing below it is resolved ([readers §5][M]).

---

## Part X — Prior art

### 48. Kotlin K2: the Analysis API's low-level FIR

- FIR declarations are resolved lazily, in place, to a requested phase (`LLFirModuleLazyDeclarationResolver`, one target resolver per phase) ([LL FIR README][llfir]).
- The lock is the declaration's own resolve state, set by compare-and-set. A contending thread installs `FirInProcessOfResolvingToPhaseStateWithBarrier`, whose latch it waits on with a timeout, calling `checkCanceled()` between waits; a "jumping" state links waiting threads so that cross-thread resolution cycles are detected ([`FirResolveState.kt`][firstate], [`LLFirLockProvider.kt`][lllock]).
- A `KaSession` is valid only inside the `analyze {}` block and read action that made it; its lifetime token reports whether it is still valid and accessible ([Analysis API fundamentals][kafund], [`KaLifetimeToken.kt`][katoken]).
- dotc's `InProgress` with an owner, the root's latch and the backoff on a wait-for cycle are this design; the deviation is that dotc's roots are coarser (a file, a loader pair), so a cycle is often a lock order (§28).

### 49. IntelliJ PSI

- Read actions run on any thread; writes are write actions, and a pending write cancels running reads, which must check for cancellation often ([threading model][ijthread]). `ProcessCanceledException` is thrown at `checkCanceled()` and must never be swallowed ([background processes][ijcancel]).
- Results that are pure functions of PSI are cached under modification trackers (`CachedValuesManager`; [PSI performance][ijpsi]).
- `RecursionManager` returns `null` on re-entry on the current thread and, with `markStack()`/`mayCacheNow()`, refuses to cache results computed above a prevented recursion ([`RecursionManager.java`][ijrm]). §18 maps it onto `completeFrom`.
- The Scala plugin's `BlockModificationTracker` is the rule behind §37 ([Track I §6][TI]).

### 50. Roslyn

- A `Compilation` is immutable, realised on demand, and a new one can be derived by deltas from an old one ([docs][roscomp]). This is what dotc cannot yet do across an edit (§20).
- Symbols complete in parts: `SymbolCompletionState` is a bitset of completed parts, and `ForceComplete` takes a cancellation token ([source][rosscs]).
- Syntax trees are red-green: an immutable persistent green tree without parent pointers, and a red facade built on demand ([Lippert 2012][lippert]). `CompilationOptions.ConcurrentBuild` lets a compilation use several threads ([docs][rosconc]).

### 51. Salsa and rust-analyzer

- A change bumps a global revision and waits for other threads; a thread that sees the bump unwinds with `Cancelled`, which the IDE layer catches ([rust-analyzer architecture][raarch], [Salsa book][salsart]).
- When one thread needs a query another is computing, it blocks; before adding the edge it checks for a path back, and a cycle runs the configured strategy ([Salsa, cycles][salsacyc]). The Lean model's `closesCycle` is this check for two forcers.
- Track I's reading: dotc under Metals approximated this with a fresh run per request; the session's writer raising the sticky flag is the revision bump.

### 52. Lazy evaluation and build systems

- Marlow, Peyton Jones, Moran and Reppy, *Asynchronous exceptions in Haskell*, PLDI 2001 ([doi][marlow01]): a thunk interrupted by an asynchronous exception is not overwritten with the exception but reverted or frozen at the point of interruption, so the next demand resumes it. That is abort safety over lazy facts, and the reason §16 restores `Touched`.
- Harris, Marlow and Peyton Jones, *Haskell on a shared-memory multiprocessor*, Haskell Workshop 2005 ([doi][harris05]): lock-free evaluation of shared thunks, black-holing lazily or eagerly, blocking queues on a black hole, and harmless duplicate evaluation bounded. dotc's roots block rather than duplicate: a Namer completion cannot run twice (I53).
- Peyton Jones, *Implementing lazy functional languages on stock hardware: the Spineless Tagless G-machine*, JFP 2(2), 1992 ([doi][stg]): update frames and black holes.
- Mokhov, Mitchell and Peyton Jones, *Build systems à la carte*, ICFP 2018 ([doi][bsalc]), and *Theory and practice*, JFP 2020 ([doi][bsalc2]): the `Task` abstraction over keys that Track L's lazy store is.

### 53. scalac's presentation compiler

- Martin Odersky wrote it: the first commits in `scala.tools.nsc.interactive` are his, "new presentation compiler Global" and "new presentation compiler design" (May 2009), and he is its main committer. Miles Sabin committed alongside him from the same week; Iulian Dragos, the second most active committer to the Scala IDE for Eclipse, has 51 commits there (git history of scala/scala, checked for this talk).
- The `ask*` API (`askTypeAt`, `askTypeCompletion`, `askLoadedTyped`) is `CompilerControl` ([scaladoc][compctl]). The Scala IDE's architecture notes describe it as an asynchronous, interruptible component for targeted type checking on its own thread ([scala-ide docs][scideppc]).
- The targeted rule of §8 descends from scalac's `typedStats` with `unit.targetPos`, which leaves siblings that do not contain the target untyped; what scalac lacks is the recorded context that makes a later resume possible ([session §8][S]).
- Unverified, and so not claimed: a paper or conference talk devoted to the Scala 2 presentation compiler; any role for Nikolay Mihaylov (his scala/scala commits, 2003–2008, are the old scalac and the MSIL backend).

### 54. Dotty: periods, the interactive driver, the Dotty team

- **Martin Odersky's** design of time in dotc: runs as hours, phases as minutes, symbols with a phase-indexed meaning, and the compiler meant to be re-run as often as every keystroke ([periods.md][periods]; the page's author is not recorded in git, which starts at the 2016 move of the wiki). The talk *Compilers are Databases*, JVM Language Summit 2015 ([video][cadb]).
- **Guillaume Martres** added dotc's interactive APIs (`InteractiveDriver`, `Interactive`) and the Dotty Language Server in May 2017, described in *Interactive development using the Dotty compiler*, Scala Symposium 2017 ([doi][martres17], [video][martres17v]), and earlier (May 2016) the API and dependency extraction phases that let Zinc compile Dotty incrementally. Everything in this talk runs inside his driver.
- **Dmytro Petrashko**: the Dotty linker, *Call graphs for languages with parametric polymorphism*, OOPSLA 2016 ([doi][petrcg]); *Miniphases*, PLDI 2017 ([doi][miniph]); his thesis, EPFL 2017 ([doi][petrth]). Miniphases is why dotc's phases fuse into few tree traversals. No work of his on parallel or incremental typing was found.

### 55. Metals and Zinc

- Metals began in November 2017 (first commit by Gabriele Petronella, Ólafur Páll Geirsson its most active early committer), absorbing Iulian Dragos's 2016 language server; Ólafur created `mtags` in October 2018 ([Metals acknowledgements][metack]). Tomasz Godzik maintains it.
- The Scala 3 presentation compiler moved into the compiler repository with Jędrzej Rochala's [scala/scala3#17528][pc17528] (2023, released in 3.4.0). That module, with mtags' `CompilerAccess` and its one-thread LIFO queue, is what this work instruments and changes; I50 is a stock mtags bug the measurement surfaced (a reset job queue whose old backlog keeps running).
- Zinc's name hashing (Grzegorz Kossakowski; default since sbt 0.13.6, class-based in Zinc 1) recompiles a dependent only if a changed member's name appears in it ([sbt docs][nh], [credits][sbtcred]). It is incrementality by name-level footprint across files; the body edit of §37 is the same idea inside one file, keyed on a definition's signature.

### 56. Where it stands

- Built, behind flags, on [retronym/scala3#84][PR]: the `Reader`, the read/write regime, completion as lazy resolve (`-Yinteractive-readers`), body edits (`-Yinteractive-body-edits`), range targets. Gates: the presentation-compiler suite (2,034 tests) and the session suites in both reader modes.
- On its own branch: diagnostics by provenance (§41, I69).
- Open: re-runnable Namer completions, which would remove I74's raised cycles (§33c); the sweep's list of shared state not yet hit (`MutableScope` enters, signature caches, read-modify-write of flags, `OfTypeImplicits`' lazy vals); I49 (one scaladoc warning of 109).
- Next: trees as facts with a barrier and the typed tree as a persistent value (step 5, after non-destructive attachments, I8); facts that outlive a run, which snapshot readers across an edit need (stage 3); and the Metals side: range forms, no restart after a build compile.

[PR]: https://github.com/retronym/scala3/pull/84
[PR68]: https://github.com/retronym/scala3/pull/68
[S]: https://github.com/retronym/scala3/blob/claude/mr-code-813f14/docs/_docs/internals/interactive-session.md
[M]: https://github.com/retronym/scala3/blob/claude/mr-code-813f14/docs/_docs/internals/interactive-multi-reader.md
[TI]: https://github.com/retronym/jvm-lang-models/blob/main/packages/scala/docs/track-i.md
[TC]: https://github.com/retronym/jvm-lang-models/blob/main/packages/scala/docs/track-i-concurrent.md
[11328]: https://github.com/scala/scala/pull/11328
[periods]: https://github.com/scala/scala3/blob/main/docs/_docs/internals/periods.md
[llfir]: https://github.com/JetBrains/kotlin/blob/master/analysis/low-level-api-fir/README.md
[firstate]: https://github.com/JetBrains/kotlin/blob/master/compiler/fir/tree/src/org/jetbrains/kotlin/fir/declarations/FirResolveState.kt
[lllock]: https://github.com/JetBrains/kotlin/blob/master/analysis/low-level-api-fir/src/org/jetbrains/kotlin/analysis/low/level/api/fir/file/builder/LLFirLockProvider.kt
[kafund]: https://kotlin.github.io/analysis-api/fundamentals.html
[katoken]: https://github.com/JetBrains/kotlin/blob/master/analysis/analysis-api/src/org/jetbrains/kotlin/analysis/api/lifetime/KaLifetimeToken.kt
[ijthread]: https://plugins.jetbrains.com/docs/intellij/threading-model.html
[ijcancel]: https://plugins.jetbrains.com/docs/intellij/background-processes.html#handling-cancellation
[ijpsi]: https://plugins.jetbrains.com/docs/intellij/psi-performance.html
[ijrm]: https://github.com/JetBrains/intellij-community/blob/master/platform/util/src/com/intellij/openapi/util/RecursionManager.java
[roscomp]: https://learn.microsoft.com/en-us/dotnet/api/microsoft.codeanalysis.compilation
[rosscs]: https://github.com/dotnet/roslyn/blob/main/src/Compilers/CSharp/Portable/Symbols/SymbolCompletionState.cs
[lippert]: https://learn.microsoft.com/en-us/archive/blogs/ericlippert/persistence-facades-and-roslyns-red-green-trees
[rosconc]: https://learn.microsoft.com/en-us/dotnet/api/microsoft.codeanalysis.compilationoptions.concurrentbuild
[raarch]: https://rust-analyzer.github.io/book/contributing/architecture.html
[salsart]: https://salsa-rs.github.io/salsa/plumbing/database_and_runtime.html
[salsacyc]: https://salsa-rs.github.io/salsa/plumbing/cycles.html
[marlow01]: https://doi.org/10.1145/378795.378858
[harris05]: https://doi.org/10.1145/1088348.1088354
[stg]: https://doi.org/10.1017/S0956796800000319
[bsalc]: https://doi.org/10.1145/3236774
[bsalc2]: https://doi.org/10.1017/S0956796820000088
[compctl]: https://www.scala-lang.org/api/2.13.2/scala-compiler/scala/tools/nsc/interactive/CompilerControl.html
[scideppc]: https://github.com/scala-ide/docs/blob/master/src/sphinx/dev/architecture/presentation-compiler.rst
[cadb]: https://www.youtube.com/watch?v=WxyyJyB_Ssc
[martres17]: https://doi.org/10.1145/3136000.3136012
[martres17v]: https://www.youtube.com/watch?v=1Nk5EL94uJc
[petrcg]: https://doi.org/10.1145/2983990.2983991
[miniph]: https://doi.org/10.1145/3062341.3062346
[petrth]: https://doi.org/10.5075/epfl-thesis-7979
[metack]: https://github.com/scalameta/metals/blob/main/docs/acknowledgements/development.md
[pc17528]: https://github.com/scala/scala3/pull/17528
[nh]: https://www.scala-sbt.org/1.x/docs/Understanding-Recompilation.html
[sbtcred]: https://www.scala-sbt.org/1.x/docs/Credits.html
