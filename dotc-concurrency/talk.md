# Several readers, one symbol table

<p class="sub">Concurrent requests in dotc's presentation compiler, and how they share one symbol table safely.</p>

Interactive mode serves several requests at once against one symbol table. Each request has its own `Reader`; edits run alone, as write actions. Symbols still complete lazily, so one reader may need a completion that another is running.

The code: [retronym/scala3#84](https://github.com/retronym/scala3/pull/84), *Interactive: concurrent typechecking over one symbol table, K2-style (experiment)*. The concurrency primitives are [scala-sharing](https://github.com/retronym/scala-sharing), vendored into the compiler. This page's source: [retronym/talks](https://github.com/retronym/talks/tree/main/dotc-concurrency).

Below is one IDE scenario, run on the real compiler. Step with `,` and `.`. Each step names the mechanisms at work; each has a card below that shows what goes wrong without it.

## The scenario

### An IDE session, step by step

<div class="scenario"></div>

### The mechanisms

What each one does, the steps of the scenario where it acts, and its card.

<div class="mechanisms"></div>

Batch compilation chooses the single-reader mode once per `ContextBase` and runs the original code: under 2% overhead. Interactive overhead is minor, and typing scales to four threads and more.

## The mechanisms, one at a time

Each card shows one mechanism: first the Problem, the moment going wrong without it, then the Solution, the same moment with it in place.

### Claim on a completion root

<p class="lede">A claim is a capability: <code>Sharing.claim(key)</code> gives its body a <code>Holds[key.type]</code>, and <code>complete</code> requires one, so completing without the claim does not compile. A key computed per call, such as the TASTy file a completer reads, is claimed with <code>claimAt[K]</code> for a phantom family <code>K</code>: the state it guards is in <code>Claimed[K, T]</code> fields, which read and write only with a <code>Holds[K]</code>. The operations are inline methods, which keep a fast path for single-threaded compilation.</p>

<div class="scenario" data-card="claim"></div>

> A reader sees a symbol's info finished, or as a lazy type to wait on: never half-built, never mistaken for a cycle.

### Publish, then release

<p class="lede"><code>Published</code> and <code>Payload</code> are opaque types with macro operations. A store needs the <code>Publishing</code> capability of a <code>publishing</code> block; a read needs the period's <code>Acquired</code> evidence. The order is checked at compile time and costs one release store and one acquire load at run time.</p>

<div class="scenario" data-card="publish"></div>

> A reader that finds the period current sees everything stored before it.

### Stamped cells

<p class="lede"><code>Stamped</code> is an immutable pair, and <code>cached</code> is a macro on the field. The current stamp is a given <code>Stamp[K]</code> whose kind (per run, per period) is a phantom type, so call sites name no stamp and cannot mix kinds.</p>

<div class="scenario" data-card="stamped"></div>

> A cache hit returns a value computed at the stamp it was read with.

### Publish once

<p class="lede">No new primitive: build in locals, then store one value of final fields.</p>

<div class="scenario" data-card="once"></div>

> Readers see a shared structure whole or not at all.

### Write action and cancel

<p class="lede">A fair read/write lock and a volatile flag, polled at the typer's existing checkpoints. Batch compilation has neither.</p>

<div class="scenario" data-card="write"></div>

> Readers never see a half-done write; a writer waits only until each reader's next checkpoint.

### Owner cancelled mid-completion

<p class="lede">The unwound completion is just another lazy type; whoever reaches it is pre-empted.</p>

<div class="scenario" data-card="unwound"></div>

> A released claim leaves its symbol finished, or marked to start over. Nobody waits on abandoned work.

### Wait-for cycles

<p class="lede">No graph is stored: each reader publishes the claim it waits on, and a waiter follows owners from claim to claim.</p>

<div class="scenario" data-card="cycles"></div>

> No two readers wait on each other forever: one gives way, or a real cycle is reported as one reader would report it.

### Epoch invalidation

<p class="lede">An edge case. A published scope changes in only a few places: a package's flat classes, entered when first needed, or a classfile completer deleting symbols it found absent. (Synthetic function classes are kept beside <code>scala</code>'s scope.) With one thread, such a change walks and clears the dependent caches. With several readers it increments a counter on the base, and a cache is valid only while that counter is unchanged since the cache was made.</p>

<div class="scenario" data-card="epoch"></div>

> A cache is used only if no published scope has changed since it was made.

### Result stamps

<p class="lede">A volatile write count on the driver and a stamp per reader, compared once at the end of each request.</p>

<div class="scenario" data-card="resultstamp"></div>

> A result reaches the editor only if no write action ran since its request last held the lock.

## Finally: the whole compiler

### Every file of dotc, N readers

`compiler/src/dotty/tools/dotc/**/*.scala`: 491 files, 188k lines. One run opens them all (parse, index, skip every statement; serial), then N reader threads type them, each taking the largest file left. A recorded run, replayed on one clock, so more readers finish sooner. Press Play, or drag across the lanes.

<div class="throughput"></div>

Every N reports the same diagnostics as one reader, with no back-offs and no cycles. Waits on other readers' claims total a few milliseconds.
