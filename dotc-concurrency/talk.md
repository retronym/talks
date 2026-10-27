# Several readers, one symbol table

<p class="sub">How dotc's presentation compiler lets a hover, a background pass and the editor share one run, and the parts that keep it safe.</p>

Interactive mode serves several requests at once against one symbol table. Each request reads through a `Reader` of its own; edits arrive as write actions that run alone. Symbols still complete lazily, and a completion may be needed by a reader other than the one running it.

The work is [retronym/scala3#84](https://github.com/retronym/scala3/pull/84), *Interactive: concurrent typechecking over one symbol table, K2-style (experiment)*.

What follows is one IDE scenario, run for real on the compiler, with the code in the middle. Step through it with `,` and `.` or the buttons. Each cog lights up at the moment it does its job; a cog with a card links to it, where the cog is taken out to show what goes wrong without it.

## The scenario

### An IDE session, step by step

<div class="scenario"></div>

### The cogs

What each cog is for, the steps of the scenario where it fires, and its card.

<div class="gears"></div>

Batch compilation picks the single-reader mode once per `ContextBase` and runs the code it always ran: under 2% overhead. Interactively the overhead is minor, and the work scales well to four threads and more.

## The cogs, one at a time

Each card starts from the same file and takes one cog away: first the problem, then the mechanism, then the same moment with the cog in place.

### Claim on a completion root

<p class="lede">In code, a claim is a capability: <code>Sharing.claim(key)</code> hands its body evidence of type <code>Holds[key.type]</code>, and a completer's <code>complete</code> asks for that evidence, so a completion run without its claim does not compile. Every such operation is an inline method whose batch branch is the original code, so the batch compiler pays a test of a final field and nothing else.</p>

<div class="scenario" data-card="claim"></div>

> A reader sees a symbol's info either finished, or as a lazy type it can wait on. It never sees another reader's half-built info, and never takes another reader's completion for a cycle.

### Publish, then release

<p class="lede"><code>Published</code> and <code>Payload</code> are opaque types over the plain fields, and their operations are macros. A payload store needs a <code>Publishing</code> capability that only the <code>publishing</code> block provides, and a payload read needs the <code>Acquired</code> evidence of the period: the order is checked at compile time and costs a release store and an acquire load at run time, nothing more.</p>

<div class="scenario" data-card="publish"></div>

> A reader that finds a cached period current sees everything stored before it.

### Stamped cells

<p class="lede"><code>Stamped</code> is a final class of two final fields; <code>cached</code> is a macro that reads and writes the field it is called on. The current stamp comes from a given <code>Stamp[K]</code> whose kind (per run or per period) is a phantom type, so a call site names no stamp and a field is never read with one kind and written with another.</p>

<div class="scenario" data-card="stamped"></div>

> A cache hit returns a value computed at the stamp it was read with.

### Publish once

<p class="lede">No new primitive: a value of final fields, built in locals and stored in one field. The Java memory model's rule for final fields does the rest.</p>

<div class="scenario" data-card="once"></div>

> A structure that readers share is seen either not at all or whole, never while it is being filled.

### Write action and cancel

<p class="lede">A fair read/write lock and one volatile flag, polled at the typer's existing checkpoints. Batch compilation has no driver and never sees either.</p>

<div class="scenario" data-card="write"></div>

> Readers never see a write half done, and a writer waits only until each reader's next checkpoint.

### Owner cancelled mid-completion

<p class="lede">No new machinery: the unwound completion is a lazy type like any other, and it pre-empts whoever reaches it through the slow path every lazy type already takes.</p>

<div class="scenario" data-card="unwound"></div>

> A released claim leaves its symbol finished, or marked so that the next reader to reach it starts over. No reader waits on work that nobody is doing.

### Wait-for cycles

<p class="lede">The graph is not kept anywhere: each reader publishes the claim it waits on in a volatile field, and a waiter walks owners from claim to claim at every slice of its wait.</p>

<div class="scenario" data-card="cycles"></div>

> No two readers wait on each other forever. A cycle that someone can give way on is broken by that reader; a real cycle between signatures is reported, as one reader would report it.

### Epoch invalidation

<p class="lede">One atomic counter on the base. A concurrent base pulls; a batch base keeps the push, chosen once by a final field of the base.</p>

<div class="scenario" data-card="epoch"></div>

> A cache computed from published scopes is used only while no published scope has changed since it was made.

### Result stamps

<p class="lede">A volatile count of write actions on the driver, and a stamp on each reader. The check runs once per request, at its end.</p>

<div class="scenario" data-card="resultstamp"></div>

> A result goes to the editor only if no write action ran between the last lock its request left and its delivery.

## Finally: the whole compiler

### Every file of dotc, N readers

The x-ray's throughput demo, replayed from a recorded run. Every file of the compiler is opened in one run (the open parses, indexes and skips every statement, serially), then typed by N reader threads, each taking the largest file left. The blocks share one clock, so more readers finish sooner; each N joins the plot when its last thread is done. Press Play, or drag across the lanes.

<div class="throughput"></div>

Every N gives the same diagnostics as one reader, file for file, with no back-offs and no cycles raised. The waits on another reader's claim are a few milliseconds in all.
