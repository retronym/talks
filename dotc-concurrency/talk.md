# Several readers, one symbol table

<p class="sub">How dotc's presentation compiler lets a hover, a background pass and the editor share one run, and the parts that keep it safe.</p>

Interactive mode serves several requests at once against one symbol table. Each request reads through a `Reader` of its own; edits arrive as write actions that run alone. Symbols still complete lazily, and a completion may be needed by a reader other than the one running it.

What follows is one IDE scenario, run for real on the compiler, with the code in the middle. Step through it with `,` and `.` or the buttons. Each cog lights up at the moment it does its job; a cog with a card links to it, where the cog is taken out to show what goes wrong without it.

## The scenario

### An IDE session, step by step

<div class="scenario"></div>

### The cogs

What each cog is for, and the steps of the scenario where it fires. The ones in grey are part of the model but have no moment of their own in this scenario.

<div class="gears"></div>

Batch compilation picks the single-reader mode once per `ContextBase` and runs the code it always ran: under 2% overhead. Interactively the overhead is minor, and the work scales well to four threads and more.

## The cogs, one at a time

Each card starts from the same file and takes one cog away: first the problem, then the mechanism, then the same moment with the cog in place.

### Claim on a completion root

<div class="scenario" data-card="claim"></div>

> A reader sees a symbol's info either finished, or as a lazy type it can wait on. It never sees another reader's half-built info, and never takes another reader's completion for a cycle.

### Publish, then release

<div class="scenario" data-card="publish"></div>

> A reader that finds a cached period current sees everything stored before it.

### Stamped cells

<div class="scenario" data-card="stamped"></div>

> A cache hit returns a value computed at the stamp it was read with.

### Write action and cancel

<div class="scenario" data-card="write"></div>

> Readers never see a write half done, and a writer waits only until each reader's next checkpoint.

### Owner cancelled mid-completion

<div class="scenario" data-card="unwound"></div>

> A released claim leaves its symbol finished, or marked so that the next reader to reach it starts over. No reader waits on work that nobody is doing.
