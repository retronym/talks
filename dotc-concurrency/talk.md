# Several readers, one symbol table

<p class="sub">How dotc's presentation compiler lets a hover, a background pass and the editor share one run, and the parts that keep it safe.</p>

Interactive mode serves several requests at once against one symbol table. Each request reads through a `Reader` of its own; edits arrive as write actions that run alone. Symbols still complete lazily, and a completion may be needed by a reader other than the one running it.

What follows is one IDE scenario, run for real on the compiler, with the code in the middle. Step through it with `,` and `.` or the buttons. Each cog lights up at the moment it does its job.

## The scenario

### An IDE session, step by step

<div class="scenario"></div>

### The cogs

Each cog fired in the scenario above. The ones in grey are part of the model but have no moment of their own in this scenario.

<div class="gears"></div>

Batch compilation picks the single-reader mode once per `ContextBase` and runs the code it always ran: under 2% overhead. Interactively the overhead is minor, and the work scales well to four threads and more.
