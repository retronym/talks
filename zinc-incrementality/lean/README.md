# Moved: the Lean model is in retronym/jvm-lang-models

The Lean model of Zinc's incremental compilation that lived here moved, with its history, to [retronym/jvm-lang-models](https://github.com/retronym/jvm-lang-models) on 12 October 2026. There it is split into packages for the JVM, Java, Scala, incremental compilation in general, Zinc, MiMa and IntelliJ's type system; its README is the map, and [`docs/history/repository-split.md`](https://github.com/retronym/jvm-lang-models/blob/4faa126ffd12acc1e45ac41c636751b26b863949/docs/history/repository-split.md) records the move.

The talks in this repository cite it at a pinned commit (the "**Lean model:**" line at the top of each `talk.md`), and `bin/lean_refs.py` checks that every Lean file, document and declaration they mention exists at that commit.
