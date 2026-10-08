# Teaching IntelliJ the cake

Talk on the intellij-scala branch [`scala-typesystem-tck`](https://github.com/retronym/intellij-scala/tree/scala-typesystem-tck): fixing IntelliJ's false errors on cake-pattern Scala at the type operations that diverge from scalac, using a differential TCK against `nsc.Global`, scala/scala's own sources as a corpus, and a Lean model of `asSeenFrom` turned into runtime checks. Part VII is about the method: posing questions precise enough for an LLM agent to hill-climb, and catching the ways the score gets gamed.

- `talk.md` is the source. Edit this.
- `make` builds `index.html` (needs only `python3`). `make watch` rebuilds on change.
- Open `index.html` directly in a browser; it works from `file://`.

## Authoring conventions

- `## ` starts a part (dark divider card), `### ` and `#### ` start a card. Number headings as `### 4. Title` so `§4` in the text becomes a link.
- `<!-- break -->` on its own line splits a long section into another card.
- Math: `$…$` inline, `$$…$$` display (KaTeX). Math inside backticks or fenced code is left alone.
- Diagrams: fenced ` ```mermaid ` blocks.
- Other fenced code is highlighted with highlight.js (e.g. ` ```scala `).

## Viewing

- Sidebar table of contents; `j`/`k` or arrow keys move between cards.
- `f` toggles focus mode (one card at a time, larger type) for presenting; `t` toggles light/dark.
- Libraries load from cdnjs/jsDelivr, so the page needs network access.
