# Zinc: incrementality as a language-design concern

Talk for maintainers of the Scala compilers and adjacent tooling.

- `talk.md` is the source. Edit this.
- `make` builds `index.html` (needs only `python3`). `make watch` rebuilds on change.
- Open `index.html` directly in a browser; it works from `file://`.

## Authoring conventions

- `## ` starts a part (dark divider card), `### ` and `#### ` start a card. Number headings as `### 4. Title` / `#### 15b. Title` so `§4`, `§15b` and ranges like `§7–10` in the text become links. `### N1. Title` is linked by "Notes N1".
- `<!-- break -->` on its own line splits a long section into another card.
- Math: `$…$` inline, `$$…$$` display (KaTeX). Math inside backticks or fenced code is left alone.
- Diagrams: fenced ` ```mermaid ` blocks. Prefer `flowchart TB` or short `LR` chains; wide diagrams get scaled down.
- Other fenced code is highlighted with highlight.js (e.g. ` ```scala `).

## Viewing

- Sidebar table of contents; `j`/`k` or arrow keys move between cards.
- `f` toggles focus mode (one card at a time, larger type) for presenting; `t` toggles light/dark.
- Libraries load from cdnjs/jsDelivr, so the page needs network access.
