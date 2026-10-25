# A more interactive Scala 3

A visual guide to a stream of work on Scala 3's presentation compiler ([retronym/scala3#84](https://github.com/retronym/scala3/pull/84), on top of [retronym/scala3#68](https://github.com/retronym/scala3/pull/68)): targeting, a session that serves many requests from one run, cancellable typechecking, and several readers over one symbol table modelled on Kotlin K2's lazy resolve and IntelliJ's read and write actions. Numbers are from the design notes (`interactive-session.md`, `interactive-multi-reader.md`) and Track I in `retronym/jvm-lang-models`, cited by section.

- `talk.md` is the source. Edit this.
- `make` builds `index.html` (needs only `python3`). `make watch` rebuilds on change.
- Open `index.html` directly in a browser; it works from `file://`.

## Authoring conventions

- `## ` starts a part (dark divider card), `### ` and `#### ` start a card. Number headings as `### 4. Title` so `§4` in the text becomes a link.
- `<!-- break -->` on its own line splits a long section into another card.
- Math: `$…$` inline, `$$…$$` display (KaTeX). Math inside backticks or fenced code is left alone.
- Diagrams: fenced ` ```mermaid ` blocks, or inline SVG inside `<figure class="fig">`. An HTML block ends at a blank line, so keep the SVG free of them; avoid `$` and `§` inside it. Reference links (`[text][KEY]`) work inside figure captions.
- SVG classes take the theme's colours: `box`, `typed`, `skip`, `own`, `wait`, `bad`, `pub` for shapes, `s-*`/`f-*` for strokes and fills, `c-*` for text; `legend` for a key.
- Chips: `{chip:B lazy fact}` renders a small label. A label starting with a letter A–E and a space is a kind of mutable state (one colour); anything else is a concurrency pattern (another). A chip first appears on the card that introduces its mechanism, and after that only on cards whose subject it is; wrap a row of them in `<div class="chips">…</div>` under the heading. The legend is the "How the labels work" card.
- Motion: give the figure `class="fig anim"`, and its elements `a-in`, `a-pop`, `a-grow-x`, `a-grow-d`, `a-draw` (with `pathLength="1"`), `a-out` (fades to `--o`), `a-slide` (from `--dx`), `a-drop`, `a-sweep` (to `--ty` over `--t`) or `a-blink`, each delayed by `--d`. Static styles are the final state: the steps play when the card comes into view or becomes current in focus mode, a replay control restarts them, and with reduced motion nothing moves.

## Viewing

- Sidebar table of contents; `j`/`k` or arrow keys move between cards.
- `f` toggles focus mode (one card at a time, larger type) for presenting; `t` toggles light/dark.
- Libraries load from cdnjs/jsDelivr, so the page needs network access.
