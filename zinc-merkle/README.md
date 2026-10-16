# Merkle hashing and in-bridge hashing in Zinc

Talk on two changes to what Zinc stores and who computes it: Merkle name hashes (store each class's own declarations, compose the rest from its ancestors) and hashing in the compiler bridge. The PoC is [retronym/zinc#24](https://github.com/retronym/zinc/pull/24); the model is [retronym/jvm-lang-models](https://github.com/retronym/jvm-lang-models).

- `talk.md` is the source. Edit this. It is currently a first draft for review.
- [`PLAN.md`](PLAN.md) tracks the work behind it: the analysis notation and the tool that prints it, scripted tests, performance tests, demos.
- `research/` holds notes the talk draws on.
- `make` builds `index.html` (needs only `python3`). `make watch` rebuilds on change.
- Authoring conventions and viewing keys are as in `../zinc-incrementality/README.md`. In addition, ` ```zan ` fences are highlighted as the analysis notation of §3, and `<div class="cols">` holding two `<div>`s lays them out side by side. Chips under a heading say what the slide describes: `<p class="kind"><span class="chip today">status quo</span></p>`, with `poc`, `model` and `proposal` as the other classes.
