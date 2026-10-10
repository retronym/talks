# Phase 24 — member selection through extensions (`Extensions.lean`)

## Question

`x.m` with `x : T` and no member `m` in `T` resolves through an extension: a Scala 3 `extension` method, or a Scala 2 implicit class or conversion. The search looks in the lexical scope (block, imports, package objects, top-level definitions, wildcard-imported packages) and then in the implicit scope of `T` (its companion, its ancestors' companions). Two candidates at one nesting level are ambiguous. A member `m` later added to `T` itself takes precedence over every extension. An extension added anywhere the search looks changes what `x.m` means, or makes it ambiguous. Which of these does Zinc see?

## Model

`SpecGivens`' level-wise search (`gsearch`, an `XCompiler` whose keys read output and trace) with the extension's scope kinds. A layout is a list of scopes, each a kind and a nesting level:

| Kind | Pinned today | Package-level container |
|---|---|---|
| `member` (`T`'s own `m`) | yes (the client records `T` and the used name `m`) | no |
| `block`, `importQual` | yes (`Spec`'s import edges) | no |
| `companion` (`T`'s) | yes (keyed with `T`, `ExtraHash`) | no |
| `pkgObject`, `topLevel` | no | yes |
| `pkgImported` (in a wildcard-imported package) | no | yes, imported |
| `ancestorCompanion` | no | no |

Keys: `today` (the pinned scopes and the one the search resolved to); the G rule (`global`: every package-level container; `narrowed`: those of the searched packages, the wildcard-imported ones only with recorded package imports); `searched`.

## Results

| Result | Status |
|---|---|
| `ext_rule_obligations`: with the G rule, global or narrowed with recorded imports, the obligations hold for every layout without an ancestor companion, so T3a (`SpecGivens.g_global_obligations`, `g_narrowed_obligations` instantiated) | proved, every layout |
| `ext_today_pkgObject` (F2/G1 shape), `ext_today_topLevel` (G2): today's keys miss an extension added in a package object, or top-level in a new file, over the companion's | witnesses, kernel `decide` |
| `ext_narrowed_without_imports`: the narrowed rule misses a wildcard-imported package's extension unless the bridge records the import | witness |
| `ext_rule_ancestorCompanion`: even the global G rule misses an extension added to an ancestor's companion; that needs Phase 7's key (the ancestor companions, pinned) | witness |

So extensions add no new failure shape: they are names (`Names`' F1–F3) searched like instances (`Givens`' level-wise rule), and they meet the same keys. Precision is the G rule's: global invalidates every user of a package-level container on any change of its extensions; narrowed only those whose search reached the package, given recorded package imports. A member added to `T` shadows the extensions and is caught today (pinned, used name `m`).

## Probed (scala-cli, Scala 3.9.0 `extension`, Scala 2.13.16 implicit classes)

The result type of `t.m` inferred in `C` and checked from another object (an ascription directs Scala 3's search, so it cannot be the probe):

| Candidates | Scala 3.9.0 | Scala 2.13.16 |
|---|---|---|
| `T`'s own `m` vs an imported extension | member | member |
| an imported extension vs `T`'s companion | import | import |
| the client's own package (top level / package object) vs the companion | package | package |
| a wildcard-imported package vs the companion | the package | the package |
| two imports at one level | ambiguous | ambiguous |
| a block import vs an outer import | block | ambiguous |
| `T`'s companion vs an ancestor's companion | own companion | own companion |
| an ancestor's companion alone | ancestor | ancestor |

The model's layout agrees with all but two rows, neither of which changes a result. Scala 2's block import is not an inner level for implicit views: its whole lexical scope is one level, as `SpecGivens` already has it for Scala 2. And within the implicit scope, `T`'s own companion beats an ancestor's by specificity, where the level-wise search would report both as hits at one level. Coverage depends on the scopes asked (both are), not on which wins, so `ext_rule_obligations` and the witnesses are unaffected; only `today`'s resolved key differs, and `T`'s companion is pinned anyway.

## Predicted tests (written on retronym/zinc)

Each should fail on develop at its last step: an extension added to a package object over the companion's (`x.m` changes, Scala 2 implicit class and Scala 3 `extension`); a top-level `extension` in a new file (Scala 3); an extension in a wildcard-imported package's package object; an extension added to an ancestor's companion (`T extends P`, `object P { extension ... }`).

## Steps

- [x] P24.1 `Extensions.lean`: the scope layout on `SpecGivens`, the G rule's obligations, a witness per scope kind.
- [x] P24.2 Precedence probed (above).
- [ ] P24.3 The predicted pending tests on retronym/zinc.
