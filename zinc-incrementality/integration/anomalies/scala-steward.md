# IncBench anomalies: scala-steward-org/scala-steward

- **Build:** scala-steward at `main` (shallow clone, 2026-10-19), Scala 2.13.18 with `-Xsource:3-cross`, module `core` (188 sources, 79 dependency jars: cats-effect, http4s, circe with semiauto derivation, fs2, ...). An application-style tagless-final codebase.
- **Run:** `lockstep --verify --profile`, the three cells as in `cats.md`, with `recompileOnMacroDef=true` (sbt's default; confirmed in every cell's generated `incOptions.properties`). Clean build ~2.9 s warm. Edit script: `edits/scala-steward.tsv`. Results: `~/code/.integration/campaigns/2026-10-20-scala-steward-macrodef-true`. Rerun of the first campaign's steps (which ran with `false`): every step, verdict and recompile count is identical, so the setting changes nothing on this build (no macro definitions in the module). Timings were taken on a loaded machine and are provisional.

## Steps

| Step | released | perf | merkle | Verdict |
|---|---|---|---|---|
| version-prerelease-body | 1 | 1 | 1 | same |
| update-add-member | 1+1 (10 cl) | 1+1 | 1+2 (10 cl) | same |
| nurture-private-member | 1 | 1 | 1 | same |
| forgetype-add-case | 1+12 (45 cl) | same | same | same |
| groupid-add-implicit | 1+37 (79 cl) | same | same | same |
| util-package-object-add-def | 1+2 | 1+2 | 1+2 | same |
| data-package-object-body | 1 | 1 | 1 | same |
| repocache-add-field (circe `deriveCodec` user) | 1+11 | same | same | same |

Every step and revert verified `same` on every Zinc.

## Anomalies

No correctness anomalies, and nothing beyond what each edit warrants. Two things worth noting:

1. **Adding an implicit is still coarse (all Zincs).** `groupid-add-implicit` (add `implicit val groupIdShow: Show[GroupId]` to `GroupId`'s companion) invalidates every member-ref dependent of `GroupId`, 37 sources, because `MemberRefInvalidator` invalidates unconditionally on any implicit name change. Only code that searches for an implicit whose type could match `Show[GroupId]` can be affected. Same rule as cats anomaly 2's cascade, where it multiplies a hash instability. Not a bug; a candidate for a narrower rule (e.g. invalidate users of `GroupId` that also use the name of the implicit's type constructor, `Show`) if anyone wants to work on implicit invalidation.
2. **Merkle's trait-private-member rule shows up in miniature (Merkle).** `update-add-member` (add `def zincCheck` to `sealed trait Update`): Merkle reports `Update.Single` as `TraitPrivateMembersModified` with no names and recompiles 2 sources in cycle 2 instead of 1 (same 10 classes in total). The mechanism is cats anomaly 3: a subtrait's extraHash moves with its parent's public API.

## Performance

- Zinc's own time is a large share on small steps: `data-package-object-body` spends 10 ms in scalac and 60-90 ms in Zinc (31 ms of it writing the analysis).
- Merkle's `analysis` phase is much higher than the others' on every step of the first campaign (e.g. 206 vs. 19 ms on `groupid-add-implicit`). That is not attributable to Merkle: the pinned cells carry a harness bug (IncHandler used an uncached `Locate.definesClass`, fixed in rz#71 4cba55a47) that adds about 100 ms per step to every Merkle cell. The rerun's timings are provisional (loaded machine) and are not compared.
