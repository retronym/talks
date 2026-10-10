# Phase 21 — derived API: export forwarders and used types' supertypes (`DerivedApi.lean`)

## Question

Two gaps where a client's answer is derived through a unit it never names. An export forwarder `B.f` has the signature of the exported `A.f`: a client of `B.f` reads `A`'s signature through `B` (BUG-MAP EX: scala/scala3#18216, partially #10182 and #11841). A client of `val p: P = B.x` with `B.x : A1` asks whether `A1 <: P`, answered from `A1`'s parents, and names neither `A1` nor its parents (U1: sbt/zinc#87, scala/bug#2558 for a structural type's members). In both the obligation that fails is coverage on the derivation's inputs.

## Model

Units: holders of a typed value (`val x: V`), classes with parents, a holder of a member with a signature (`A.f`), an exporter (`B` with `export A.*`), and two clients: one of the exporter's forwarder, one assigning `B.x` to a `P`. Queries: `typeOf`, `parents`, `sig` (a forwarder's), `baseSig` (the exported member's). Keys: per-unit class keys. Bridges: `today` (the exporter records nothing on `A`, the client records only the units it names); `fix` (the exporter records `A`, as #10182's export edge does; the client records the type of the value it used, as #87's types-in-used-names does).

## Results (`DerivedApi.lean`)

| Result | Status |
|---|---|
| `obligations_comp`: the two-stage joint compile (forwarders and clients read the round's fresh signatures) is a fixed point | proved, every program |
| `obligations_fix`, `fix_sound`: the exporter's edge to the exported object (#10182) and the used value's type (#87) meet the obligations, so T3a | proved, every program |
| `export_not_coverage`: before #10182 the exporter's `baseSig` query has no key | proved, one witness |
| `usedType_not_coverage`: before #87, `val p: P = B.x`'s `parents` query on `B.x`'s type has no key | proved, one witness |

Cost of the fix: an exporter now depends on everything it exports (a wildcard export is a dependency on the whole object, as an inheritance edge is), and a client depends on the type of every value it uses, which #87 already pays.

What the single-project instance cannot show, stated rather than proved: scala/scala3#18216 fails with #10182's edge present, across subprojects. Since the in-project case is sound here, the failure must be on the external path (`Classpath.lean`): an upstream member's signature change must reach the downstream exporter as it reaches an inheritor. #87 records the first hop; the supertypes beyond it reach the client through Zinc's inheritance invalidation of the used type (its API changes when an ancestor's does), which the instance does not model. Export chains (an exporter of an exporter) are outside the two-stage group.

## The clusters' scripted tests

On develop: `types-in-used-names-a`, `-b`, `struct`, `struct-usage`, `struct-projection`, `variance` pass (U1's first hop and structural members); `export-jars` is pending (exports across a jar boundary, the external path above).

## Steps

- [x] P21.1 `DerivedApi.lean`: the instance, obligations for the fix, the two counterexamples.
- [x] P21.2 The clusters' scripted tests mapped.
- [ ] Future: #18216 on `Classpath.lean`'s external invalidation; export chains.
