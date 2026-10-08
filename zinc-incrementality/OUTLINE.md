# Zinc: incrementality as a language-design concern

**Audience:** maintainers of scalac / dotc, IDEs (Metals, IntelliJ), build tools (sbt, Mill, Bazel, Pants, Gradle). They know the compilers; most don't know Zinc's internals.

**Thesis:** every language feature has an incrementality story, whether or not its designer wrote one down. Incremental soundness is a property of the *compiler's* API summary, which now lives in the compiler repos. So it should be designed, specified and tested alongside each feature, not reverse-engineered from user bug reports years later.

**Arc:**

1. What incremental compilation *is*, precisely (so "under/overcompilation" stop being vibes); what Zinc trades away for speed (hashes instead of resolution); and the premise it all rests on: separate ≡ joint compilation.
2. How Zinc approximates it, and three design choices worth arguing about: members vs decls, who computes the hashes, and what a used name is (name kinds).
3. How everyone else does it.
4. Where it breaks: worked examples (implicits, value classes, macros), then a taxonomy.
5. The machinery we maintain: bridge, tests, persisted state.
6. The cheapest incremental compile is the one you skip.
7. Can we prove it? A Lean model.
8. Asks.

**Suggested budget (~60 min):** I 12 · II 10 · III 3 · IV 14 · V 10 · VI 4 · VII 5 · close 2. Cut Part III to a single slide if time is short; Part VII can be a 2-slide teaser.

---

## Part I — First principles

### 1. The contract

- Program = set of sources `S`. Clean compile `C : P(S) → Out` (classfiles/TASTy + diagnostics).
- Incremental compile `I : (State, S', Δ) → (Out', State')`, where `State` summarises the previous run.
- **Correctness:** `I(…) ≡ C(S')` up to observational equivalence (bytes modulo known nondeterminism; same diagnostics).
- **Undercompilation:** `I ≢ C`, so it is unsound. **Overcompilation:** `I ≡ C` but the recompiled set `R` is much larger than the minimal `R*`, so it is sound but slow.
- Users experience both as "sbt is flaky", type `clean`, and stop trusting the tool. Undercompilation is a correctness bug; overcompilation is a perf bug that trains users to throw away the incremental state.

### 2. Summaries as abstractions

- For each class `c` the compiler extracts `API(c) = π(c)`, a projection of its typed definition; for each client `d`, the *used names* `U(d)`.
- **Soundness condition** (the one-line slide):
  `π_{U(d)}(c) = π_{U(d)}(c')  ⟹  C(d | c) = C(d | c')`
  In words: `π` must capture *everything a client's compilation can observe*.
- Every undercompilation bug is a counterexample: an observable not in `π`.
- Every overcompilation bug is the dual: `π` distinguishes things no client observes (positions, fresh names, iteration order).
- Precision/soundness lattice: coarser `π` gives sound but slow results; finer `π` is fast and correct only if every observable is captured.
- **Observables are closed under the backend.** The client's output is `g(typed(d))`, and codegen applies functions to referenced definitions: erasure `E`, name mangling, bridge and forwarder generation, boxing, constant folding. If `d`'s output depends on `f(c)` for one of these, then `π(c)` must determine `f(c)`.
  - For an ordinary class, `E(A) = A`: erasure is a function of the *name*, so a name-keyed `π` is enough.
  - For a value class, `E(A) = E(underlying(A))`: erasure is a function of the *contents*, and the name-keyed view breaks (§14b).

### 3. The algorithm: a fixed point over a dependency graph

- `R₀ = changed ∪ dependents-of-deleted`; compile `R_n`; diff APIs → `ΔAPI_n`; `R_{n+1} = invalidated(ΔAPI_n) \ ⋃ R_i`; stop at `∅`.
- Edges: `memberRef`, `inheritance`, `localInheritance`, `macroExpansion`; plus library dependencies, tracked by classfile/jar stamps.
- **Name hashing:** `API(c)` is split into `{ name ↦ hash }`; a `memberRef` client `d` is invalidated only if `U(d) ∩ changedNames(c) ≠ ∅`. Inheritance edges bypass the filter.
- `UseScope` (`Default`, `Implicit`, `PatMatTarget`) exists because "used name" alone is not enough. This is the first hint that some observables aren't names (§14–15).
- Granularity: source-level (sbt ≤ 0.13) → class-level (Zinc 1.0). Finer nodes give smaller `R` but more state, and more ways to be wrong.
- Escape hatch: past `transitiveStep` cycles, invalidate everything. The fallback is part of the semantics.
- Key point for this audience: `π` and `U` are computed *inside the compiler* (bridge phases `ExtractAPI`, `ExtractDependencies`). Zinc only does set algebra on them, so **incremental soundness is mostly a compiler property.**
- **Unconditional fallbacks in the invalidator** (`MemberRefInvalidator`) show where name hashing gives up and every `memberRef` client is invalidated: any change to an *implicit* member, any change in a file that *declares a macro*, any change in a file that declares an annotation. Each one is a confession that `U(d)` can't express the dependency (worked examples in §14).

### 4. Efficiency vs minimality: Zinc deliberately doesn't compute `R*`

- **True minimality is as expensive as compiling.** `d ∈ R*` iff `C(d | new) ≠ C(d | old)`. Deciding that exactly means re-running `d`'s compilation, or at least re-running every query `d` made and comparing the answers. Any practical incremental compiler computes a cheap, sound over-approximation of `R*`.
- **Zinc's approximations, each trading precision for cost:**

| Zinc does | Instead of (closer to `R*`) | Saves | Costs (overcompilation) |
|---|---|---|---|
| compares **hashes** of `π` (an `int` API hash, `int` per-name hashes) | structural diff of old vs new API | O(1) compare; small state; no old API kept (`APIUtil.minimize`) | can't tell *compatible* changes (widening, adding a default) from breaking ones; can't explain what changed without `apiDebug`. In theory 32-bit collisions are unsound; in practice negligible per comparison |
| invalidates `d` if it **uses name `n`** and depends on `c` | **re-resolve** `d`'s uses of `n` against the new `c` (overloads, qualifiers, overriding) | no per-use resolution data stored; no lookups at invalidation time | `size` on any receiver; overloads it never picks (§11) |
| hashes **all defs named `n`** together | per-overload / per-signature keys | additions are visible (§11) | any overload change hits every user of the name |
| **class** nodes, **source-file** recompilation units | member-level nodes | small graph | every class in an invalidated file recompiles |
| **inheritance** edges bypass name filtering, transitively | per-member override analysis | no override tracking | a change to any member reaches every heir |
| **materialises members as seen from `C`** and hashes them (§6–8) | resolve `C#m` through linearization on demand | invalidation never walks the hierarchy | `Σ |members|` extraction and state; N-fold re-detection |
| `transitiveStep` cap → recompile everything | keep iterating | bounded cycles | rare full rebuilds |

- **The one place Zinc *is* precise: early cutoff.** After recompiling `R_n`, propagation happens only if the *new* hash differs from the old. Without this, every edit would recompile the transitive dependents, as `make` would. With it, a body-only change stops after one cycle. (*Build Systems à la Carte* calls this early cutoff; §21.)
- **The pattern:** Zinc replaces *resolution* (an expensive semantic question about the new program) with *hash equality over a projection* (cheap and syntactic). Soundness comes from the projection covering everything resolution could depend on (§2). Precision is whatever survives that coarsening.

**Merkle hashing as the same trade applied to member resolution** (links to §9):

- Today `nameHash_C(n) = h(res_C(n))`, where `res_C(n)` is the materialised set of members named `n` as seen from `C` (after linearization, overriding and `asSeenFrom`). That is *resolution, precomputed and hashed*.
- The Merkle alternative is `nameHash'_C(n) = h(decl_C(n), ⟨(P_i, targs_i, nameHash'_{P_i}(n))⟩_{P_i ∈ parents(C)})`.
- **Sound:** `res_C(n)` is a function of `C`'s own decls named `n`, its parents with their type arguments, and the parents' resolutions of `n`. With `h` treated as injective, equal Merkle hashes imply equal inputs, which imply equal `res_C(n)`.
- **Not complete:** inputs can change while `res_C(n)` doesn't, e.g. a parent's `n` that `C` overrides, or a type-argument change irrelevant to `n`. That gives a little more overcompilation, the *same direction* as every other Zinc approximation.
- **Cheap:** `O(|decls| + |parents|)` per class, memoised per parent. No `asSeenFrom` of every inherited member, and no `Σ |members|` state.
- **Possible bonus (hypothesis, check against the invalidation logs):** if Zinc can re-evaluate `C`'s Merkle hash from stored ingredients when a parent changes, clients of `C` that use `n` can be invalidated in the *same* cycle as `C`. Today `C` must first be recompiled to discover that its materialised API changed, which costs one extra cycle per hierarchy level.
- Zinc already uses this pattern for traits: `extraHash` "folds in the parents' later". So Merkle composition is an extension of existing practice, not a new idea.
- **Slogan:** *Merkle hashing is to member resolution what name hashing is to symbol resolution.* Both are sound, hash-based over-approximations that are cheaper than doing the resolution.

### 5. The hidden premise: separate compilation ≡ joint compilation

*(Tangent, but it underpins everything else.)*

- An incremental compile **is** a separate compilation: `R` is compiled from source against *classfiles/TASTy* of `S \ R`. So `I ≡ C` silently assumes
  `C_sep(R | out(S∖R)) ≡ C_joint(S)|_R`, **byte for byte**.
- If that premise fails, the consequences are:
  - *spurious API diffs*, i.e. overcompilation that never converges ("recompiled `B` again, no source change");
  - *semantic* divergence: the program means something different depending on build history;
  - broken JAR-equivalence and remote caches (§20), because a Bazel cache hit and an sbt incremental build disagree on the bytes.
- **Why the two views differ in Scala:**
  - a symbol typed from source and a symbol unpickled from Scala signatures or TASTy are different objects. They differ in flags, completion order, inferred types, companion pairing and annotations;
  - Symbol ids leak into sort keys and fresh names (lambda-lift ordering by `Symbol.id`, [scala/scala3#7661](https://github.com/scala/scala3/issues/7661));
  - flags mutated by later phases leak into output: `InnerClass` access flags differed joint vs separate ([scala/bug#12085](https://github.com/scala/bug/issues/12085) → [scala/scala#9131](https://github.com/scala/scala/pull/9131));
  - still being found: TASTy sharing depends on type identity ([scala/scala3#26551](https://github.com/scala/scala3/issues/26551)); classfile member order and `InnerClasses` differ ([#26552](https://github.com/scala/scala3/issues/26552)); source-file order changes the result ([#10634](https://github.com/scala/scala3/issues/10634));
  - the backend's `companionSymbol` lookup observed stale classfiles ([scala/scala-dev#402](https://github.com/scala/scala-dev/issues/402));
  - reflective calls on structural types break under separate compilation ([scala/bug#11773](https://github.com/scala/bug/issues/11773)).
- **Java interop multiplies the problem.** scalac has *two independent front ends for Java*: `JavaParsers` (a signature-only parse of `.java`, used in joint/mixed compilation) and `ClassfileParser` (reading javac's output). They must agree, and often don't:
  - Constants: `static final` fields not folded to `ConstantType` from source ([scala/bug#5333](https://github.com/scala/bug/issues/5333), [#10410](https://github.com/scala/bug/issues/10410), still open).
  - Annotations parsed differently ([scala/bug#5699](https://github.com/scala/bug/issues/5699), [scala/scala3#10788](https://github.com/scala/scala3/issues/10788)).
  - Typing differs: `T[]` overriding needs `Array[T with Object]` vs `Array[T]` depending on joint vs separate ([scala/bug#4390](https://github.com/scala/bug/issues/4390)); Java inner classes get path-dependent types only under joint compilation ([scala/bug#11569](https://github.com/scala/bug/issues/11569)); record varargs work separately but not jointly ([scala/scala3#24167](https://github.com/scala/scala3/issues/24167)).
  - Every new Java language feature needs a `JavaParsers` port in *both* compilers: records ([scala/bug#11908](https://github.com/scala/bug/issues/11908), [scala/scala3#14846](https://github.com/scala/scala3/issues/14846)), sealed ([scala/bug#12159](https://github.com/scala/bug/issues/12159)), text blocks ([#12290](https://github.com/scala/bug/issues/12290)), value objects ([#13194](https://github.com/scala/bug/issues/13194), open).
- **Zinc makes the choice visible:** `CompileOrder` (`Mixed`, `JavaThenScala`, `ScalaThenJava`) chooses which Java view scalac sees. **Pipelining** (`-Ypickle-java`) *always* gives downstream the source view of Java, so pipelined and non-pipelined builds see different symbols for the same Java class.
- **The real invariant:** for every pos test, `compile({A,B})` and `compile(A); compile(B | A.class)` emit identical bytes for `B`, and the same holds with A in Java. Scala 3 has started enforcing this mechanically (`DeterminismTest`, [scala/scala3#26553](https://github.com/scala/scala3/pull/26553)); partest's `_1`/`_2` convention tests only that separate compilation *works*, not that it gives *identical* output.

---

## Part II — Three design choices worth arguing about: the shape of `π`, who hashes it, and what a "used name" is

*(Discussion section. Aim to provoke, not to conclude.)*

### 6. What ExtractAPI actually records

- A class's `Structure` has three parts (`xsbti.api.Structure`): `parents` (the *linearized* ancestor types, as seen from `C`), `declared`, and `inherited = nonPrivateMembers \ decls`. All are rendered *as seen from `C`* (Scala 2: `internal/compiler-bridge/.../ExtractAPI.scala` `mkStructureWithInherited`; Scala 3: `ExtractAPI.apiClassStructure`).
- Both the class's API hash (`HashAPI.hashStructure0`) and its name hashes cover `inherited`.
- It has been this way since 2009 (Mark Harrah, "linearization instead of parents and add inherited members for structure", [42c5d47b](https://github.com/scala/scala/commit/42c5d47b99f6d4ed215957d784934c3580c36968)).
- The code admits it in the doc comment: the class hash includes parents only by *name*, "so we must ensure changes propagate somehow", followed by a TODO asking whether parent hashes could be used instead.

### 7. Why it's done (what it buys)

- **Locality of dependencies:** a client of `c.m`, where `m` is inherited from `A`, depends on `C`'s API. A change to `A.m` shows up as a change to `C`, so no hierarchy walk is needed at invalidation time.
- **`asSeenFrom`:** in `class B extends A[Int]`, `def f: T` is observed as `f: Int`. Changing only `B`'s extends clause changes the members clients see, with no change to any decl.
- **Linearization:** adding an override in a mixin changes *which* member wins for `C`. A member-level view captures that; a decls-only view would have to recompute the linearization.

### 8. What it costs (what makes it non-local)

- **API(C) depends on C's whole ancestor closure.** Editing `A` changes the API hash and name hashes of *every* descendant. Each descendant then counts as "API changed", which drives another invalidation round over the descendants' clients.
- **Duplication of work:** inheritance invalidation is already transitive, so the same change gets re-detected N times, once per subclass. Invalidation logs become hard to explain ("why did `Z` recompile?" → because `Y`'s API changed → because `X` …).
- **Size:** state grows with `Σ_c |members(c)|`, not `Σ_c |decls(c)|`. Deep or wide hierarchies blow this up: collections, cake pattern, big framework traits, anything extending `java.util.AbstractList`. Analysis size, hashing and extraction time all scale with it. `inherited` is `lazy` in the schema for this reason; laziness was removed and then reverted ([371b374d](https://github.com/scala/scala/commit/371b374db34ade9ef3af927e9b95094995202cf0) / [b9bd9ecb](https://github.com/scala/scala/commit/b9bd9ecb53fbb7209d0bddc033c8dc8cefdca6ec)).
- **Extraction cost on every run:** `members` plus `asSeenFrom` for each compiled class, including members from library parents that can only change when the library jar changes.
- **Overcompilation amplifier:** any nondeterminism in rendering an inherited member (unstable owners, refinement type params: [sbt/zinc#1782](https://github.com/sbt/zinc/pull/1782), [scala/bug#6596](https://github.com/scala/bug/issues/6596)) is multiplied across every subclass.
- Traits make it worse in a different way: trait bodies leak into subclasses (fields, super accessors, mixin forwarders), so there is a separate `extraHash` / "trait breakers" channel for subclasses.

### 9. Alternatives to put on the table

- **Merkle composition** (worked out in §4): `nameHash'_C(n) = h(decl_C(n), ⟨(P_i, targs_i, nameHash'_{P_i}(n))⟩)`. The hash stays non-local but the *storage* and *computation* become local and memoised. This is what the bridge's TODO suggests. It is a sound over-approximation of today's materialised resolution. Open questions: self-types and refinements as parents; library parents (treat their hash as a constant keyed by the jar stamp); whether per-name composition is precise enough for `asSeenFrom`-heavy code (type-argument changes now move every inherited name).
- **Decls-only + hierarchy-aware invalidation:** record each `memberRef` against the *declaring* owner and the *receiver* type. When `A.m` changes, walk subclasses at invalidation time, the way some other IC systems compute "affected subclasses" (verify Kotlin IC before claiming). This moves `asSeenFrom` and linearization concerns from extraction into the invalidator.
- **Hybrid:** decls-only for classes whose parents are library types (which change only by jar stamp), member-level within the module.
- Discussion questions:
  - Is member-level storage a *soundness* requirement or a *convenience*? Which scripted tests break under decls-only?
  - What fraction of a real analysis file is `inherited`? (TODO: measure on scala/scala and on a large app before the talk; one number on a slide beats an argument.)
  - Scala 3 has TASTy: could `π` be derived from TASTy-level signatures plus a structural parent hash, making it shareable with IDEs and other build tools?

### 10. Who computes the hash? Bridge-side hashing vs projecting into `xsbti.api`

**Today's pipeline** (`AnalysisCallback.api`, then `Incremental.scala`):

1. The bridge projects compiler types into a full `xsbti.api.ClassLike` tree: every member including inherited ones, as seen from the class, with lazy fields.
2. It hands the tree to Zinc via `api(sourceFile, classApi)`.
3. Zinc computes `HashAPI` (the API hash), `NameHashing` (name hashes, partitioned by `UseScope`), and the trait `extraHash` (parents folded in later, already Merkle-style). It sets the `hasMacro` and `isAnnotationDefinition` flags.
4. Zinc then *throws most of the tree away*. Unless `apiDebug` is set, `APIUtil.minimize` keeps a stub with the name, modifiers, annotations, `savedAnnotations`, sealed children, top-level flag and type parameters.
5. `AnalyzedClass` persists the hashes plus that stub.

So for every compiled class, on every run, we build a large object graph mainly so it can be hashed and discarded.

**Alternative:** the bridge computes `{apiHash, nameHashes, extraHash, flags}` directly over compiler symbols and types, and sends opaque hashes. Zinc's invalidator already works only on hashes.

**What it buys:**

- **No intermediate representation:** no allocation, laziness or interning of `xsbti.api` trees. (TODO: profile the `xsbt-api` phase and the callback on scala/scala with async-profiler to put a number on it.)
- **Hash what codegen actually sees:** include erased descriptors directly, which closes the §14b class of bugs *by construction* (§2: `π` must determine `E`). Also inline bodies, sealed children and TASTy-level detail, without growing a cross-repo schema.
- **Memoise per symbol per run:** a parent's hash is computed once and reused by every subclass. That gives the Merkle composition of §9 without paying `Σ |members|`.
- **Less drift (§17):** a new observable becomes a compiler-local change. Today it can need an `xsbti.api` schema change, MiMa review, a Zinc release and two bridge releases.
- **Smaller analysis, faster loads (§19).**

**What it costs:**

- **Collateral consumers of the stored API:**
  - test discovery: `xsbt.api.Discovery` walks the minimized `ClassLike` (annotations, parents, `savedAnnotations`) for sbt's `definedTests`;
  - explaining invalidations: `apiDebug`, `APIDiff`, `ShowAPI` "what changed?" diffs;
  - any external tool reading `Analysis.apis` (verify Bloop/Mill/IntelliJ).
- **Mitigations:**
  - a separate thin *discovery* callback (class name, kind, parent names, class/def annotations, main methods — `mainClass` is already a callback), or discovery from classfiles the way JUnit-platform scanners do it;
  - for debugging, the bridge emits a canonical *text rendering* behind a flag and hashes that text, so the diff stays free.
- **Hashing is no longer shared code:** two bridges plus Zinc's Java path (`ClassToAPI`) each hash. Mitigation: a tiny stable `Hasher` in `compiler-interface`, so the compiler decides *what* to hash and Zinc owns *how* hashes are mixed.
  - Producers needn't agree with each other: a class's hash is only ever compared with its own previous hash from the same producer. A compiler-version change already forces a full recompile (`MiniSetup`).
- **The name-hash contract must be written down:** the `UseScope` partition, sealed handling, private-member rules. Arguably a feature (§16, §22).
- **Zinc can no longer fix a hashing bug without a compiler release.** But extraction bugs, which already require one, dominate the bug history (Part IV).

**Variant: derive `π` from outputs, not internals.**

- Hash the classfile ABI (`ijar`-style descriptors, per member) plus the signature payload (Scala sig / TASTy signatures).
- This is compiler-agnostic and erasure-correct by construction. Zinc 2.x's `bytecodeHash` / `transitiveBytecodeHash` already lean this way, replacing timestamps.
- It still needs the compiler for `U(d)` and for macro observation.

**The trade, stated for the room:** the `xsbti.api` tree is a *general* reflection of the type system that we pay for on every compile, while incremental compilation only needs a *hash* of it. If we optimise for incremental compilation alone, the tree is overhead, and test discovery should get its own narrow channel.

### 11. What is a "used name"? Name kinds and the key space of `U`

**What ExtractUsedNames records today** (Scala 2 bridge `ExtractUsedNames.scala`; Scala 3 `ExtractDependencies`):

- *Simple, decoded, unqualified* names, per using class, each tagged with a set of `UseScope`s (`Default`, `Implicit`, `PatMatTarget`).
- Names come from:
  - symbols in non-definition position;
  - **names of the types of trees**, including inferred ones (`types-in-used-names-*`, `as-seen-from-*` tests). That's why `C` "uses" `A` in §14b;
  - import selectors;
  - `TypeTree.original`;
  - pre-expansion macro trees (`OriginalTreeAttachments`);
  - pattern-match targets (`PatMatTarget`).
- Synthetic names are normalised: a constructor shows up as `A;init;` in the invalidation log.

**The invalidation key is a conjunction:** `d` is invalidated by a change in `c` iff `d →memberRef c` *and* `U(d) ∩ changedNames(c) ≠ ∅`. The name is not tied to its qualifier.

- If `d` depends on `c` for any reason and calls `.size` on *anything*, a change to `c.size` invalidates `d`.
- That is precision lost by design.

**Why simple names, not symbols?** Because the dangerous changes are *additions*, and you cannot record a dependency on a symbol that doesn't exist yet:

- a new overload `foo(Int)` changes the resolution of `foo(1)`, which used to pick `foo(Long)`;
- a new member shadows an import (§14a);
- a new override changes linearization (§7).

A name hash covers *all* definitions with that name in `c`, so adding one changes the hash. Simple names are the coarsest key that sees "something named `n` appeared or disappeared", which is a *negative lookup*.

**Name kinds: the conflations, and recent Zinc work:**

- **Class vs companion object.** `class A` and `object A` share one `AnalyzedClass`, and their name hashes are merged. Changing `class A.x` recompiles users of `object A.x` ([sbt/zinc#1796](https://github.com/sbt/zinc/issues/1796), open).
- **Inheritance edges had the same conflation:** `object B extends A` looked like `trait B extends A`, so a private change in `A` recompiled subclasses of `trait B` ([sbt/zinc#1795](https://github.com/sbt/zinc/issues/1795), fixed).
- **`AnalysisCallback4`** (commit 0a463347a) adds `ClassRef` (a name plus a `NameKind` of `Term` or `Type`) to dependency edges. It also adds a `usedName` overload carrying `qualifierKinds`: the namespace the name is *selected from* (class, object, or unknown, e.g. for an import selector). Zinc does not consume it yet; it is groundwork for #1796.
- **Still conflated:** whether the *referenced name itself* is a term or a type. A class mentioning only the type `A` is invalidated when the `object A` signature line changes. Cheap in practice, because each member has its own name hash and only the class/object header shares the name `A` (#1796, "related").

**The key-space ladder** (each rung is more precise and needs more from the compiler):

| Key | Example | Sound if… | Status |
|---|---|---|---|
| simple name | `x` | name hash covers all defs named `x` | today |
| name × `UseScope` | `x`@Implicit | scope-specific semantics are hashed separately | today (implicits → unconditional) |
| name × qualifier namespace | `x` from `object A` | companions get separate hashes | callback ready, Zinc pending (#1796) |
| name × referenced namespace | type `A` vs term `A` | term and type hashes are separated | open |
| (qualifier class, name) | `A#x` | *failed* lookups are recorded too (extension methods, implicit conversions: `a.foo` resolving elsewhere because `A` *lacks* `foo`) | not attempted |
| symbol | `A#x(I)J` | additions are impossible (closed world) | unsound for Scala |

**In the terms of §2 and §21:**

- `U(d)` is the abstraction of `d`'s query trace, and the name kind is the *key type*.
- Coverage requires every lookup, including failed ones, to map to a recorded key. The qualified rungs are sound only if the compiler also records *misses*: "looked for `foo` in `A`, didn't find it, fell back to an extension". That is a new bridge obligation, and it is exactly where Scala's extension methods, implicit conversions and `Dynamic` make lookup non-local.
- Precision improves monotonically down the ladder, but each rung adds a coverage obligation that an extractor bug can silently violate, turning an overcompilation fix into an undercompilation bug.

**Discussion:**

- Which rung pays for itself? Measure the share of invalidations caused by name collisions on unrelated qualifiers (e.g. `size`, `apply`, `map`) in a large build's invalidation logs.
- Should "failed lookup" be a first-class recorded event in both compilers? It would also make implicit/extension invalidation precise instead of unconditional (§14a).

---

## Part III — How we got here, and how everyone else does it

### 12. History (one timeline slide, three swim-lanes: algorithm · bridge · state)

- **2008–10:** scalac `-make`; "Incremental compilation is broken" ([scala/bug#354](https://github.com/scala/bug/issues/354)); Java/Scala deps ([scala/bug#2889](https://github.com/scala/bug/issues/2889)).
- **sbt 0.7–0.10 (Mark Harrah):** API extraction phase, source-level invalidation, member-level `Structure` (2009), and the bridge compiled from source per Scala version.
- **Standalone Typesafe `zinc`** (nailgun) serves Maven/Gradle/Pants; Pants contributes the interned analysis format (2013).
- **2013:** name hashing (Grzegorz Kossakowski): [`memberRef`/`inheritance`](https://github.com/sbt/zinc/commit/33635302cd73adbaf8c21476828bdae092610bc7), [algorithm](https://github.com/sbt/zinc/commit/e6c04434055657b679cbb50c2a1e6997a657b0f6). Later made the default (version: see TODOs).
- **2016:** class-based dependency tracking ([sbt/zinc#86](https://github.com/sbt/zinc/pull/86)); sealed hierarchies need [special handling](https://github.com/scala/scala/commit/14a5784fad6537a42cf67ae355122d3462cac1e3).
- **2017, Zinc 1.0** (Lightbend + Scala Center): Java API for build tools, protobuf analysis, relocatable/cached analysis ([#216](https://github.com/sbt/zinc/pull/216), [#218](https://github.com/sbt/zinc/issues/218)).
- **2019–20:** `VirtualFile` ([#712](https://github.com/sbt/zinc/pull/712)); build pipelining ([scalac `-Ypickle-java`](https://github.com/scala/scala/commit/b066d7e6402820879a970d6a88635018b8512dfe), [early output/analysis](https://github.com/scala/scala/commit/7b88ad4e5f2baba971a3461a45a19a090da319f1)); Dotty owns its bridge, `CompilerInterface2` ([scala/scala3#10607](https://github.com/scala/scala3/pull/10607)).
- **2023:** Scala 2 bridge moves in-tree in 2.13.12 ([scala/scala#10472](https://github.com/scala/scala/pull/10472)).
- **2024:** Consistent analysis format ([#1326](https://github.com/sbt/zinc/pull/1326)); hashes replace timestamps ([#1430](https://github.com/sbt/zinc/pull/1430)); Scala 3 pipelining ([scala/scala3#18880](https://github.com/scala/scala3/pull/18880)).
- **2025–26:** Zinc 2.x / sbt 2; a wave of Scala 3 macro, pattern-match and determinism fixes (§14–15).

### 13. Prior art: everyone converged on the same three ideas

ABI summaries · fine-grained use tracking · content addressing.

| System | Summary (`π`) | Use tracking (`U`) | Notable |
|---|---|---|---|
| GHC | `.hi` interface fingerprints | per-entity usages | cross-module inlining → unfoldings are part of the interface |
| Kotlin IC | ABI snapshots | lookup tracker (scope, name) | near-isomorphic to name hashing; `inline fun` bodies are ABI |
| Swift driver | `.swiftdeps` | fine-grained provides/depends | same name-filtered fixed point |
| rustc | query fingerprints, red/green | query dependency graph | demand-driven rather than phase-driven |
| Gradle (Java) | class ABI | class-level | historically full recompile on constant change |
| Bazel / Buck | `ijar`/`hjar`, ABI jars | target-level | skip the compiler entirely if ABI bytes are equal |
| TypeScript | `.d.ts` / `.tsbuildinfo` | file + signature hash | project references |

Best practices to extract:

- Derive summaries from the **same typed trees codegen sees**.
- Make summaries **canonical**: no positions, fresh names or iteration order.
- Treat **cross-module inlining as ABI**.
- Use **content hashes, not timestamps**; make state **relocatable and reproducible**.
- Keep a **differential oracle** (incremental ≡ clean) in CI.
- Log *why* each unit was invalidated.
- Offer a **one-command bug report** for a user who just hit under- or overcompilation, capturing enough state to replay the build as a test (Notes N2).
- Members-vs-decls (§6–9) is a place where systems diverge. Worth a row in the table once verified.

---

## Part IV — Where it breaks: language features vs incrementality

### 14. Three worked examples: implicits, value classes, macros

One slide each. Show the code, ask the room "what must recompile?", then show what Zinc records and why. All examples come from Zinc's own scripted tests (`zinc/src/sbt-test/`).

#### 14a. Implicits: resolution depends on names you never wrote

*Shadowing* (`source-dependencies/implicit-search`):

```scala
// B.scala
object B { implicit val x: Ordering[Int] = ??? }
// A.scala  v1: object A        v2: object A { val x = 1 }
// C.scala
object C { import A._, B._; implicitly[Ordering[Int]] }
```

- Adding an *unrelated, non-implicit* `val x` to `A` shadows `B.x` in `C`'s scope. The implicit is no longer eligible, so resolution silently falls back to `Ordering.Int`, and `C`'s behaviour changes (`???` stops throwing).
- Likely mechanism (verify with the invalidation log): `C`'s used names include `x`, the name of the implicit it selected. Eligibility is name-based, so name hashing happens to model it.

*Implicit scope through the type hierarchy* (`companion-object-implicit-scope`):

```scala
trait A; object A { implicit val sad: Pretty[A] = ... }
trait B extends A
class D extends B
object User { implicitly[Pretty[A]].show(new D) }
```

- `User` reaches `A`'s companion through implicit scope; adding an ordinary `def y` to `object A` recompiles 0 files, as it should.
- Removing `sad` must break `User`.

*Modifier as API* (`implicit-params`): making `(implicit y: E)` explicit must break the call site `x(3)`.

What Zinc does: implicit members get their own name hashes (`UseScope.Implicit`), and **any** change to an implicit member invalidates **all** `memberRef` clients of that class, with no name filtering (`MemberRefInvalidator`).

- That is sound only for classes the client already depends on. The *negative* case is open: a client whose resolution would change because a *new, better* candidate appears somewhere it never referenced. Removing `implicit` isn't noticed ([sbt/zinc#945](https://github.com/sbt/zinc/issues/945)); Scala 3 constructor implicits ([scala/scala3#18309](https://github.com/scala/scala3/issues/18309)).
- Scala 3 `given`s, `using` clauses, and `given` imports (`import A.given`) make implicit scope larger and more structured. Same problem, more surface.

#### 14b. Value classes: erasure makes representation observable

`source-dependencies/value-class-underlying`:

```scala
class A(val x: Int) extends AnyVal      // → class A(val x: Double) extends AnyVal
object B { def foo: A = new A(0) }
object C { val duck = B.foo; println(duck) }
```

- At Scala level, `B`'s API is unchanged (`foo: A`); `B.scala` isn't even edited. At the JVM level, `B.foo()I` becomes `B.foo()D`. `C`'s bytecode still calls the old descriptor, so it fails with `NoSuchMethodError`.
- **In the terms of §2:**
  - `C`'s output contains the descriptor `E(sig_B(foo)) = E(A) = E(underlying(A))`, so `C` observes `f(A) = underlying(A)`.
  - `π(B)` is unchanged, which makes this a counterexample to soundness if `C`'s dependency is keyed only on `B.foo`.
  - The observation reaches `A` *through* `B`'s signature, but it is about `A`'s contents, not about any member of `A` that `C` names. `C` never mentions `x`.
- **Fix:** make `π(A)`, under the *name* `A`, determine `E(A)`. ExtractAPI adds the underlying type to a value class's ancestor types (comment in `mkStructureWithInherited`), so the hash for name `A` changes.
  - This relies on `C` "using" the name `A`. It does, because used names come from *typed* trees, so the inferred type of `duck` counts.
  - The expected invalidation log: cycle 1 detects modified names `A`, `A;init;`, `x`; `B` and `C` are both invalidated because both use name `A`; cycle 2 finds nothing further.
- `source-dependencies/value-class`: toggling `extends AnyVal` on/off changes erased signatures of every method mentioning `A`. One case flips `null` from legal to illegal (`-> compile` expected); another is a pure binary change that must recompile to *run*.
- General lesson: `π` is a *Scala-level* summary, but clients link against *JVM-level* descriptors. Anything that changes erasure without changing the Scala signature needs a hook: value classes, opaque types (do they? discuss), `@specialized`, SAM vs non-SAM, varargs, Java generic signatures.

#### 14c. Macros: the expansion depends on whatever the macro looked at

*Macro inspects a type argument* (`macros/macro-type-change`):

```scala
def hasAnyField[T]: Boolean = macro hasAnyFieldImpl[T]   // reads weakTypeOf[T].members
class A                       // → class A { val hello = "" }
Macros.hasAnyField[A]         // false → must become true
```

- The client names only `A` as a type argument. The macro read `A.members`. Fixed by recording type arguments of macro calls as `DependencyByMacroExpansion` ([sbt/zinc#1316](https://github.com/sbt/zinc/pull/1316); Scala 3 port [scala/scala3#23900](https://github.com/scala/scala3/pull/23900)). That new edge kind was then silently dropped by the new analysis format until [#1432](https://github.com/sbt/zinc/pull/1432).

*Macro erases its argument's dependency* (`macros/macro-arg-dep`):

```scala
def printTree(arg: Any): String = macro ...   // expands to Literal(arg.tree.toString)
object Client { Provider.printTree(Foo.str) }  // remove Foo.str → Client must fail
```

- After expansion, the tree is a string literal, and the reference to `Foo.str` is *gone*. Dependency extraction must traverse the pre-expansion tree (the macro-expansion attachment), not only what typer left.

*The macro implementation changes*: any change in a file that declares a macro invalidates all clients unconditionally. Clients of a macro defined upstream additionally recompile transitively ([warning + opt-out](https://github.com/sbt/zinc/commit/083b432e9bbd91d5ae8ab4a227b85ccdfdef8e42)), which is sound but expensive ([sbt/zinc#1333](https://github.com/sbt/zinc/issues/1333)).

*Scala 3* (quotes reflection can walk anything):

- `macwire`'s `wire[Dep]` reads `Dep`'s constructor; changing it isn't detected ([sbt/zinc#1574](https://github.com/sbt/zinc/issues/1574), [scala/scala3#23852](https://github.com/scala/scala3/issues/23852), [#24969](https://github.com/scala/scala3/pull/24969)).
- Macro annotations' `transform` isn't tracked ([#22999](https://github.com/scala/scala3/issues/22999)).
- Feature request: "make Zinc Scala 3 macro-aware" ([sbt/zinc#1478](https://github.com/sbt/zinc/issues/1478)).

Discussion: the principled answer is to **record every symbol the macro observes** by instrumenting `Context`/`Quotes` reflection, and emit those as dependencies of the expansion site. This is a compiler-side change that only the compiler teams can make.

**Moral of 11a–c:** in each case the client's compiled output depends on information *not reachable from the names it wrote*. Implicit scope, erased representation and macro observation are the three big leaks, and each needed a special channel bolted onto name hashing.

### 15. A taxonomy (organise by *kind of observable*, not by feature)

**(a) Bodies that are API** — the client's bytecode embeds the implementation.

- Scala 3 `inline`: nested inline calls missed ([scala/scala3#11861](https://github.com/scala/scala3/issues/11861) → [#12931](https://github.com/scala/scala3/pull/12931)); inherited inline defs overcompiled ([62dfdaf6](https://github.com/scala/scala3/commit/62dfdaf6226db9cc4ef42b4534a4fe4904b9fda6)).
- Scala 2 `@inline` + `-opt:inline`: broken from 2018 to 2023 ([sbt/zinc#537](https://github.com/sbt/zinc/issues/537) → [#1310](https://github.com/sbt/zinc/pull/1310)).
- Constant folding (`final val`, Java `static final`).
- Trait bodies mixed into subclasses (`extraHash`).

**(b) Non-local or negative information** — meaning depends on what *else* exists, or on what *doesn't*.

- Sealed children determine exhaustivity; `useOptimizedSealed` broken on 2.13 ([sbt/zinc#1229](https://github.com/sbt/zinc/issues/1229)).
- Implicit/given resolution observes shadowing, implicit scope and the *absence* of a better candidate (§14a).
- Pattern matching observes `unapply` shape and arity: [scala/scala3#26231](https://github.com/scala/scala3/issues/26231) undercompiled in *every* Scala 3 version, giving `NoSuchMethodError` ([#26262](https://github.com/scala/scala3/pull/26262), 3.10.0-RC1).
- SAM conversion adds an inheritance edge the source never spells out ([sbt/zinc#830](https://github.com/sbt/zinc/issues/830) → [scala/scala#10617](https://github.com/scala/scala/pull/10617), [scala/scala3#16996](https://github.com/scala/scala3/pull/16996)).
- Inherited members (§6–9) belong in this category too, and are the *reason* `π` is member-level.

**(c) Generated code** — the expansion depends on things the call site never names.

- Macros, def and annotation, Scala 2 and 3 (§14c).

**(d) Synthetic owners** — definitions that don't map 1:1 to source classes.

- Exports ([scala/scala3#11841](https://github.com/scala/scala3/issues/11841)), top-level defs ([#18447](https://github.com/scala/scala3/issues/18447), [#13994](https://github.com/scala/scala3/issues/13994)), package objects, companion pairing.

**(e) Nondeterminism** — `π` changes when nothing observable did (overcompilation).

- Context-bound evidence names ([scala/scala3#19132](https://github.com/scala/scala3/pull/19132)), refinement owners ([sbt/zinc#1782](https://github.com/sbt/zinc/pull/1782)), [scala/scala3#26434](https://github.com/scala/scala3/issues/26434), [#25520](https://github.com/scala/scala3/issues/25520), whitespace changing line numbers ([sbt/zinc#718](https://github.com/sbt/zinc/issues/718)).

**(e′) Erasure and representation** — the JVM descriptor changes while the Scala signature doesn't: value classes (§14b), `@specialized`, varargs, Java generic signatures.

**(f) Cross-language and pipelining** — the two Java front ends (§5); — Java sources invalidated every cycle ([#918](https://github.com/sbt/zinc/issues/918), [#867](https://github.com/sbt/zinc/issues/867), [#1819](https://github.com/sbt/zinc/issues/1819)).

**(g) The compiler itself isn't robust to incremental inputs** — stale-symbol crashes ([scala/scala3#17152](https://github.com/scala/scala3/issues/17152), [#13532](https://github.com/scala/scala3/issues/13532)).

### 16. Incrementality is the forgotten dimension of feature design

- A SIP or feature PR covers syntax, typing, erasure, binary compatibility and TASTy compatibility, but never "which new observables does this introduce, and where are they hashed?"
- **Time-to-fix as evidence:** `@inline` + optimizer took 5 years; refinement-owner instability was open for years; Scala 3 patmat existed since 3.0 and was found in 2026.
- **Who finds these:** users of large builds and IDE vendors (IntelliJ runs Zinc in its IC tests, [scala/scala3#21179](https://github.com/scala/scala3/issues/21179)), not feature authors.
- **MiMa analogy:** MiMa made "is this binary compatible?" a mechanical PR-time check. We can do the same for incremental soundness.
- **Determinism is a shared precondition:** unstable synthetic names are both overcompilation bugs and reproducible-build bugs ([scala/scala-dev#405](https://github.com/scala/scala-dev/issues/405)).

---

## Part V — The machinery we maintain

### 17. The compiler bridge: architecture, relocation, drift

**Architecture (diagram):** `compiler-interface` (Java `xsbti.*`, stable, MiMa-checked) ⟵ *bridge* (compiler-specific: extraction phases + callbacks) ⟵ loaded by Zinc into the compiler's classloader. Originally Zinc shipped bridge *sources* and compiled them on first use per Scala version.

**Relocation:**

- 2016: [sbt/zinc#78](https://github.com/sbt/zinc/issues/78) proposes splitting interface and bridge out.
- 2019: first in-tree attempt closed for lack of motivation ([scala/scala#8531](https://github.com/scala/scala/pull/8531)).
- 2020: Scala 3's bridge is in-tree from the start.
- 2023: [scala/scala#10472](https://github.com/scala/scala/pull/10472). Code actions/quick fixes needed lock-step bridge changes; history kept via filter-branch ([80e8df93](https://github.com/scala/scala/commit/80e8df93f854e8bb5ba7971c2af4d85671ccda08)); precompiled bridge ships with 2.13.12 ([forum](https://contributors.scala-lang.org/t/scala-2-13-12-in-source-sbt-compiler-bridge-clarifications/6289)).
- Porting the scripted tests ([scala/scala#10554](https://github.com/scala/scala/pull/10554)) immediately found a missing invalidation ([scala/bug#12887](https://github.com/scala/bug/issues/12887) → [sbt/zinc#1268](https://github.com/sbt/zinc/issues/1268)).

**Benefits:** the bridge evolves with compiler internals; no compile-on-first-use; the people who own the language also own `π`.

**Drift risks:**

- **Three bridges** (Zinc's for ≤ 2.13.11, scala/scala's, scala3's) and three copies of the scripted suite. Fixes land in one place: forward-ports ([scala/scala#10542](https://github.com/scala/scala/pull/10542)); Zinc PRs now carry "may also need to be applied in scala/scala and scala/scala3" ([#1782](https://github.com/sbt/zinc/pull/1782)). A live example: forward-porting five Zinc bridge fixes (#1316, #1324, #1507, #1782, #1803) to `scala2-sbt-bridge` ([scala/scala#11287](https://github.com/scala/scala/pull/11287), open), while the same batch is backported to Zinc 1.x ([sbt/zinc#1838](https://github.com/sbt/zinc/pull/1838), [#1839](https://github.com/sbt/zinc/pull/1839)). One fix, four branches.
- **Version matrix** (Zinc × compiler). New `xsbti` APIs must degrade on old Zinc (the lazy `DiagnosticCode` trick, [scala/scala3#15565](https://github.com/scala/scala3/pull/15565); `CompilerInterface` vs `CompilerInterface2`, [#10816](https://github.com/scala/scala3/issues/10816)).
- **Implicit protocol:** callback ordering and completeness are unwritten (`dependencyPhaseCompleted` under pipelining, [scala/scala3#27139](https://github.com/scala/scala3/issues/27139) / [sbt/zinc#1823](https://github.com/sbt/zinc/pull/1823); `generatedNonLocalClass` regression breaking IntelliJ, [#21179](https://github.com/scala/scala3/issues/21179)).
- **Release coupling:** a bridge fix reaches users only with the next compiler release. Users on an old compiler never get it, even with a new sbt.
- **Packaging:** `scala3-sbt-bridge` was published depending on a never-published compiler ([scala/scala3#23604](https://github.com/scala/scala3/issues/23604)).
- **Design decisions get frozen:** members-vs-decls (§6–9) now needs coordinated changes in three repos plus Zinc's hashing.

**Mitigations:**

- Zinc runs its scripted suite against the *released* in-tree bridges, selected by label, with provenance checks (recent work on this branch).
- One canonical scripted corpus consumed by all three repos, instead of forks.
- Specify the callback protocol (ordering, mandatory callbacks per phase) and add a conformance test.

### 18. How Zinc is tested, and where the oracle is weak

- **Scripted** (`zinc/src/sbt-test/`): ~170 `source-dependencies/*` plus `macros`, `pipelining`, `apiinfo`, `reporter`. File swaps, `> compile`, `> checkRecompilations n A B`, `-> compile`. The oracle is hand-written expected recompile sets.
- **Bridge unit tests:** compile snippets, assert on extracted API, used names and class names; Hedgehog properties for analysis invariants.
- **Cross-version bridge tests:** rerun whenever a bridge changes.
- **Benchmarks:** `zinc-benchmarks`, including `AnalysisFormatBenchmark`.
- **Downstream:** scala/scala `sbtTest/scripted`, scala3 `sbt-test/` and `IncrementalCompileSimulator` ([#26262](https://github.com/scala/scala3/pull/26262)), IntelliJ IC tests, community build.
- **Weakness:** scripted checks *how much* was recompiled, not *that the result equals a clean build*.
- **Where bugs come from:** field reports from large builds, and lately LLM-driven exploration. Many of the autumn 2026 batch were found by LLM agents writing probing scripted tests (Notes N1). Field reports are hard to turn into tests because the user's pre-change state is gone (Notes N2).
- **Proposals:**
  - After every scripted step, also clean-build and compare outputs (differential testing).
  - Generate edit sequences by mutating upstream APIs (property-based or fuzzed), relying on deterministic output.
  - Generalise the Scala 3 simulator so feature authors can write `v1/v2/client` tests next to the feature.

### 19. Persisted state: analysis format history and performance

| Era | Format | Notes |
|---|---|---|
| sbt 0.13 | text + sbinary/Java-serialization shortcuts | slow, nondeterministic |
| 2013 | interned ([fa226927](https://github.com/sbt/zinc/commit/fa226927a5f176cc9367c15e1d3fcacb6a403cdd), Pants) | dedupe strings / API nodes |
| Zinc 1.0 | protobuf ([#268](https://github.com/sbt/zinc/issues/268), [#351](https://github.com/sbt/zinc/pull/351)) | versioned, relocatable via mappers |
| 2018–21 | protobuf tuning | slow writes ([#623](https://github.com/sbt/zinc/issues/623)); reads dominate no-op builds ([#984](https://github.com/sbt/zinc/issues/984)) → [#989](https://github.com/sbt/zinc/pull/989), [#995](https://github.com/sbt/zinc/pull/995) |
| 1.10 (2024) | **ConsistentAnalysisFormat** ([#1326](https://github.com/sbt/zinc/pull/1326), Stefan Zeiger) | structural, deterministic, binary + text from one impl |
| 2.0 | protobuf removed ([#1388](https://github.com/sbt/zinc/pull/1388)); reproducible flag; dummy output paths; content hashes | |
| 2026 | Java serialization dropped from text ([#1769](https://github.com/sbt/zinc/pull/1769)); quadratic API-node interning fixed ([c8376846](https://github.com/sbt/zinc/commit/c83768463adf0c0f5fdab7cf63027a0e3d9757e3)) | |

From #1326 (scala-library + reflect + compiler):

| Format | Write | Read | Size |
|---|---|---|---|
| sbt text | 1002 ms | 791 ms | ~7.1 MB |
| sbt binary (protobuf) | 654 ms | 277 ms | ~6.2 MB |
| Consistent binary | 157 ms | 100 ms | 3.1 MB |
| Consistent binary (unsorted) | 79 ms | — | ~3.8 MB |

- **Why read time matters:** on no-op and one-file builds, loading every module's analysis is the critical path. This is the *common* case.
- **Interning is the big win,** and it is big *because* `π` is member-level: the same inherited definitions repeat across every subclass (link back to §8).
- **Format bugs are IC bugs** (`DependencyByMacroExpansion` dropped on round-trip).
- **Determinism and speed didn't conflict.**

---

## Part VI — The cheapest incremental compile is the one you skip

### 20. Layers of avoidance

- **Don't run** (action-cache hit) ⊃ **don't compile the module** (ABI unchanged) ⊃ **compile a few files** (Zinc).
- **Hermetic builds** (Bazel, Pants, sbt 2 remote cache): inputs are content-addressed (sources + dependency ABI jars + flags). A hit means no Zinc at all.
- **JAR-equivalence / ABI jars:** if upstream's ABI jar (pickles/TASTy-only, Zinc early output, Bazel `ijar`) is byte-identical, downstream is skipped without even loading its analysis. This requires:
  - reproducible compiler output ([scala/scala-dev#405](https://github.com/scala/scala-dev/issues/405); absolute paths under `-Xcheckinit`, [scala/bug#12698](https://github.com/scala/bug/issues/12698));
  - reproducible jars (timestamps, entry order);
  - reproducible, machine-independent analysis ([#218](https://github.com/sbt/zinc/issues/218), `WriteMapper`, `VirtualFile`, hashes instead of timestamps). The consistent format was built for this: identical state gives identical bytes, so Bazel can skip ([#1326](https://github.com/sbt/zinc/pull/1326); author reports ~27k Bazel targets using it).
- **Pipelining:** downstream starts on upstream pickles before codegen; early analysis lets downstream name-hash against it.
- **Where Zinc still matters:** large single targets, IDE/BSP loops, the inner dev loop. There, `π`'s precision (and its size, §8) is what users feel.

---

## Part VII — Can we prove it? Towards a mechanised model (Lean)

### 21. Formalising incremental compilation

**Is there scope?** Yes, provided we prove Zinc's algorithm sound *relative to stated obligations on the compiler*, rather than verifying scalac. That is the useful deliverable anyway: the hypotheses of the theorem *are* the bridge spec that §16 and §22 ask for.

**The model of the compiler we need:**

1. **Compilation units with an explicit environment.** `compile : Unit → Env → Out`, where `Env` is the *interface* view of everything else, derived from outputs: `iface : Out → Env`. This makes separate compilation a definable notion.
2. **Compositionality axiom (§5):** `compile_joint S |_R = compile_sep R (iface (compile_joint (S \ R)))`, byte for byte. Mutually recursive units compile as one SCC; Zinc already compiles each invalidated set together. Every §5 bug is a violation of this axiom, so stating it is half the value.
3. **Purity.** The output is a function of the unit and the environment *answers* only: no `Symbol.id`, iteration order or other global state (§15(e)). Scala 2's mutable global symbol table is precisely a back-channel the model forbids. Stale-symbol crashes are what that back-channel looks like in practice.
4. **A query interface (the key modelling choice).** The compiler touches `Env` only through typed queries. Examples:
   - `lookup(scope, name)`;
   - `members(C)` / `decls(C)` / `parents(C)`;
   - `erasure(T)`;
   - `implicitCandidates(type, scope)`;
   - `sealedChildren(C)`;
   - `inlineBody(m)`;
   - `macroObserve(sym)`.

   Model compilation as a monadic task with dynamic dependencies, `F_d : (Query → Answer) → Out`, where queries can depend on previous answers. This is the *Build Systems à la Carte* framing (Mokhov, Mitchell, Peyton Jones, ICFP 2018), applied *inside* the compiler.
5. **Recorded keys.** The bridge records an abstraction of the query trace, `U(d) ⊆ Key`, and the API summary `π : Class → Key → Hash`.

**Theorems:**

- **T1 (trace soundness, essentially free):** if every query in `trace(F_d, env)` has the same answer in `env'`, then `F_d env = F_d env'`. Proof by induction on the task's query sequence. This is the "verifying traces" result.
- **T2 (Zinc soundness)** follows from two obligations on the bridge:
  - **Coverage:** every query `q` that `d` issues is covered by some key `k ∈ U(d)`. This includes *negative* queries (implicit search keyed on the scope, not the name; §14a) and *closure* queries (`erasure(A)` keyed on `(A, repr)`; §14b).
  - **Abstraction:** `π(c)(k) = π(c')(k) → answer_q(c) = answer_q(c')` for every `q` covered by `k`. Hashes are treated as injective, or collision-freedom is carried as a hypothesis.
- **T3 (fixed point):** the invalidation loop terminates (finite classes, monotone `R`, measure `|classes \ compiled|`). At termination, every unrecompiled unit's trace answers are unchanged, so by T1 + T2 + compositionality the result equals the clean build.
- **Overcompilation as a theorem about precision:** a minimality statement relative to `π` (no unit outside `R` has a changed covered key) is the formal version of "no spurious invalidations".

**What the model makes crisp:**

- **Members vs decls (§6–9)** becomes a question about *which query keys the compiler issues*: `members(C)` keyed on `C`, or `decls(P)` for each ancestor plus `parents(C)`. Both are sound if `U` records the matching keys; they differ only in precision and cost.
- **Name kinds (§11)** are the *key type* of the trace abstraction. Each rung of the ladder trades precision against a stronger coverage obligation (record misses).
- **Bridge-side hashing (§10)** is the natural reading: the compiler supplies `π(c)(k)` directly as a hash of the answer to the queries `k` covers.
- **Macros (§14c):** `macroObserve` queries must be recorded; "invalidate all clients" is the coarsest sound key, `⊤`.
- **Joint ≡ separate (§5)** is the compositionality axiom. Determinism is purity.

**A Lean 4 plan:**

1. An abstract model (Mathlib `Finset`, a free-monad or `StateT` encoding of tasks, well-founded recursion for T3): a few hundred lines.
2. Instantiate it on a toy object language with classes, inheritance, type-directed implicit lookup and an erasure function with value classes.
3. State the §14 examples as Lean `example`s. *Counterexamples* show that name-only keys are unsound for value classes and for implicit addition; repaired keys yield proofs. Each counterexample doubles as a scripted test.
4. Optional: connect to reality by checking the bridge's *recorded* keys against a query log instrumented in the real compiler. That is differential testing (§18) with the formal model as the oracle.

**Prior art to cite (verify the references before the talk):**

- *Build Systems à la Carte* — traces, minimality, early cutoff.
- Adapton (Hammer et al., PLDI 2014) and Salsa / rustc's query system — demand-driven incremental computation.
- Incremental λ-calculus / "A theory of changes for higher-order languages" (Cai, Giarrusso, Rendel, Ostermann, PLDI 2014).
- "What is Java binary compatibility?" (Drossopoulou, Wragg, Eisenbach, OOPSLA 1998) — descriptors and linking, the §14b world.
- CompCert's separate-compilation correctness work (Kang et al., POPL 2016) — the compositionality axiom, proved for C.

**Honest limits:**

- The model proves the *algorithm* sound given the obligations. It says nothing about whether scalac/dotc meet them; that remains a testing problem.
- The value is in turning tribal knowledge ("implicits invalidate unconditionally", "value classes fold their underlying type into ancestors") into named hypotheses that a feature author must discharge (§16).

---

## Close

### 22. Asks

1. An **incremental-compilation item in the SIP / feature-PR template:** what new observables, where hashed, which test.
2. **Differential tests** (incremental ≡ clean) in compiler CI, with a `v1/v2/client` harness next to the feature tests.
3. **One shared scripted corpus** and a **written callback protocol** across the three bridges.
4. **Determinism as a first-class requirement**, including **joint ≡ separate, byte for byte** (Scala and Java dependencies alike), checked over the whole pos test suite. It pays three times: overcompilation, reproducible builds, cache hits.
5. **Revisit `π`'s shape** (members vs decls, Merkle parent hashes, a TASTy-derived summary), and measure before deciding.
6. **Record failed lookups** in both compilers, so qualified used-name keys (§11) and precise implicit/extension invalidation become possible.
7. **Move hashing into the bridges** (opaque hashes over the callback), with a narrow discovery callback for test frameworks.
8. **Ship a one-command bug report and a CI canary** (clean-vs-incremental on a sample of builds) that emit ready-to-run scripted tests (Notes N2).
9. **Write the bridge obligations down as theorem hypotheses** (coverage and abstraction, §21), and try a small Lean model to see which ones we can actually state.

### 23. Questions to leave the room with

- Should `π` be *specified* (like TASTy) rather than "whatever ExtractAPI does"?
- Is member-level `π` a soundness requirement or an implementation convenience?
- Could IDEs (Metals, IntelliJ's bytecode-based IC) and build tools share one summary format?
- Should macro APIs (`Context`, `Quotes`) record what a macro observes, so that macro dependencies are exact rather than "invalidate everything"?
- Should scalac/dotc keep their own Java source parsers at all, or delegate Java signatures to javac (e.g. a Turbine-style Java header compiler producing classfiles up front) so joint and separate views share one front end?

---

## Notes (content that doesn't fit the arc yet)

### N1. The autumn 2026 fix wave, and LLMs as bug finders

Lukas Rytz and Jason Zaugg, roughly June–October 2026. Many of these already appear as examples above; the list is the raw material for a "what we found this year" slide.

**Undercompilation:**

- Scala 3 pattern match after case class/extractor change → `NoSuchMethodError`, in every Scala 3 version ([scala/scala3#26231](https://github.com/scala/scala3/issues/26231) → [#26262](https://github.com/scala/scala3/pull/26262)). Came with `IncrementalCompileSimulator`.
- Pipelining: a run can end before early TASTy is written, dropping Zinc callbacks ([scala/scala3#27139](https://github.com/scala/scala3/issues/27139)); `dependencyPhaseCompleted` was called before dependencies were sent ([#27125](https://github.com/scala/scala3/issues/27125)); Zinc now waits and announces "no early output" ([sbt/zinc#1822](https://github.com/sbt/zinc/pull/1822), [#1823](https://github.com/sbt/zinc/pull/1823), [#1817](https://github.com/sbt/zinc/pull/1817)).
- With `-Xjava-tasty`, dependencies of Java sources weren't sent to Zinc ([scala/scala3#27133](https://github.com/scala/scala3/issues/27133)).

**Overcompilation:**

- A comment-only edit to a trait recompiled its heirs ([sbt/zinc#1794](https://github.com/sbt/zinc/issues/1794) → [#1799](https://github.com/sbt/zinc/pull/1799)).
- Adding a member to an object recompiled classes inheriting its companion trait ([#1793](https://github.com/sbt/zinc/issues/1793) → [#1801](https://github.com/sbt/zinc/pull/1801)).
- A compound type in a member signature was recorded as inheritance ([#1798](https://github.com/sbt/zinc/issues/1798) → [#1803](https://github.com/sbt/zinc/pull/1803)).
- A private change in a trait recompiled classes that don't inherit it, from object/trait conflation ([#1795](https://github.com/sbt/zinc/issues/1795) → [#1807](https://github.com/sbt/zinc/pull/1807), `AnalysisCallback4`); the class/companion name-hash merge is still open ([#1796](https://github.com/sbt/zinc/issues/1796)). See §11.
- Trait `extraHash` over-invalidations ([#1787](https://github.com/sbt/zinc/pull/1787)); refinement-owned type params ([#1782](https://github.com/sbt/zinc/pull/1782)).
- Pipelining: any change recompiled everything depending on a Java class ([#1819](https://github.com/sbt/zinc/issues/1819) → [#1821](https://github.com/sbt/zinc/pull/1821)); a trait with a parent recompiled all heirs under Scala 3 ([#1820](https://github.com/sbt/zinc/issues/1820)).
- Intermittent overcompilation from `Symbol.copy` ignoring its compilation unit ([scala/scala3#25520](https://github.com/scala/scala3/issues/25520) → [#27162](https://github.com/scala/scala3/pull/27162)).
- Under `-release`, JDK classes were reported to Zinc as project classes ([scala/scala3#27117](https://github.com/scala/scala3/issues/27117)); the empty package was included in names of Java classes ([#27136](https://github.com/scala/scala3/pull/27136)).

**Test-infrastructure bugs (the oracle itself was wrong):**

- Scripted tests shared a directory ([sbt/zinc#1802](https://github.com/sbt/zinc/pull/1802)).
- `"scalaVersion": "2.13.y"` scripted projects never actually selected the in-tree `scala2-sbt-bridge` ([#1836](https://github.com/sbt/zinc/issues/1836) → [#1837](https://github.com/sbt/zinc/pull/1837)), so the in-tree bridge was untested by Zinc's suite. That is a drift risk realised (§17).

**The LLM angle (worth a slide):**

- Many of these were *discovered*, not just fixed, with LLM agents: they read the invalidator, hypothesise a conflation, write a minimal scripted test, and observe over- or under-invalidation in the log.
- The batch filed on 2026-09-14 (#1793–#1798) has that shape: one systematic probe per dependency kind.
- Rough signal from this repo: 27 of 106 non-merge commits since June 2026 carry an AI co-author or `Generated-by` trailer. That *undercounts*, since not every author adds trailers. (TODO: Lukas and Jason to confirm which bugs were agent-found and how.)
- **Why it works here:** incrementality bugs have a mechanical oracle (`checkRecompilations`, invalidation logs, clean-vs-incremental diffs), tiny reproducers, and a large but regular space of (feature × edit × dependency kind). That is ideal territory for agentic search.
- **Where it doesn't:** deciding the *right* key (§11) or obligation (§21) is still a design judgement. Agents found the conflations; humans chose `AnalysisCallback4`.
- **Tie-in with §16:** a feature author could ask an agent to "enumerate edits to this feature's definitions and check incremental ≡ clean" as part of the PR. That is a cheap version of the missing checklist item.

### N2. Best practice: a one-command under/over-compilation bug report

Problem: by the time a user notices undercompilation (a runtime `NoSuchMethodError`, or "works after `clean`"), the pre-change state needed to reproduce it is gone. So reports arrive as "sbt is flaky".

**What a good report command captures:**

- the previous and current `Analysis` (the consistent format is deterministic and text-renderable, so it diffs well);
- the source change set: VCS revision plus diff, or a content-addressed snapshot of changed sources kept by the build tool for the last N compiles;
- compiler and Zinc versions, bridge provenance, scalac options, compile order, pipelining flags;
- the invalidation log for the offending run (`relationsDebug`/`apiDebug`-level, as `checkInvalidationLog` uses);
- for undercompilation: a background or on-demand **clean compile of the affected module and a classfile diff**. The diff names the stale classes, and for each, the used names `U(d)` and the API diff of what changed. Either a name is missing (a coverage bug) or a hash didn't move (an abstraction bug), which are exactly §21's two obligations.

**Output:**

- a ready-to-run scripted test directory (sources before, `changes/`, `test` script, `incOptions.properties`), so a maintainer — or an agent (N1) — can minimise it;
- optionally anonymised: hash identifiers while keeping the structure.

**Canary mode:** in CI, sample a fraction of incremental builds and also run a clean build; on a mismatch, emit the report automatically. Field data then flows into the scripted corpus.

**Prior art to check:**

- `ninja -d explain` and Bazel's execution log / `--explain` (why something reran);
- Gradle build scans;
- Kotlin build reports;
- Swift driver incremental remarks;
- rustc's incremental debugging flags.

Most explain *overcompilation*; few help with *undercompilation*, which needs the clean-build diff.

---

## Appendix

### Demo candidates (pick 2)

- `@inline` + optimizer undercompilation (Scala 2, pre-1.10).
- Scala 3 `unapply` change → `NoSuchMethodError` (pre-3.10).
- Removing `implicit` goes undetected ([sbt/zinc#945](https://github.com/sbt/zinc/issues/945), still open).
- Value class underlying-type change → `NoSuchMethodError` with the ExtractAPI hook disabled (`value-class-underlying`).
- Joint vs separate: compile a Scala/Java pair both ways and `diff` the classfiles (`javap -v`); pick one of the open §5 issues.
- Members-vs-decls cascade: edit a root trait, show the invalidation log across a deep hierarchy.

### Diagrams to draw

- Compiler phases → bridge callbacks → Analysis → invalidation fixed point.
- `Structure { parents, declared, inherited }` for a 3-level hierarchy, highlighting the duplicated inherited members.
- Avoidance layers (action cache ⊃ ABI equality ⊃ Zinc).

### TODOs

- Measure the inherited-vs-declared share of the analysis (count definitions and bytes) for scala/scala and one large app.
- Verify how `memberRef` targets are chosen (declaring owner vs receiver type) in both bridges before presenting §9.
- Confirm the sbt version where name hashing became the default, and verify the Kotlin/Swift/GHC rows against current docs.
- Profile the cost of building `xsbti.api` trees (the `xsbt-api` phase plus the `api` callback) on scala/scala, to size the §10 win.
- Check which external tools read `Analysis.apis` or the minimized `ClassLike` (sbt `definedTests`, Bloop, Mill, IntelliJ).
- Verify the §21 citations (titles, venues, years).
