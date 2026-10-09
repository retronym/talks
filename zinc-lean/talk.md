# Whack-a-mole, mechanised: Zinc in Lean

**Status:** outline for review. Each card gives the section's *point*, the *evidence* (a Lean file, theorem or checked example, or "future work"), a candidate *slide* or snippet, and a *time* budget. No prose yet.

**Audience:** Scala tooling people: compiler, build-tool and IDE maintainers. They know Zinc as users and some of its internals, know dependent types and maybe Curry–Howard, but not Lean. So Parts I–II are a recap and the primer gets the extra time.

**Thesis:** incremental compilation is sound *relative to a small set of obligations on the compiler*. Writing those obligations down in Lean turned Zinc bug whack-a-mole into a loop: model a language feature as a new kind of query, re-prove the obligations or find the counterexample, check the model exhaustively, then test real Zinc against the model's program space.

**Where the Lean lives:** the full model stays in `../zinc-incrementality/lean/` (Lean and Mathlib `v4.34.1`, no `sorry`); Parts VIII–IX cite it by path. This talk gets its own Lake project, `zinc-lean/lean/` (**new work**), pinned to the same toolchain and Mathlib, holding simplified snapshots for the slides:

- `Primer/`: the P1–P4 snippets, no Mathlib imports.
- `V1/`: Parts V–VI. `Task` and T1; a typecheck-only toy (lookups with misses, implicits with shadowing, no erasure); `Compiler`, `Obligations`, `round`, `zinc`; T2, T3a, T3 and T4 as in the full model; name-only vs repaired keys as checked examples.
- `V2/`: Part VII. V1 plus codegen queries (erasure through a value class, one forwarder), a non-local hash and the stale-Δ counterexample, with one general compiler structure instead of three.

The snapshots are copies cut down for reading, not imports of the full model, so slides show short code. Each says in its header which full-model file it simplifies.

<!-- break -->

**Arc and budget (~55 min):**

| part | minutes |
|---|---|
| I. The problem, and Zinc (recap) | 4 |
| II. Whack-a-mole | 4 |
| III. Why formalise | 3 |
| IV. A Lean primer | 9 |
| V. A compiler as a query tree (typechecking a Scala subset) | 6 |
| VI. Zinc on top | 8 |
| VII. The backend and separate compilation | 6 |
| VIII. Language features grow the model | 6 |
| IX. What we got out of it | 7 |
| Close | 2 |

Cut order if short: VIII down to one feature (value classes), VII's projects card, IV's tactic card.

All Lean and tool output is shown as screenshots (infoview, terminal), not live.

---

## Part I — The problem, and Zinc

### 1. Incremental compilation has a one-line spec

- **Point:** an incremental build must equal a clean build. Undercompilation breaks that; overcompilation keeps it but is slow. Everything later is about that equation.
- **Evidence:** `zinc-incrementality` §1. In the model: `Compiler.clean` and the conclusion of `zinc_eq_clean_of_wf` / `zinc_eq_clean_of_explicit` (`Zinc/Uniqueness.lean`).
- **Slide:** $I(\mathit{State}, S', \Delta) \equiv C(S')$, with the two failure modes and what users do about each (type `clean`).
- **Time:** 0.5 min.

### 2. How Zinc approximates it

- **Point:** Zinc does not resolve anything at invalidation time. The compiler emits a per-class API summary $\pi$ and per-client used names $U(d)$; Zinc diffs hashes and loops to a fixed point. Soundness lives in what the compiler records, not in Zinc's set algebra.
- **Evidence:** `zinc-incrementality` §2–4 (the loop formula, name hashing, the `transitiveStep` fallback, round counts).
- **Slide:** the §3 loop diagram (compile $R_n$ → diff hashes → invalidate → stop when $\mathrm{inv}(\Delta_n) \subseteq R_n$) and the compiler/bridge/Zinc split diagram. A recap for this audience: dwell only on "Zinc does set algebra; the compiler decides what is recorded".
- **Time:** 2.5 min.

### 3. The premise underneath: separate ≡ joint

- **Point:** every incremental round is a separate compilation against classfiles/TASTy of the rest. If that isn't byte-identical to a joint compile, no invalidation scheme can help. This becomes an axiom in Part VI.
- **Evidence:** `zinc-incrementality` §6; a fresh instance: forwarder signatures depend on the batch (`compose[A]` vs `compose[A$]`), found by a classfile differential on Spark's catalyst ([scala/scala#11289](https://github.com/scala/scala/pull/11289), open).
- **Slide:** the joint vs separate diagram from §6, one line of `javap` diff.
- **Time:** 1 min.

---

## Part II — Whack-a-mole

### 4. Every feature adds an observable

- **Point:** undercompilation bugs come from observables the summary doesn't capture, and each language feature adds some: implicit scope, erasure through value classes, macro observation, pattern-matcher names, forwarders. They are found years later, one at a time, in user reports.
- **Evidence:** `zinc-incrementality` §15 (implicits, value classes, macros), §16 (taxonomy), §17 (time to fix: `@inline` + optimiser 5 years; Scala 3 patmat found in 2026), Notes N1 (the autumn 2026 fix wave).
- **Slide:** a timeline of feature → bug → fix pairs; each fix adds a special case in `ExtractAPI`/`ExtractUsedNames` or an unconditional fallback in `MemberRefInvalidator`.
- **Time:** 2 min.

### 5. The oracle is weak, so the moles hide

- **Point:** scripted tests assert *how much* was recompiled, not that the result equals a clean build. A stale mixin forwarder is usually invisible at runtime. Without a spec, a fix for one shape rarely says what else it covers, or what it misses.
- **Evidence:** `zinc-incrementality` §19 (the `merkle-trait-override` story); sbt/zinc#1844 closed as a point patch for a wider erasure problem (`zinc-incrementality` §15b).
- **Slide:** "what we lack": (1) a statement of what the compiler must record, (2) a way to tell whether a proposed rule is sound before shipping it, (3) a generator of tests that matter.
- **Time:** 2 min.

---

## Part III — Why formalise

### 6. Prove Zinc sound relative to the compiler, not the compiler

- **Point:** verifying scalac is out of reach and not the useful result. Proving Zinc's loop sound *given hypotheses about the compiler* is tractable, and the hypotheses are the deliverable: they are the bridge spec a feature author must discharge.
- **Evidence:** `Compiler.Obligations` (`Zinc/Model.lean`): `comp`, `coverage`, `abstraction`, plus `Policy.Sound`.
- **Slide:** the three obligations in one line each, before any Lean syntax. Then "each §15 bug is a violation of exactly one of them".
- **Time:** 1.5 min.

### 7. Why a proof assistant, and why Lean

- **Point:** three things at once from one artefact: proofs (the general theorems), computation (the toy compilers run, so counterexamples are concrete and checked), and a program generator (the model's program space drives real Zinc). Lean 4 is a dependently typed language that is also a decent programming language, and Mathlib supplies `Finset` and well-founded induction.
- **Evidence:** `lakefile.toml` (library + two executables: `exhaustive`, `conformance`).
- **Prior art (one slide):** *Build Systems à la Carte* (Mokhov, Mitchell, Peyton Jones, ICFP 2018: tasks, traces, early cutoff), Adapton and Salsa (demand-driven incrementality), Drossopoulou et al. on Java binary compatibility, CompCert's separate-compilation work (Kang et al., POPL 2016). (Verify citations; `zinc-incrementality` TODO.)
- **Time:** 1.5 min.

---

## Part IV — A Lean primer

Goal: the audience can read every later snippet. Four cards, each built on the talk's own definitions, not on generic examples. The snippets live in `zinc-lean/lean/Primer/` (**new work**) and appear as screenshots with the infoview beside them.

### P1. Types, inductives, functions

- **Point:** `inductive`, `structure`, pattern-matching `def`, `#eval`. Lean is a functional language first.
- **Evidence:** new `Primer/`: a two-class lookup with `Option`, e.g. `inductive Cls | A | B`, `def members : Cls → List (Name × Ty)`, `#eval lookup B .m`.
- **Slide:** 8 lines of Lean beside the equivalent Scala `enum`/`case class`/`match`.
- **Time:** 2 min.

### P2. Dependent types: a query whose answer type depends on the query

- **Point:** the one dependent type the model really needs. A compiler task asks typed queries; the answer type is a function of the query. This is the free monad of *Build Systems à la Carte*, with a dependent answer type.
- **Evidence:** `Zinc/Task.lean`, `Task`, `run`, `trace`.
- **Slide:**

```lean
inductive Task (Q : Type) (A : Q → Type) (α : Type) : Type
  | pure (a : α)
  | ask (q : Q) (k : A q → Task Q A α)

def run (e : (q : Q) → A q) : Task Q A α → α
  | pure a => a
  | ask q k => (k (e q)).run e

def trace (e : (q : Q) → A q) : Task Q A α → List Q
  | pure _ => []
  | ask q k => q :: (k (e q)).trace e
```

- Say: the next query may depend on the last answer (dynamic dependencies), which is why a trace is data, not a static list.
- **Time:** 2 min.

### P3. Propositions as types, proofs as programs

- **Point:** `theorem` is a `def` whose type is a `Prop`. Induction on `Task` *is* the proof that an oracle agreeing on the trace gives the same output. Curry–Howard, concretely, on a definition they just saw.
- **Evidence:** `Task.run_eq_of_trace` (**T1**, `Zinc/Task.lean`).
- **Slide:** the statement, then the proof with the `induction t with | pure | ask` skeleton highlighted; the tactic lines greyed out.

```lean
theorem run_eq_of_trace (t : Task Q A α) (e e' : Env Q A)
    (h : ∀ q ∈ t.trace e, e q = e' q) :
    t.run e = t.run e' ∧ t.trace e = t.trace e'
```

- **Time:** 2 min.

### P4. Tactics, `structure` of propositions, and `decide`

- **Point:** three tools used everywhere later. Tactics build proof terms interactively (show the infoview goal once). A `structure` whose fields are propositions is a spec (`Obligations`). `decide` / `native_decide` prove a decidable proposition by running it: this is how counterexamples become checked facts.
- **Evidence:** `Compiler.Obligations` (`Zinc/Model.lean`); every `example … := by native_decide` in `Zinc/Examples.lean`.
- **Slide:** a screenshot of the infoview mid-proof, from the T1 proof; one `example : … ≠ … := by native_decide`. One honest line: `native_decide` trusts the compiler (it adds the `Lean.ofReduceBool` axiom); kernel `decide` gets stuck on `Finset` here (`PLAN.md` step 8).
- **Time:** 3 min.

---

## Part V — A compiler as a query tree: typechecking a Scala subset

### 8. The per-unit compiler is a `Task`

- **Point:** model the compiler of one class as a query tree over the interfaces of other classes. Purity and determinism are free: the output is a function of the source and the answers, by the type. Scala 2's global symbol table, `Symbol.id` sort keys and iteration order are exactly the back-channels this type forbids.
- **Evidence:** `Compiler.unit : Src → Task (CUnit × Q) (fun p => A p.2) Out` (`Zinc/Model.lean`). Queries are addressed to a unit; a negative lookup is a query whose answer is `none`.
- **Slide:** the §22 query/answer diagram from `zinc-incrementality`, redrawn smaller.
- **Time:** 1.5 min.

### 9. A restricted Scala: classes, members, lookups with misses, implicits

- **Point:** a toy object language is enough to state real bugs. Classes with typed members and an `implicit` flag; bodies that select members and search for implicits over imports with shadowing. The shadowing check is itself a lookup, so a miss is recorded.
- **Evidence:** `Zinc/Toy.lean`: `Member`, `ClassDecl`, `Expr`, `Q` (`lookup`, `underlying`, `implicitCandidates`), `search`, `shadowed`, `compileBody`.
- **Slide:** `shadowed` and `search` (10 lines), with the matching Scala from `zinc-incrementality` §15a beside it.
- **Snapshot:** `Toy.lean` already includes erasure of value classes in `compileBody`. `V1/` has the typecheck-only slice (no `erase`, `Out` without descriptors); erasure comes back in `V2/` for Part VII.
- **Time:** 2.5 min.

### 10. Hierarchies: lookup is a walk

- **Point:** member lookup walks the linearization, with type arguments (`asSeenFrom`) and misses. That walk is where most of Zinc's design questions live (members vs declarations vs Merkle).
- **Evidence:** `Zinc/Hier.lean` (one type parameter, parents with type arguments, right-to-left walk with misses), `resolve`, `walkWith`.
- **Slide:** `A[T] ← B extends A[Int] ← C with M`, and the trace of `C.m` as a list of queries.
- **Time:** 2 min.

---

## Part VI — Zinc on top

### 11. State, round, invalidation, policy, loop

- **Point:** Zinc's loop is a few lines once the compiler is a `Task`: compile $R$ jointly, re-record keys from each unit's trace, diff hashes per key, invalidate the units holding a changed key, stop when $\mathrm{inv}(\Delta) \subseteq R$. Heuristics are a *policy* with one obligation.
- **Evidence:** `Zinc/Model.lean`: `State`, `round`, `changed`, `invalidated`, `Policy`, `Policy.Sound`, `zinc` (fuelled).
- **Slide:**

```lean
def zinc (S) (src) (P : Policy CUnit Out K) : ℕ → ℕ → Finset CUnit → State → Option State
  | 0, _, _, _ => none
  | fuel + 1, n, R, s =>
    let s' := C.round src R s
    let I := C.invalidated S R s s'
    if I ⊆ R then some s' else zinc S src P fuel (n + 1) (P n R s s' I) s'
```

- Say: fuel because the general loop need not terminate; soundness is stated for any run that returns `some`.
- **Time:** 2 min.

### 12. The bridge obligations

- **Point:** the three hypotheses, now in Lean. Compositionality is §3's premise in usable form (joint = fixed point of the per-unit tasks). Coverage: every traced query, misses included, has a recorded key. Abstraction: equal hash on a key gives equal answers to everything it covers.
- **Evidence:** `Compiler.Obligations` (`Zinc/Model.lean`).
- **Slide:** the `structure Obligations` with `comp`, `coverage`, `abstraction`, each annotated with the §15 bug family that violates it.
- **Time:** 1.5 min.

### 13. Theorems T1–T4

- **Point:** the loop is sound for any sound policy; the result is the clean build under one extra hypothesis; termination depends on the policy.
- **Evidence:**
  - T1 `Task.run_eq_of_trace` (trace soundness).
  - T2 `round_preserves` (`Zinc/Soundness.lean`): a round leaves exactly $\mathrm{inv}(\Delta) \setminus R$ dirty.
  - T3a `zinc_sound`: at termination, a per-unit fixed point.
  - T3 `zinc_eq_clean_of_wf`, `zinc_eq_clean_of_explicit` (`Zinc/Uniqueness.lean`).
  - T4 `zinc_some_of_monotoneFrom`, `zinc_some_of_explicit` (2 rounds), `zinc_some_of_wf` (height + 2) (`Zinc/Termination.lean`).
- **Slide:** a dependency graph of the theorems, each node with its file.
- **Time:** 1.5 min.

### 14. Two findings about Zinc from writing the proof

- **Point:** the proof found two things that were wrong or missing in our own understanding before any program ran.
  1. `transitiveStep` is what makes termination provable: Zinc subtracts $R_n$ only in the stop test, so the plain loop can revisit classes; from `transitiveStep` on the round set only grows.
  2. "Terminates ⇒ equals clean" is false without uniqueness of the fixed point: `A.x: typeof(B.y)`, `B.y: typeof(A.x)`. Two sufficient conditions, both Scala best practices: acyclic unit dependencies, or explicit result types (source-determined interfaces). This is the sbt/zinc#1284 / #1462 story.
- **Evidence:** `PLAN.md` "Two findings"; T3b `fixpoint_unique_of_wf`, `fixpoint_unique_of_explicit`; `zinc-incrementality` §3–4 corrected accordingly.
- **Gap:** the ping-pong non-termination of the plain policy is prose, not a Lean `example` (**future work**, listed in `zinc-incrementality` §22).
- **Time:** 1.5 min.

### 15. The first counterexample: name-only keys, and the repaired extractor

- **Point:** instantiate the abstract model with the toy, two extractors. Name-only keys fail the obligations, and the loop undercompiles; the repaired keys meet them, and T3/T4 apply.
- **Evidence:** `Zinc/Toy.lean` `not_obligations_nameOnly`, `obligations_repaired`; `Zinc/Examples.lean`: value class (§15b) undercompiles under name-only (`C` keeps `B.foo()I`), implicit addition undercompiles, shadowing is caught by the recorded miss; `repaired_sound`, `repaired_terminates`.
- **Slide:** the three-row table from `zinc-incrementality` §22 (name-only vs repaired), each cell an `example`.
- **Time:** 1.5 min.

---

## Part VII — The backend and separate compilation

### 16. Observables are closed under the backend

- **Point:** a client links against JVM descriptors, not Scala signatures. So $\pi$ must determine every backend function of what a client references: erasure, bridges, mixin and static forwarders. In the model these are just more queries, asked by codegen rather than the typer.
- **Evidence:** `Zinc/Toy.lean` `erase` (a dynamic chain of `underlying` queries); `Zinc/Flat.lean` codegen epilogue (mixin forwarders ask the trait for its declarations and earlier ancestors for presence; static forwarders ask every ancestor; `final` and kind in the header), `Fl_obligations`.
- **Slide:** a class's output = typer queries + codegen queries; the codegen ones are the ones Zinc forgot.
- **Time:** 2 min.

### 17. Non-local hashes, and the stale-Δ trap

- **Point:** materialised inherited members and Merkle hashes are *non-local*: $\pi_C$ reads ancestors. The round invariant still holds, but only if $\Delta$ is diffed over the affected units, not just the recompiled ones. Getting this wrong undercompiles, and the counterexample has two units.
- **Evidence:** `Zinc/NonLocal.lean` (`GCompiler`, T2′ `round_preserves`), `Zinc/Stale.lean` (`stale_unsound`, `stale_affected`), `Zinc/NonLocalAns.lean` (`NCompiler`, T2″, T3a″, answers that read several interfaces).
- **Slide:** the two-unit picture: `P` changes, `C`'s hash reads `P`, `C` not recompiled, nothing invalidated.
- **Snapshot:** the full model has three compiler structures (`Compiler`, `GCompiler`, `NCompiler`) with parallel theorem names. `V2/` has one, the `NCompiler` shape, with the local model as the case `hashDeps c = {c}`. An embedding lemma in the full model would make that a theorem (**future work**).
- **Time:** 1.5 min.

### 18. Members vs declarations vs Merkle, and the PoC (one slide)

- **Point:** three designs for hashing inherited members are three sound instances of one model; their differences in rounds and recompiles are computed, not argued. The Merkle PoC ([retronym/zinc#24](https://github.com/retronym/zinc/pull/24)) is the third design plus a table of descendant rules (header, overrides, conflicts, abstract, trait, mirror) that decide which subclasses recompile; Part IX's findings are mostly about those rules.
- **Evidence:** `Zinc/Hier.lean` scenarios (checked `example`s), `walkPolicy_sound`; `Zinc/HierSound.lean` `D_obligations`, `W_obligations`, `Mk_obligations`.
- **Slide:** left, the materialised vs Merkle diagram from `zinc-incrementality` §5; right, the PoC's headline (catalyst: adding a member to `TreeNode` recompiles 1,371 classes today, 420 with the PoC) and its rule names. The 3×5 computed table goes to a backup slide.
- **Time:** 1 min.

### 19. Separate compilation across projects as a policy

- **Point:** within a subproject Zinc has extra rules (transitive inheritance invalidation, the implicit fallback); across subprojects only recorded keys count. Model projects as a policy on one loop and the cross-project bugs appear, while the single-project runs stay clean.
- **Evidence:** `Zinc/Erasure.lean` and `Zinc/ImplicitScope.lean` (projects as policies; `report … (.proj twoP)` vs `(.proj oneP)` examples); compositionality as the axiom `comp`, proved as a lemma in each toy because interfaces there are source-determined (`Fl_comp`, `Is_comp`, `Toy.comp`).
- **Slide:** same edit, two layouts, two verdicts (from `ImplicitScope.lean`: develop across projects leaves `X` stale; one project recompiles it).
- **Time:** 1.5 min.

---

## Part VIII — Language features grow the model

The pattern for each feature: a new *query* kind → a new *key* kind → re-prove `Obligations` (or find the counterexample) → add a dimension to the program space → exhaustive check with per-key ablation → conformance cases for free. One card per feature; pick two if short.

### 20. Value classes and erasure

- **Point:** erasure-only edits reach descendants in two hops (the declarer must notice, then the descendant must). Each erasure input fails at a different hop, so each needs a different fix; the model compared five alternatives over the same space.
- **Evidence:** `Zinc/Erasure.lean`: `asf_of_decl`, `asfInh_of_declInh` (as declared determines as seen from), `Er_obligations`, `fresh_obligations`, `dep_obligations`, `dep_sound`; `lake exe exhaustive erasure` (189,888 legal pairs, 13 variants, 24 s): Scala 2 today 12,064 unclean, Scala 3 today 7,456, erased signature at definition 2,176, plus kind in the class-name hash 0.
- **Slide:** the erasure table from `zinc-incrementality` §22, three columns (generic, value class, intersection).
- **Outcome:** retronym/zinc#27 (kind in class-name hash) and #28 (erased signature as declared), open.
- **Time:** 2 min.

### 21. Macros: whole-class observation

- **Point:** a macro that reflects over `members` asks one query whose answer is every member along the linearization. As a key that's a non-local hash, so T2″ says $\Delta$ must range over descendants of the recompiled set, which is the PoC's macro-edge-from-descendants fix.
- **Evidence:** `Zinc/Flat.lean` `(c, all)` keys; `PLAN.md` Phase 5: dropping macro keys leaves 437,696 unclean runs; the conformance run found two things the model leaves out (stale stored external API, `macro-upstream-member-removed`, fixed in the PoC; a macro reading private members, `macro-observes-private-member`, outside any name-keyed cover).
- **Gap:** macro *expansion* and Scala 3 `inline` bodies are not modelled; only observation is (**future work**).
- **Time:** 1.5 min.

### 22. Implicit scope through an ancestor's companion

- **Point:** a client of `Show[C]` depends on the companion of every base class of `C` without naming them. The fix in sbt/zinc#1845 publishes a transitive summary. The model proves the recomputed form sound with no in-project rule, shows the stored form equals it on consistent states, finds that folding the summary into `apiHash` is necessary across projects, and finds the one remaining gap (an object's singleton type).
- **Evidence:** `Zinc/ImplicitScope.lean`: `is_obligations`, `is_sound`, `stored_eq_recomputed`, `consistent_of_upToDate`; checked examples for grandparent companion, type argument, three projects, the no-fold ablation and the object gap; `lake exe exhaustive implicit` (120 bases, 1,080 pairs: without the fold 312 unclean; fix as shipped 136, all object singletons; published for objects too, 0).
- **Slide:** the inheritance chain `A ← B ← C`, companions, projects `lib/mid/app`, and the three verdicts.
- **Time:** 1.5 min.

### 23. Trait fields and private members

- **Point:** a class that mixes in a trait implements its fields and private members, none of which is public API. The model shows the private channel is needed (48,000 unclean runs without it) and only for trait parents, which backs the PoC's `extraHash` change.
- **Evidence:** `Zinc/Flat.lean` (`Mod`, private members), `FlatRules` `traitPub`; `PLAN.md` Phase 5 table.
- **Time:** 1 min (first to cut).

---

## Part IX — What we got out of it

### 24. Theorems, as a spec

- **Point:** the obligations are a written spec for `ExtractAPI`/`ExtractUsedNames`, and each modelled feature is a proved instance. That changes the conversation on a PR from "does this test pass" to "which obligation does this discharge".
- **Evidence:** one row per `*_obligations` theorem: `obligations_repaired`, `D/W/Mk_obligations`, `Fl_obligations`, `Er_obligations`, `is_obligations`.
- **Slide:** a table: feature → query kind → key → obligations theorem.
- **Time:** 1 min.

### 25. Counterexamples that became Zinc changes

- **Point:** the model found unsound rules before they shipped, and justified narrower ones.
- **Evidence:**

| model finding | file / check | Zinc change |
|---|---|---|
| `abstract` rule as stated is unsound (minimal: deleting `B.m` must break `C`) | `FlatRules.lean` checked example; 672 → 0 unclean when widened | PoC fix + scripted test `merkle-abstract-ancestor` (retronym/talks#5) |
| header changes must reach *transitive* descendants | `Flat.lean` Edit 4 | PoC header rule |
| `trait` rule can be narrowed to direct mixins | exhaustive, 0 unclean | PoC switch to `traitDirect` (retronym/talks#8) |
| private trait members needed, trait parents only | 48,000 → 0 | PoC `extraHash` folds trait parents only |
| macro keys are non-local | T2″ + 437,696 ablation | PoC macro edges from descendants |
| erasure: two hops, kind in class-name hash | `Erasure.lean` | retronym/zinc#27, #28 |
| implicit summary must be folded into `apiHash`; object gap | `ImplicitScope.lean` | sbt/zinc#1845 (and an object follow-up) |
| Zinc's loop formula; uniqueness hypothesis | proof of T3/T4 | `zinc-incrementality` §3–4 corrected |

- **Time:** 2 min.

### 26. Exhaustive checks: bounded model checking by evaluation

- **Point:** proofs say "sound given a cover"; the exhaustive checks say *which* cover, by running every program in a bounded space under every rule set, with each rule ablated. A whole-space `native_decide` is too slow, so this is a compiled executable; each minimal counterexample is then a checked `example`.
- **Evidence:** `Exhaustive.lean`, `lake exe exhaustive` (main space 216,000 bases × 27 edits: none 3,874,336 unclean; default as stated 9,600; widened 0; ablations in `PLAN.md` Phase 5); `exhaustive erasure`, `exhaustive implicit`.
- **Slide:** the Phase 5 ablation table as a bar chart (log scale).
- **Honesty line:** these are executions, not theorems; the space is bounded; hashes are modelled injectively.
- **Time:** 1.5 min.

### 27. Conformance: real Zinc against the model's program space

- **Point:** the model generates programs; a harness renders them as Scala, builds incrementally and clean, and compares classfiles byte for byte. Each disagreement is either a Zinc bug or a model gap, and both happened.
- **Evidence:** `Conformance.lean` (`lake exe conformance` → JSON lines with the model's verdict); the harness in [retronym/zinc#25](https://github.com/retronym/zinc/pull/25) (`sbt.internal.inc.bench.Conformance`, covering-array order finds each known family within 7–436 cases).
- **Findings in Zinc:** upstream class becomes a trait, client keeps `invokevirtual` (baseline, and PoC split layout; `merkle-x-header-kind`); stale bridge `StackOverflowError` (PoC, `merkle-x-abstract-bridge`); `final` parent not rejected (baseline); `erasure-bridge-upstream-grandparent` (baseline, split only); a pipelining revert (`pipelining-failed-upstream-revert`, pending).
- **Findings in the model:** a deferred declaration hides a concrete one in its own ancestors; a selection's answer must include the receiver's kind (retronym/talks#8).
- **Slide:** the loop diagram: Lean space → JSON → Scala → Zinc inc vs clean → diff → (Zinc fix | model fix) → back to Lean.
- **Time:** 2 min.

### 28. Limits

- **Point:** say plainly what's not claimed.
- **Evidence (from `zinc-incrementality` §22 and `PLAN.md`):** the model proves the algorithm, not that scalac meets the obligations; `S` is fixed (no added/deleted units, no source→class mapping); libraries and pipelining absent; precision is examples, not theorems (P2.6 parked); hash collisions out of scope; `transitiveStep` modelled as one step of dependents.
- **Time:** 0.5 min.

---

## Close

### 29. What's next, and the ask

- **Point:** the cheapest next step for compiler teams is to adopt the obligations as the review checklist for features, and to run the conformance harness (or a source-file space) when a feature touches $\pi$.
- **You can do this too, with help:** the model, the harness and most fixes were built with LLM agents doing much of the Lean and the test-writing. A model like this is within reach of a feature author, not only of a verification specialist.
- **Future work worth naming:** precision theorems for the hierarchy designs; SCC-closed initial invalidation (would T3 hold without acyclicity?); a non-termination witness; instrumenting the compiler to log queries and checking recorded keys against `coverage` (differential testing at the level of obligations).
- **Time:** 2 min.

---

## Notes for Jason

### D. Demos, as screenshot sequences (pick two)

1. **A counterexample by evaluation.** In VS Code with the infoview, open `FlatRules.lean` at the `abstract` example; flip `abstractAll` from `true` to `false` and watch `reportR … = some ⟨[C], 2, true⟩` go red, then `#eval` the `false` case to show `⟨[], 1, false⟩`. Under 10 s once the file is elaborated; pre-build with `lake build`.
2. **A proof breaks where the key is missing.** In `Toy.lean`, map `keyOf .underlying` to `.name x` instead of `.self` and show `coverage_repaired` (hence `obligations_repaired`) failing with the uncovered `underlying` query in the context. *To verify:* that the failing goal is readable on a slide; may need a smaller primer copy.
3. **`lake exe exhaustive erasure`** live: 24 s, prints the 13-variant table. Safe and visual.
4. **The conformance harness finding a Zinc bug** (pre-recorded): `lake exe conformance > cases.jsonl`, then the harness on the baseline with `--order covering`, stopping at the class-becomes-trait divergence; show the `javap` diff (`invokevirtual` vs `invokeinterface`). Too slow (sbt) to run live.

My pick: 1 and 4 (one in Lean, one in Zinc), with 3 as a fallback. All are captured as screenshots or a short terminal recording, not run live: for 1 and 2, the infoview before and after the edit; for 3 and 4, the terminal output.

### C. Cleanup and new work before this is presentable

- **New Lake project** `zinc-lean/lean/` with `Primer/`, `V1/`, `V2/` (see the top card), green with `lake build`.
- **An embedding lemma** in the full model, so `V2/`'s single compiler structure is justified rather than asserted.
- **Naming:** theorem names are inconsistent across files (`round_preserves` in three namespaces, `Fl_`/`Er_`/`is_` prefixes, T2′/T2″ in docs). A table mapping slide names → Lean names may be enough; renaming is optional.
- **Stale docs:** `zinc-incrementality` §22 says "~1100 lines" (now ~8,300 across `Zinc/*.lean`); `PLAN.md` P6.6/P6.8 cite `wit_obligations`, `wit_sound`, `vEdge_obligations`, `vEdge_sound`, which no longer exist after P6.9's restructure (now `Er_obligations`, `fresh_obligations`, `dep_obligations`, `dep_sound`).
- **Missing results the talk would like:** the non-termination `example` for the plain policy; precision inclusions for the hierarchy designs (P2.6); added/deleted units.
- **Snapshot the numbers:** the conformance PR (retronym/zinc#25) and the PoC (#24) are moving; freeze a commit for the talk's tables.
- **Lean highlighting:** highlight.js has no Lean grammar, so Lean blocks render plain in `template.html`. Add a small language definition, or accept plain.
- **Diagrams:** theorem dependency graph (§13), conformance loop (§27), two-hop erasure (§20).

### Q. Decisions (2026-10-09)

1. **Audience:** Scala tooling. Parts I–II are a recap; the primer gets the minute.
2. **Overlap with `zinc-incrementality` Part VII:** leave it until this talk is fleshed out.
3. **Lean location:** the full model stays in `zinc-incrementality/lean/`; this talk adds `zinc-lean/lean/` with `Primer/`, `V1/`, `V2/` snapshots.
4. **Screenshots**, not live Lean.
5. **Merkle PoC:** one slide (§18).
6. **Agents:** one line, "you can do this too, with help" (§29).
7. **Title:** "Whack-a-mole, mechanised: Zinc in Lean".

Still open: should a check keep the `V1/`/`V2/` theorem statements in step with the full model, or are they frozen copies? Frozen is simpler; the risk is a slide showing a statement the model has since generalised.
