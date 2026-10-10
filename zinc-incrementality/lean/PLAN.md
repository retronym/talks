# Zinc soundness in Lean 4 — plan

A small Lean 4 + Mathlib model of §22 of `talk.md`: Zinc's invalidation loop is sound *relative to stated obligations on the compiler bridge*. Nothing here verifies scalac; the hypotheses of the theorems are the deliverable. They are the written spec for `ExtractAPI` / `ExtractUsedNames`.

## Status: proved generally, and checked on a space

The model is a specification (`DESIGN-spec.md`). A compiler is an instance of the framework: its algorithm is a task whose trace is what compilation read, and its bridge is `keys`, `π` and `covers`. Zinc's soundness (T3a, and T5 across subprojects) follows from three obligations on that instance. A family of incremental-compilation bugs is a failed obligation with a witness; a fix is a key with the obligations proved.

Enumerations over bounded program spaces (`native_decide`) and the Zinc conformance harness check the instances against scalac, dotc, javac and Zinc, and measure costs. They are checks, not theorems. `REVIEW-2026-10-11.md` reviews the framework and lists what to do next.

| Phase | Topic | Proved, for every program | Checked on a space, or by the harness |
|---|---|---|---|
| 1 | The framework | T1 `Task.run_eq_of_trace`; T2 and T3a (`Soundness`); T3b, incremental equals clean under acyclic dependencies or source-determined interfaces (`Uniqueness`); T4, termination per regime (`Termination`); the toy's obligations (`Toy`) | §15a/§15b counterexamples (`Examples`) |
| 2 | Members, declarations, Merkle | `NonLocal` (T2′, non-local hash); `Stale.obligations`; `HierSound`: `D_obligations`, `W_obligations`, `Mk_obligations` | scenarios 1–3 (`Hier`); `Stale.stale_unsound` |
| 3 | The Merkle PoC's design | `NonLocalAns` (T2″, T3a″); `Flat`: `Fl_obligations`, `flat_sound` | the rule table over 7,500 programs (`FlatRules`, `lake exe exhaustive`); the conformance harness |
| 6 | Erasure through inheritance | `Erasure`: `asf_of_decl`, `Er_obligations`, `dep_obligations`, `dep_sound` | `lake exe exhaustive erasure`; the scripted cases |
| 7 | Implicit scope across projects (sbt/zinc#1845) | `ImplicitScope`: `is_obligations`, `is_sound`, `stored_eq_recomputed` | `lake exe exhaustive implicit` |
| 8 | Classpath, pipelining, keys from the tree | T5 `Classpath.downstream_sound`; `Tree` (T2, T3a for keys from the output); `Snapshot.obligations`; `Pipelining.early_agreement`; `Inline.obligations_withBodies`, `not_obligations_today` | refresh after revert (`Snapshot`), failed upstream (`Pipelining`), `pipelined_ne_final` (`Inline`) |
| 9 | Termination, additions, sealed | `PingPong.zinc_diverges` (no `transitiveStep`: Zinc's loop need not terminate); `Embed.lift_obligations`, `zinc_lift`; `Added.obligations_fixed`, `not_obligations_today`; `Sealed.obligations_withChildren`, `not_obligations_noChildren` | `transitiveStep_stops` and the run (`PingPong`); `Added`, `Sealed` scenarios |
| 10 | Name resolution and implicits (`PLAN-names.md`) | `SplitProof.Spec`: `rules_obligations`, `global_obligations`, `narrowed_obligations` (given recorded package imports); witnesses F2, F3, narrowed without imports; precision (`necessary_invalidated`, `searched_exact`, `narrowed_le_global`, `rules_over`); F4/F5 as `joint_not_comp`. `GivensSpec`: the G rule's obligations, witnesses G1, G2; `decls_violates_abstraction` | resolution per version, F6, F7, recompiled sets, cost (`Names`, `Givens`, `NamesRules`); the harness on develop and #34 |
| 11 | Scala 3 `inline` and opaque types (`PLAN-inline.md`) | being moved to an instance | the families I1–I3, O1 and the fixes (`InlineOpaque`); the harness, both layouts |
| 12 | Java in mixed builds (`PLAN-java.md`) | `JavaSpec`: `obligations_fix`, `fix_sound`, witnesses J1–J4; `JavaSealedSpec` | `JavaNames`, `JavaSealed`; the harness |
| 13 | The split layout (`PLAN-split.md`) | `SplitProof`: `proposed_sound`, `cheap_sound_of_local`; `Spec`: `today_not_obligations`, `cheap_not_obligations`, `cross_obligations`, `cross_downstream_sound` (T5) | `Split.check_*` (the slot language matches the concrete model on the bases); the harness |
| 14 | Compile order and pipelining (`PLAN-order.md`) | `JavaOrder`: `obligations_mixed`, `mixed_sound`, `exclusion_exact`, `flip_spurious`; witnesses V1, V2, O1, O2 | none needed so far |

Phases 4 and 5 are design notes; their results are in phases 6 to 8.

No `theorem` is proved by `native_decide`: the enumerated facts are `example`s (`InlineOpaque.lean`'s with talks#25). CI (`.github/workflows/lean.yml`) lints this (`scripts/lint_native_decide.py`) and checks that the core theorems T1–T5, per framework variant, use only `propext`, `Classical.choice` and `Quot.sound` (`scripts/Axioms.lean`, `scripts/check_axioms.py`). `PingPong.zinc_diverges` had leaned on `native_decide` through its step lemmas; they are now kernel `decide`.

Every witness and obligation in the table uses kernel `decide` or a proof.

## Two findings from working out the proof (for the talk)

1. **Zinc's loop formula in §3/§4 is slightly off.** In `IncrementalCommon.invalidateAfterInternalCompilation`, the subtraction `-- recompiledClasses` is only in the *stop test*. The next round is the full `inv(ΔAPI_n)` (plus macro/collision extras), so:

   $$\text{stop iff } \mathrm{inv}(\Delta\mathrm{API}_n) \subseteq R_n, \qquad R_{n+1} = \mathrm{inv}(\Delta\mathrm{API}_n)$$

   and from `transitiveStep` on, $R_{n+1} = \mathrm{closure}(\mathrm{inv}(\Delta\mathrm{API}_n)) \cup R_n$, which is *monotone* and therefore terminates in at most $|S|$ rounds. So the brute-force regime is not just a heuristic; it is what makes termination provable without any assumption on the dependency graph. The plain regime needs an acyclicity assumption (below). Worth fixing in §3, §4 and §22.

2. **T3 needs a hypothesis the talk doesn't list: uniqueness of the fixed point.** At termination the state is a per-unit fixed point of separate compilation: every unit's output equals its own compilation against the interfaces of the current outputs. The clean build is *also* such a fixed point (that is the compositionality axiom). But fixed points of separate compilation need not be unique when units are mutually recursive: `A.x: typeof(B.y)`, `B.y: typeof(A.x)` has any type as a solution, and joint compilation picks one (or reports a cyclic reference). That is exactly the sbt/zinc#1284 "include mutual dependencies in initial invalidation" story. Two sufficient conditions, both corresponding to real Scala best practices:
   - **acyclic**: the traced dependency relation between units is well-founded (no mutual recursion across separately compiled units);
   - **explicit interfaces**: `iface (compile s e)` depends only on `s`, not on `e` (explicit result types on public members, §4). This also bounds the loop at 2 rounds.

   Either closes the gap; the plain T3 statement is false without one.

## Encoding choices

| Concern | Choice | Why |
|---|---|---|
| Tasks with dynamic dependencies | Free monad `Task Q A α` with `pure` and `ask (q : Q) (k : A q → Task)` — a query tree | T1 needs the *trace* as data; `StateT`/`ReaderT` over an oracle only gives the extensional function `Env → Out`, which cannot express "the answers on the trace". Induction on the tree *is* T1. Answers are dependently typed per query (`lookup` returns `Option Type`, `underlying` returns `Option Type`, …). |
| Compilation units | A type `CUnit` with `DecidableEq`, `S : Finset CUnit` | `Unit` clashes with Lean's unit type. Added/deleted units are future work; `S` is fixed. |
| Queries and keys are *per unit* | `Query := CUnit × Q`, `Key := CUnit × K`, `covers : Q → K → Prop` | Mirrors Zinc: `U(d)` is a set of (class, key) pairs and `π : Class → Key → Hash`. A multi-scope lookup is a sequence of per-scope queries, which is also how Zinc records it (one `memberRef` edge per class). Negative lookups are ordinary queries whose answer is `none`. |
| Environment | `Env := (q : Query) → Ans q`, built as `envOf (I : CUnit → Iface)` with `answer : Iface → (q : Q) → A q` | Purity is built into the model: `Out` is a function of `Src` and the answers only. There is no other channel. |
| Joint compilation | A black box `group : Finset CUnit → (CUnit → Src) → Env → (CUnit → Out)` plus the compositionality axiom, not a `Task` | The talk's formula has the group result on the right-hand side; the usable form is "joint compilation of G is a fixed point of the per-unit tasks, with group-mates answered from their fresh interfaces". The per-unit task is what the bridge traces (Zinc records `U(d)` per class even for internal dependencies), so T1 only needs the per-unit `Task`. |
| Hashes | Abstract `Hash` with `DecidableEq`; abstraction is a hypothesis | In the toy instance `Hash` is the projected answer itself, so abstraction is *proved* rather than assumed (perfect hashing). Collision-freedom stays an explicit hypothesis of the abstract theorem, as in §22. |
| Invalidation policy | A parameter `next : ℕ → State → Finset CUnit` with one obligation: `next ⊇ inv(Δ) \ R_n` | Soundness holds for *any* over-approximating policy, which is how the heuristics should be read: `transitiveStep`, `recompileAllFraction` and macro-downstream only enlarge the set. Termination is proved per policy. |
| The loop | Fuel-bounded `zinc (fuel : ℕ) : State → Option State` | The general loop need not terminate (ping-pong between mutually recursive units is consistent with the model). Soundness is stated for any run that returns `some`; termination theorems say which fuel suffices. Fuel also keeps everything computable for `decide` on the examples. |
| Decidable examples | `CUnit := Fin n`, names as a small inductive, `example : zinc … ≠ clean … := by decide` | Each counterexample is a scripted test. `native_decide` as fallback if the kernel is slow on `Finset` of structures. |
| Mathlib | `Finset`, `WellFounded`, `Finset.card` measures | Tag `v4.34.1` matches the installed toolchain. The `lake exe cache get` download is 1–2 GB. |

## Definitions (file `Zinc/Task.lean`, `Zinc/Model.lean`)

```lean
inductive Task (Q : Type) (A : Q → Type) (α : Type)
  | pure (a : α)
  | ask (q : Q) (k : A q → Task Q A α)

def Task.run (e : (q : Q) → A q) : Task Q A α → α
def Task.trace (e : (q : Q) → A q) : Task Q A α → List Q

structure Compiler where
  CUnit Src Out Iface K Hash : Type        -- (bundled as parameters in practice)
  Q : Type;  A : Q → Type
  unit   : Src → Task (CUnit × Q) (fun p => A p.2) Out     -- F_d
  group  : Finset CUnit → (CUnit → Src) → Env → (CUnit → Out)
  iface  : Out → Iface
  answer : Iface → (q : Q) → A q
  π      : Iface → K → Hash                 -- bridge-side API hash per key
  keys   : List (CUnit × Q) → Finset (CUnit × K)   -- the extractor: trace ↦ U(d)
  covers : Q → K → Prop

def envOf (I : CUnit → Iface) : Env := fun ⟨u, q⟩ => answer (I u) q
def Env.override (e : Env) (G : Finset CUnit) (I : CUnit → Iface) : Env
```

Build state and one round:

```lean
structure State where
  out : CUnit → Out
  U   : CUnit → Finset (CUnit × K)

def round (src : CUnit → Src) (R : Finset CUnit) (s : State) : State × Finset Key   -- new state, ΔKeys
  -- o := group R src (envOf (iface ∘ s.out)); out' := s.out[R ↦ o]
  -- U' d := keys (trace (envOf (iface ∘ out')) (unit (src d))) for d ∈ R
  -- Δ := { (c, k) | c ∈ R, π (iface (s.out c)) k ≠ π (iface (out' c)) k }
def inv (s : State) (Δ : Finset Key) : Finset CUnit := S.filter (fun d => ¬ Disjoint (s.U d) Δ)
def clean (src) : CUnit → Out := group S src ext      -- ext: the external/library env
```

## Obligations on the compiler (the bridge spec)

```lean
structure Obligations (C : Compiler) : Prop where
  -- Compositionality (§6, §22 item 2): joint = fixed point of separate, group-mates seen fresh.
  comp : ∀ G src e, let o := C.group G src e
         ∀ d ∈ G, o d = (C.unit (src d)).run (e.override G (C.iface ∘ o))
  -- Coverage (§22): every traced query, including misses and closure queries, has a recorded key.
  coverage : ∀ tr, ∀ q ∈ tr, ∃ k ∈ C.keys tr, q.1 = k.1 ∧ C.covers q.2 k.2
  -- Abstraction (§22): equal hash on a key ⇒ equal answers to everything it covers.
  abstraction : ∀ i i' k, C.π i k = C.π i' k → ∀ q, C.covers q k → C.answer i q = C.answer i' q
```

Purity needs no clause: it is the type of `unit`. Determinism likewise.

## Theorems

- **T1 (trace soundness)** — `Zinc/Task.lean`
  `(∀ q ∈ t.trace e, e q = e' q) → t.run e = t.run e' ∧ t.trace e = t.trace e'`. Induction on `t`. Needs no `DecidableEq`.

- **T2 (one round preserves the invariant)** — `Zinc/Soundness.lean`
  Invariant `Inv src s D`: every `u ∉ D` is *up to date*: `s.out u = (unit (src u)).run (envOf (iface ∘ s.out))` and `s.U u` covers that run's trace. Theorem: `Inv src s D → D ⊆ R → let (s', Δ) := round src R s; Inv src s' (inv s' Δ \ R)`. Proof: units in `R` by `comp`; units outside `R` and outside `inv Δ \ R` by T1 + coverage + abstraction (a covered key with owner in `R` has an unchanged hash, so its answers are unchanged; owners outside `R` are untouched).

- **T3a (fixed point at termination)**
  For any policy with `next ⊇ inv Δ \ R`, if `zinc fuel s₀ = some s` then `Inv src' s ∅`: the final state is a per-unit fixed point for the new sources. Initial `D` = changed units ⊆ `R₀`; the old state satisfies `Inv src s_old ∅` because it was itself a clean build (by `comp` with `G = S`).

- **T3b (uniqueness ⇒ equals clean build)**, two variants
  - *acyclic*: given a well-founded `≺` on `CUnit` with `∀ u e, ∀ q ∈ trace e (unit (src u)), q.1 ≺ u`, any two per-unit fixed points agree (well-founded induction + T1). Hence `s.out = clean src'`.
  - *explicit interfaces*: given `∀ s e, iface ((unit s).run e) = ifaceSrc s`, any two fixed points have the same environment, hence agree by purity.

- **T4 (termination)**
  - brute-force regime (`transitiveStep = 0`, i.e. `R_{n+1} = closure(inv Δ) ∪ R_n`): `R` grows strictly until the stop test holds; measure `S.card - R.card`; at most `S.card + 1` rounds.
  - `transitiveStep = k`: at most `k + S.card + 1` rounds, by the above after round `k`.
  - plain regime under *acyclic*: units of rank `r` are stable after round `r + 1`; at most `height + 2` rounds.
  - under *explicit interfaces*: `Δ` is empty from round 1 on; at most 2 rounds (the §4 "signature change takes 2" observation).
  - `recompileAllFraction`: `R = S` for a round ⇒ next stop test holds; trivially bounded.

- **Precision (optional, time permitting)**: minimality relative to `π`: a unit outside `inv Δ` has no covered key with a changed hash. Formal version of "no spurious invalidation" at the key granularity; the heuristics violate it by design (§5).

## Toy instance — `Zinc/Toy.lean`, `Zinc/Examples.lean`

Object language, just enough for §15a and §15b:

```lean
inductive Ty | int | double | ref (c : CUnit)
structure Member where (name : Name) (ty : Ty) (implicit : Bool)
structure ClassDecl where (parents : List CUnit) (members : List Member) (underlying : Option Ty)  -- some ⇒ value class
inductive Expr | select (c : CUnit) (m : Name) | implicitly (ty : Ty) (imports : List CUnit)
structure Src where (decl : ClassDecl) (body : List Expr)

inductive Q | lookup (n : Name) | underlying | implicitCandidates (ty : Ty) | parents
-- A (lookup n) = Option Ty;  A underlying = Option Ty;  A (implicitCandidates ty) = List Name;  A parents = List CUnit

inductive JvmTy | I | D | L (c : CUnit)          -- erasure's codomain
-- Out = (iface part, descriptors emitted for each select, resolved implicit per implicitly)
```

The per-unit task: for `select c m`, ask `lookup (c, m)`, then *erase* the result type by asking `underlying` of the referenced class, recursing while it is a value class (dynamic dependencies: the next query depends on the last answer). For `implicitly ty imports`, ask `implicitCandidates` of each imported class and pick the first, with a `lookup` miss-check on the other scopes for shadowing (§15a). Interfaces are source-determined (explicit types), so `group` is definable as "run each unit against group-mates' source interfaces" and `comp` is a lemma, not an axiom.

Two extractors / key spaces:

```lean
inductive K | name (n : Name) | implicitScope
-- keysNameOnly tr   : records (c, name m) for lookups only           (today's U, §12 rung 1)
-- keysRepaired tr   : + (c, name c) for `underlying`  (the value-class fold of §15b)
--                     + (c, implicitScope) for implicitCandidates  (the §15a unconditional channel)
-- πNameOnly i (name n)   = members of i named n
-- πRepaired i (name n)   = members named n, plus `underlying` when n is the class's own name
-- πRepaired i implicitScope = the implicit members
```

Examples (each a scripted test):

- `valueClass_nameOnly_unsound : zinc … (A.underlying := int → double) ≠ clean …` — `C` keeps `B.foo()I`. By `decide`.
- `valueClass_coverage_fails : ¬ Obligations toyNameOnly` — exhibit the `underlying` query with no covering key.
- `valueClass_repaired : zinc … = clean …` as an instance of T3, discharging `Obligations toyRepaired` by `decide`/`simp` on the finite structure.
- `implicitAddition_nameOnly_unsound` and `implicitAddition_repaired`: `object A {}` → `object A { implicit val y }` changes `C`'s resolution with no name `C` wrote.
- `implicitShadowing`: §15a's `val x` shadowing case *is* caught by name-only keys because the miss-check records `(A, name x)` — the "name hashing happens to model it" remark, now a theorem.

Macros (§15c) are out of scope for the toy; `macroObserve` is just another query and `⊤` the coarsest covering key, which the abstract model already handles.

## Steps

- [x] 0. Review this plan. Decided: Mathlib.
- [x] 1. Lake project `zinc-incrementality/lean/` with Mathlib `v4.34.1`; `lake build` green on an empty module. Commit.
- [x] 2. `Task.lean`: free monad, `run`, `trace`, T1. Commit.
- [x] 3. `Model.lean`: `Compiler`, `Env`, `State`, `round`, `inv`, `Obligations`, generic policy and fuelled `zinc`. Commit.
- [x] 4. `Soundness.lean`: T2 (round invariant), T3a. Commit.
- [x] 5. `Uniqueness.lean`: T3b acyclic and explicit-interface variants; T3 corollaries. Commit.
- [x] 6. `Termination.lean`: T4 for the brute-force, `transitiveStep`, acyclic and explicit regimes. Commit. (`transitiveStep` is modelled as one step of `dependents` rather than the full closure; the bound only needs `I ∪ R ⊆ next`.)
- [x] 7. `Toy.lean`: object language, per-unit task, the two key spaces, `group` with `comp` proved. Commit.
- [x] 8. `Examples.lean`: §15a/§15b counterexamples and repaired proofs. Commit. (`decide` gets stuck in the kernel on `Finset`/`Option` matching; `native_decide` is used.)
- [x] 9a. `README.md` for the Lean dir.
- [ ] 9b. Update §3, §4 and §22 of the talk with the two findings and pointers to the theorem names.
- [ ] Future work: added/deleted units; external (library) units and classpath stamps; the macro-downstream policy as a modelled channel; precision/minimality theorem; `localInheritance` and inheritance edges that bypass the name filter (today both are just keys with `covers = ⊤`).

## Phase 2 — members vs decls vs Merkle: what the model can say

### What Zinc does today, read off the code

Two facts that change the question in §7–10:

1. **The invalidator already walks the hierarchy.** `IncrementalNameHashing.invalidateClassesInternally`: for a change to `A` with modified names $N$, it computes the *transitive inheritors* of `A` (`invalidateByInheritance`, seed included) and then invalidates the `memberRef` clients of **every** inheritor `C` whose used names meet $N$. So a client of `C.m`, with `m` declared in `A`, is invalidated in the *same* round as `A`'s own clients, with `A`'s name hashes, not `C`'s.
2. **So the materialised `inherited` members never drive a round.** After the inheritors recompile, their changed name hashes point at clients that were already in that round, and the stop test ($\mathrm{inv}(\Delta_n) \subseteq R_n$) absorbs it. §9's "each descendant counts as API changed, which drives another invalidation round" is wrong as stated: it drives a *redundant* $\Delta$, not a round. The real costs of `inherited` are extraction, storage and nondeterminism amplification, as §9 also says.

That leaves the actual job `inherited` does: it makes a **non-local** hash. `π_C(m)` depends on `A`'s decl of `m`, on `C`'s parents with their type arguments (`asSeenFrom`) and on the linearization. The walk in (1) is what keeps that non-local hash *fresh enough*: when `A` changes, the invalidator does not trust the stale `π_C`, it goes to `C`'s clients through the hierarchy. Merkle composition is the same non-local hash, memoised. Decls-only is the local alternative, where the client's keys must name the ancestor and the parents list. All three are instances of one generalised model.

### The generalised model

Today `π : Iface → K → Hash` reads one unit's interface, and coverage requires the key's owner to be the query's owner (`q.1 = k.1`). Generalise:

- `π : (CUnit → Iface) → CUnit → K → Hash` with a declared read set `hashDeps : CUnit → Finset CUnit` and the obligation **hash locality**: `π I c k` depends only on `I` restricted to `hashDeps c`.
- **Coverage** may cover queries addressed to units in `hashDeps k.1`: `q.1 ∈ hashDeps k.1 ∧ covers q.2 k.2` (closure keys: `(C, m)` covers `decl(A, m)`, `parents(C)`, …).
- **Δ over the hash-dependency closure**: `changed` ranges over $R \cup \{c \mid \mathrm{hashDeps}(c) \cap R \neq \emptyset\}$ (transitively), with hashes recomputed from the current interfaces. Today's model is the special case `hashDeps c = {c}`.

Theorems:

- **T2′** (`round_preserves'`): the round invariant holds for the generalised model. Same proof shape; the new case is a key whose owner was not recompiled but whose hash read a recompiled unit.
- **T2-stale** (counterexample, as a Lean `example`): with a non-local `π`, taking Δ over $R$ only is unsound. This is the trap in the bridge's own TODO ("use parent hashes instead"): memoised Merkle hashes of unrecompiled descendants must be recomputed (or their clients reached by the walk), or the build undercompiles.
- **Today = Merkle + walk**: Zinc's inheritance walk is `hashDeps⁻¹` applied at invalidation time, and the materialised `inherited` is the Merkle composition done eagerly inside the compiler. The inheritance edge is not merely "unfiltered"; it is the mechanism that makes a non-local hash sound.

### The toy, extended

Add to `Toy.lean`: `parents : List (Cls × TyArg)` (one type parameter per class is enough for `asSeenFrom`: member types may be `param`, instantiated through the parent's argument), and a linearization walk for member lookup that records misses. Three $\pi$/key designs over the same compiler trace:

| design | keys the client records | `π` | explicit ifaces? |
|---|---|---|---|
| materialised (today) | `(C, name m)`; inheritance `(A, ⊤)` for subclasses | hash of the resolved, as-seen-from member; `Iface` includes `inherited` | no |
| decls + walk | `(C, parents)`, `(X, name m)` for every class `X` visited in the walk, misses included | hash of the local decl | yes |
| Merkle per name | `(C, name m)` | $h(\mathrm{decl}_C(m), \langle (P_i, T_i, h_{P_i}(m))\rangle)$, non-local | n/a (hash is non-local, iface is local) |

Scenarios, each an `example` computing the invalidated sets and round counts under all three:

1. **Edit an inherited member's type** `A.m : Int → String`, clients of `A.m`, `B.m` and `C.m` (B, C descendants). Expect equal invalidated sets, 2 rounds everywhere; the materialised design shows a redundant non-empty $\Delta_1$.
2. **`asSeenFrom`**: `class B extends A[Int]` → `A[String]`, `A.f : T`. Expect: materialised moves only `f`; Merkle per name moves every inherited name of `B`; decls + walk moves every client of `B` through `(B, parents)`. This is the precision ladder of §10, now computed rather than argued.
3. **Linearization**: add an override of `m` to a mixin `M` of `C`. Expect all three sound; decls + walk catches it through `(M, name m)` recorded by the walk of `C.m`'s clients, which is the hierarchy walk made explicit in $U$.
4. **Stale Merkle**: scenario 1 with Δ over $R$ only. Expect undercompilation (T2-stale).

Precision statements worth attempting as theorems, after the examples confirm them: for a fixed trace, the invalidated set under materialised ⊆ Merkle-per-name ⊆ decls-with-parents-key (coarser keys invalidate more), and all three are equal when no `asSeenFrom` is involved (member types mention no type parameter).

### What it answers for the talk

- §10's discussion question "soundness requirement or convenience?": the materialised `inherited` is one of three sound ways to make the hash of an inherited member depend on the ancestor; what is *required* is either a non-local hash kept fresh (walk or recompute) or local keys that name the ancestor. The walk already exists, so decls-only is a change to `π` and to what `U` records, not to the invalidator.
- §9's round claim is corrected; the honest cost of `inherited` is extraction, storage and nondeterminism, plus a redundant $\Delta$.
- §11's bridge-side memoised hashing *is* the Merkle design; its obligation is T2′'s Δ-over-`hashDeps⁻¹`, which the existing inheritance walk discharges.

### Steps

- [x] P2.1 `NonLocal.lean`: `GCompiler` with env-dependent `π`, `hashDeps`/`hashRevDeps`, interface-dependent `covers`; T2′ with `Δ` over `affected R = R ∪ hashRevDeps(R)`. Kept separate from `Model.lean` rather than generalising in place; the local model is the `hashDeps c = {c}` case.
- [x] P2.2 `Stale.lean`: T2-stale on two units.
- [x] P2.3 `Hier.lean`: one type parameter, parents with a type argument, right-to-left walk with misses, `select` marker so a flat trace identifies receivers.
- [x] P2.4 `D`, `W` as `Compiler`, `Mk` as `GCompiler`; `HierSound.lean` proves `Obligations` for all three. Policies were given the old state so Zinc's hierarchy walk can be written as `walkPolicy`.
- [x] P2.5 Scenarios 1–3 (+ stale Merkle) as `example`s. Results: inherited-member edit: D `X Y`/2, W `B C X Y`/3 (2 with walk), Mk `X Y`/2, stale Mk undercompiles. `asSeenFrom`: D `X Y Z`/2, W `C X Y`/3 (2), Mk `X Y Z`/2. Mixin override: D `Y`/2, W `C Y`/3 (2), Mk `Y`/2.
- [ ] P2.6 Precision inclusions as theorems (materialised ⊆ decls, materialised ⊆ Merkle-chain on `asSeenFrom`; equality without type parameters). Parked: the examples support it; a general statement over all toy programs needs an induction over the walk.
- [x] P2.7 Slides: §9 corrected (the walk already exists; the cost is hierarchy recompiles and a redundant Δ), §10 "what the model says" table, §22 non-local card and computed table, future work updated.

Observations worth keeping:

- The Merkle hash that fits the per-query model is the *verifying trace* of the lookup (§10's formula is exactly that). Hashing only the resolved member is sound by a different, semantic argument (the client observes the walk only through its result), which the model expresses as the materialised design's single `members` query.
- Materialised members' real cost is not rounds but recompiling every subclass to refresh hashes; the walk at invalidation time makes that affordable, and it is a `Policy.Sound` policy.
- `asSeenFrom` is where the designs differ in precision, and the difference is in the hash function, not the architecture.

## Phase 3 — checking the Merkle PoC's design (`PLAN-merkle-poc.md` in the Zinc worktree)

- [x] P3.1 `NonLocalAns.lean`: `NCompiler`, answers that read several interfaces (a lookup along a stored linearization), interface-dependent `hashDeps`, extractor that knows its unit; T2″, T3a″.
- [x] P3.2 `Flat.lean`: decision 1 (flattened composition over the stored linearization). Proved sound with header keys (`flat_sound`); the PoC's `Δ` domain (`R ∪ inheritance.reverse*(R)`) agrees on the scenarios. Header edits take 3 rounds (the header round diffs descendants over their stale linearization). Header rule as a policy: transitive is equivalent to the keys; direct children only, or none, undercompiles (Edit 4: grandparent `A extends M[Int] → M[String]`).
- [x] P3.3 Refchecks prelude (PoC decision 3, talk §10a): override, conflict (presence, then members of cross-parent pairs, skipping pairs within one parent as scalac does) and abstract-member queries to ancestors, recorded as keys of kinds `overrides`/`conflicts`/`abstract`. Still proved (`Fl_obligations`). Edit 1 recompiles no descendant; override, conflict and abstract edits recompile exactly the descendant running the check; dropping any one kind (`client`, `uses`, `header`, `overrides`, `conflicts`, `abstract`) leaves some scenario unclean. Presence keys are coarser than the rule table's `conflicts` rule: they fire when an ancestor adds a concrete name nobody else declares.
- [x] P3.4 `FlatRules.lean` + `lake exe exhaustive`: the rule table as a policy over 7,500 programs × 19 single-class edits. `none`: 72,032 unclean. Default as stated: 672 unclean, all from `abstract` firing only on names deferred in the *changed* class: deleting (or adding) a concrete implementation in `B` of a member deferred in `A` changes whether concrete `C` compiles. Widened (`m` deferred in any ancestor of `d`): 0 unclean. Each rule's ablation against the widened default is unclean (uses 1,320, overrides 20,650, conflicts 504, abstract 2,272, header 22,500); recording self-selections as keys makes `uses` unnecessary (0). The header counterexamples are stale stored linearizations only, i.e. observable only by a reader of stored `lin` (cross-project composition). A whole-space `native_decide` is too slow for the build; minimal counterexamples are checked examples.
- [x] P3.5 Codegen observables in `Flat.lean`: a class's bytecode also derives from ancestors its source never names. Mixin forwarders: a class asks each trait it mixes in (one not in its superclass's linearization) for its declarations (key `(t, decls)`, kind `trait`), and the ancestors ahead of the trait whether they declare the name (`(q, has n)`). Static forwarders: an object asks every ancestor for its declarations, for its mirror class (`(q, decls)`, kind `mirror`). Kind and `final` join the header (`(p, parents)`), with a `final`-parent check. Still proved (`Fl_obligations`). Fidelity fix found by the Zinc conformance run: a deferred declaration in `q` hides a concrete one in an ancestor of `q` (`abstract class A extends M { def m: Int }` makes `M.m` abstract again for `B extends A`); a concrete member through another path still implements it.
- [x] P3.6 `FlatRules.lean` gains `trait`, `traitDirect` (only descendants that mix the trait in directly) and `mirror`, and the space gains a `final` toggle on `B` and an `X` that `extends C[Int]` instead of selecting (30,000 bases × 21 edits; 60,000 × 22 with `A` as a trait, P3.6b). On the larger space: `none`: 764,944 unclean; as stated: 3,072; widened: 0; widened with `trait` narrowed to direct mixins: 0. Ablations against the widened default: uses 4,480, overrides 55,656, conflicts 864, abstract 21,632, header 180,000 (the smallest: `B` made `final`), trait 18,400 (`M` gains a concrete member: `C`'s forwarder), mirror 25,568 (`C` gains a member: `X`'s static forwarder). Recording self-selections as keys still makes `uses` unnecessary.
- [x] P3.6b `A` may be a trait (trait extends trait; a class whose first parent is a trait), and a selection's answer includes the receiver's kind, which the client key hashes: a trait receiver is `invokeinterface`. Both found by the conformance run, where an upstream `abstract class A` becoming a trait left the client `Z` with `invokevirtual`; the model had predicted no recompile for `Z`.
- [x] P3.7 `lake exe conformance`: the program space as JSON lines for the Zinc conformance harness (`sbt.internal.inc.bench.Conformance` in the PoC's `zincScripted` tests), which renders each program as Scala and compares an incremental build's classfiles with a clean build's after every edit and its revert. Bases are those whose model build is error-free, resolves every selection and inherits one instance of each ancestor (scalac rejects `M[Int]` and `M[String]` in one linearization).

## Phase 4 — the next observables

The proofs say the loop is sound *given a cover*. The conformance harness checks the other half against scalac, but only for the observables a program space exercises. Each extension below adds queries (and so keys and a rule), a program-space dimension, and therefore conformance cases, so the harness covers what the model adds without further work.

**Forwarders as queries (done, P3.5/P3.6).** Mixin forwarders are a query from the class that mixes a trait in directly to the trait for its declarations, plus presence queries to the ancestors ahead of it in the linearization (the forwarder exists only if the trait's member wins). Static forwarders are a query from a top-level object to every ancestor. The model then derives the PoC's `trait` and `mirror` rules as covers, and shows `trait` can be narrowed to direct mixins (`traitDirect`, the PoC's TODO) with no unclean run in the space. Next: a trait that overrides a class member (`merkle-trait-override`, the case where a missing forwarder changes behaviour), which needs a trait with a class ancestor.

**Macro observation as a whole-class key.** A macro that reflects over `c.tpe.members` or `baseClasses` asks one query whose answer is every member of the receiver, inherited ones included, and names no owner. Model it as a client query `(c, all)` covered by a key whose hash reads every interface in the receiver's stored linearization (`hashDeps` = `lin(c)`), so it is non-local and T2″ applies: `Δ` must be taken over `R ∪ descendants(R)`, which is the macro-edge-from-descendants fix (`merkle-move-ancestor-downstream-macro`) and the cross-module case (`MerkleHashes` composing for `macro-type-change-3`). Program space: a client `W` whose body is `observe(C)`; the harness renders it as a macro from a fixed upstream macro project that emits one forwarder per member (so the observation reaches bytecode). The model predicts which edits must recompile `W`; the harness checks that Zinc's macro edges agree, including across subprojects, where the PoC found a hole.

**Erasure as an observable.** A client's bytecode depends on `erase(type)` of what it references, and for a value class `V(u: U)` erasure is `U`, so `π` keyed by the name `V` must determine `U` (talk §2, §15b; `Toy.lean` has it for one class). In `Flat`, add a class `V` whose decl is `underlying : Option Ty` and let member types range over `V`; a selection's descriptor then asks `(V, underlying)` (covered by a header-like key on `V`), and `Out.descs` records erased types. The edit "`V`'s underlying `Int → String`" must recompile clients of members typed `V`, and also descendants that override such a member (bridges) and mix in a trait declaring one (forwarder descriptors). This is where the rule table meets erasure: `overrides` and `trait` fire on name hashes of the *declaring* class, which do not move when only `V` changed. The model will say whether a key on `V` reached through the member's type covers them, or whether the rules need `V`'s dependents; the harness checks the bridges.

**Trait private members and fields: the `extraHash` channel.** A class that mixes in a trait implements the trait's fields (getters, setters, initialisation in `$init$`) and private members it calls through, none of which is in the trait's public API. The PoC folds trait parents' `extraHash` into a descendant's hash. Model it as a trait decl kind `field` (private, not selectable by clients) that the mixing class must implement: a forwarder-like query `(t, fields)` from each class mixing `t` in directly. Program space: `M` optionally declares a `val` or `private def`; edits change its type or remove it. Clients cannot see it, so only `trait` (or a narrower `fields` rule) can recompile the mixing class; the harness checks that the class's field and its `$init$` call match a clean build.

Order: macros first (the one hole found so far that the model does not express), then erasure (it touches the rule table's assumption that a changed name lives in the changed class), then fields.

## Phase 5 — the next observables, built (branch `claude/lean-extensions-overnight`)

All four Phase 4 extensions are now queries with keys in `Flat.lean`, and `Fl_obligations` still holds, so T2″/T3a″ cover them.

- **Fields and private members.** `Mem` has a kind (`def`, `val`, `var`, `lazy val`) and may be private. A class that mixes a trait in directly implements its fields, private ones included. Override checks reject what scalac rejects. In `FlatRules`, `M` may declare a field, and `traitPub` is `traitDirect` blind to private members, i.e. a trait API without Zinc's `extraHash`. Result: 48,000 unclean runs without the private channel, 0 with it. This backs the PoC's `extraHash` folding trait parents only: a class parent's private members reach no descendant's bytecode.
- **Whole-class observation (macros).** A client may observe a class: key `(c, all)`, hashed over every member along the stored linearization. It is non-local, so `Δ` must range over the descendants of the recompiled set (T2″), which is the PoC's macro-edge fix. Dropping the macro keys leaves 437,696 unclean runs. The conformance run also found what the model leaves out: Zinc's stored external API of an upstream class went stale when no direct dependent recompiled (`macro-upstream-member-removed`, PoC-only, fixed in the PoC); and a macro can read private members, which no API records (`macro-observes-private-member`, pre-existing, outside any name-keyed cover).
- **The extends clause.** A descendant's key on the parent it names (Zinc's `memberRef` on the parent's name), hashed by the parent's header and stored linearization. With it, header changes cascade one level per round, and the `header` rule is subsumed: without `header`, recording extends clauses leaves 0 unclean runs (648,000 without either).
- **Erasure and value classes.** `V` is a class with an optional underlying type. Erasure is a query `(V, under ctx)` asked by a selection, a mixin forwarder, a static forwarder and a bridge. Under Zinc's keys (client and macro) only the selection's is recorded. Over the value-class space (4,320 bases × 16 edits, `exhaustive v`), the widened default leaves 5,428 unclean runs, and recording codegen's erasure reads leaves 0. The checked examples are the pre-existing `value-class-mixin-forwarder` and `value-class-mirror-forwarder`, and `erasure-bridge-upstream-grandparent` for a type parameter's erasure. The PoC's bridge fix ("Hash the erasure of value-class references") is the implementation of that key: a reference's API now determines its erasure.

Main space: 216,000 bases × 27 edits (`M` may declare a field; `Z` may observe `C`). Run before `V` was added; `V` does not occur in this space.

| rule set | unclean |
|---|---|
| none | 3,874,336 |
| default as stated | 9,600 |
| widened | 0 |
| widened, `traitDirect` | 0 |
| widened, `traitDirect` without private members (`traitPub`) | 48,000 |
| widened, no macro keys | 437,696 |
| widened without `header`, extends clauses recorded | 0 |
| widened without uses / overrides / conflicts / abstract | 22,240 / 293,104 / 3,456 / 77,440 |
| widened without header / trait / mirror | 648,000 / 189,568 / 100,864 |

## Phase 6 — rendering inherited members: as seen from, as declared, erasure witness

Input: a research session comparing Scala 3's `ExtractAPI` (inherited members rendered as declared, type arguments only in `parents`, no override dedup, Scala2x ancestors skipped) with the Scala 2 bridge (`memberInfo`, as seen from), backed by scripted runs on 3.9.0 and 2.13.18 (zinc branch `claude/asf-research`, local). The question: which rendering must key which invalidation path, and does either determine erasure? Phase 5's erasure keys in `Flat.lean` (codegen's reads of `V`) answer the value-class half inside the PoC's model; `Erasure.lean` (P6.8, `vEdge`) reaches the same answer from the rendering side and adds the generic half.

- [x] P6.1 `Erasure.lean`: two type parameters, a value class `V` by name, erasure from the owner's declared type; a descendant's output has bridges (per overridden declaration, no dedup) and forwarders (mixin or mirror); queries carry their context (descendant through parent `p`, client selection, macro observation, own erasure) so the extractor maps them to Zinc's keys: inheritance on the direct parent, `(c, name n)` + class-name key `(c, cls)` for clients, `(V, und)` for own erasure. Interfaces are source-determined; the materialised rendering is a non-local hash over the chain (T2″).
- [x] P6.2 Item 1, erasure observable: `erasure-bridge-upstream-grandparent` as checked examples. As seen from undercompiles across subprojects (`B` wrong), and is clean with transitive inheritance invalidation (one subproject); as declared and witness recompile `B`.
- [x] P6.3 Item 2, determination: `asf_of_decl` (name key with class-name key) and `asfInh_of_declInh` (inheritance key) prove as-seen-from hashes are functions of as-declared ones; the converse fails on the precision case (checked example). The precision case: as declared recompiles `B` (and `X`) for nothing, as seen from does not.
- [x] P6.4 Item 3, class-name key: on `B extends A[Int] → A[Long]` with `A.m: T`, as declared moves only `(B, cls)`; the client `X` recompiles through it. A macro that observes `B.m` as seen from `B` and records only the name escapes (checked example); recording its reads of `B`'s parents fixes it. No other client shape escapes in the exhaustive space.
- [x] P6.5 Item 4, value classes: `value-class-mixin-forwarder` as checked examples. As seen from and as declared leave the forwarder stale; the witness (erasure of `V` in `(p, inh)` when the chain mentions `V`) recompiles it. Modelled as a non-local witness; a witness stored at the owner's compile reaches the same set one round later through the owner's own `(V, und)` key and the inheritance edge.
- [x] P6.6 Item 5: `wit_obligations` (witness, faithful macro keys) meets `NCompiler.Obligations`; `wit_sound` by T3a″.
- [x] P6.7 `lake exe exhaustive erasure`: 6,912 bases × 17 single-choice edits, 25,120 legal pairs, six variants. Unclean runs: as seen from across subprojects 1,716 (864 miss a bridge or forwarder through a type-argument erasure change, 852 value class), one subproject 0; as declared 1,204 (852 value class, 352 macro), with recorded macro reads 852; witness 352 (macro only), with recorded macro reads **0**. Full table in `Erasure.lean`. Wasted recompiles: as declared costs clients too (`X` 12,032 vs 5,440), through no-dedup per-name lists.
- [x] P6.8 Value classes without a witness: `Ext.vEdge` records the descendant's read of `V`'s erasure as a dependency on the name `V` (already hashed with the underlying type) instead of folding it into the parent's inheritance key. `Er_obligations` generalises the proof: as declared + faithful macro keys is sound with the witness *or* the `V` edge (`vEdge_obligations`, `vEdge_sound`). Exhaustively, the `V` edge gives the witness's exact counts (0 unclean, 60,144 recompiles); under as seen from it removes the 852 value-class runs and leaves the 864 generic ones. So generic erasure needs the as-declared rendering, value-class erasure needs a dependency, and neither needs a change to member hashes beyond that.
- [x] P6.9 Erasure inputs beyond value classes (prompted by sbt/zinc#1844's closing comment, which found intersection erasure missed and rejected the dependency edge for it). `Erasure.lean` restructured: an intersection `W with Z` (erases to `Z` if `Z` is a class or extends `W`); interfaces store each class's own erased signatures, computed when it compiles, so a witness is only as fresh as its declarer; clients emit descriptors and record Zinc's `memberRef` on the owner; as-seen-from hashes include the winning owner (Zinc's declared/inherited distinction and `override`). Options: witness `vcStored` (#1844 as implemented), `stored` (erased signature at definition), `fresh` (recomputed), `diverge` (Scala 2, generic only); `dep` (dependency edge); `kind` (class-name hash covers trait vs class). `Er_obligations`: as declared + faithful macro keys + kind is sound with `fresh` or `dep` (`fresh_obligations`, `dep_obligations`, `dep_sound`); a stored witness is not provable here (its soundness is a run invariant: the declarer is up to date). Exhaustive (41,472 bases × 20 edits, 189,888 legal pairs, 13 variants, parallel, 24 s): Scala 2 today 12,064 unclean (generic 4,608, value class 3,648, intersection 3,808); the divergence witness leaves Scala 2 exactly where Scala 3 is today (7,456); stored witness or dependency edge leave only intersection trait-to-class (2,176), which needs the kind in the class-name hash (first hop); with it, 0. Cost of closing everything: +24% recompiles over Scala 2 today, +6% over Scala 3 today.
- [ ] P6.10 Future: owner `memberRef`s for clients (Zinc records one; the model does not, so its client precision gap overstates Scala 3's); a stored (not recomputed) witness as its own design; opaque types and `inline` as further erasure sources (Scala 3); multiple inheritance in the erasure model (chain only today).

Findings for the talk:

- As seen from is the wrong input for erasure; as declared plus parent type arguments is the sound key for descendants, and it determines as seen from. The resolved-member (as-seen-from) hash may refine `memberRef` clients, never the descendant rules.
- Neither rendering determines erasure through a value class referenced by name. An erasure witness on inherited members does, but so does a plain dependency edge from the descendant to the value class, with no hash change; with either and faithfully recorded macro reads the bounded space is clean.
- Scala 3's per-name hashes don't move on a type-argument change; the class-name key does, and is sufficient for every recorded client. The escape is a reader that observes as-seen-from types without recording the class name (a macro).

## Phase 7 — implicit scope through an ancestor's companion, across projects (sbt/zinc#1845)

Input: the fix on retronym/zinc `fix/implicit-scope-ancestor-companion` (`AnalysisCallback.InheritedImplicitScopes`). A client of `Show[C]` depends on the companion of every base class of `C` without naming them. In a project, `MemberRefInvalidator` reaches it (memberRef clients of every inheritor of the owner); downstream only diffs `C`, whose `AnalyzedClass` doesn't change. The fix publishes, per class, one more `Implicit` name hash: the set of its direct parents' implicit name-hash sets (which include their own entry, so it is transitive), folded into `apiHash`; external parents' sets are captured on the inheritance dependency.

### Model (`Zinc/ImplicitScope.lean`)

- Classes `A B C` (a chain; `B` may be a trait), an object `O extends B`, a trait `L` that `C`'s companion may extend, clients `X` (`Show[C]`), `W` (`Show[List[C]]`), `Y` (`Show[O.type]`), `Z` (names an unrelated class). Each unit has a project (`lib`/`mid`/`app`), a few fixed layouts.
- A class's contents: companion implicits `(name, bound, shape, value)` (`implicit def sb[T <: B]: Show[T]`, or `Show[List[T]]`), class-side implicits, a non-implicit companion member. Search: candidates from the companions of the type's base classes (and what the companion inherits), applicable by bound and shape, most specific by owner derivation, else ambiguous.
- Name hashes as Zinc computes them: per class, `Implicit` entries over class side + companion, *including inherited members* (`Visit` walks `structure.inherited`); everything else under one non-implicit key. Clients record `(T, imp)` and `(T, cls)` for the type they search (memberRef on `T`), plus the selected implicit's owner. Descendants record `(p, inh)` on direct parents, hash = `apiHash`.
- Projects as policies on one loop, as in `Erasure.lean`: Zinc's transitive inheritance invalidation and the implicit fallback (memberRef clients of the owner's inheritors) apply only within the owner's project; across projects only recorded keys count.
- Two forms of the fix: **recomputed** (`(T, imp)` a non-local hash over `T`'s ancestors, `NCompiler`, T2″) and **stored** (the summary is part of the published interface, computed at `T`'s compile from its parents' published summaries; local hashes; freshness from the inheritance key, which covers the summary because it is folded into `apiHash`).

### Results

- [x] P7.1 `Zinc/ImplicitScope.lean`: the model, and the scripted tests as checked examples: grandparent companion (`Z` untouched, non-implicit member reaches no client, removal works on develop too because the selected implicit's owner is a memberRef dependency); type argument (`W`); ancestor in an upstream project (`lib → mid → app`). On develop across projects the client stays wrong; in one project the fallback recompiles it. A trait parent is just a parent in this model.
- [x] P7.2 `is_obligations`: the recomputed fix, published for every class (objects too), meets `NCompiler.Obligations`; `is_sound` by T3a″ with any sound policy, the plain one included, so no in-project rule is needed. Without the summary (develop) the obligations fail: checked example where `(C, imp)` keeps its hash and covers `X`'s read of `B`'s companion, whose answer changes; the same for `(O, imp)` when the fix is published only for classes.
- [x] P7.3 `stored_eq_recomputed`: on a `Consistent` state (every published interface is its own compile against the current ones; `consistent_of_upToDate`) over an acyclic hierarchy of height below `depth`, the stored `π` equals the recomputed `π` on the class-name and implicit keys. Ablation: without folding the summary into `apiHash`, `A` gaining an implicit leaves `C` in `mid` stale (`B` recompiles in `lib`, its own API unchanged); in one project transitive inheritance invalidation hides it.
- [x] P7.4 `lake exe exhaustive implicit` (120 bases, 1,080 pairs, 11 variants; table in the file): the fix never recompiles a client the in-project fallback does not, and across projects recompiles exactly the fallback's clients except clients of an object's singleton type; stored and recomputed agree on every client; without the fold 312 unclean runs; published for objects too, 0. The fallback's own coarseness carries over (most client recompiles leave the output unchanged).
- [x] P7.5 Over-approximation: a class-side implicit on an ancestor moves the summary, but it is a public inherited member of every descendant, so their own names move too and develop recompiles the same clients (checked example; the exhaustive check finds no extra client). It would cost something only for members that are not inherited into the descendant's API (private, overridden); the model has no privacy.
- [x] P7.6 Non-coverage: `object O extends B` and a client of `Show[O.type]`: wrong across projects, clean in one project, clean if the summary is published for objects too (checked examples; all 136 unclean runs of the fix in the exhaustive space).
- [x] P7.7 `object C extends L` is covered, by develop too: the inherited implicit is in object `C`'s name hashes and object `C` recompiles when `L` changes. It escapes only if inherited members are missing from name hashes (`inhNames := false`, checked example; 120 runs in the exhaustive space).
- [ ] P7.8 Future: diamonds (Zinc's summary is a set, so it merges duplicate parents; order and empty ancestors are lost, which matters only for parent edits, covered by the class-name key); the summary as Zinc hashes it (nested sets without owner identity) instead of the injective list; privacy (the over-approximation's real cost); Scala 3 givens' priority rules; publishing the summary for objects (`NameKind.Term` sources) as a Zinc follow-up; a scripted test for `object C extends L` with a Scala2x parent under Scala 3.

Findings for the talk:

- The fix is the in-project fallback made portable: across projects it recompiles exactly what the fallback recompiles within one, no more. Its imprecision is the fallback's.
- It is sound as a recomputed (Merkle) hash with no in-project rule at all; as Zinc stores it, it is sound because the inheritance edge refreshes every descendant, which across projects works only because the summary is folded into `apiHash`.
- The remaining gap is the implicit scope of an object's singleton type; the companion-inherits shape is not a gap, because inherited members are already hashed.

### Not modelled

Show's own companion and `List`'s companion (constant across edits); type-parameter bounds beyond "subclass of"; given priorities in Scala 3; hash collisions (hashes are modelled injectively, as elsewhere).

## Phase 8 — the classpath, pipelining, and keys from the tree (design, for review)

The model compiles a fixed set `S` from source against a constant environment, and represents subprojects as a policy on one loop. Zinc has three kinds of dependency with different state and different invalidation, and many recent bugs sit at the boundaries between them (talk `zinc-lean` §2a). Pipelining adds a fourth interface, the early output. Separately, Zinc's extractor reads the typed tree, not a trace, which is where the post-typer and desugaring bugs come from. This phase brings these into the model.

### What Zinc does, read off the code (`merkle-baseline`)

- **Libraries.** A classpath entry with no Analysis. The stamp is a content hash (FarmHash, `Stamper.forHashInRootPaths`; mtime only caches it); a class inside the output JAR is stamped by the whole JAR. A changed stamp invalidates every source that uses the library, with no name filter (`IncrementalCommon.scala` `byLibraryDep`, `usesLibrary`).
- **Upstream subprojects.** A class whose name resolves to an upstream Analysis through `Lookup` (jar or directory alike). The downstream Analysis stores a snapshot of each external `AnalyzedClass` (`apis.external`). Every run diffs every stored snapshot against the upstream's current API (`detectAPIChanges`) and invalidates with `invalidateClassesExternally`: inheritance transitively, then name-filtered memberRef clients of every class reached, then direct name-filtered memberRef and macro-expansion dependents. This runs only for the initial invalidation.
- **Snapshot refresh.** A snapshot is refreshed when a recompiled source references the class (`Analysis.addSource` → `markExternalAPI`), or, when nothing compiles, for every changed external. Reading the code, a run that compiles something but no source referencing a changed external leaves its snapshot stale. To confirm with a scripted test before modelling it as a finding.
- **Pipelining.** Upstream writes an early pickle JAR and an early Analysis (internal APIs and `productClassName` only) after the dependency phase, unless the project has a macro. Downstream's choice of early vs final outputs is the build tool's. No rollback of the early JAR or early Analysis if the upstream compile then fails. With `-Ypickle-java`, downstream sees Java through its source, not its classfile.

### Model changes

1. **Projects and external units.** A build is a DAG of projects, each with its own loop and `State`. A project's state gains, per external unit it used, the snapshot of the hashes it compared against (upstream) or the stamp (library). A build of the DAG runs the loops in topological order.
2. **Initial invalidation as a step of its own.** `R₀ = changed sources ∪ users of changed libraries ∪ inv(Δ_external)`, with `Δ_external` the upstream keys whose snapshot differs from the upstream's current hash, closed by Zinc's external walk. Today the loop starts from a given `R₀` and a previous clean build.
3. **Libraries** are external units with a single key, `(lib, whole)`, which covers every query and whose hash is the stamp.
4. **Pipelining.** An upstream output has two interfaces, `early` and `final`. Downstream compiles against `early` when pipelining is on. An upstream run may fail after `early` was published.
5. **Keys from the tree.** `keys` becomes a function of the typed tree (part of `Out`), and the per-unit task has two phases: typer (trace₁), then the phases after extraction (trace₂: pattern matcher, erasure, mixin). The trace stays the ground truth; coverage relates the two.

### Obligations and theorems

- **Stamp abstraction:** equal stamps give equal answers. Holds for a content hash under injective hashing; a whole-JAR stamp is coarser and still sound.
- **Snapshot freshness** (a run invariant, not a compiler obligation): for every up-to-date downstream unit, the stored snapshot of each external key it recorded is the hash of the interface it was compiled against. Check whether Zinc's refresh rule preserves it; expected counterexample: the stale snapshot above (and `macro-upstream-member-removed`, fixed in the PoC); expected fix: refresh every external whose snapshot changed.
- **T5, composition:** if the upstream loop ends up to date (T3a″) and the downstream's initial invalidation uses fresh snapshots, the downstream loop ends up to date against the upstream's final interfaces. Corollary for a DAG. Then relate it to today's encoding: on the `Erasure` and `ImplicitScope` spaces, does the composed run equal the single loop with the cross-project policy? A difference is a finding about one of them.
- **Early agreement (pipelining):** for every query a downstream can ask, the early answer equals the final one. Instances that fail: Scala 2 optimizer inlining across projects reads bytecode, which has no early answer; Java through `-Ypickle-java` (source view) vs classfile view, e.g. `static final` constants not folded from source (scala/bug#5333), so downstream bytes differ between pipelined and non-pipelined builds.
- **Failure after early output:** with no rollback, a downstream compiled against the early interface of a failed upstream stays wrong after the upstream is reverted (`pipelining-failed-upstream-revert`, pending in Zinc). Expected theorem: sound if a failed upstream run invalidates the downstream snapshots it published.
- **Coverage from the tree:** every query in trace₁ ++ trace₂ is covered by a key of the tree. Counterexamples: an extractor pattern's `_N` asked by the pattern matcher (scala/scala3#26231), `x += y` falling back to `+` (`assign-op-member-added`), `Dynamic`. Fixes as keys: anticipatory keys for names a later phase may ask (`_N+1`, `C;init;`, scala/scala3#26262), and failed lookups recorded by the typer.

### More language features, in order

1. **Source files with several classes, and sealed hierarchies.** Recompilation is per file. The sealed-children query is non-local and negative, and Scala's same-file rule is what makes a local key enough; Java `permits` across files breaks it (retronym/zinc#21).
2. **Inline bodies.** A query for a method's body; the key hashes the body. Interacts with early agreement: Scala 3 `inline` bodies are in TASTy (early), Scala 2 optimizer inlining is not.

### Program spaces and conformance

Each step adds a layout or a dimension that the harness (retronym/zinc#25) already has or can add: `split` exists; add a `library` layout (the upstream published as a JAR without an Analysis) and pipelining on/off, which the harness already runs.

### Results

- **P8.1, T5** (`Classpath.lean`). External units, a stored snapshot per downstream, Zinc's initial external invalidation (`extInvalidated`). `inv_external` (T5a): from an up-to-date downstream with fresh snapshots, the new classpath leaves dirty only the changed sources and the holders of keys whose hash moved; `downstream_sound` (T5) composes it with T3a″. A library is the instance whose every key hashes the stamp: coarse, sound by the abstraction obligation alone.
- **P8.2, snapshot refresh** (`Classpath.lean`, `Snapshot.lean`). `fresh_refreshAll`: refreshing every upstream class keeps snapshots fresh. `fresh_refreshRef_local`: with local hashes, Zinc's rule (refresh the classes a recompiled unit references) is enough, and needs no freshness before the build. With a non-local hash (a key on `C` reading its ancestor `A`), it is not: `stale_after_revert` (edit `A`, `X` recompiles, `A`'s record is not refreshed, revert `A`, nothing is seen). Zinc today stores local APIs (materialised members), so its rule is sound; the Merkle PoC composes across subprojects, which made `macro-upstream-member-removed` possible, and its fix `9904df698` refreshes every changed upstream class (`refreshAll`). P8.0 (a scripted test for the gap on develop) is dropped: on develop the gap only re-detects a change, it cannot hide one.
- **P8.3, composed vs single loop** (`ImplicitScope.lean` `reportComposed`, `lake exe exhaustive composed`). One loop per project, upstream first, starting from Zinc's external walk as the bridge records it: direct parents only (`Dependency.scala` records `parents`), then transitive inheritors in the project, name-filtered clients, and nothing unless the upstream class's `apiHash` moved (`detectAPIChanges`). Over 1,080 runs per layout: develop and the fix agree with the single-loop encoding run for run (wrong sets and client recompiles), in `lib → app` and `lib → mid → app`. Without the `apiHash` fold they differ: 384 unclean composed against 312 in the single loop, which compares every key's hash across projects and so sees a summary change that Zinc's `apiHash` gate hides (smallest: `A` gains an implicit, `Z`, a client of `D extends A`, stays stale). The single-loop encoding is sound to use for the designs that publish everything through `apiHash`; ablations that move a name hash without `apiHash` need the composed run.
- **P8.4, pipelining** (`Pipelining.lean`, `Inline.lean`). `early_agreement` (T1 restated). `stale_after_failed_upstream`: an upstream fails after writing its early output, the downstream compiles against it, the upstream is reverted and sees no change against its last successful build, and the downstream keeps the failed output; `rollback_after_failed_upstream`: rolling the early output back with the rest fixes it (Zinc's pending `pipelining-failed-upstream-revert`). `pipelined_ne_final`: with a Scala 2 `@inline` body or a Java constant, a pipelined clean build differs from a non-pipelined one; Scala 3 `inline` agrees.
- **P8.5, keys from the tree** (`Tree.lean`, `TreeToy.lean`). `TCompiler`: `keysOf : Out → Keys`; T2 and T3a with the same proofs. Toy with `x += 1` (desugared through a failed lookup of `+=`) and a two-binder extractor pattern (the pattern matcher's `_1`, `_2` and an arity check on `_3` after extraction). Zinc's extractor (`today`) fails coverage (`not_obligations_today`) and misses all three edits; recording the selectors fixes the field-type edit only; recording the failed lookup and the `_3` sentinel (`fixed`) meets the obligations (`obligations_fixed`) and is clean on all three.
- **P8.7, bodies as API** (`Inline.lean`). Today's hash leaves a Scala 2 `@inline` body out (`not_obligations_today`, sbt/zinc#537): a body-only edit leaves `C` with the old inlined value, and is hidden whenever another hashed body changes too. Hashing every body meets the obligations in either view (`obligations_withBodies`).

### Steps

- [x] P8.0 Dropped (see P8.2).
- [x] P8.1 Projects, external units, snapshots, initial invalidation; stamp abstraction; T5 and the DAG corollary.
- [x] P8.2 Snapshot freshness: Zinc's refresh rule as a checked example (counterexample or proof).
- [x] P8.3 Composed run vs single loop with the cross-project policy, on the `Erasure` and `ImplicitScope` spaces.
- [x] P8.4 Pipelining: early and final interfaces, early agreement, failure after early output.
- [x] P8.5 Keys from the tree, two-phase tasks, anticipatory keys.
- [ ] P8.6 Source files and sealed hierarchies. Not started: the same-file rule makes the children query local to the parent's file, so the model's interest is in making units files; Java `permits` (retronym/zinc#21) is an abstraction failure (the hash omitted the clause), not a non-local query.
- [x] P8.7 Inline bodies.
- [ ] P8.8 `library` layout and pipelining in the conformance dump. Not started; needs the harness (retronym/zinc#25).

## Phase 9 — termination, additions, sealed hierarchies

- [x] P9.1 `PingPong.lean`: without `transitiveStep`, Zinc's loop need not terminate. Zinc's next round is the invalidated classes plus the classes whose API changed (the seed of `invalidateByInheritance`), `zincPolicy`; so two mutually inferred classes recompile together and cannot alternate, but three can, a pair per round. Three classes in a read cycle, joint compilation at a common fixed point, obligations proved (a first version assumed every table short, which made its obligations theorem vacuous; tables are now `Fin 3 → ℕ`). From a per-unit fixed point, a table edit makes Zinc's loop rotate through the pairs with period 6: `zinc_diverges` for every amount of fuel; `transitiveStep_stops`. `lake exe exhaustive pingpong` (12,402 runs): the model's old loop never stops on 1,080 runs (900 on two-class cycles), Zinc's rule on 180 (all three-class cycles), Zinc's rule with `transitiveStep 3` on none. **Confirmed in Zinc**: scripted test `inferred-type-cycle-rounds` (retronym/zinc branch `claude/inferred-type-cycle-rounds`), `C.z = Some(A.x)` over `A.x = B.y`, `B.y = C.z`, with `transitiveStep = 6`: the log shows the pairs `B C`, `A B`, `A C`, `B C`, `A B` with the types growing one `Some` per cycle, then all three at cycle 7 and the cyclic-inference error a clean build reports.
- [x] P9.2 `Embed.lean`: the local `Compiler` lifts to `NCompiler` (`lift_obligations`, `zinc_lift`), ported from the talk's V2 snapshot.
- [x] P9.3 `Added.lean`: added and deleted classes as edits from and to an absent source. Keys from the tree (`TCompiler`). A class added in an inner package scope (`a.b.Foo` for a client in `package a; package b` that resolved `a.Foo`) is missed: the tree shows the resolved class only, and Zinc invalidates only the added class's dependents (`invalidateInitial` schedules added sources and nothing else). Recording the scopes searched meets the obligations. Deletion is caught by the key on the resolved class. **Confirmed on Zinc `develop`**, Scala 2.13 and 3, for an inner package scope and for a wildcard import that now supplies the name (over the client's package, or over `scala.Option`); not for an import over a class added to the client's package (the import wins). Pending scripted tests `added-class-*` (retronym/zinc branch `claude/added-class-inner-package`); probes showed the incremental build compiling only the added file and succeeding, and a clean build failing. Cheap fix: on an addition, invalidate the users of the added class's simple name.
- [x] P9.4 `Sealed.lean`: exhaustivity reads a sealed parent's children; the same-file rule (and Java's `permits`) keeps the query local to the parent, and a hash covering the children meets the obligations. A hash without them (Zinc's `ClassToAPI` for Java before retronym/zinc#21) fails abstraction; adding a permitted subclass leaves the client without its warning (`java_permits_wrong`).
- [ ] Future: files as recompilation units (Zinc recompiles every class of an invalidated file); a scripted variant of P9.3 under Scala 3 and with an explicit import (precedence rules differ); class vs companion keys (sbt/zinc#1796).

## Phase 10 — name resolution and implicits: see `PLAN-names.md`

## Phase 11 — Scala 3 `inline` and opaque types: see `PLAN-inline.md`

## Phase 12 — Java in mixed builds, name resolution and sealed hierarchies: see `PLAN-java.md`

## Phase 13 — name resolution and givens across subprojects (the `split` layout): see `PLAN-split.md`

## Phase 14 — compile order and pipelining, a Java unit's two interfaces: see `PLAN-order.md`
