# Zinc soundness in Lean 4 — plan

A small Lean 4 + Mathlib model of §22 of `talk.md`: Zinc's invalidation loop is sound *relative to stated obligations on the compiler bridge*. Nothing here verifies scalac; the hypotheses of the theorems are the deliverable. They are the written spec for `ExtractAPI` / `ExtractUsedNames`.

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
