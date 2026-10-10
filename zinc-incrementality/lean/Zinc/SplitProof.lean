import Zinc.Classpath
import Mathlib.Data.Fintype.Option

/-!
# Name resolution across subprojects, proved

`Split.lean` checks its rules on the enumerated bases (an executable spec, brute force). Here the
same rules are stated over every program of the slot language and proved by case analysis, with
no enumeration.

## The slot language

A client looks a simple name up in scopes `0, 1, …, n-1`, in search order, any number of them
(Scala 2 and Scala 3 differ only in the order and in the ambiguities). Scope `j` binds the name
or not (`b j`), and is

* `pinned` when Zinc records an edge from a class of the client's file that uses the name to the
  scope's class, whatever the client resolved to: the inherited `P`, the block import's `V`, the
  explicit import's `X`, a wildcard-imported `W` charged to a class that uses the name;
* `required` when the client fails to compile without a binding there (an explicit import's
  selector); a required scope is pinned;
* `topLevel` when a binding is a class of its own (a file), as a class of a package;
* `upstream` when it lives in another subproject.

The client resolves to the first scope that binds, unless an ambiguity applies. The ambiguities of
both compilers ask for two bindings, so they are monotone: removing bindings cannot create one
(`Amb.mono`). Zinc records, besides the pinned edges, an edge to the class owning the resolved
symbol. An edit changes any set of bindings.

## Rules

* `today`: a changed scope with an edge: pinned, or the resolved one. Inside a subproject this is
  `IncrementalCommon`'s internal rule (the resolved class's API changes, or its source is
  deleted); across subprojects it is `invalidateClassesExternally` on the upstream classes in
  `allExternals` (`Split.ext_eq_internal` checks the correspondence on the bases).
* `cheap` (retronym/zinc#34): also a top-level scope of the client's own subproject that gained a
  binding.
* `proposed`: also any unpinned scope that gained a binding, upstream or not: the users of the
  simple name of an added top-level class anywhere on the classpath, or of a name added to a
  package object. (An unpinned scope that is not top-level is a package object, or a wildcard
  import charged to a class that does not use the name; charging the import to every class of the
  file makes the latter pinned.)

## Results

* `proposed_sound`: under `proposed`, the client is invalidated or its resolution is unchanged,
  for every program and every edit.
* `today_misses_added_class`, `cheap_misses_upstream_class`, `cheap_misses_package_object`: the
  counterexamples, two scopes each, decided by evaluation (`decide`).
* `Spec` (below): the specification, an `NCompiler` (`NonLocalAns.lean`) whose units are split
  into `Up` and `S` as in `Classpath.lean`. Today's keys fail coverage on the upstream miss
  (`today_not_obligations`); #34's key fails abstraction across subprojects
  (`cheap_not_obligations`, the trace of `added-class-upstream`) and meets the obligations within
  one (`cheap_obligations_of_local`); the cross-subproject key meets them (`cross_obligations`), so
  T5 applies (`cross_downstream_sound`).

The slot language and `Spec` agree on what matters: `proposed` invalidates on an added binding,
`cross` on any change of a binding of the name anywhere (its hash is symmetric), which also fires
on a deletion in a scope the lookup did not reach. `proposed_sound` says the additions are enough;
the deletions are `cross`'s over-invalidation.
-/

namespace Zinc.SplitProof

structure Scope where
  pinned : Bool
  required : Bool
  topLevel : Bool
  upstream : Bool
  deriving DecidableEq, Repr

/-- The first scope below `n` that binds. -/
def first (b : ℕ → Bool) : ℕ → Option ℕ
  | 0 => none
  | n + 1 =>
    match first b n with
    | some i => some i
    | none => if b n then some n else none

theorem first_spec (b : ℕ → Bool) : ∀ n,
    (∀ i, first b n = some i ↔ i < n ∧ b i = true ∧ ∀ j < i, b j = false) ∧
    (first b n = none ↔ ∀ j < n, b j = false) := by
  intro n
  induction n with
  | zero => simp [first]
  | succ n ih =>
    obtain ⟨ihs, ihn⟩ := ih
    cases h : first b n with
    | some i₀ =>
      obtain ⟨hi₀, hb₀, hlt₀⟩ := (ihs i₀).1 h
      simp only [first, h]
      refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
      · intro e; cases e; exact ⟨by omega, hb₀, hlt₀⟩
      · rintro ⟨_, hb, hlt⟩
        rcases Nat.lt_trichotomy i i₀ with hl | rfl | hl
        · rw [hlt₀ i hl] at hb; cases hb
        · rfl
        · rw [hlt i₀ hl] at hb₀; cases hb₀
      · simp only [reduceCtorEq, false_iff, not_forall]
        exact ⟨i₀, by omega, by simp [hb₀]⟩
    | none =>
      have hall := ihn.1 h
      simp only [first, h]
      refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
      · intro e
        split at e
        · cases e
          refine ⟨by omega, by assumption, hall⟩
        · cases e
      · rintro ⟨hi, hb, hlt⟩
        have : i = n := by
          rcases Nat.lt_or_ge i n with hl | hl
          · rw [hall i hl] at hb; cases hb
          · omega
        subst this
        simp [hb]
      · constructor
        · intro e j hj
          split at e
          · cases e
          · rcases Nat.lt_or_ge j n with hl | hl
            · exact hall j hl
            · have : j = n := by omega
              subst this; simpa using ‹¬b j = true›
        · intro hj
          have : b n = false := hj n (by omega)
          simp [this]

theorem first_some {b : ℕ → Bool} {n i : ℕ} :
    first b n = some i ↔ i < n ∧ b i = true ∧ ∀ j < i, b j = false := (first_spec b n).1 i

theorem first_none {b : ℕ → Bool} {n : ℕ} : first b n = none ↔ ∀ j < n, b j = false :=
  (first_spec b n).2

/-- A client: its scopes, how many, and an ambiguity that needs bindings (monotone). -/
structure Client where
  n : ℕ
  sc : ℕ → Scope
  amb : (ℕ → Bool) → Prop
  mono : ∀ b b', (∀ j < n, b' j = true → b j = true) → amb b' → amb b
  pinned_of_required : ∀ j, (sc j).required = true → (sc j).pinned = true

/-- The client compiles: no ambiguity, and every required scope binds. -/
def Client.ok (c : Client) (b : ℕ → Bool) : Prop :=
  ¬ c.amb b ∧ ∀ j < c.n, (c.sc j).required = true → b j = true

def Client.resolve (c : Client) (b : ℕ → Bool) : Option ℕ := first b c.n

def changed (b b' : ℕ → Bool) (j : ℕ) : Prop := b j ≠ b' j

def added (b b' : ℕ → Bool) (j : ℕ) : Prop := b j = false ∧ b' j = true

/-- Zinc today, inside a subproject or across: a changed scope with an edge. -/
def Client.today (c : Client) (b b' : ℕ → Bool) : Prop :=
  ∃ j < c.n, changed b b' j ∧ ((c.sc j).pinned = true ∨ c.resolve b = some j)

/-- retronym/zinc#34: also an added top-level class in the client's subproject. -/
def Client.cheap (c : Client) (b b' : ℕ → Bool) : Prop :=
  c.today b b' ∨ ∃ j < c.n, added b b' j ∧ (c.sc j).topLevel = true ∧ (c.sc j).upstream = false

/-- The proposal: also any unpinned scope that gained a binding, in any subproject. -/
def Client.proposed (c : Client) (b b' : ℕ → Bool) : Prop :=
  c.today b b' ∨ ∃ j < c.n, added b b' j ∧ (c.sc j).pinned = false

instance (c : Client) (b b' : ℕ → Bool) : Decidable (c.today b b') := by
  unfold Client.today changed; infer_instance
instance (c : Client) (b b' : ℕ → Bool) : Decidable (c.cheap b b') := by
  unfold Client.cheap added; infer_instance
instance (c : Client) (b b' : ℕ → Bool) : Decidable (c.proposed b b') := by
  unfold Client.proposed added; infer_instance

/-- If no scope below `n` gained a binding, and the one resolved to keeps it, resolution stands. -/
theorem first_stable (b b' : ℕ → Bool) (n : ℕ) (hadd : ∀ j < n, b' j = true → b j = true)
    (hres : ∀ i, first b n = some i → b' i = true) : first b' n = first b n := by
  cases h : first b n with
  | none =>
    rw [first_none] at h ⊢
    intro j hj
    cases hb : b' j
    · rfl
    · have := hadd j hj hb
      rw [h j hj] at this; cases this
  | some i =>
    obtain ⟨hi, _, hlt⟩ := first_some.1 h
    rw [first_some]
    refine ⟨hi, hres i h, fun j hj => ?_⟩
    cases hb : b' j
    · rfl
    · have := hadd j (by omega) hb
      rw [hlt j hj] at this; cases this

/-- **The proposed rule is sound for resolution.** For every client compiling before the edit,
and every edit: the client is invalidated, or it still compiles and resolves to the same scope.
-/
theorem proposed_sound (c : Client) (b b' : ℕ → Bool) (hok : c.ok b) :
    c.proposed b b' ∨ (c.ok b' ∧ c.resolve b' = c.resolve b) := by
  by_cases hp : c.proposed b b'
  · exact .inl hp
  right
  -- no scope gained a binding: a pinned one would be `today`, an unpinned one `proposed`
  have hadd : ∀ j < c.n, b' j = true → b j = true := by
    intro j hj hb'
    by_contra hb
    have hb : b j = false := by simpa using hb
    apply hp
    cases hpin : (c.sc j).pinned
    · exact .inr ⟨j, hj, ⟨hb, hb'⟩, hpin⟩
    · exact .inl ⟨j, hj, by simp [changed, hb, hb'], .inl hpin⟩
  -- a pinned scope did not change
  have hpinned : ∀ j < c.n, (c.sc j).pinned = true → b' j = b j := by
    intro j hj hpin
    by_contra hne
    exact hp (.inl ⟨j, hj, fun h => hne h.symm, .inl hpin⟩)
  -- the resolved scope did not change
  have hres : ∀ i, first b c.n = some i → b' i = true := by
    intro i hi
    obtain ⟨hin, hbi, _⟩ := first_some.1 hi
    by_contra hne
    exact hp (.inl ⟨i, hin, by simp_all [changed], .inr hi⟩)
  refine ⟨⟨?_, ?_⟩, first_stable b b' c.n hadd hres⟩
  · exact fun hamb => hok.1 (c.mono b b' hadd hamb)
  · intro j hj hreq
    rw [hpinned j hj (c.pinned_of_required j hreq)]
    exact hok.2 j hj hreq

/-! ## Counterexamples: two scopes each, decided by evaluation -/

/-- A top-level class of a package, in another subproject or not. -/
def cls (up : Bool) : Scope := ⟨false, false, true, up⟩

/-- A member of a package object. -/
def pobj (up : Bool) : Scope := ⟨false, false, false, up⟩

/-- A client searching scope `0` before scope `1`, with no ambiguity. -/
def two (s₀ s₁ : Scope) (h₀ : s₀.required = false) (h₁ : s₁.required = false) : Client where
  n := 2
  sc := fun j => if j = 0 then s₀ else s₁
  amb := fun _ => False
  mono := fun _ _ _ h => h
  pinned_of_required := by
    intro j h
    split at h <;> simp_all

/-- Before: only scope `1` binds. After: both. -/
def b₁ : ℕ → Bool := fun j => j == 1
def b₂ : ℕ → Bool := fun _ => true

/-- The client resolves to scope `1` before and to scope `0` after. -/
theorem shadowed (c : Client) (h : c.n = 2) : c.resolve b₁ = some 1 ∧ c.resolve b₂ = some 0 := by
  simp [Client.resolve, h, first, b₁, b₂]

/-- **F1 today**: a class added in an inner package, in any subproject. -/
theorem today_misses_added_class (up : Bool) :
    ¬ (two (cls up) (cls up) rfl rfl).today b₁ b₂ := by
  cases up <;> simp [Client.today, Client.resolve, two, changed, first, b₁, b₂, cls]

/-- **#34 within a subproject**: the added class invalidates the client. -/
theorem cheap_catches_local_class : (two (cls false) (cls false) rfl rfl).cheap b₁ b₂ :=
  .inr ⟨0, by decide, ⟨rfl, rfl⟩, rfl, rfl⟩

/-- **#34 across subprojects**: an added upstream class does not. -/
theorem cheap_misses_upstream_class : ¬ (two (cls true) (cls true) rfl rfl).cheap b₁ b₂ := by
  simp [Client.cheap, Client.today, Client.resolve, two, changed, added, first, b₁, b₂, cls]

/-- **F2**: nor does a member added to a package object, in any subproject. -/
theorem cheap_misses_package_object (up : Bool) :
    ¬ (two (pobj up) (cls up) rfl rfl).cheap b₁ b₂ := by
  cases up <;> simp [Client.cheap, Client.today, Client.resolve, two, changed, added, first, b₁, b₂,
    cls, pobj] <;> decide

/-- The proposal catches both, upstream. -/
theorem proposed_catches : (two (cls true) (cls true) rfl rfl).proposed b₁ b₂ ∧
    (two (pobj true) (cls true) rfl rfl).proposed b₁ b₂ :=
  ⟨.inr ⟨0, by decide, ⟨rfl, rfl⟩, rfl⟩, .inr ⟨0, by decide, ⟨rfl, rfl⟩, rfl⟩⟩

/-- #34 is sound exactly where every unpinned scope is a top-level class of the client's own
subproject: there `cheap` is `proposed`. -/
theorem cheap_sound_of_local (c : Client) (b b' : ℕ → Bool) (hok : c.ok b)
    (hloc : ∀ j < c.n, (c.sc j).pinned = false → (c.sc j).topLevel = true ∧ (c.sc j).upstream = false) :
    c.cheap b b' ∨ (c.ok b' ∧ c.resolve b' = c.resolve b) := by
  rcases proposed_sound c b b' hok with (h | ⟨j, hj, ha, hpin⟩) | h
  · exact .inl (.inl h)
  · exact .inl (.inr ⟨j, hj, ha, hloc j hj hpin⟩)
  · exact .inr h

/-! ## The specification: an `NCompiler` with upstream and downstream units

Units: the client (`none`) and scopes `some i`, `n` of them, each with its flags (`sc`). A scope is
in `Up` (another subproject) or in `S` (the client's), as `Classpath.lean` splits units. A scope's
interface is whether it binds `Foo`. The client's task is the lookup: ask `bound i` for scope
`0, 1, …` and stop at the first hit; its trace is what it read, misses included.

Keys (`Design`):

* `today`: an existence key (`presence`) on the scope the lookup stopped at (the owner of the
  resolved symbol) and on every pinned scope (inheritance, imports charged to a user of the name).
* `cheap` (retronym/zinc#34): also `named false`, the users of the name `Foo` against the
  top-level classes named `Foo`. It claims every top-level scope (`covers`), but its hash is
  computed over one subproject's analysis: the top-level scopes of `S`.
* `cross`: `named true`, the same key with its hash over every scope of `Up ∪ S`, any kind (a
  top-level class or a package object member).
* `searched`: an existence key on every scope asked.

Results: `today` fails coverage on the upstream miss (`today_not_obligations`); `cheap` fails
abstraction across subprojects (`cheap_not_abstraction`, the trace of the pending scripted test
`added-class-upstream`) and meets the obligations when every top-level scope is local and every
other scope pinned (`cheap_obligations_of_local`); `cross` and `searched` meet the obligations, so
T3a″ and T5 apply (`cross_downstream_sound`). -/

namespace Spec

variable {n : ℕ}

abbrev U (n : ℕ) := Option (Fin n)

instance : Fintype (U n) := inferInstanceAs (Fintype (Option (Fin n)))
instance : DecidableEq (U n) := inferInstanceAs (DecidableEq (Option (Fin n)))

inductive Src | bind (x : Bool) | client
  deriving DecidableEq

inductive Q | binds
  deriving DecidableEq

inductive K | presence | named (cross : Bool)
  deriving DecidableEq

inductive Design | today | cheap | cross | searched
  deriving DecidableEq

structure Out where
  iface : Bool
  res : Option ℕ
  deriving DecidableEq

abbrev T (n : ℕ) := Task (U n × Q) (fun _ => Bool) Out

variable (n) in
/-- The client's lookup from scope `k` on. -/
def search (k : ℕ) : T n :=
  if h : k < n then
    .ask (some ⟨k, h⟩, .binds) fun x => if x then .pure ⟨false, some k⟩ else search (k + 1)
  else .pure ⟨false, none⟩
termination_by n - k

variable (n) in
def unit : Src → T n
  | .bind x => .pure ⟨x, none⟩
  | .client => search n 0

def ifaceSrc : Src → Bool
  | .bind x => x
  | .client => false

def answer (I : U n → Bool) (q : U n × Q) : Bool := I q.1

def group (G : Finset (U n)) (src : U n → Src) (I : U n → Bool) : U n → Out :=
  fun u => (unit n (src u)).run (answer fun v => if v ∈ G then ifaceSrc (src v) else I v)

variable (sc : Fin n → Scope)

/-- The scopes a `named` key's hash reads: `cheap`'s, the top-level scopes of `S`; `cross`'s, all. -/
def reads (cross : Bool) (i : Fin n) : Bool := cross || ((sc i).topLevel && !(sc i).upstream)

def π (I : U n → Bool) : U n → K → List Bool
  | u, .presence => [I u]
  | none, .named b => (List.finRange n).map fun i => reads sc b i && I (some i)
  | some _, .named _ => []

def hashDeps (_ : U n → Bool) : U n → Finset (U n)
  | none => Finset.univ
  | some i => {some i}

/-- The `named` key a design records: `cheap` the one-subproject key, `cross` the other. -/
def namedOf : Design → Option Bool
  | .cheap => some false
  | .cross => some true
  | _ => none

/-- What a key claims to cover: an existence key its scope; the design's `named` key every
top-level scope (#34's claim, whatever its hash reads) or, for `cross`, every scope. -/
def covers (d : Design) (_ : U n → Bool) (q : U n × Q) : U n × K → Prop
  | (u, .presence) => q.1 = u
  | (none, .named b) => namedOf d = some b ∧ ∃ i, q.1 = some i ∧ (b = true ∨ (sc i).topLevel = true)
  | (some _, .named _) => False

def pinnedKeys : Finset (U n × K) :=
  ((List.finRange n).filter fun i => (sc i).pinned).map (fun i => (some i, K.presence)) |>.toFinset

/-- The keys a compilation records; a scope's compilation asks nothing, and records nothing. -/
def keys : Design → U n → List (U n × Q) → Finset (U n × K)
  | .today, _, tr => (tr.getLast?.map fun q => (q.1, K.presence)).toList.toFinset ∪ pinnedKeys sc
  | .cheap, _, tr =>
    (tr.getLast?.map fun q => (q.1, K.presence)).toList.toFinset ∪ pinnedKeys sc ∪ {(none, .named false)}
  | .cross, _, tr =>
    (tr.getLast?.map fun q => (q.1, K.presence)).toList.toFinset ∪ pinnedKeys sc ∪ {(none, .named true)}
  | .searched, _, tr => (tr.map fun q => (q.1, K.presence)).toFinset

def compiler (d : Design) : NCompiler (U n) Src Out Bool K (List Bool) Q (fun _ => Bool) where
  unit := unit n
  group := group
  iface := Out.iface
  answer := answer
  π := π sc
  hashDeps := hashDeps
  keys := keys sc d
  covers := covers sc d

/-! ### The lookup's trace -/

theorem iface_search (e : Task.Env (U n × Q) (fun _ => Bool)) :
    ∀ k, ((search n k).run e).iface = false := by
  intro k
  induction k using search.induct n with
  | case1 k h ih =>
    rw [search, dite_eq_left_of_eq_true (eq_true h), Task.run_ask]
    split
    · rfl
    · exact ih
  | case2 k h => rw [search, dite_eq_right_of_eq_false (eq_false h)]; rfl

theorem iface_run (s : Src) (e : Task.Env (U n × Q) (fun _ => Bool)) :
    ((unit n s).run e).iface = ifaceSrc s := by
  cases s with
  | bind x => rfl
  | client => exact iface_search e 0

/-- Every query asks a scope `i ≥ k`, after misses on the scopes between. -/
theorem trace_search (e : Task.Env (U n × Q) (fun _ => Bool)) :
    ∀ k, ∀ q ∈ (search n k).trace e, ∃ i, ∃ h : i < n, k ≤ i ∧ q = (some ⟨i, h⟩, .binds) ∧
      ∀ j, ∀ hj : j < n, k ≤ j → j < i → e (some ⟨j, hj⟩, .binds) = false := by
  intro k
  induction k using search.induct n with
  | case1 k h ih =>
    intro q hq
    rw [search, dite_eq_left_of_eq_true (eq_true h), Task.trace_ask] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨k, h, le_refl k, rfl, fun j _ h1 h2 => absurd h2 (by omega)⟩
    · split at hq
      · simp at hq
      · rename_i hmiss
        obtain ⟨i, hi, hki, rfl, hlt⟩ := ih q hq
        refine ⟨i, hi, by omega, rfl, fun j hj h1 h2 => ?_⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · simpa using hmiss
        · exact hlt j hj h1 h2
  | case2 k h => intro q hq; rw [search, dite_eq_right_of_eq_false (eq_false h)] at hq; simp at hq

/-- A hit ends the lookup: it is the last query. -/
theorem hit_last (e : Task.Env (U n × Q) (fun _ => Bool)) :
    ∀ k, ∀ q ∈ (search n k).trace e, e q = true → ((search n k).trace e).getLast? = some q := by
  intro k
  induction k using search.induct n with
  | case1 k h ih =>
    intro q hq hhit
    rw [search, dite_eq_left_of_eq_true (eq_true h), Task.trace_ask] at hq ⊢
    rcases List.mem_cons.1 hq with rfl | hq
    · simp [hhit]
    · split at hq
      · simp at hq
      · rename_i hmiss
        simp only [hmiss, Bool.false_eq_true, ite_false]
        have hl := ih q hq hhit
        have hne : (search n (k + 1)).trace e ≠ [] := List.ne_nil_of_mem hq
        rw [List.getLast?_cons, hl]
        simp
  | case2 k h => intro q hq; rw [search, dite_eq_right_of_eq_false (eq_false h)] at hq; simp at hq

/-! ### Obligations: compositionality, abstraction of the keys, coverage per design -/

theorem comp (d : Design) : ∀ (G : Finset (U n)) (src : U n → Src) (I : U n → Bool), ∀ u ∈ G,
    (compiler sc d).group G src I u =
      ((compiler sc d).unit (src u)).run ((compiler sc d).answer
        (NCompiler.override I G ((compiler sc d).iface ∘ (compiler sc d).group G src I))) := by
  intro G src I u _
  have : NCompiler.override I G (Out.iface ∘ group G src I) =
      fun v => if v ∈ G then ifaceSrc (src v) else I v := by
    funext v
    simp only [NCompiler.override, Function.comp]
    split
    · simp only [group, iface_run]
    · rfl
  show group G src I u = (unit n (src u)).run (answer (NCompiler.override I G (Out.iface ∘ group G src I)))
  rw [this]
  rfl

theorem locality (d : Design) : ∀ (I I' : U n → Bool) (c : U n),
    (∀ u ∈ (compiler sc d).hashDeps I c, I u = I' u) → ∀ k, (compiler sc d).π I c k = (compiler sc d).π I' c k := by
  intro I I' c h k
  cases c with
  | none =>
    have hall : ∀ u, I u = I' u := fun u => h u (by simp [compiler, hashDeps])
    cases k <;> simp [compiler, π, hall]
  | some i =>
    have hi : I (some i) = I' (some i) := h (some i) (by simp [compiler, hashDeps])
    cases k <;> simp [compiler, π, hi]

/-- The keys are honest where their hash reads what they cover: an existence key always; `cheap`'s
`named` key when every top-level scope is one its hash reads (all in `S`). -/
theorem abstraction_of (d : Design)
    (hread : d = .cheap → ∀ i, (sc i).topLevel = true → reads sc false i = true) :
    ∀ (I I' : U n → Bool) (k : U n × K), (compiler sc d).π I k.1 k.2 = (compiler sc d).π I' k.1 k.2 →
      ∀ q, (compiler sc d).covers I q k →
        (compiler sc d).answer I q = (compiler sc d).answer I' q ∧ (compiler sc d).covers I' q k := by
  rintro I I' ⟨u, k⟩ h q hc
  refine ⟨?_, hc⟩
  show I q.1 = I' q.1
  cases k with
  | presence =>
    simp only [compiler, π, List.cons.injEq, and_true] at h
    simp only [compiler, covers] at hc
    rw [hc]; exact h
  | named b =>
    cases u with
    | some _ => simp [compiler, covers] at hc
    | none =>
      obtain ⟨hd, i, hq, hb⟩ := hc
      rw [hq]
      have hr : reads sc b i = true := by
        cases b
        · have : d = .cheap := by cases d <;> simp_all [namedOf]
          exact hread this i (by simpa using hb)
        · rfl
      simp only [compiler, π] at h
      have := (List.map_inj_left.1 h) i (List.mem_finRange i)
      simpa [hr] using this

theorem trace_unit (I : U n → Bool) (s : Src) :
    ∀ q ∈ (unit n s).trace (answer I), ∃ i, q = (some i, Q.binds) ∧
      (I (some i) = true → ((unit n s).trace (answer I)).getLast? = some q) := by
  intro q hq
  cases s with
  | bind x => simp [unit] at hq
  | client =>
    obtain ⟨i, hi, -, rfl, -⟩ := trace_search (answer I) 0 q hq
    exact ⟨⟨i, hi⟩, rfl, fun hhit => hit_last (answer I) 0 _ hq hhit⟩

theorem last_key (d : Design) (hd : d ≠ .searched) (u : U n) (tr : List (U n × Q)) (q : U n × Q)
    (h : tr.getLast? = some q) : (q.1, K.presence) ∈ keys sc d u tr := by
  cases d <;> simp_all [keys]

theorem pinned_key (d : Design) (hd : d ≠ .searched) (u : U n) (tr : List (U n × Q)) (i : Fin n)
    (h : (sc i).pinned = true) : (some i, K.presence) ∈ keys sc d u tr := by
  have : (some i, K.presence) ∈ pinnedKeys sc := by simp [pinnedKeys, h]
  cases d <;> simp_all [keys]

theorem cross_coverage : ∀ (I : U n → Bool) (u : U n) (s : Src),
    ∀ q ∈ ((compiler sc .cross).unit s).trace ((compiler sc .cross).answer I),
      ∃ k ∈ (compiler sc .cross).keys u (((compiler sc .cross).unit s).trace ((compiler sc .cross).answer I)),
        (compiler sc .cross).covers I q k := by
  intro I u s q hq
  obtain ⟨i, rfl, -⟩ := trace_unit I s q hq
  exact ⟨(none, .named true), by simp [compiler, keys], rfl, i, rfl, .inl rfl⟩

theorem searched_coverage : ∀ (I : U n → Bool) (u : U n) (s : Src),
    ∀ q ∈ ((compiler sc .searched).unit s).trace ((compiler sc .searched).answer I),
      ∃ k ∈ (compiler sc .searched).keys u (((compiler sc .searched).unit s).trace ((compiler sc .searched).answer I)),
        (compiler sc .searched).covers I q k := by
  intro I u s q hq
  refine ⟨(q.1, .presence), ?_, rfl⟩
  show (q.1, K.presence) ∈ (List.map _ _).toFinset
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨q, hq, rfl⟩

/-- #34's key covers a lookup when every scope is pinned or a top-level class. -/
theorem cheap_coverage (hk : ∀ i, (sc i).pinned = true ∨ (sc i).topLevel = true) :
    ∀ (I : U n → Bool) (u : U n) (s : Src),
    ∀ q ∈ ((compiler sc .cheap).unit s).trace ((compiler sc .cheap).answer I),
      ∃ k ∈ (compiler sc .cheap).keys u (((compiler sc .cheap).unit s).trace ((compiler sc .cheap).answer I)),
        (compiler sc .cheap).covers I q k := by
  intro I u s q hq
  obtain ⟨i, rfl, hlast⟩ := trace_unit I s q hq
  cases hI : I (some i)
  · rcases hk i with hp | ht
    · exact ⟨(some i, .presence), pinned_key sc .cheap (by decide) u _ i hp, rfl⟩
    · exact ⟨(none, .named false), by simp [compiler, keys], rfl, i, rfl, .inr ht⟩
  · exact ⟨(some i, .presence), last_key sc .cheap (by decide) u _ _ (hlast hI), rfl⟩

/-- **The cross-subproject key meets the obligations.** -/
theorem cross_obligations : (compiler sc .cross).Obligations where
  comp := comp sc .cross
  coverage := cross_coverage sc
  abstraction := abstraction_of sc .cross (by simp)
  locality := locality sc .cross

theorem searched_obligations : (compiler sc .searched).Obligations where
  comp := comp sc .searched
  coverage := searched_coverage sc
  abstraction := abstraction_of sc .searched (by simp)
  locality := locality sc .searched

/-- **#34 meets them inside one subproject**: every scope is pinned or a top-level class, and every
top-level class is in `S`. -/
theorem cheap_obligations_of_local (hk : ∀ i, (sc i).pinned = true ∨ (sc i).topLevel = true)
    (hloc : ∀ i, (sc i).topLevel = true → (sc i).upstream = false) : (compiler sc .cheap).Obligations where
  comp := comp sc .cheap
  coverage := cheap_coverage sc hk
  abstraction := abstraction_of sc .cheap (fun _ i ht => by simp [reads, ht, hloc i ht])
  locality := locality sc .cheap

/-! ### Across subprojects -/

/-- The scopes in other subprojects. -/
def Up : Finset (U n) := Finset.univ.filter fun u => u.elim false fun i => (sc i).upstream

/-- The client's subproject: the client and the local scopes. -/
def S : Finset (U n) := Finset.univ.filter fun u => !(u.elim false fun i => (sc i).upstream)

theorem disjoint_Up_S : Disjoint (Up sc) (S sc) := by
  rw [Finset.disjoint_left]
  intro u hu hS
  simp only [Up, S, Finset.mem_filter, Finset.mem_univ, true_and] at hu hS
  simp_all

/-- **T5 for the cross-subproject key.** From an up-to-date downstream with fresh snapshots of the
upstream scopes, replacing the upstream outputs and running Zinc's loop from the changed sources and
the units whose keys moved against the snapshot (`extInvalidated`): if the loop stops, every unit of
the client's subproject is up to date against the new upstream, whatever the program, the edit and
the (sound) policy. -/
theorem cross_downstream_sound (src₀ src : U n → Src) (s : Compiler.State (U n) Out K)
    (snap : U n → Bool) (o : U n → Out) (D : Finset (U n)) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : (compiler sc .cross).Inv (S sc) src₀ s ∅)
    (hFresh : (compiler sc .cross).Fresh (Up sc) (S sc) s snap ∅)
    (P : Compiler.Policy (U n) Out K) (hP : P.Sound (S sc)) (fuel : ℕ) (R₀ : Finset (U n))
    (hR₀ : D ∪ (compiler sc .cross).extInvalidated (Up sc) (S sc) s snap
      (NCompiler.withUpstream (Up sc) s o) ⊆ R₀)
    (s' : Compiler.State (U n) Out K)
    (h : (compiler sc .cross).zinc (S sc) src P fuel 0 R₀ (NCompiler.withUpstream (Up sc) s o) = some s') :
    (compiler sc .cross).Inv (S sc) src s' ∅ :=
  (compiler sc .cross).downstream_sound (cross_obligations sc) (Up sc) (S sc) (disjoint_Up_S sc)
    src₀ src s snap o D hD hInv hFresh P hP fuel R₀ hR₀ s' h

/-! ### The witnesses: `added-class-upstream`

Two upstream scopes: `a.b.Foo` (scope 0, a class of the inner package) and `a.Foo` (scope 1). Before,
only `a.Foo` exists; after, both. -/

/-- Both scopes are top-level classes upstream, neither pinned. -/
def upClasses : Fin 2 → Scope := fun _ => ⟨false, false, true, true⟩

def before : U 2 → Bool := fun u => u == some 1
def after : U 2 → Bool := fun u => u == some 0 || u == some 1

theorem trace_before : (unit 2 .client).trace (answer before) = [(some 0, .binds), (some 1, .binds)] := by
  simp [unit, search, answer, before]

/-- **Today's keys miss the upstream lookup**: the client asked `bound a.b.Foo` (no), and records an
existence key on `a.Foo` only. -/
theorem today_not_obligations : ¬ (compiler upClasses .today).Obligations := by
  intro ob
  obtain ⟨k, hk, hc⟩ := ob.coverage before none .client (some 0, .binds)
    (by show _ ∈ (unit 2 .client).trace (answer before); rw [trace_before]; simp)
  change k ∈ keys upClasses .today none ((unit 2 .client).trace (answer before)) at hk
  rw [trace_before] at hk
  simp [keys, pinnedKeys, upClasses] at hk
  subst hk
  simp [compiler, covers] at hc

/-- **#34's key is not an abstraction across subprojects.** Its hash, over the client's subproject,
is the same before and after the upstream adds `a.b.Foo`; the lookup it claims to cover, `bound
a.b.Foo`, answers differently. -/
theorem cheap_not_abstraction :
    (compiler upClasses .cheap).π before none (.named false) = (compiler upClasses .cheap).π after none (.named false) ∧
    (compiler upClasses .cheap).covers before (some 0, .binds) (none, .named false) ∧
    (compiler upClasses .cheap).answer before (some 0, .binds) ≠ (compiler upClasses .cheap).answer after (some 0, .binds) := by
  refine ⟨?_, ⟨rfl, 0, rfl, .inr rfl⟩, by simp [compiler, answer, before, after]⟩
  simp [compiler, π, reads, upClasses]

theorem cheap_not_obligations : ¬ (compiler upClasses .cheap).Obligations := by
  intro ob
  obtain ⟨hπ, hc, hne⟩ := cheap_not_abstraction
  exact hne (ob.abstraction before after (none, .named false) hπ _ hc).1

/-- The cross-subproject key's hash moves. -/
theorem cross_moves :
    (compiler upClasses .cross).π before none (.named true) ≠ (compiler upClasses .cross).π after none (.named true) := by
  simp [compiler, π, reads, before, after, List.finRange]

/-! ## Phase 10: the rules for F1–F3, global or narrowed

`Names.lean`'s families as kinds of scope, beside `Scope`'s flags (`Ext`): a member of a package
object (F2, `pobj`); a wildcard import charged to a class of the file that does not use the name
(F3, `wildOther`, the unpinned `W`); a scope in a package the client reaches through a wildcard
import of the package (`imported`: `a.q.Foo`, `package object q`'s member). A top-level class is
`Scope.topLevel` (F1).

The rules record one key on the client, `rule`, whose hash reads the scopes the rules reach: #34
the top-level classes, F2 the package-object members; `global` reaches all of them, `narrowed` only
those of the enclosing packages and, when the bridge records `import q._` (`imports`), of the
imported ones. F3 pins `wildOther` scopes (an existence key, as if the import were charged to every
class of the file). In one client's view, `global` and `narrowed` with `imports` cover the same
scopes; they differ in the classes of other clients, which the enumeration counts (`User`, `Far`). -/

structure Ext where
  pobj : Bool
  wildOther : Bool
  imported : Bool
  deriving DecidableEq

inductive Reach | off | narrowed | global
  deriving DecidableEq

structure Rules where
  cheap : Reach := .off
  f2 : Reach := .off
  f3 : Bool := false
  imports : Bool := false
  deriving DecidableEq

def Reach.at (rc : Reach) (imports : Bool) (x : Ext) : Bool :=
  match rc with
  | .off => false
  | .global => true
  | .narrowed => !x.imported || imports

variable (sx : Fin n → Ext)

/-- The scopes the rules' key covers and its hash reads. -/
def ruled (r : Rules) (i : Fin n) : Bool :=
  ((sc i).topLevel && r.cheap.at r.imports (sx i)) || ((sx i).pobj && r.f2.at r.imports (sx i))

inductive KR | presence | rule
  deriving DecidableEq

def πR (r : Rules) (I : U n → Bool) : U n → KR → List Bool
  | u, .presence => [I u]
  | none, .rule => (List.finRange n).map fun i => ruled sc sx r i && I (some i)
  | some _, .rule => []

def coversR (r : Rules) (_ : U n → Bool) (q : U n × Q) : U n × KR → Prop
  | (u, .presence) => q.1 = u
  | (none, .rule) => ∃ i, q.1 = some i ∧ ruled sc sx r i = true
  | (some _, .rule) => False

/-- The `wildOther` scopes, pinned by F3. -/
def f3Keys (r : Rules) : Finset (U n × KR) :=
  if r.f3 then ((List.finRange n).filter fun i => (sx i).wildOther).map (fun i => (some i, KR.presence)) |>.toFinset
  else ∅

/-- Today's keys (the resolved scope, the pinned ones), F3's, and the rules' key. -/
def keysR (r : Rules) (_ : U n) (tr : List (U n × Q)) : Finset (U n × KR) :=
  (tr.getLast?.map fun q => (q.1, KR.presence)).toList.toFinset ∪
  (((List.finRange n).filter fun i => (sc i).pinned).map (fun i => (some i, KR.presence))).toFinset ∪
  f3Keys sx r ∪ {(none, KR.rule)}

def rules (r : Rules) : NCompiler (U n) Src Out Bool KR (List Bool) Q (fun _ => Bool) where
  unit := unit n
  group := group
  iface := Out.iface
  answer := answer
  π := πR sc sx r
  hashDeps := hashDeps
  keys := keysR sc sx r
  covers := coversR sc sx r

theorem rules_comp (r : Rules) : ∀ (G : Finset (U n)) (src : U n → Src) (I : U n → Bool), ∀ u ∈ G,
    (rules sc sx r).group G src I u =
      ((rules sc sx r).unit (src u)).run ((rules sc sx r).answer
        (NCompiler.override I G ((rules sc sx r).iface ∘ (rules sc sx r).group G src I))) := by
  intro G src I u _
  have : NCompiler.override I G (Out.iface ∘ group G src I) =
      fun v => if v ∈ G then ifaceSrc (src v) else I v := by
    funext v
    simp only [NCompiler.override, Function.comp]
    split
    · simp only [group, iface_run]
    · rfl
  show group G src I u = (unit n (src u)).run (answer (NCompiler.override I G (Out.iface ∘ group G src I)))
  rw [this]
  rfl

theorem rules_locality (r : Rules) : ∀ (I I' : U n → Bool) (c : U n),
    (∀ u ∈ (rules sc sx r).hashDeps I c, I u = I' u) → ∀ k, (rules sc sx r).π I c k = (rules sc sx r).π I' c k := by
  intro I I' c h k
  cases c with
  | none =>
    have hall : ∀ u, I u = I' u := fun u => h u (by simp [rules, hashDeps])
    cases k <;> simp [rules, πR, hall]
  | some i =>
    have hi : I (some i) = I' (some i) := h (some i) (by simp [rules, hashDeps])
    cases k <;> simp [rules, πR, hi]

theorem rules_abstraction (r : Rules) : ∀ (I I' : U n → Bool) (k : U n × KR),
    (rules sc sx r).π I k.1 k.2 = (rules sc sx r).π I' k.1 k.2 →
      ∀ q, (rules sc sx r).covers I q k →
        (rules sc sx r).answer I q = (rules sc sx r).answer I' q ∧ (rules sc sx r).covers I' q k := by
  rintro I I' ⟨u, k⟩ h q hc
  refine ⟨?_, hc⟩
  show I q.1 = I' q.1
  cases k with
  | presence =>
    simp only [rules, πR, List.cons.injEq, and_true] at h
    simp only [rules, coversR] at hc
    rw [hc]; exact h
  | rule =>
    cases u with
    | some _ => simp [rules, coversR] at hc
    | none =>
      obtain ⟨i, hq, hr⟩ := hc
      rw [hq]
      simp only [rules, πR] at h
      have := (List.map_inj_left.1 h) i (List.mem_finRange i)
      simpa [hr] using this

/-- **The rules cover the lookup** when every scope is pinned, pinned by F3, or reached. -/
theorem rules_coverage (r : Rules)
    (hk : ∀ i, (sc i).pinned = true ∨ (r.f3 = true ∧ (sx i).wildOther = true) ∨ ruled sc sx r i = true) :
    ∀ (I : U n → Bool) (u : U n) (s : Src),
    ∀ q ∈ ((rules sc sx r).unit s).trace ((rules sc sx r).answer I),
      ∃ k ∈ (rules sc sx r).keys u (((rules sc sx r).unit s).trace ((rules sc sx r).answer I)),
        (rules sc sx r).covers I q k := by
  intro I u s q hq
  obtain ⟨i, rfl, hlast⟩ := trace_unit I s q hq
  cases hI : I (some i)
  · rcases hk i with hp | ⟨h3, hw⟩ | hr
    · refine ⟨(some i, .presence), ?_, rfl⟩
      simp [rules, keysR, hp]
    · refine ⟨(some i, .presence), ?_, rfl⟩
      simp [rules, keysR, f3Keys, h3, hw]
    · exact ⟨(none, .rule), by simp [rules, keysR], i, rfl, hr⟩
  · refine ⟨(some i, .presence), ?_, rfl⟩
    have := hlast hI
    simp [rules, keysR, this]

/-- **The rules meet the obligations** (and so T3a″, `NCompiler.zinc_sound`) whenever every scope
of the lookup is pinned, a `wildOther` import with F3 on, or reached by #34 or F2. -/
theorem rules_obligations (r : Rules)
    (hk : ∀ i, (sc i).pinned = true ∨ (r.f3 = true ∧ (sx i).wildOther = true) ∨ ruled sc sx r i = true) :
    (rules sc sx r).Obligations where
  comp := rules_comp sc sx r
  coverage := rules_coverage sc sx r hk
  abstraction := rules_abstraction sc sx r
  locality := rules_locality sc sx r

/-- Names' slot language: every scope is pinned (`P`, `V`, `X`, `W` charged to a class that uses
the name), a `wildOther` import, a top-level class, or a package-object member. -/
def NamesScopes : Prop :=
  ∀ i, (sc i).pinned = true ∨ (sx i).wildOther = true ∨ (sc i).topLevel = true ∨ (sx i).pobj = true

/-- **#34 with F2 and F3, global**: the obligations hold for every names lookup. -/
theorem global_obligations (h : NamesScopes sc sx) :
    (rules sc sx { cheap := .global, f2 := .global, f3 := true }).Obligations :=
  rules_obligations sc sx _ fun i => by
    rcases h i with h | h | h | h
    · exact .inl h
    · exact .inr (.inl ⟨rfl, h⟩)
    · exact .inr (.inr (by simp [ruled, Reach.at, h]))
    · exact .inr (.inr (by simp [ruled, Reach.at, h]))

/-- **Narrowed, given recorded package imports**: the obligations hold for every names lookup. The
hypothesis `imports` is the bridge change (Scala 2's `Dependency`, dotc's `ExtractDependencies`). -/
theorem narrowed_obligations (h : NamesScopes sc sx) :
    (rules sc sx { cheap := .narrowed, f2 := .narrowed, f3 := true, imports := true }).Obligations :=
  rules_obligations sc sx _ fun i => by
    rcases h i with h | h | h | h
    · exact .inl h
    · exact .inr (.inl ⟨rfl, h⟩)
    · exact .inr (.inr (by simp [ruled, Reach.at, h]))
    · exact .inr (.inr (by simp [ruled, Reach.at, h]))

/-! ### Precision

After an edit from interfaces `I` to `I'`, a unit is **necessary** when an answer its lookup read
changed (T1's converse, as a definition), and **invalidated** when a key it recorded changed hash.
Sound keys invalidate every necessary unit; the **over-invalidation** is invalidated and not
necessary. -/

section Precision

variable {CUnit Src' Out' Iface K' Hash Q' : Type} {A : Q' → Type} [DecidableEq CUnit]
variable (C : NCompiler CUnit Src' Out' Iface K' Hash Q' A)

/-- An answer the unit's lookup read changed: the unit must recompile. -/
def Necessary (s : Src') (I I' : CUnit → Iface) : Prop :=
  ∃ q ∈ (C.unit s).trace (C.answer I), C.answer I q ≠ C.answer I' q

/-- A key the unit recorded changed hash: Zinc recompiles it. -/
def Invalidated (d : CUnit) (s : Src') (I I' : CUnit → Iface) : Prop :=
  ∃ k ∈ C.keys d ((C.unit s).trace (C.answer I)), C.π I k.1 k.2 ≠ C.π I' k.1 k.2

def OverInvalidated (d : CUnit) (s : Src') (I I' : CUnit → Iface) : Prop :=
  Invalidated C d s I I' ∧ ¬ Necessary C s I I'

/-- Sound keys invalidate every necessary unit. -/
theorem necessary_invalidated (ob : C.Obligations) (d : CUnit) (s : Src') (I I' : CUnit → Iface)
    (h : Necessary C s I I') : Invalidated C d s I I' := by
  obtain ⟨q, hq, hne⟩ := h
  by_contra hno
  obtain ⟨k, hk, hc⟩ := ob.coverage I d s q hq
  have : C.π I k.1 k.2 = C.π I' k.1 k.2 := by
    by_contra h'
    exact hno ⟨k, hk, h'⟩
  exact hne (ob.abstraction I I' k this q hc).1

end Precision

/-- **`searched` is exact**: it invalidates only when an answer the lookup read changed. -/
theorem searched_exact (d : U n) (s : Src) (I I' : U n → Bool)
    (h : Invalidated (compiler sc .searched) d s I I') : Necessary (compiler sc .searched) s I I' := by
  obtain ⟨⟨u, k⟩, hk, hne⟩ := h
  simp only [compiler, keys, List.mem_toFinset, List.mem_map] at hk
  obtain ⟨q, hq, hqk⟩ := hk
  simp only [Prod.mk.injEq] at hqk
  obtain ⟨rfl, rfl⟩ := hqk
  refine ⟨q, hq, fun he => hne ?_⟩
  simp only [compiler, π]
  simp only [compiler, answer] at he
  rw [he]

/-- **The narrowed rules invalidate no more than the global ones.** -/
theorem narrowed_le_global (d : U n) (s : Src) (I I' : U n → Bool) (imports : Bool)
    (h : Invalidated (rules sc sx { cheap := .narrowed, f2 := .narrowed, f3 := true, imports := imports }) d s I I') :
    Invalidated (rules sc sx { cheap := .global, f2 := .global, f3 := true }) d s I I' := by
  obtain ⟨⟨u, k⟩, hk, hne⟩ := h
  cases k with
  | presence =>
    refine ⟨(u, .presence), ?_, hne⟩
    simpa [rules, keysR, f3Keys] using hk
  | rule =>
    cases u with
    | some _ => simp [rules, keysR, f3Keys] at hk
    | none =>
      refine ⟨(none, .rule), by simp [rules, keysR], fun heq => hne ?_⟩
      simp only [rules, πR] at heq ⊢
      apply List.map_congr_left
      intro i _
      have := (List.map_inj_left.1 heq) i (List.mem_finRange i)
      by_cases hr : ruled sc sx { cheap := .narrowed, f2 := .narrowed, f3 := true, imports := imports } i = true
      · have hg : ruled sc sx { cheap := .global, f2 := .global, f3 := true } i = true := by
          simp only [ruled, Reach.at, Bool.or_eq_true, Bool.and_eq_true] at hr ⊢
          rcases hr with ⟨h1, _⟩ | ⟨h1, _⟩
          · simp [h1]
          · simp [h1]
        simpa [hr, hg] using this
      · simp [hr]

/-! ### F4 and F5 fail compositionality

Scala 2 (F4) and Scala 3 (F5) compile a class `a.b.Foo` (scope `c`) differently when a member
`Foo` of `package object b` (scope `m`) is compiled with it: Scala 3 reports a double definition,
Scala 2 emits the class's mirror without its `ScalaSignature`, which a later compile cannot read
as the class. Either way the class comes out unusable only from the joint compilation. That is a
failure of `comp`, not of coverage, so no key fixes it. -/

/-- Joint compilation where `c` and `m` interfere. -/
def jointGroup (c m : U n) (G : Finset (U n)) (src : U n → Src) (I : U n → Bool) : U n → Out :=
  fun u => if u = c ∧ c ∈ G ∧ m ∈ G ∧ ifaceSrc (src m) = true then ⟨false, none⟩ else group G src I u

/-- **F4/F5 refute `comp`**: with `a.b.Foo` and the package object's `Foo` compiled together, the
joint output differs from the per-unit compilation of the class against its group-mates. -/
theorem joint_not_comp : ¬ ∀ (G : Finset (U 2)) (src : U 2 → Src) (I : U 2 → Bool), ∀ u ∈ G,
    jointGroup (some 1) (some 0) G src I u =
      (unit 2 (src u)).run (answer (NCompiler.override I G (Out.iface ∘ jointGroup (some 1) (some 0) G src I))) := by
  intro h
  have := h {some 0, some 1} (fun _ => .bind true) (fun _ => false) (some 1) (by simp)
  simp [jointGroup, unit, ifaceSrc] at this

/-! ### Witnesses: two scopes, scope 1 the class `a.Foo` that binds -/

/-- Scope 0 of the kind given, scope 1 a top-level class `a.Foo`. -/
def two (s₀ : Scope) (x₀ : Ext) : (Fin 2 → Scope) × (Fin 2 → Ext) :=
  (fun i => if i = 0 then s₀ else ⟨false, false, true, false⟩,
   fun i => if i = 0 then x₀ else ⟨false, false, false⟩)

def only1 : U 2 → Bool := fun u => u == some 1

theorem trace_only1 : (unit 2 .client).trace (answer only1) = [(some 0, .binds), (some 1, .binds)] := by
  simp [unit, search, answer, only1]

/-- A traced miss on scope 0 that no key of the design covers refutes the obligations. -/
theorem not_obligations_of (sc' : Fin 2 → Scope) (sx' : Fin 2 → Ext) (r : Rules)
    (h : ∀ k ∈ keysR sc' sx' r none [(some 0, .binds), (some 1, .binds)],
      ¬ coversR sc' sx' r only1 (some 0, .binds) k) : ¬ (rules sc' sx' r).Obligations := by
  intro ob
  obtain ⟨k, hk, hc⟩ := ob.coverage only1 none .client (some 0, .binds)
    (by show _ ∈ (unit 2 .client).trace (answer only1); rw [trace_only1]; simp)
  change k ∈ keysR sc' sx' r none ((unit 2 .client).trace (answer only1)) at hk
  rw [trace_only1] at hk
  exact h k hk hc

/-- **F2 under #34 and F3**: a member added to `package object b` (scope 0) over `a.Foo`. -/
theorem f2_not_obligations :
    ¬ (rules (two ⟨false, false, false, false⟩ ⟨true, false, false⟩).1
      (two ⟨false, false, false, false⟩ ⟨true, false, false⟩).2 { cheap := .global, f3 := true }).Obligations :=
  not_obligations_of _ _ _ (by
    intro k hk
    simp [keysR, f3Keys, two, List.finRange] at hk
    rcases hk with rfl | rfl <;> simp [coversR, ruled, two, Reach.at])

/-- **F3 under #34 and F2**: a member added to `W`, the import charged to a class that does not use
the name (scope 0). -/
theorem f3_not_obligations :
    ¬ (rules (two ⟨false, false, false, false⟩ ⟨false, true, false⟩).1
      (two ⟨false, false, false, false⟩ ⟨false, true, false⟩).2 { cheap := .global, f2 := .global }).Obligations :=
  not_obligations_of _ _ _ (by
    intro k hk
    simp [keysR, f3Keys, two, List.finRange] at hk
    rcases hk with rfl | rfl <;> simp [coversR, ruled, two, Reach.at])

/-- **Narrowed without the recorded import**: a class added in a wildcard-imported package (scope
0, `a.q.Foo`). -/
theorem narrowed_without_imports :
    ¬ (rules (two ⟨false, false, true, false⟩ ⟨false, false, true⟩).1
      (two ⟨false, false, true, false⟩ ⟨false, false, true⟩).2
      { cheap := .narrowed, f2 := .narrowed, f3 := true }).Obligations :=
  not_obligations_of _ _ _ (by
    intro k hk
    simp [keysR, f3Keys, two, List.finRange] at hk
    rcases hk with rfl | rfl <;> simp [coversR, ruled, two, Reach.at])

/-- **The rules over-invalidate**: the client resolves `a.b.Foo` (scope 0); `a.Foo` (scope 1),
searched only after it, is added. The rules' key moves, no answer the lookup read did. -/
theorem rules_over :
    OverInvalidated (rules (fun (_ : Fin 2) => ⟨false, false, true, false⟩) (fun (_ : Fin 2) => ⟨false, false, false⟩)
      { cheap := .narrowed, f2 := .narrowed, f3 := true, imports := true })
      none .client (fun u => u == some 0) (fun u => u == some 0 || u == some 1) := by
  have ht : (unit 2 .client).trace (answer fun u => u == some 0) = [(some 0, .binds)] := by
    simp [unit, search, answer]
  refine ⟨⟨(none, .rule), by simp [rules, keysR], ?_⟩, ?_⟩
  · simp [rules, πR, ruled, Reach.at, List.finRange]
  · rintro ⟨q, hq, hne⟩
    change q ∈ (unit 2 .client).trace (answer fun u => u == some 0) at hq
    rw [ht] at hq
    simp at hq
    subst hq
    simp [rules, answer] at hne

end Spec

end Zinc.SplitProof
