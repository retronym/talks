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
* `searched_obligations` and `proposed_downstream_sound` (below): the framework of `Model.lean` and
  `Classpath.lean` instantiated with the external path. Keys on every scope the lookup searched,
  misses included, meet the obligations, so T5 applies; the proposed rule invalidates whatever
  those keys would, so it inherits T5.
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

/-! ## The framework of `Model.lean`, instantiated with the external path

Units: the client (`none`, downstream) and scopes `some i` (upstream), `n` of them. A scope's
interface is whether it binds; the client asks scope `0`, `1`, … in turn whether it binds and stops
at the first that does. The hash of a key on a scope is its interface: whether it binds, which is
the hash Zinc's name hashing gives the name in the scope's class (absent, or present). The
`searched` extractor keys every scope asked, misses included; `resolved` keys only the last one
asked, the scope the client resolved to (Zinc today).

`searched_obligations`: the obligations hold, so T5 (`NCompiler.downstream_sound`) applies to the
downstream. `ext_proposed`: whenever a key `searched` records moves, the proposed rule fires on the
client. So a downstream loop started from the proposed rule's invalidations is sound
(`proposed_downstream_sound`), without recording the misses. -/

namespace Inst

variable (n : ℕ)

abbrev U := Option (Fin n)

instance : Fintype (U n) := inferInstanceAs (Fintype (Option (Fin n)))
instance : DecidableEq (U n) := inferInstanceAs (DecidableEq (Option (Fin n)))

inductive Src | bind (x : Bool) | client
  deriving DecidableEq

inductive Q | binds
  deriving DecidableEq

inductive K | presence
  deriving DecidableEq

structure Out where
  iface : Bool
  res : Option ℕ
  deriving DecidableEq

abbrev T := Task (U n × Q) (fun _ => Bool) Out

/-- The client's lookup from scope `k` on. -/
def search (k : ℕ) : T n :=
  if h : k < n then
    .ask (some ⟨k, h⟩, .binds) fun x => if x then .pure ⟨false, some k⟩ else search (k + 1)
  else .pure ⟨false, none⟩
termination_by n - k

def unit : Src → T n
  | .bind x => .pure ⟨x, none⟩
  | .client => search n 0

def ifaceSrc : Src → Bool
  | .bind x => x
  | .client => false

def answer (I : U n → Bool) (q : U n × Q) : Bool := I q.1

def group (G : Finset (U n)) (src : U n → Src) (I : U n → Bool) : U n → Out :=
  fun u => (unit n (src u)).run (answer n fun v => if v ∈ G then ifaceSrc (src v) else I v)

inductive Extractor | searched | resolved

def keys : Extractor → U n → List (U n × Q) → Finset (U n × K)
  | .searched, _, tr => (tr.map fun q => (q.1, K.presence)).toFinset
  | .resolved, _, tr => (tr.getLast?.map fun q => (q.1, K.presence)).toList.toFinset

def compiler (x : Extractor) : NCompiler (U n) Src Out Bool K Bool Q (fun _ => Bool) where
  unit := unit n
  group := group n
  iface := Out.iface
  answer := answer n
  π := fun I c _ => I c
  hashDeps := fun _ c => {c}
  keys := keys n x
  covers := fun _ q k => k.1 = q.1

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
  | client => exact iface_search n e 0

/-- Every query of the lookup from `k` asks a scope `i ≥ k` after misses on the scopes between. -/
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

theorem searched_obligations : (compiler n .searched).Obligations where
  comp := by
    intro G src I d _
    have : NCompiler.override I G (Out.iface ∘ group n G src I) =
        fun v => if v ∈ G then ifaceSrc (src v) else I v := by
      funext v
      simp only [NCompiler.override, Function.comp]
      split
      · simp only [group, iface_run]
      · rfl
    show group n G src I d = (unit n (src d)).run (answer n (NCompiler.override I G (Out.iface ∘ group n G src I)))
    rw [this]
    rfl
  coverage := by
    intro I d s q hq
    refine ⟨(q.1, K.presence), ?_, rfl⟩
    show (q.1, K.presence) ∈ (List.map _ _).toFinset
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, rfl⟩
  abstraction := by
    intro I I' k h q hc
    refine ⟨?_, hc⟩
    show I q.1 = I' q.1
    rw [← show k.1 = q.1 from hc]
    exact h
  locality := by
    intro I I' c h _
    exact h c (Finset.mem_singleton_self c)

theorem trace_miss : (unit 2 .client).trace (answer 2 fun _ => false) =
    [(some 0, .binds), (some 1, .binds)] := by
  simp [unit, search, answer]

/-- Keying only the scope the client resolved to (Zinc today) misses the scopes it searched first. -/
theorem not_resolved_obligations : ¬ (compiler 2 .resolved).Obligations := by
  intro ob
  have := ob.coverage (fun _ => false) none .client (some 0, .binds)
    (by show _ ∈ (unit 2 .client).trace (answer 2 fun _ => false); rw [trace_miss]; simp)
  obtain ⟨k, hk, hc⟩ := this
  change k ∈ keys 2 .resolved none ((unit 2 .client).trace (answer 2 fun _ => false)) at hk
  rw [trace_miss] at hk
  simp [keys] at hk
  change k.1 = some 0 at hc
  rw [hk] at hc
  simp at hc

/-- The bindings an interface vector gives the slot language. -/
def bits (I : U n → Bool) (j : ℕ) : Bool := if h : j < n then I (some ⟨j, h⟩) else false

/-- **A searched key moved ⇒ the proposed rule fires.** If the client asked scope `i`, against `I`,
and `i`'s binding differs in `I'`, then either `i` gained a binding, or `i` was the scope it
resolved to and lost it. -/
theorem ext_proposed (c : Client) (hn : c.n = n) (I I' : U n → Bool) (i : Fin n)
    (hq : (some i, Q.binds) ∈ (unit n .client).trace (answer n I))
    (hne : I (some i) ≠ I' (some i)) : c.proposed (bits n I) (bits n I') := by
  obtain ⟨i', hi', -, heq, hmiss⟩ := trace_search n (answer n I) 0 _ hq
  have hii : i = ⟨i', hi'⟩ := by
    have := congrArg Prod.fst heq
    simp only [Option.some.injEq] at this
    exact this
  subst hii
  have hin : i' < c.n := hn ▸ hi'
  have hb : ∀ J : U n → Bool, bits n J i' = J (some ⟨i', hi'⟩) := by
    intro J; simp [bits, hi']
  cases hI : I (some ⟨i', hi'⟩) with
  | false =>
    have hI' : I' (some ⟨i', hi'⟩) = true := by
      cases h' : I' (some ⟨i', hi'⟩) <;> simp_all
    have hadd : added (bits n I) (bits n I') i' := ⟨by rw [hb, hI], by rw [hb, hI']⟩
    cases hpin : (c.sc i').pinned
    · exact .inr ⟨i', hin, hadd, hpin⟩
    · exact .inl ⟨i', hin, by simp [changed, hadd.1, hadd.2], .inl hpin⟩
  | true =>
    have hres : c.resolve (bits n I) = some i' := by
      rw [Client.resolve, first_some]
      refine ⟨hin, by rw [hb, hI], fun j hj => ?_⟩
      have hjn : j < n := by omega
      simp only [bits, hjn, dite_true]
      exact hmiss j hjn (Nat.zero_le j) hj
    refine .inl ⟨i', hin, ?_, .inr hres⟩
    simp only [changed, hb, hI]
    intro h; exact hne (by rw [hI, h])

abbrev Up : Finset (U n) := Finset.univ.filter (·.isSome)
abbrev S : Finset (U n) := {none}

/-- **The proposed rule inherits T5.** From an up-to-date downstream with fresh snapshots, whose
client recorded the keys of its last compilation, a new upstream (any number of scopes changed)
and a downstream loop started from the changed sources and, when the proposed rule fires, the
client: if the loop stops, the downstream is up to date against the new upstream. -/
theorem proposed_downstream_sound (c : Client) (hn : c.n = n)
    (src₀ src : U n → Src) (hcl : src₀ none = .client)
    (s : Compiler.State (U n) Out K) (snap : U n → Bool) (o : U n → Out)
    (D : Finset (U n)) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : (compiler n .searched).Inv (S n) src₀ s ∅)
    (hFresh : (compiler n .searched).Fresh (Up n) (S n) s snap ∅)
    (hU : ∀ k ∈ s.U none, ∃ q ∈ (unit n .client).trace (answer n ((compiler n .searched).ifaces s)),
      k.1 = q.1)
    (P : Compiler.Policy (U n) Out K) (hP : P.Sound (S n)) (fuel : ℕ) (R₀ : Finset (U n))
    (hRD : D ⊆ R₀)
    (hRp : c.proposed (bits n ((compiler n .searched).ifaces s))
      (bits n ((compiler n .searched).ifaces (NCompiler.withUpstream (Up n) s o))) → none ∈ R₀)
    (s' : Compiler.State (U n) Out K)
    (h : (compiler n .searched).zinc (S n) src P fuel 0 R₀ (NCompiler.withUpstream (Up n) s o) = some s') :
    (compiler n .searched).Inv (S n) src s' ∅ := by
  have _ := hcl
  refine (compiler n .searched).downstream_sound (searched_obligations n) (Up n) (S n) ?_
    src₀ src s snap o D hD hInv hFresh P hP fuel R₀ ?_ s' h
  · rw [Finset.disjoint_left]
    intro u hu hS
    simp only [S, Finset.mem_singleton] at hS
    subst hS
    simp at hu
  · intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact hRD hu
    obtain ⟨huS, k, hk, hne⟩ := Finset.mem_filter.1 hu
    simp only [S, Finset.mem_singleton] at huS
    subst huS
    obtain ⟨q, hq, hkq⟩ := hU k hk
    obtain ⟨i, hi, -, rfl, -⟩ := trace_search n _ 0 q hq
    have hfr := hFresh none (Finset.mem_singleton_self _) (Finset.notMem_empty _) k hk
    rw [hfr] at hne
    apply hRp
    apply ext_proposed n c hn _ _ ⟨i, hi⟩ hq
    simpa [compiler, hkq] using hne

end Inst

end Zinc.SplitProof
