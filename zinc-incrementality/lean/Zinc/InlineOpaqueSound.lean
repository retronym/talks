import Zinc.NonLocalAns

/-!
# Inline bodies and opaque types in the Phase 1 framework

`InlineOpaque.lean` checks Zinc's rules on bounded program spaces. Here the same observables are an
instance of `NCompiler` (`NonLocalAns.lean`), over every program of a small language, so the fixes
inherit T2″/T3a″ (`NCompiler.round_preserves`, `NCompiler.zinc_sound`).

The language. Units (classes) of any finite type `U`; a unit declares members by name:

* `member t`: a plain member (a helper, a `val`, an inline accessor, `O.mk`) with a signature
  `t`, a primitive erasure or an opaque type `c.n`;
* `const v`: a constant (`final val K = v`, or an alias `type N = v` read at the type level);
* `inl trans body`: an `inline` (or `transparent inline`) def whose body is a list of items;
* `opq rhs`: an opaque type, erased to `rhs`;
* `meth t`: a concrete trait method, which each descendant forwards (mixin forwarder).

A unit's code is a list of items: a literal, a call (emits the erasure of the callee's signature),
a constant read through `this` or through a path, a signature mentioning a type (emits its erasure),
an inline call (expands the callee's body, nested up to a depth). Its output is its declarations
(the interface), the code's emitted values with its own members' erasures, and its forwarders.

Inlining is a dynamic dependency: the client asks for the callee's body and then issues the body's
queries itself. So "what the inliner read" needs no new framework concept: it is the client's
trace. What changes is the *context* a query is issued in, which the bridge looks at when recording
keys (`recorded`): the client's own code, a plain or transparent expansion, or a forwarder's
erasure. Zinc on Scala 3.9.0 (`today`) drops a constant read through a path inside an expansion
(the inliner folded it), everything inside a transparent expansion (typer expanded it), and the
opaque right-hand side read when erasing a forwarder.

Results:

* `obligations_record`: recording every query (`bodyDeps` with `dep`) meets the obligations, for
  every program, so `record_sound` (T3a″) and `record_recompiles_or_unchanged` (T2″ for one round:
  after any edit, each unit outside the edited ones is invalidated or its output is already its
  compilation against the new interfaces).
* `obligations_denot`: hashing what an inline def's references denote (`hashDenot`: the key of the
  inline def hashes, besides its tree, every query its expansion issues with its current answer, a
  *fresh* verifying-trace hash over the units the expansion reads) with `dep` meets them too. The
  non-local coverage needs `trace_code`: every query issued in an expansion belongs to the expansion
  of a body the unit's own code asked for, whose key the bridge recorded. dotc would *store* such a
  hash in the owner's API at the owner's compilation; that is P6.9's stored witness, sound only as a
  run invariant (the owner up to date), not an instance.
* Families as counterexamples under today's bridge, each a concrete program pair where every key
  the client recorded hashes the same and the client's output differs: `I1_today` (a constant
  through a path), `I2_today` (an alias read at the type level: the same folded read),
  `I3_today` (a transparent expansion), `O1_today` (an opaque type in an inherited signature).
  `not_obligations_today`: today's bridge fails coverage.
-/

namespace Zinc.InlineOpaqueSound

abbrev Name := ℕ

inductive TyRef (U : Type) | prim (t : ℕ) | opq (c : U) (n : Name)
  deriving DecidableEq, Repr

inductive Item (U : Type)
  | lit (v : ℕ)
  | call (c : U) (n : Name)
  | const (c : U) (n : Name) (path : Bool)
  | inl (c : U) (n : Name)
  | sig (t : TyRef U)
  deriving DecidableEq, Repr

inductive Def (U : Type)
  | member (t : TyRef U)
  | const (v : ℕ)
  | inl (trans : Bool) (body : List (Item U))
  | opq (rhs : ℕ)
  | meth (t : TyRef U)
  deriving DecidableEq, Repr

abbrev Iface (U : Type) := List (Name × Def U)

structure Src (U : Type) where
  defs : Iface U := []
  parents : List U := []
  code : List (Item U) := []

structure Out (U : Type) where
  iface : Iface U
  code : List ℕ
  fwds : List ℕ
  deriving DecidableEq, Repr

/-- Where a query is issued: the unit's own code, an expansion (transparent if its outermost call
is), or the erasure of a forwarder. -/
inductive Ctx | code | exp (trans : Bool) | fwd
  deriving DecidableEq, Repr

def Ctx.enter : Ctx → Bool → Ctx
  | .code, t => .exp t
  | c, _ => c

inductive Kind | sig (n : Name) | const (n : Name) (path : Bool) | body (n : Name) | rhs (n : Name)
  | meths
  deriving DecidableEq, Repr

structure Q where
  ctx : Ctx
  kind : Kind
  deriving DecidableEq, Repr

variable {U : Type}

def Def.isSig : Def U → Bool | .member _ => true | .meth _ => true | _ => false
def Def.isConst : Def U → Bool | .const _ => true | _ => false
def Def.isInl : Def U → Bool | .inl _ _ => true | _ => false
def Def.isOpq : Def U → Bool | .opq _ => true | _ => false
def Def.isMeth : Def U → Bool | .meth _ => true | _ => false

abbrev Ans (U : Type) := Iface U

/-- The answer to a query, from the interface of the unit it is addressed to. -/
def answerK (i : Iface U) : Kind → Ans U
  | .sig n => i.filter fun d => d.1 == n && d.2.isSig
  | .const n _ => i.filter fun d => d.1 == n && d.2.isConst
  | .body n => i.filter fun d => d.1 == n && d.2.isInl
  | .rhs n => i.filter fun d => d.1 == n && d.2.isOpq
  | .meths => i.filter fun d => d.2.isMeth

def answer (I : U → Iface U) (q : U × Q) : Ans U := answerK (I q.1) q.2.kind

def sigOf : Ans U → Option (TyRef U)
  | (_, .member t) :: _ => some t
  | (_, .meth t) :: _ => some t
  | _ => none

def constOf : Ans U → ℕ
  | (_, .const v) :: _ => v
  | _ => 0

def bodyOf : Ans U → Option (Bool × List (Item U))
  | (_, .inl tr b) :: _ => some (tr, b)
  | _ => none

def rhsOf : Ans U → ℕ
  | (_, .opq r) :: _ => r
  | _ => 0

def methsOf (a : Ans U) : List (TyRef U) :=
  a.filterMap fun d => match d.2 with | .meth t => some t | _ => none

/-! ## The per-unit task -/

abbrev T (U : Type) := Task (U × Q) (fun _ => Ans U)

def seqT : List (T U (List ℕ)) → T U (List ℕ)
  | [] => .pure []
  | t :: ts => t.bind fun x => (seqT ts).bind fun xs => .pure (x ++ xs)

def erase (ctx : Ctx) : TyRef U → T U ℕ
  | .prim t => .pure t
  | .opq c n => .ask (c, ⟨ctx, .rhs n⟩) fun a => .pure (rhsOf a)

def item (rec : Ctx → List (Item U) → T U (List ℕ)) (ctx : Ctx) : Item U → T U (List ℕ)
  | .lit v => .pure [v]
  | .call c n => .ask (c, ⟨ctx, .sig n⟩) fun a =>
      match sigOf a with
      | some t => (erase ctx t).bind fun e => .pure [e]
      | none => .pure []
  | .const c n p => .ask (c, ⟨ctx, .const n p⟩) fun a => .pure [constOf a]
  | .sig t => (erase ctx t).bind fun e => .pure [e]
  | .inl c n => .ask (c, ⟨ctx, .body n⟩) fun a =>
      match bodyOf a with
      | some (tr, b) => rec (ctx.enter tr) b
      | none => .pure []

/-- Compile items; an inline call expands its body with one level of nesting less. -/
def expand : ℕ → Ctx → List (Item U) → T U (List ℕ)
  | 0, ctx, is => seqT (is.map (item (fun _ _ => .pure []) ctx))
  | f + 1, ctx, is => seqT (is.map (item (expand f) ctx))

def ownDescs (ds : Iface U) : T U (List ℕ) :=
  seqT (ds.map fun d => match d.2 with
    | .member t => (erase .code t).bind fun e => .pure [e]
    | .meth t => (erase .code t).bind fun e => .pure [e]
    | .const v => .pure [v]
    | _ => .pure [])

def fwds (ps : List U) : T U (List ℕ) :=
  seqT (ps.map fun p => .ask (p, ⟨.code, .meths⟩) fun a =>
    seqT ((methsOf a).map fun t => (erase .fwd t).bind fun e => .pure [e]))

def unit (depth : ℕ) (s : Src U) : T U (Out U) :=
  (expand (depth + 1) .code s.code).bind fun c =>
    (ownDescs s.defs).bind fun o =>
      (fwds s.parents).bind fun w => .pure ⟨s.defs, c ++ o, w⟩

theorem iface_run (depth : ℕ) (s : Src U) (e : Task.Env (U × Q) (fun _ => Ans U)) :
    ((unit depth s).run e).iface = s.defs := by
  simp [unit]

/-! ## Keys, hashes, bridges -/

inductive K | name (n : Name) | cls
  deriving DecidableEq, Repr

def keyOf : Kind → K
  | .sig n | .const n _ | .body n => .name n
  | .rhs _ | .meths => .cls

/-- Inline: Zinc today; recording the expansion's references before folding (`bodyDeps`); hashing
what the references denote (`hashDenot`). Opaque: today; recording the types a forwarder's erasure
reads (`dep`). -/
inductive InlFix | today | bodyDeps | hashDenot
  deriving DecidableEq, Repr

inductive OpqFix | today | dep
  deriving DecidableEq, Repr

structure Bridge where
  inl : InlFix
  opq : OpqFix
  deriving DecidableEq, Repr

/-- Does the bridge record a key for a query issued in this context? -/
def recorded (b : Bridge) (q : Q) : Bool :=
  match q.ctx, q.kind with
  | .code, _ => true
  | .exp false, .const _ true => b.inl == .bodyDeps
  | .exp false, _ => true
  | .exp true, _ => b.inl == .bodyDeps
  | .fwd, _ => b.opq == .dep

def recordedKeys (b : Bridge) (tr : List (U × Q)) : List (U × K) :=
  tr.filterMap fun q => if recorded b q.2 then some (q.1, keyOf q.2.kind) else none

def keys [DecidableEq U] (b : Bridge) (_ : U) (tr : List (U × Q)) : Finset (U × K) :=
  (recordedKeys b tr).toFinset

/-- The rendering under a name: an opaque type's right-hand side is not in it (it is in the owner's
self type, `cls`). -/
def render : Def U → Def U
  | .opq _ => .opq 0
  | d => d

def own (i : Iface U) : K → Iface U
  | .name n => (i.filter fun d => d.1 == n).map fun d => (d.1, render d.2)
  | .cls => i.filter fun d => d.2.isOpq || d.2.isMeth

/-- The queries an expansion of inline def `n` of interface `i` issues, under interfaces `I`. -/
def expansion (depth : ℕ) (I : U → Iface U) (i : Iface U) (n : Name) : List (U × Q) :=
  match bodyOf (answerK i (.body n)) with
  | some (tr, b) => (expand depth (Ctx.code.enter tr) b).trace (answer I)
  | none => []

abbrev Hash (U : Type) := Iface U × List ((U × Q) × Ans U)

instance [DecidableEq U] : DecidableEq (Hash U) := instDecidableEqProd

def π (b : Bridge) (depth : ℕ) (I : U → Iface U) (c : U) (k : K) : Hash U :=
  (own (I c) k, match b.inl, k with
    | .hashDenot, .name n => (expansion depth I (I c) n).map fun q => (q, answer I q)
    | _, _ => [])

def hashDeps [DecidableEq U] (b : Bridge) (depth : ℕ) (I : U → Iface U) (c : U) : Finset U :=
  if b.inl = .hashDenot then
    insert c (((I c).flatMap fun d => (expansion depth I (I c) d.1).map Prod.fst).toFinset)
  else {c}

/-- A key covers the queries addressed to its unit with its name (or, for `cls`, the opaque
right-hand sides and the trait's methods); under `hashDenot`, an inline def's key also covers every
query of its expansion. -/
def covers (b : Bridge) (depth : ℕ) (I : U → Iface U) (q : U × Q) (k : U × K) : Prop :=
  (q.1 = k.1 ∧ keyOf q.2.kind = k.2) ∨
    (b.inl = .hashDenot ∧ ∃ n, k.2 = .name n ∧ q ∈ expansion depth I (I k.1) n)

def group [DecidableEq U] (depth : ℕ) (G : Finset U) (src : U → Src U) (I : U → Iface U) :
    U → Out U :=
  fun u => (unit depth (src u)).run (answer fun c => if c ∈ G then (src c).defs else I c)

def compiler [DecidableEq U] (b : Bridge) (depth : ℕ) :
    NCompiler U (Src U) (Out U) (Iface U) K (Hash U) Q (fun _ => Ans U) where
  unit := unit depth
  group := group depth
  iface := Out.iface
  answer := answer
  π := π b depth
  hashDeps := hashDeps b depth
  keys := keys b
  covers := covers b depth

/-! ## Compositionality -/

theorem comp [DecidableEq U] (b : Bridge) (depth : ℕ) :
    ∀ (G : Finset U) (src : U → Src U) (I : U → Iface U), ∀ d ∈ G,
      (compiler b depth).group G src I d =
        ((compiler b depth).unit (src d)).run ((compiler b depth).answer
          (NCompiler.override I G ((compiler b depth).iface ∘ (compiler b depth).group G src I))) := by
  intro G src I d _
  show group depth G src I d = (unit depth (src d)).run (answer _)
  simp only [group]
  congr 2
  funext c
  simp only [NCompiler.override, compiler, Function.comp]
  split
  · rw [group, iface_run]
  · rfl

/-! ## Abstraction -/

theorem filter_map_render (l : Iface U) (P : Def U → Bool)
    (hP : ∀ d, P (render d) = P d) (hfix : ∀ d, P d = true → render d = d) :
    ((l.map fun d => (d.1, render d.2)).filter fun d => P d.2) = l.filter fun d => P d.2 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons, hP]
    split
    · rename_i h; rw [hfix _ h, ih]
    · exact ih

/-- Every answer is a function of the hash's rendering under the query's key. -/
theorem answerK_of_own (i : Iface U) (k : Kind) :
    answerK i k = match k with
      | .sig _ => (own i (keyOf k)).filter fun d => d.2.isSig
      | .const _ _ => (own i (keyOf k)).filter fun d => d.2.isConst
      | .body _ => (own i (keyOf k)).filter fun d => d.2.isInl
      | .rhs n => (own i (keyOf k)).filter fun d => d.1 == n && d.2.isOpq
      | .meths => (own i (keyOf k)).filter fun d => d.2.isMeth := by
  cases k with
  | sig n =>
    simp only [answerK, own, keyOf]
    rw [filter_map_render _ _ (fun d => by cases d <;> rfl) (fun d h => by cases d <;> simp_all [Def.isSig, render]),
      List.filter_filter]
    congr 1; funext d; exact Bool.and_comm _ _
  | const n p =>
    simp only [answerK, own, keyOf]
    rw [filter_map_render _ _ (fun d => by cases d <;> rfl) (fun d h => by cases d <;> simp_all [Def.isConst, render]),
      List.filter_filter]
    congr 1; funext d; exact Bool.and_comm _ _
  | body n =>
    simp only [answerK, own, keyOf]
    rw [filter_map_render _ _ (fun d => by cases d <;> rfl) (fun d h => by cases d <;> simp_all [Def.isInl, render]),
      List.filter_filter]
    congr 1; funext d; exact Bool.and_comm _ _
  | rhs n =>
    simp only [answerK, own, keyOf, List.filter_filter]
    congr 1; funext d; cases d.2 <;> simp [Def.isOpq, Def.isMeth]
  | meths =>
    simp only [answerK, own, keyOf, List.filter_filter]
    congr 1; funext d; cases d.2 <;> simp [Def.isOpq, Def.isMeth]

theorem abstraction [DecidableEq U] (b : Bridge) (depth : ℕ) :
    ∀ (I I' : U → Iface U) (k : U × K), π b depth I k.1 k.2 = π b depth I' k.1 k.2 →
      ∀ q, covers b depth I q k → answer I q = answer I' q ∧ covers b depth I' q k := by
  intro I I' k h q hc
  rcases hc with ⟨h1, h2⟩ | ⟨hb, n, hk, hq⟩
  · have hown : own (I k.1) k.2 = own (I' k.1) k.2 := congrArg Prod.fst h
    refine ⟨?_, Or.inl ⟨h1, h2⟩⟩
    simp only [answer]
    rw [h1, answerK_of_own, answerK_of_own, h2, hown]
  · obtain ⟨c, k2⟩ := k
    simp only at hk
    subst hk
    have hl : (expansion depth I (I c) n).map (fun q => (q, answer I q)) =
        (expansion depth I' (I' c) n).map (fun q => (q, answer I' q)) := by
      have := congrArg Prod.snd h
      simpa [π, hb] using this
    have hmem : (q, answer I q) ∈ (expansion depth I' (I' c) n).map (fun q => (q, answer I' q)) :=
      hl ▸ List.mem_map_of_mem hq
    obtain ⟨q', hq', heq⟩ := List.mem_map.1 hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, ha⟩ := heq
    exact ⟨ha.symm, Or.inr ⟨hb, n, rfl, hq'⟩⟩

/-! ## Locality -/

theorem expansion_congr (depth : ℕ) (I I' : U → Iface U) (i : Iface U) (n : Name)
    (h : ∀ q ∈ expansion depth I i n, I q.1 = I' q.1) :
    expansion depth I i n = expansion depth I' i n := by
  cases hb : bodyOf (answerK i (.body n)) with
  | none => simp [expansion, hb]
  | some p =>
    obtain ⟨tr, b⟩ := p
    simp only [expansion, hb] at h ⊢
    apply Task.trace_congr
    intro q hq
    simp only [answer, h q hq]

theorem expansion_nil_of (depth : ℕ) (I : U → Iface U) (i : Iface U) (n : Name)
    (h : expansion depth I i n ≠ []) : n ∈ i.map Prod.fst := by
  unfold expansion at h
  split at h
  · rename_i tr b hb
    simp only [answerK] at hb
    cases hl : (i.filter fun d => d.1 == n && d.2.isInl) with
    | nil => rw [hl] at hb; simp [bodyOf] at hb
    | cons x xs =>
      have hx : x ∈ i.filter fun d => d.1 == n && d.2.isInl := by rw [hl]; simp
      rw [List.mem_filter] at hx
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      exact List.mem_map.2 ⟨x, hx.1, hx.2.1⟩
  · exact absurd rfl h

theorem locality [DecidableEq U] (b : Bridge) (depth : ℕ) :
    ∀ (I I' : U → Iface U) (c : U), (∀ d ∈ hashDeps b depth I c, I d = I' d) →
      ∀ k, π b depth I c k = π b depth I' c k := by
  intro I I' c h k
  have hc : I c = I' c := h c (by unfold hashDeps; split <;> simp)
  simp only [π, hc]
  congr 1
  cases hb : b.inl <;> cases k <;> simp only
  rename_i n
  have hdeps : ∀ q ∈ expansion depth I (I c) n, I q.1 = I' q.1 := by
    intro q hq
    apply h
    simp only [hashDeps, hb, ite_true, Finset.mem_insert, List.mem_toFinset, List.mem_flatMap,
      List.mem_map]
    right
    obtain ⟨⟨n', dd⟩, hd, rfl⟩ := List.mem_map.1 (expansion_nil_of depth I (I c) n
      (List.ne_nil_of_mem hq))
    exact ⟨(n', dd), hd, q, hq, rfl⟩
  rw [← hc, ← expansion_congr depth I I' (I c) n hdeps]
  apply List.map_congr_left
  intro q hq
  simp only [answer, hdeps q hq]

/-! ## Coverage -/

theorem trace_seqT (e : Task.Env (U × Q) (fun _ => Ans U)) (ts : List (T U (List ℕ))) :
    (seqT ts).trace e = ts.flatMap fun t => t.trace e := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [seqT, Task.trace_bind, ih]

theorem trace_erase (e : Task.Env (U × Q) (fun _ => Ans U)) (ctx : Ctx) (t : TyRef U) :
    ∀ q ∈ (erase ctx t).trace e, q.2.ctx = ctx := by
  cases t <;> simp [erase]

/-- Queries of an item compiled in context `ctx`, other than a nested expansion, carry `ctx`. -/
theorem trace_item_code (e : Task.Env (U × Q) (fun _ => Ans U))
    (rec : Ctx → List (Item U) → T U (List ℕ)) (it : Item U) :
    ∀ q ∈ (item rec .code it).trace e, q.2.ctx = .code ∨
      ∃ c n tr b, it = .inl c n ∧ bodyOf (e (c, ⟨.code, .body n⟩)) = some (tr, b) ∧
        q ∈ (rec (Ctx.code.enter tr) b).trace e := by
  intro q hq
  cases it with
  | lit v => simp [item] at hq
  | call c n =>
    simp only [item, Task.trace_ask, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Or.inl rfl
    · left
      split at hq
      · simp only [Task.trace_bind, List.mem_append] at hq
        rcases hq with hq | hq
        · exact trace_erase e _ _ q hq
        · simp at hq
      · simp at hq
  | const c n p =>
    simp only [item, Task.trace_ask, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Or.inl rfl
    · simp at hq
  | sig t =>
    simp only [item, Task.trace_bind, List.mem_append] at hq
    rcases hq with hq | hq
    · exact Or.inl (trace_erase e _ _ q hq)
    · simp at hq
  | inl c n =>
    simp only [item, Task.trace_ask, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Or.inl rfl
    · right
      split at hq
      · rename_i tr b hb
        exact ⟨c, n, tr, b, rfl, hb, hq⟩
      · simp at hq

/-- **What the inliner read.** Every query a unit issues is issued in its own code or a forwarder,
or belongs to the expansion of an inline def its own code asked for. -/
theorem trace_code [DecidableEq U] (depth : ℕ) (I : U → Iface U) (s : Src U) :
    ∀ q ∈ (unit depth s).trace (answer I), q.2.ctx = .code ∨ q.2.ctx = .fwd ∨
      ∃ c n, (c, (⟨.code, .body n⟩ : Q)) ∈ (unit depth s).trace (answer I) ∧
        q ∈ expansion depth I (I c) n := by
  intro q hq
  have hsplit : (unit depth s).trace (answer I) =
      (expand (depth + 1) .code s.code).trace (answer I) ++
        ((ownDescs s.defs).trace (answer I) ++ (fwds s.parents).trace (answer I)) := by
    simp [unit, Task.trace_bind]
  rw [hsplit] at hq ⊢
  rcases List.mem_append.1 hq with hq | hq
  · simp only [expand, trace_seqT, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨_, ⟨it, hit, rfl⟩, hq⟩ := hq
    rcases trace_item_code (answer I) (expand depth) it q hq with h | ⟨c, n, tr, b, rfl, hb, hq'⟩
    · exact Or.inl h
    · right; right
      refine ⟨c, n, ?_, ?_⟩
      · apply List.mem_append_left
        simp only [expand, trace_seqT, List.mem_flatMap, List.mem_map]
        exact ⟨_, ⟨.inl c n, hit, rfl⟩, by simp [item]⟩
      · simp only [expansion]
        have : answerK (I c) (.body n) = answer I (c, ⟨.code, .body n⟩) := rfl
        rw [this, hb]
        exact hq'
  · rcases List.mem_append.1 hq with hq | hq
    · left
      simp only [ownDescs, trace_seqT, List.mem_flatMap, List.mem_map] at hq
      obtain ⟨_, ⟨d, _, rfl⟩, hq⟩ := hq
      split at hq
      · simp only [Task.trace_bind, List.mem_append] at hq
        rcases hq with hq | hq
        · exact trace_erase _ _ _ q hq
        · simp at hq
      · simp only [Task.trace_bind, List.mem_append] at hq
        rcases hq with hq | hq
        · exact trace_erase _ _ _ q hq
        · simp at hq
      · simp at hq
      · simp at hq
    · simp only [fwds, trace_seqT, List.mem_flatMap, List.mem_map] at hq
      obtain ⟨_, ⟨p, _, rfl⟩, hq⟩ := hq
      simp only [Task.trace_ask, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Or.inl rfl
      · right; left
        simp only [trace_seqT, List.mem_flatMap, List.mem_map] at hq
        obtain ⟨_, ⟨t, _, rfl⟩, hq⟩ := hq
        simp only [Task.trace_bind, List.mem_append] at hq
        rcases hq with hq | hq
        · exact trace_erase _ _ _ q hq
        · simp at hq

theorem mem_keys [DecidableEq U] (b : Bridge) (d : U) (tr : List (U × Q)) (q : U × Q)
    (hq : q ∈ tr) (hr : recorded b q.2 = true) : (q.1, keyOf q.2.kind) ∈ keys b d tr := by
  simp only [keys, recordedKeys, List.mem_toFinset, List.mem_filterMap]
  exact ⟨q, hq, by simp [hr]⟩

/-- Recording every query: coverage by the query's own key. -/
theorem coverage_record [DecidableEq U] (depth : ℕ) :
    ∀ (I : U → Iface U) (d : U) (s : Src U), ∀ q ∈ (unit depth s).trace (answer I),
      ∃ k ∈ keys ⟨.bodyDeps, .dep⟩ d ((unit depth s).trace (answer I)),
        covers ⟨.bodyDeps, .dep⟩ depth I q k := by
  intro I d s q hq
  refine ⟨_, mem_keys _ d _ q hq ?_, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨_, ⟨ctx, kind⟩⟩ := q
  cases ctx with
  | code => rfl
  | exp t => cases t <;> cases kind <;> simp [recorded] <;> rename_i p <;> cases p <;> rfl
  | fwd => rfl

/-- Hashing what references denote: a query in an expansion is covered by the key of the inline
def whose body the unit's code asked for. -/
theorem coverage_denot [DecidableEq U] (depth : ℕ) :
    ∀ (I : U → Iface U) (d : U) (s : Src U), ∀ q ∈ (unit depth s).trace (answer I),
      ∃ k ∈ keys ⟨.hashDenot, .dep⟩ d ((unit depth s).trace (answer I)),
        covers ⟨.hashDenot, .dep⟩ depth I q k := by
  intro I d s q hq
  rcases trace_code depth I s q hq with h | h | ⟨c, n, hbody, hexp⟩
  · refine ⟨_, mem_keys _ d _ q hq ?_, Or.inl ⟨rfl, rfl⟩⟩
    simp [recorded, h]
  · refine ⟨_, mem_keys _ d _ q hq ?_, Or.inl ⟨rfl, rfl⟩⟩
    simp [recorded, h]
  · exact ⟨_, mem_keys _ d _ _ hbody rfl, Or.inr ⟨rfl, n, rfl, hexp⟩⟩

/-! ## The fixes are instances -/

variable [DecidableEq U]

theorem obligations_record (depth : ℕ) : (compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).Obligations where
  comp := comp (U := U) ⟨.bodyDeps, .dep⟩ depth
  coverage := coverage_record depth
  abstraction := abstraction (U := U) ⟨.bodyDeps, .dep⟩ depth
  locality := locality (U := U) ⟨.bodyDeps, .dep⟩ depth

theorem obligations_denot (depth : ℕ) : (compiler (U := U) ⟨.hashDenot, .dep⟩ depth).Obligations where
  comp := comp (U := U) ⟨.hashDenot, .dep⟩ depth
  coverage := coverage_denot depth
  abstraction := abstraction (U := U) ⟨.hashDenot, .dep⟩ depth
  locality := locality (U := U) ⟨.hashDenot, .dep⟩ depth

/-- The starting point of an incremental build, for `NCompiler`: the previous build was a fixed
point for the old sources, and `D` holds every unit whose source changed. -/
theorem inv_of_changed {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
    (C : NCompiler CUnit Src Out Iface K Hash Q A) [DecidableEq CUnit] [Fintype CUnit]
    (S : Finset CUnit) (src₀ src : CUnit → Src) (s : Compiler.State CUnit Out K)
    (D : Finset CUnit) (hD : ∀ u, src₀ u ≠ src u → u ∈ D) (h : C.Inv S src₀ s ∅) :
    C.Inv S src s D := by
  intro u hu huD
  have : src₀ u = src u := by by_contra hne; exact huD (hD u hne)
  simpa [NCompiler.UpToDate, this] using h u hu (Finset.notMem_empty u)

/-- **Per edit.** After any edit of the units `D` (a single edit: one unit) of any program, a unit
outside `D` is invalidated, or its output, untouched, is already its compilation against the new
interfaces: the client recompiles or its inlined and erased results are unchanged. -/
theorem recompiles_or_unchanged {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
    (C : NCompiler CUnit Src Out Iface K Hash Q A) [DecidableEq CUnit] [Fintype CUnit]
    [DecidableEq K] [DecidableEq Hash] (ob : C.Obligations)
    (S : Finset CUnit) (src₀ src : CUnit → Src) (s : Compiler.State CUnit Out K) (D : Finset CUnit)
    (hD : ∀ u, src₀ u ≠ src u → u ∈ D) (hfix : C.Inv S src₀ s ∅) :
    ∀ u ∈ S, u ∉ D → u ∈ C.invalidated S (C.affected D s) s (C.round src D s) ∨
      s.out u = (C.unit (src u)).run (C.answer (C.ifaces (C.round src D s))) := by
  intro u hu huD
  by_cases hI : u ∈ C.invalidated S (C.affected D s) s (C.round src D s)
  · exact Or.inl hI
  · right
    have hinv := C.round_preserves ob S src s D D (subset_refl _)
      (inv_of_changed C S src₀ src s D hD hfix)
    have hup := (hinv u hu (fun h => hI (Finset.mem_sdiff.1 h).1)).1
    have hout : (C.round src D s).out u = s.out u := by simp [NCompiler.round, huD]
    rw [← hout, hup]

theorem record_recompiles_or_unchanged [Fintype U] (depth : ℕ) (S : Finset U)
    (src₀ src : U → Src U) (s : Compiler.State U (Out U) K) (D : Finset U)
    (hD : ∀ u, src₀ u ≠ src u → u ∈ D) (hfix : (compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).Inv S src₀ s ∅) :
    ∀ u ∈ S, u ∉ D → u ∈ (compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).invalidated S ((compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).affected D s) s ((compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).round src D s) ∨
      s.out u = ((compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).unit (src u)).run ((compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).answer ((compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).ifaces ((compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).round src D s))) :=
  recompiles_or_unchanged (compiler (U := U) ⟨.bodyDeps, .dep⟩ depth) (obligations_record depth) S src₀ src s D hD hfix

theorem denot_recompiles_or_unchanged [Fintype U] (depth : ℕ) (S : Finset U)
    (src₀ src : U → Src U) (s : Compiler.State U (Out U) K) (D : Finset U)
    (hD : ∀ u, src₀ u ≠ src u → u ∈ D) (hfix : (compiler (U := U) ⟨.hashDenot, .dep⟩ depth).Inv S src₀ s ∅) :
    ∀ u ∈ S, u ∉ D → u ∈ (compiler (U := U) ⟨.hashDenot, .dep⟩ depth).invalidated S ((compiler (U := U) ⟨.hashDenot, .dep⟩ depth).affected D s) s ((compiler (U := U) ⟨.hashDenot, .dep⟩ depth).round src D s) ∨
      s.out u = ((compiler (U := U) ⟨.hashDenot, .dep⟩ depth).unit (src u)).run ((compiler (U := U) ⟨.hashDenot, .dep⟩ depth).answer ((compiler (U := U) ⟨.hashDenot, .dep⟩ depth).ifaces ((compiler (U := U) ⟨.hashDenot, .dep⟩ depth).round src D s))) :=
  recompiles_or_unchanged (compiler (U := U) ⟨.hashDenot, .dep⟩ depth) (obligations_denot depth) S src₀ src s D hD hfix

/-- **T3a″ for the fixes.** If Zinc's loop stops, every unit is a per-unit fixed point. -/
theorem record_sound [Fintype U] (depth : ℕ) (S : Finset U) (src : U → Src U)
    (P : Compiler.Policy U (Out U) K) (hP : P.Sound S) (fuel n : ℕ) (R : Finset U)
    (s : Compiler.State U (Out U) K) (D : Finset U) (hD : D ⊆ R) (hInv : (compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).Inv S src s D)
    (s' : Compiler.State U (Out U) K) (h : (compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).zinc S src P fuel n R s = some s') :
    (compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).Inv S src s' ∅ :=
  (compiler (U := U) ⟨.bodyDeps, .dep⟩ depth).zinc_sound (obligations_record depth) S src P hP fuel n R s D hD hInv s' h

theorem denot_sound [Fintype U] (depth : ℕ) (S : Finset U) (src : U → Src U)
    (P : Compiler.Policy U (Out U) K) (hP : P.Sound S) (fuel n : ℕ) (R : Finset U)
    (s : Compiler.State U (Out U) K) (D : Finset U) (hD : D ⊆ R) (hInv : (compiler (U := U) ⟨.hashDenot, .dep⟩ depth).Inv S src s D)
    (s' : Compiler.State U (Out U) K) (h : (compiler (U := U) ⟨.hashDenot, .dep⟩ depth).zinc S src P fuel n R s = some s') :
    (compiler (U := U) ⟨.hashDenot, .dep⟩ depth).Inv S src s' ∅ :=
  (compiler (U := U) ⟨.hashDenot, .dep⟩ depth).zinc_sound (obligations_denot depth) S src P hP fuel n R s D hD hInv s' h

end Zinc.InlineOpaqueSound

/-! ## Families under today's bridge -/

namespace Zinc.InlineOpaqueSound.Ex

open Zinc.InlineOpaqueSound

inductive Cls | L | D | O | Tr | K | Client
  deriving DecidableEq, Repr

open Cls

/-- The client is stale: every key it recorded hashes the same under the old and new interfaces,
and its output differs. -/
def Stale (b : Bridge) (depth : ℕ) (I₀ I₁ : Cls → Iface Cls) (s : Src Cls) : Prop :=
  (∀ k ∈ recordedKeys b ((unit depth s).trace (answer I₀)), π b depth I₀ k.1 k.2 = π b depth I₁ k.1 k.2) ∧
    (unit depth s).run (answer I₀) ≠ (unit depth s).run (answer I₁)

instance (b : Bridge) (depth : ℕ) (I₀ I₁ : Cls → Iface Cls) (s : Src Cls) :
    Decidable (Stale b depth I₀ I₁ s) := by unfold Stale; infer_instance

/-- `L.inl = D.K` through the path (`K` is name 0, `inl` name 1); `K = 1` becomes `K = 2`. -/
def ifI1 (k : ℕ) : Cls → Iface Cls
  | L => [(1, .inl false [.const D 0 true])]
  | D => [(0, .const k)]
  | _ => []

def client : Src Cls := { code := [.inl L 1] }

/-- **I1.** A constant through a path. -/
theorem I1_today : Stale ⟨.today, .dep⟩ 1 (ifI1 1) (ifI1 2) client := by decide

/-- `L.inl = constValue[D.N]` (`N` is name 7); `type N = 1` becomes `type N = 2`. In the language
a type-level read of an alias is a folded read, like a constant through a path. -/
def ifI2 (v : ℕ) : Cls → Iface Cls
  | L => [(1, .inl false [.const D 7 true])]
  | D => [(7, .const v)]
  | _ => []

/-- **I2.** An alias read at the type level. -/
theorem I2_today : Stale ⟨.today, .dep⟩ 1 (ifI2 1) (ifI2 2) client := by decide

/-- `transparent inline def inl = h` with `h: Int` (name 2, erasure 0) becoming `h: String` (1). -/
def ifI3 (t : ℕ) : Cls → Iface Cls
  | L => [(2, .member (.prim t)), (1, .inl true [.call L 2])]
  | _ => []

/-- **I3.** A transparent expansion. -/
theorem I3_today : Stale ⟨.today, .dep⟩ 1 (ifI3 0) (ifI3 1) client := by decide

/-- `opaque type T` (name 4) in `O`, `Tr.h(t: O.T)` (name 6), `class K extends Tr`. -/
def ifO1 (rhs : ℕ) : Cls → Iface Cls
  | O => [(4, .opq rhs)]
  | Tr => [(6, .meth (.opq O 4))]
  | _ => []

def k : Src Cls := { parents := [Tr] }

/-- **O1.** An opaque type in an inherited signature: `K`'s forwarder. -/
theorem O1_today : Stale ⟨.bodyDeps, .today⟩ 1 (ifO1 0) (ifO1 1) k := by decide

/-- The same programs are not stale under the fixes (as the obligations imply). -/
theorem I1_bodyDeps : ¬ Stale ⟨.bodyDeps, .dep⟩ 1 (ifI1 1) (ifI1 2) client := by decide
theorem I1_hashDenot : ¬ Stale ⟨.hashDenot, .dep⟩ 1 (ifI1 1) (ifI1 2) client := by decide
theorem I3_bodyDeps : ¬ Stale ⟨.bodyDeps, .dep⟩ 1 (ifI3 0) (ifI3 1) client := by decide
theorem I3_hashDenot : ¬ Stale ⟨.hashDenot, .dep⟩ 1 (ifI3 0) (ifI3 1) client := by decide
theorem O1_dep : ¬ Stale ⟨.bodyDeps, .dep⟩ 1 (ifO1 0) (ifO1 1) k := by decide

/-- Today's bridge fails coverage: the client's read of `D.K` in `I1` has no recorded key that
covers it. -/
theorem not_obligations_today : ¬ (compiler (U := Cls) ⟨.today, .dep⟩ 1).Obligations := by
  intro ob
  obtain ⟨⟨c, kk⟩, hk, hc⟩ :=
    ob.coverage (ifI1 1) Client client (D, ⟨.exp false, .const 0 true⟩) (by decide)
  rcases hc with ⟨h1, h2⟩ | ⟨h, _⟩
  · simp only at h1 h2
    subst h1 h2
    revert hk
    decide
  · cases h

end Zinc.InlineOpaqueSound.Ex
