import Zinc.Tree

/-!
# SAM conversion and local classes as a specification

A `TCompiler` (keys read off the output) for top-level clients whose bodies hold lambdas converted
to SAM types and anonymous or local classes. Neither has a Zinc class: their reads are recorded on
the enclosing top-level class, the client unit. Over an arbitrary finite set `N` of names (classes,
methods and types share it) and arbitrary programs.

**Units** are top-level classes. A class's source declares whether it is an interface, its
parents, and its methods (name, parameter types, result, abstract or not). **The query** `info`
returns that declaration; `member m` returns its methods named `m`.

**The task** (`PLAN-sam.md`). A lambda of arity `n` to a target `t`, and an anonymous class
extending `t`, walk `t`'s ancestry, asking `info` of each class. Merging the walk (the first
declaration of a name wins) gives the abstract members: a lambda converts if exactly one remains
and takes `n` parameters, through `invokedynamic` if every class of the walk is an interface and
through a class at compile time otherwise (Java requires an interface); an anonymous class must
implement them all. A lambda passed to `o.m` asks `o` for the alternatives named `m`, walks each
alternative's parameter type, and converts to the one that is functional at that arity.

**Keys** per design (`Design`), read off the output, for the edges each bridge records
(`PLAN-sam.md`'s table). An inheritance or local-inheritance edge on `t` stands for `(x, api)` for
every class `x` of `t`'s walk, because Zinc invalidates the transitive inheritors of a changed
class and their local inheritors; a Scala member-ref edge with used name `t` is `(t, present)`,
which covers no member.

**Results.** `pre` (Scala 2 before sbt/zinc#1288, Java before #217) fails coverage: `w830_pre`,
`w192_pre`. `today` fails it for a lambda in argument position: `p1_today` (Java: the parameter type
is only in a descriptor) and `p2_today` (an alternative not chosen). `today` meets the obligations
on the sources without such lambdas (`obligations_today_argFree`, `today_sound_argFree`). `fix`
records the walk of every alternative's parameter type; it meets the obligations everywhere
(`obligations_fix`, `fix_sound`) and costs nothing elsewhere (`fix_eq_today`).
-/

set_option linter.unusedSectionVars false

namespace Zinc.Sam

open Compiler (State Policy)

variable {N : Type} [DecidableEq N]

structure Meth (N : Type) where
  name : N
  params : List N
  res : N
  abs : Bool
  deriving DecidableEq

structure Info (N : Type) where
  itf : Bool
  sup : List N
  ms : List (Meth N)
  deriving DecidableEq

inductive Q (N : Type) | info | member (m : N)
  deriving DecidableEq

abbrev Iface (N : Type) := Option (Info N)

abbrev Ans (_ : Q N) : Type := Iface N

/-- A use in a client's body. -/
inductive Use (N : Type)
  /-- A lambda of arity `ar` converted to `t`, which the client names. -/
  | lam (t : N) (ar : ℕ)
  /-- An anonymous or local class extending `t`. -/
  | anon (t : N)
  /-- `o.m(lambda)`, a lambda of arity `ar` as the argument. -/
  | lamArg (o m : N) (ar : ℕ)
  deriving DecidableEq

inductive Src (N : Type)
  | absent
  | ty (i : Info N)
  | client (java : Bool) (uses : List (Use N))

/-- How a use lowers. -/
inductive Res (N : Type)
  /-- A lambda implementing `m`: `invokedynamic` if `lmf`, else a class at compile time. -/
  | sam (lmf : Bool) (m : Meth N)
  /-- An anonymous class implementing these abstract members. -/
  | impl (ms : List (Meth N))
  /-- A lambda argument converted to the alternative whose parameter type is `t`. -/
  | via (t : N) (lmf : Bool) (m : Meth N)
  | err
  | ambiguous
  deriving DecidableEq

/-- What the output shows of a use: the classes walked from each type it converts to or extends
(the target, or each alternative's parameter type), the alternative chosen, and the lowering. -/
structure Rec (N : Type) where
  use : Use N
  walks : List (N × List N)
  chosen : Option N
  res : Res N
  deriving DecidableEq

structure Out (N : Type) where
  iface : Iface N
  java : Bool
  recs : List (Rec N)

abbrev T (N : Type) := Task (N × Q N) (fun p => Ans p.2)
abbrev Env (N : Type) := Task.Env (N × Q N) (fun p => Ans p.2)

def answer (i : Iface N) : (q : Q N) → Ans q
  | .info => i
  | .member m => i.map fun x => ⟨x.itf, [], x.ms.filter (·.name = m)⟩

/-- Ask `info` up the parents, depth-first, at most `k` classes. -/
def walk : ℕ → List N → T N (List (N × Iface N))
  | 0, _ => .pure []
  | _ + 1, [] => .pure []
  | k + 1, x :: xs => .ask (x, .info) fun i =>
      (walk k (((i.map (·.sup)).getD []) ++ xs)).bind fun r => .pure ((x, i) :: r)

def fuel : ℕ := 8

/-- The members up the walk, the first declaration of a name winning. -/
def merged (w : List (N × Iface N)) : List (Meth N) :=
  (w.flatMap fun p => (p.2.map (·.ms)).getD []).foldl
    (fun acc m => if acc.any (·.name = m.name) then acc else acc ++ [m]) []

def abstracts (w : List (N × Iface N)) : List (Meth N) := (merged w).filter (·.abs)

/-- Every class of the walk exists and is an interface. -/
def allItf (w : List (N × Iface N)) : Bool := w.all fun p => match p.2 with
  | some i => i.itf
  | none => false

/-- A lambda of arity `ar` to the walked type. -/
def lamRes (java : Bool) (ar : ℕ) (w : List (N × Iface N)) : Res N :=
  match w.head?, abstracts w with
  | some (_, some _), [m] =>
    if m.params.length = ar then
      if java && !allItf w then .err else .sam (allItf w) m
    else .err
  | _, _ => .err

/-- The single-parameter alternatives' parameter types. -/
def cands (i : Iface N) : List N :=
  ((i.map (·.ms)).getD []).filterMap fun m => match m.params with
    | [t] => some t
    | _ => none

def walks : List N → T N (List (N × List (N × Iface N)))
  | [] => .pure []
  | t :: ts => (walk fuel [t]).bind fun w => (walks ts).bind fun r => .pure ((t, w) :: r)

def names (w : List (N × Iface N)) : List N := w.map (·.1)

def choose (java : Bool) (ar : ℕ) (ws : List (N × List (N × Iface N))) : Option N × Res N :=
  match ws.filter fun p => lamRes java ar p.2 != .err with
  | [(t, w)] => match lamRes java ar w with
    | .sam lmf m => (some t, .via t lmf m)
    | _ => (none, .err)
  | [] => (none, .err)
  | _ => (none, .ambiguous)

def useT (java : Bool) : Use N → T N (Rec N)
  | .lam t ar => (walk fuel [t]).bind fun w => .pure ⟨.lam t ar, [(t, names w)], none, lamRes java ar w⟩
  | .anon t => (walk fuel [t]).bind fun w => .pure ⟨.anon t, [(t, names w)], none, .impl (abstracts w)⟩
  | .lamArg o m ar => .ask (o, .member m) fun i => (walks (cands i)).bind fun ws =>
      let c := choose java ar ws
      .pure ⟨.lamArg o m ar, ws.map (fun p => (p.1, names p.2)), c.1, c.2⟩

def usesT (java : Bool) : List (Use N) → T N (List (Rec N))
  | [] => .pure []
  | u :: us => (useT java u).bind fun r => (usesT java us).bind fun rs => .pure (r :: rs)

def ifaceOf : Src N → Iface N
  | .absent => none
  | .ty i => some i
  | .client _ _ => some ⟨false, [], []⟩

def unit : Src N → T N (Out N)
  | .client java us => (usesT java us).bind fun rs => .pure ⟨some ⟨false, [], []⟩, java, rs⟩
  | s => .pure ⟨ifaceOf s, false, []⟩

/-! ## The trace -/

/-- The queries a use's output shows it asked. -/
def Rec.qs (r : Rec N) : List (N × Q N) :=
  (match r.use with
   | .lamArg o m _ => [(o, .member m)]
   | _ => []) ++ r.walks.flatMap fun p => p.2.map (·, .info)

theorem trace_walk (e : Env N) : ∀ (k : ℕ) (xs : List N),
    (walk k xs).trace e = ((walk k xs).run e).map fun p => (p.1, Q.info)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    simp only [walk, Task.trace_ask, Task.run_ask, Task.trace_bind, Task.run_bind, Task.trace_pure,
      Task.run_pure, List.append_nil, List.map_cons]
    rw [trace_walk e k]

theorem mem_trace_walks (e : Env N) : ∀ (ts : List N), ∀ q ∈ (walks ts).trace e,
    ∃ p ∈ (walks ts).run e, q ∈ (names p.2).map (·, Q.info)
  | [], q, h => by simp [walks] at h
  | t :: ts, q, h => by
    simp only [walks, Task.trace_bind, Task.run_bind, Task.trace_pure, Task.run_pure,
      List.append_nil, List.mem_append, List.mem_cons] at h ⊢
    rcases h with h | h
    · refine ⟨_, .inl rfl, ?_⟩
      rw [trace_walk] at h
      simpa [names, List.map_map] using h
    · obtain ⟨p, hp, hq⟩ := mem_trace_walks e ts q h
      exact ⟨p, .inr hp, hq⟩

theorem mem_trace_useT (e : Env N) (java : Bool) (u : Use N) :
    ∀ q ∈ (useT java u).trace e, q ∈ ((useT java u).run e).qs := by
  intro q h
  cases u with
  | lam t ar =>
    simp only [useT, Task.trace_bind, Task.run_bind, Task.trace_pure, Task.run_pure, List.append_nil,
      trace_walk] at h ⊢
    simpa [Rec.qs, names, List.map_map] using h
  | anon t =>
    simp only [useT, Task.trace_bind, Task.run_bind, Task.trace_pure, Task.run_pure, List.append_nil,
      trace_walk] at h ⊢
    simpa [Rec.qs, names, List.map_map] using h
  | lamArg o m ar =>
    simp only [useT, Task.trace_ask, Task.run_ask, Task.trace_bind, Task.run_bind, Task.trace_pure,
      Task.run_pure, List.append_nil, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · simp [Rec.qs]
    · obtain ⟨p, hp, hq⟩ := mem_trace_walks e _ q h
      simp only [Rec.qs, List.cons_append, List.nil_append, List.mem_cons, List.mem_flatMap,
        List.mem_map]
      exact .inr ⟨(p.1, names p.2), ⟨p, hp, rfl⟩, by simpa using hq⟩

theorem mem_trace_usesT (e : Env N) (java : Bool) : ∀ (us : List (Use N)), ∀ q ∈ (usesT java us).trace e,
    ∃ r ∈ (usesT java us).run e, q ∈ r.qs
  | [], q, h => by simp [usesT] at h
  | u :: us, q, h => by
    simp only [usesT, Task.trace_bind, Task.run_bind, Task.trace_pure, Task.run_pure,
      List.append_nil, List.mem_append, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact ⟨_, .inl rfl, mem_trace_useT e java u q h⟩
    · obtain ⟨r, hr, hq⟩ := mem_trace_usesT e java us q h
      exact ⟨r, .inr hr, hq⟩

theorem iface_unit (e : Env N) (s : Src N) : ((unit s).run e).iface = ifaceOf s := by
  cases s with
  | client java us => simp [unit, ifaceOf]
  | _ => rfl

theorem trace_unit (e : Env N) (s : Src N) : ∀ q ∈ (unit s).trace e,
    ∃ r ∈ ((unit s).run e).recs, q ∈ r.qs := by
  intro q h
  cases s with
  | client java us =>
    simp only [unit, Task.trace_bind, Task.run_bind, Task.trace_pure, Task.run_pure,
      List.append_nil] at h ⊢
    exact mem_trace_usesT e java us q h
  | _ => simp [unit] at h

/-! ## Keys -/

inductive K (N : Type) | api | name (m : N) | present
  deriving DecidableEq

def coversB : Q N → K N → Bool
  | _, .api => true
  | .member m, .name m' => m = m'
  | _, _ => false

def covers (q : Q N) (k : K N) : Prop := coversB q k = true

def π (i : Iface N) : K N → Iface N
  | .api => i
  | .name m => answer i (.member m)
  | .present => i.map fun _ => ⟨false, [], []⟩

/-- The bridges: Scala 2 before sbt/zinc#1288 and Java before #217 (`pre`); Scala 2.13.13+,
Scala 3 and Java now (`today`); the fix. -/
inductive Design | pre | today | fix
  deriving DecidableEq

/-- The `api` keys of walked classes: an inheritance edge with Zinc's transitive invalidation. -/
def walkKeys (ws : List (N × List N)) : List (N × K N) := ws.flatMap fun p => p.2.map (·, .api)

/-- The edges a bridge records for a use. -/
def recKeys : Design → Bool → Rec N → List (N × K N)
  | .pre, false, ⟨.lam t _, _, _, _⟩ => [(t, .present)]
  | .pre, true, ⟨.anon _, _, _, _⟩ => []
  | _, _, ⟨.lam _ _, ws, _, _⟩ => walkKeys ws
  | _, _, ⟨.anon _, ws, _, _⟩ => walkKeys ws
  | d, java, ⟨.lamArg o m _, ws, ch, _⟩ =>
    (if java then (o, .api) else (o, .name m)) ::
      match d with
      | .pre => []
      | .today => if java then [] else walkKeys (ws.filter fun p => some p.1 = ch)
      | .fix => walkKeys ws

def keysOf (d : Design) (o : Out N) : Finset (N × K N) :=
  (o.recs.flatMap (recKeys d o.java)).toFinset

/-! ## The compiler -/

def group (G : Finset N) (src : N → Src N) (e : Env N) : N → Out N :=
  fun u => (unit (src u)).run fun p => if p.1 ∈ G then answer (ifaceOf (src p.1)) p.2 else e p

/-- The compiler of a design over the sources `S` (all of them, or a subtype). -/
def compiler (d : Design) (S : Type) (val : S → Src N) :
    TCompiler N S (Out N) (Iface N) (K N) (Iface N) (Q N) Ans where
  unit := fun s => unit (val s)
  group := fun G src e => group G (val ∘ src) e
  iface := Out.iface
  answer := answer
  π := π
  keysOf := keysOf d
  covers := covers

theorem obligations_comp (d : Design) (S : Type) (val : S → Src N) :
    ∀ (G : Finset N) (src : N → S) (e : Env N), ∀ u ∈ G,
      (compiler d S val).group G src e u =
        ((compiler d S val).unit (src u)).run
          ((compiler d S val).override e G ((compiler d S val).iface ∘ (compiler d S val).group G src e)) := by
  intro G src e u _
  show (unit (val (src u))).run _ = (unit (val (src u))).run _
  congr 1
  funext p
  simp only [TCompiler.override, compiler, group, Function.comp, iface_unit]

theorem obligations_abstraction (d : Design) (S : Type) (val : S → Src N) :
    ∀ (i i' : Iface N) (k : K N), (compiler d S val).π i k = (compiler d S val).π i' k →
      ∀ q, (compiler d S val).covers q k → (compiler d S val).answer i q = (compiler d S val).answer i' q := by
  intro i i' k h q hq
  simp only [compiler] at h hq ⊢
  cases k with
  | api => simp only [π] at h; rw [h]
  | name m =>
    cases q with
    | info => simp [covers, coversB] at hq
    | member m' =>
      simp only [covers, coversB, decide_eq_true_eq] at hq
      subst hq
      exact h
  | present => cases q <;> simp [covers, coversB] at hq

/-- A walked class has its `api` key. -/
theorem mem_walkKeys (ws : List (N × List N)) (p : N × List N) (hp : p ∈ ws) (x : N) (hx : x ∈ p.2) :
    (x, K.api) ∈ walkKeys ws := by
  simp only [walkKeys, List.mem_flatMap, List.mem_map]
  exact ⟨p, hp, x, hx, rfl⟩

/-- The keys a design records for a use cover its queries, given that they include the walks'
keys and, for a lambda argument, a key on the owner's member. -/
theorem covers_rec (d : Design) (java : Bool) (r : Rec N)
    (hw : ∀ p ∈ r.walks, ∀ x ∈ p.2, (x, K.api) ∈ recKeys d java r)
    (ho : ∀ o m ar, r.use = .lamArg o m ar → ∃ k ∈ recKeys d java r, o = k.1 ∧ covers (.member m) k.2) :
    ∀ q ∈ r.qs, ∃ k ∈ recKeys d java r, q.1 = k.1 ∧ covers q.2 k.2 := by
  intro q hq
  simp only [Rec.qs, List.mem_append, List.mem_flatMap, List.mem_map] at hq
  rcases hq with hq | ⟨p, hp, x, hx, rfl⟩
  · revert hq
    rcases r with ⟨u, ws, ch, res⟩
    cases u with
    | lamArg o m ar =>
      intro hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      exact ho o m ar rfl
    | _ => simp
  · exact ⟨(x, .api), hw p hp x hx, rfl, rfl⟩

theorem recKeys_fix (java : Bool) (r : Rec N) :
    ∀ q ∈ r.qs, ∃ k ∈ recKeys .fix java r, q.1 = k.1 ∧ covers q.2 k.2 := by
  apply covers_rec
  · intro p hp x hx
    rcases r with ⟨u, ws, ch, res⟩
    cases u <;> cases java <;>
      simp only [recKeys, List.mem_cons] <;> first
        | exact mem_walkKeys ws p hp x hx
        | exact .inr (mem_walkKeys ws p hp x hx)
  · intro o m ar hu
    rcases r with ⟨u, ws, ch, res⟩
    simp only at hu
    subst hu
    cases java
    · exact ⟨(o, .name m), by simp [recKeys], rfl, by simp [covers, coversB]⟩
    · exact ⟨(o, .api), by simp [recKeys], rfl, rfl⟩

/-- Coverage from the per-use statement. -/
theorem coverage_of (d : Design) (S : Type) (val : S → Src N)
    (h : ∀ (s : S) (e : Env N), ∀ r ∈ ((unit (val s)).run e).recs, ∀ q ∈ r.qs,
      ∃ k ∈ recKeys d ((unit (val s)).run e).java r, q.1 = k.1 ∧ covers q.2 k.2) :
    ∀ (s : S) (e : Env N), ∀ q ∈ ((compiler d S val).unit s).trace e,
      ∃ k ∈ (compiler d S val).keysOf (((compiler d S val).unit s).run e),
        q.1 = k.1 ∧ (compiler d S val).covers q.2 k.2 := by
  intro s e q hq
  obtain ⟨r, hr, hq⟩ := trace_unit e (val s) q hq
  obtain ⟨k, hk, h1, h2⟩ := h s e r hr q hq
  refine ⟨k, ?_, h1, h2⟩
  simp only [compiler, keysOf, List.mem_toFinset, List.mem_flatMap]
  exact ⟨r, hr, hk⟩

/-- **The fix meets the obligations.** -/
theorem obligations_fix : (compiler .fix (Src N) id).Obligations where
  comp := obligations_comp .fix (Src N) id
  coverage := coverage_of .fix (Src N) id fun _ _ r _ => recKeys_fix _ r
  abstraction := obligations_abstraction .fix (Src N) id

/-- **T3a for the fix**: when Zinc's loop stops, every class is up to date, for every program,
edit and sound invalidation policy. -/
theorem fix_sound (S : Finset N) (src : N → Src N) (P : Policy N (Out N) (K N)) (hP : P.Sound S)
    (fuel n : ℕ) (R : Finset N) (s : State N (Out N) (K N)) (D : Finset N) (hD : D ⊆ R)
    (hInv : (compiler .fix (Src N) id).Inv S src s D) (s' : State N (Out N) (K N))
    (h : (compiler .fix (Src N) id).zinc S src P fuel n R s = some s') :
    (compiler .fix (Src N) id).Inv S src s' ∅ :=
  (compiler .fix (Src N) id).zinc_sound obligations_fix S src P hP fuel n R s D hD hInv s' h

/-! ## Today, without lambdas in argument position -/

def Use.isArg : Use N → Bool
  | .lamArg .. => true
  | _ => false

def Src.argFree : Src N → Prop
  | .client _ us => ∀ u ∈ us, u.isArg = false
  | _ => True

/-- The sources without a lambda in argument position. -/
abbrev ArgFree (N : Type) [DecidableEq N] := { s : Src N // s.argFree }

theorem use_useT (e : Env N) (java : Bool) (u : Use N) : ((useT java u).run e).use = u := by
  cases u <;> simp [useT]

theorem uses_usesT (e : Env N) (java : Bool) : ∀ us : List (Use N),
    ((usesT java us).run e).map (·.use) = us
  | [] => rfl
  | u :: us => by
    simp only [usesT, Task.run_bind, Task.run_pure, List.map_cons, use_useT]
    rw [uses_usesT e java us]

theorem recKeys_today (java : Bool) (r : Rec N) (hr : r.use.isArg = false) :
    ∀ q ∈ r.qs, ∃ k ∈ recKeys .today java r, q.1 = k.1 ∧ covers q.2 k.2 := by
  apply covers_rec
  · intro p hp x hx
    rcases r with ⟨u, ws, ch, res⟩
    cases u with
    | lamArg => simp [Use.isArg] at hr
    | _ => cases java <;> exact mem_walkKeys ws p hp x hx
  · intro o m ar hu
    rw [hu] at hr
    simp [Use.isArg] at hr

/-- **Today meets the obligations without lambdas in argument position**: sbt/zinc#1288 and
scala/scala3#16996 cover a lambda whose target the client names, and #217 an anonymous class. -/
theorem obligations_today_argFree : (compiler .today (ArgFree N) Subtype.val).Obligations where
  comp := obligations_comp .today (ArgFree N) Subtype.val
  coverage := coverage_of .today (ArgFree N) Subtype.val fun s e r hr => by
    obtain ⟨s, hs⟩ := s
    apply recKeys_today
    cases s with
    | client java us =>
      simp only [unit, Task.run_bind, Task.run_pure] at hr
      have : r.use ∈ us := by rw [← uses_usesT e java us]; exact List.mem_map_of_mem hr
      exact hs r.use this
    | _ => simp [unit] at hr
  abstraction := obligations_abstraction .today (ArgFree N) Subtype.val

theorem today_sound_argFree (S : Finset N) (src : N → ArgFree N) (P : Policy N (Out N) (K N))
    (hP : P.Sound S) (fuel n : ℕ) (R : Finset N) (s : State N (Out N) (K N)) (D : Finset N)
    (hD : D ⊆ R) (hInv : (compiler .today (ArgFree N) Subtype.val).Inv S src s D)
    (s' : State N (Out N) (K N))
    (h : (compiler .today (ArgFree N) Subtype.val).zinc S src P fuel n R s = some s') :
    (compiler .today (ArgFree N) Subtype.val).Inv S src s' ∅ :=
  (compiler .today (ArgFree N) Subtype.val).zinc_sound obligations_today_argFree S src P hP fuel n R s D hD hInv s' h

/-! ## The fix's cost -/

/-- The fix records everything today does. -/
theorem today_sub_fix (o : Out N) : keysOf .today o ⊆ keysOf .fix o := by
  intro k hk
  simp only [keysOf, List.mem_toFinset, List.mem_flatMap] at hk ⊢
  obtain ⟨r, hr, hk⟩ := hk
  refine ⟨r, hr, ?_⟩
  rcases r with ⟨u, ws, ch, res⟩
  cases u <;> cases hj : o.java <;> simp only [hj, recKeys] at hk ⊢ <;> try exact hk
  all_goals
    simp only [List.mem_cons, Bool.false_eq_true, ite_false, ite_true] at hk ⊢
    rcases hk with hk | hk
    · exact .inl hk
    · right
      simp only [walkKeys, List.mem_flatMap, List.mem_filter] at hk ⊢
      first
        | (obtain ⟨p, ⟨hp, _⟩, hx⟩ := hk; exact ⟨p, hp, hx⟩)
        | simp at hk

/-- **The fix costs nothing outside lambdas in argument position.** -/
theorem fix_eq_today (o : Out N) (h : ∀ r ∈ o.recs, r.use.isArg = false) :
    keysOf .fix o = keysOf .today o := by
  simp only [keysOf]
  congr 1
  apply List.flatMap_congr
  intro r hr
  have := h r hr
  rcases r with ⟨u, ws, ch, res⟩
  cases u with
  | lamArg => simp [Use.isArg] at this
  | _ => cases o.java <;> rfl

/-! ## Witnesses -/

/-- A traced query with no covering key refutes the obligations. -/
theorem not_obligations_of (d : Design) (s : Src N) (e : Env N) (q : N × Q N)
    (hq : q ∈ (unit s).trace e)
    (hnot : ∀ k ∈ keysOf d ((unit s).run e), ¬ (q.1 = k.1 ∧ coversB q.2 k.2 = true)) :
    ¬ (compiler d (Src N) id).Obligations := by
  intro ob
  obtain ⟨k, hk, h⟩ := ob.coverage s e q hq
  exact hnot k hk h

end Zinc.Sam

/-! The witnesses, over the names `F` (0), `F1` (1), `F2` (2), `O` (3), `apply` (4), `other` (5),
`run` (6) and `Int` (7). -/

namespace Zinc.Sam.Witness

open Zinc.Sam

abbrev Nm := Fin 8

/-- The oracle of a class table. -/
def env (l : List (Nm × Info Nm)) : Env Nm := fun q => answer ((l.find? (·.1 = q.1)).map (·.2)) q.2

def applyM (res : Nm := 7) : Meth Nm := ⟨4, [], res, true⟩

/-- `interface F { int apply(); }` -/
def samF (res : Nm := 7) : Info Nm := ⟨true, [], [applyM res]⟩

/-- `interface F1 { int apply(); int other(); }`, and with `other` a default. -/
def f1 (dflt : Bool) : Info Nm := ⟨true, [], [applyM, ⟨5, [], 7, !dflt⟩]⟩

/-- `class O { static void run(F f) }` -/
def oneAlt : Info Nm := ⟨false, [], [⟨6, [0], 7, false⟩]⟩

/-- `class O { static void run(F1 f); static void run(F2 f) }` -/
def twoAlts : Info Nm := ⟨false, [], [⟨6, [1], 7, false⟩, ⟨6, [2], 7, false⟩]⟩

/-- **sbt/zinc#830**, Scala 2 before #1288: `val f: F = () => …`. The lambda implements `F.apply`;
changing its result changes the output, but the only key is `(F, present)`. -/
theorem w830_pre : ¬ (compiler .pre (Src Nm) id).Obligations :=
  not_obligations_of .pre (.client false [.lam 0 0]) (env [(0, samF)]) (0, .info) (by decide +kernel) (by decide +kernel)

example : ((unit (.client false [.lam 0 0])).run (env [(0, samF)])).recs.map (·.res) =
      [.sam true (applyM 7)] ∧
    ((unit (.client false [.lam 0 0])).run (env [(0, samF 0)])).recs.map (·.res) =
      [.sam true (applyM 0)] := by decide +kernel

/-- **sbt/zinc#192**, Java before #217: an anonymous class extending `F` leaves no key. -/
theorem w192_pre : ¬ (compiler .pre (Src Nm) id).Obligations :=
  not_obligations_of .pre (.client true [.anon 0]) (env [(0, samF)]) (0, .info) (by decide +kernel) (by decide +kernel)

/-- **P1**, Java today: `O.run(() -> 1)`. The walk of `F` is asked; `J`'s constant pool names `O`
only (`F` is in the `Methodref` and `invokedynamic` descriptors, which `ClassFile.types` does not
read), so the only key is `(O, api)`. -/
theorem p1_today : ¬ (compiler .today (Src Nm) id).Obligations :=
  not_obligations_of .today (.client true [.lamArg 3 6 0]) (env [(3, oneAlt), (0, samF)]) (0, .info)
    (by decide +kernel) (by decide +kernel)

/-- **P2**, Scala today: `O.run(() => 1)` with `run(F1)` and `run(F2)`. `F1` is walked and not
chosen, so it has no key. -/
theorem p2_today : ¬ (compiler .today (Src Nm) id).Obligations :=
  not_obligations_of .today (.client false [.lamArg 3 6 0]) (env [(3, twoAlts), (1, f1 false), (2, samF)])
    (1, .info) (by decide +kernel) (by decide +kernel)

/-- …and the edit to `F1` that makes it functional turns the call ambiguous. -/
example : ((unit (.client false [.lamArg 3 6 0])).run (env [(3, twoAlts), (1, f1 false), (2, samF)])).recs.map
      (·.res) = [.via 2 true applyM] ∧
    ((unit (.client false [.lamArg 3 6 0])).run (env [(3, twoAlts), (1, f1 true), (2, samF)])).recs.map
      (·.res) = [.ambiguous] := by decide +kernel

/-- The fix covers both: P2's walk of `F1` has a key. -/
example : (1, K.api) ∈ keysOf .fix ((unit (.client false [.lamArg 3 6 0])).run
    (env [(3, twoAlts), (1, f1 false), (2, samF)])) := by decide +kernel

end Zinc.Sam.Witness
