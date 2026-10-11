import Zinc.Tree

/-!
# Annotations as API and as dependencies

A `TCompiler` instance. Units are annotation classes, constant holders, annotated definitions and
clients that read a definition's annotations.

* `annCls st ar tr`: an annotation class, static or not, whose constructor takes `ar` arguments,
  with `transform` body `tr` (a macro annotation; `0` for a plain one);
* `consts v`: an object with a constant `v`;
* `defn a arg`: `@a(arg) class S`, whose argument is a literal or a constant reference. Its compile
  asks `a`'s constructor arity (the annotation must type-check), whether `a` is static (static
  annotations are pickled and part of the API), `a`'s `transform` (the expansion of `S`), and the
  constant a reference names;
* `client d`: reads `d`'s annotations (a macro, a derivation).

Bridges (`Rec`): `today` records, for a definition, no key on its annotation's class or on the
holder of a constant argument (Scala 2's `Dependency` and `ExtractUsedNames` do not visit
`sym.annotations`; Scala 3's `ExtractDependencies` likewise); `rec1842` records both
(sbt/zinc#1842). A client records its definition. Hashing (`Hashing`): `noBody` hashes an
annotation class without its `transform` body (a method body); `withBody` includes it.

* `obligations_fix`, `fix_sound`: `rec1842` with `withBody` meets the obligations, so T3a.
* `today_not_coverage` (#1842): the definition's `ctor` query has no key.
* `noBody_not_abstraction` (scala/scala3#22999): two macro annotations that differ in `transform`
  hash alike.
-/

set_option linter.unusedSectionVars false

namespace Zinc.Annotations

open Compiler (State Policy)

variable {U : Type} [DecidableEq U]

inductive Arg (U : Type) | lit (n : ℕ) | ref (c : U)
  deriving DecidableEq

inductive Src (U : Type)
  | absent
  | annCls (static : Bool) (arity : ℕ) (transform : ℕ)
  | consts (v : ℕ)
  | defn (a : U) (arg : Arg U)
  | client (d : U)

inductive Q | ctor | static | transform | const | annots
  deriving DecidableEq

abbrev Ans (U : Type) : Q → Type
  | .ctor => ℕ
  | .static => Bool
  | .transform => ℕ
  | .const => ℕ
  | .annots => List (U × ℕ)

inductive Iface (U : Type)
  | none
  | ann (static : Bool) (arity : ℕ) (transform : ℕ)
  | const (v : ℕ)
  /-- A definition: its static annotations with their argument values, and its expansion. -/
  | defn (anns : List (U × ℕ)) (body : ℕ)
  | client (seen : List (U × ℕ))
  deriving DecidableEq

def answer : Iface U → (q : Q) → Ans U q
  | .ann _ ar _, .ctor => ar
  | .ann st _ _, .static => st
  | .ann _ _ tr, .transform => tr
  | .const v, .const => v
  | .defn as _, .annots => as
  | _, .ctor => 0
  | _, .static => false
  | _, .transform => 0
  | _, .const => 0
  | _, .annots => []

structure Out (U : Type) where
  iface : Iface U
  ok : Bool
  /-- What #1842's extractor records for a definition: its annotation's class, a constant's holder. -/
  annDeps : List U
  /-- What a client records: the definition it reads. -/
  reads : List U

abbrev T (U : Type) := Task (U × Q) (fun p => Ans U p.2)
abbrev Env (U : Type) := Task.Env (U × Q) (fun p => Ans U p.2)

def argVal : Arg U → T U ℕ
  | .lit n => .pure n
  | .ref c => .ask (c, .const) .pure

def argDeps : Arg U → List U
  | .lit _ => []
  | .ref c => [c]

def unit : Src U → T U (Out U)
  | .absent => .pure ⟨.none, true, [], []⟩
  | .annCls st ar tr => .pure ⟨.ann st ar tr, true, [], []⟩
  | .consts v => .pure ⟨.const v, true, [], []⟩
  | .defn a arg => .ask (a, .ctor) fun ar => (argVal arg).bind fun v =>
      .ask (a, .static) fun st => .ask (a, .transform) fun tr =>
        .pure ⟨.defn (if st then [(a, v)] else []) tr, ar == 1, a :: argDeps arg, []⟩
  | .client d => .ask (d, .annots) fun as => .pure ⟨.client as, true, [], [d]⟩

inductive K | cls
  deriving DecidableEq

inductive Rec | today | rec1842
  deriving DecidableEq

inductive Hashing | noBody | withBody
  deriving DecidableEq

def keysOf : Rec → Out U → Finset (U × K)
  | .today, o => (o.reads.map (·, K.cls)).toFinset
  | .rec1842, o => ((o.reads ++ o.annDeps).map (·, K.cls)).toFinset

def π : Hashing → Iface U → K → Iface U
  | .noBody, .ann st ar _, _ => .ann st ar 0
  | _, i, _ => i

/-- The interface a unit presents to the queries a definition asks (`ctor`, `static`, `transform`,
`const`): a function of its source alone. -/
def kindIface : Src U → Iface U
  | .absent => .none
  | .annCls st ar tr => .ann st ar tr
  | .consts v => .const v
  | .defn _ _ => .defn [] 0
  | .client _ => .client []

/-- Joint compilation in two stages: the definitions read the round's classes and holders through
their sources (`e₁`); the clients read the round's definitions through their stage-one outputs
(`e₂`). -/
def e₁ (G : Finset U) (src : U → Src U) (e : Env U) : Env U :=
  fun p => if p.1 ∈ G then answer (kindIface (src p.1)) p.2 else e p

def e₂ (G : Finset U) (src : U → Src U) (e : Env U) : Env U :=
  fun p => if p.1 ∈ G then answer ((unit (src p.1)).run (e₁ G src e)).iface p.2 else e p

def group (G : Finset U) (src : U → Src U) (e : Env U) : U → Out U :=
  fun u => (unit (src u)).run (e₂ G src e)

def compiler (r : Rec) (h : Hashing) : TCompiler U (Src U) (Out U) (Iface U) K (Iface U) Q (Ans U) where
  unit := unit
  group := group
  iface := Out.iface
  answer := answer
  π := π h
  keysOf := keysOf r
  covers := fun _ _ => True

/-- A unit's answers to the definition-side queries do not depend on what it asked. -/
theorem answer_kind (s : Src U) (e : Env U) (q : Q) (hq : q ≠ .annots) :
    answer ((unit s).run e).iface q = answer (kindIface s) q := by
  cases s with
  | absent => rfl
  | annCls st ar tr => rfl
  | consts v => rfl
  | defn a arg =>
    simp only [unit, Task.run_ask, Task.run_bind, Task.run_pure, kindIface]
    cases q <;> simp_all [answer]
  | client d =>
    simp only [unit, Task.run_ask, Task.run_pure, kindIface]
    cases q <;> simp_all [answer]

/-- A definition asks no `annots`. -/
theorem trace_defn (a : U) (arg : Arg U) (e : Env U) :
    ∀ q ∈ (unit (.defn a arg)).trace e, q.2 ≠ .annots := by
  intro q hq
  simp only [unit, Task.trace_ask, Task.run_ask, List.mem_cons] at hq
  cases arg with
  | lit n =>
    simp only [argVal, Task.trace_bind, Task.run_bind, Task.trace_pure, Task.run_pure,
      Task.trace_ask, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp
  | ref c =>
    simp only [argVal, Task.trace_bind, Task.run_bind, Task.trace_ask, Task.run_ask, Task.trace_pure,
      Task.run_pure, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp

/-- Two oracles that agree on every query but `annots` give a unit the same answer to `annots`. -/
theorem annots_stable (s : Src U) (e e' : Env U) (h : ∀ p : U × Q, p.2 ≠ .annots → e p = e' p) :
    answer ((unit s).run e).iface .annots = answer ((unit s).run e').iface .annots := by
  cases s with
  | absent => rfl
  | annCls st ar tr => rfl
  | consts v => rfl
  | client d => simp [unit, answer]
  | defn a arg =>
    rw [Task.run_congr (unit (.defn a arg)) e e' (fun q hq => h q (trace_defn a arg e q hq))]

theorem e₂_eq_e₁ (G : Finset U) (src : U → Src U) (e : Env U) (p : U × Q) (hp : p.2 ≠ .annots) :
    e₂ G src e p = e₁ G src e p := by
  simp only [e₂, e₁]
  split
  · exact answer_kind _ _ _ hp
  · rfl

theorem obligations_comp (r : Rec) (h : Hashing) : ∀ (G : Finset U) (src : U → Src U) (e : Env U),
    ∀ u ∈ G, (compiler r h).group G src e u =
      ((compiler r h).unit (src u)).run ((compiler r h).override e G ((compiler r h).iface ∘ (compiler r h).group G src e)) := by
  intro G src e u _
  show (unit (src u)).run (e₂ G src e) = (unit (src u)).run _
  congr 1
  funext p
  obtain ⟨v, q⟩ := p
  simp only [TCompiler.override, compiler, Function.comp, group, e₂]
  split
  · rename_i hv
    by_cases hq : q = .annots
    · subst hq
      exact annots_stable _ _ _ (fun p hp => (e₂_eq_e₁ G src e p hp).symm)
    · rw [answer_kind _ _ _ hq, answer_kind _ _ _ hq]
  · rfl

/-- The units a definition's or client's compile asks about are among those its output names. -/
theorem trace_units (s : Src U) (e : Env U) :
    ∀ q ∈ (unit s).trace e, q.1 ∈ ((unit s).run e).annDeps ++ ((unit s).run e).reads := by
  intro q hq
  cases s with
  | absent => simp [unit] at hq
  | annCls st ar tr => simp [unit] at hq
  | consts v => simp [unit] at hq
  | client d =>
    simp only [unit, Task.trace_ask, Task.trace_pure, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; simp [unit]
  | defn a arg =>
    cases arg with
    | lit n =>
      simp only [unit, argVal, Task.trace_ask, Task.run_ask, Task.trace_bind, Task.run_bind,
        Task.trace_pure, Task.run_pure, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp [unit, argVal, argDeps]
    | ref c =>
      simp only [unit, argVal, Task.trace_ask, Task.run_ask, Task.trace_bind, Task.run_bind,
        Task.trace_pure, Task.run_pure, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp [unit, argVal, argDeps]

/-- **The fix meets the obligations**: #1842's keys, and a macro annotation's `transform` body in
its hash. -/
theorem obligations_fix : (compiler .rec1842 .withBody (U := U)).Obligations where
  comp := obligations_comp .rec1842 .withBody
  coverage := by
    intro s e q hq
    refine ⟨(q.1, .cls), ?_, rfl, trivial⟩
    have := trace_units s e q hq
    show (q.1, K.cls) ∈ keysOf .rec1842 ((unit s).run e)
    simp only [keysOf, List.mem_toFinset, List.mem_map, Prod.mk.injEq, and_true, exists_eq_right,
      List.mem_append] at this ⊢
    rcases this with h | h
    · exact .inr h
    · exact .inl h
  abstraction := by
    intro i i' _ h _ _
    cases i <;> cases i' <;> simp_all [compiler, π]

/-- **T3a for the fix.** -/
theorem fix_sound (S : Finset U) (src : U → Src U) (P : Policy U (Out U) K) (hP : P.Sound S)
    (fuel n : ℕ) (R : Finset U) (s : State U (Out U) K) (D : Finset U) (hD : D ⊆ R)
    (hInv : (compiler .rec1842 .withBody).Inv S src s D) (s' : State U (Out U) K)
    (h : (compiler .rec1842 .withBody).zinc S src P fuel n R s = some s') :
    (compiler .rec1842 .withBody).Inv S src s' ∅ :=
  (compiler .rec1842 .withBody).zinc_sound obligations_fix S src P hP fuel n R s D hD hInv s' h

/-- **sbt/zinc#1842**: `@Ann(1) class S` asks `Ann`'s constructor, and today's bridge records no
key on `Ann`; with any hashing. -/
theorem today_not_coverage (h : Hashing) : ¬ (compiler .today h (U := Fin 2)).Obligations := by
  intro ob
  obtain ⟨k, hk, _, _⟩ := ob.coverage (.defn 0 (.lit 1)) (fun p => answer (Iface.ann true 1 0) p.2)
    (0, .ctor) (by simp [compiler, unit])
  simp [compiler, unit, keysOf, argVal] at hk

/-- **scala/scala3#22999**: two macro annotations that differ in their `transform` body hash alike
without the body, and the annotated definition's expansion differs; with any keys. -/
theorem noBody_not_abstraction (r : Rec) : ¬ (compiler r .noBody (U := Fin 2)).Obligations := by
  intro ob
  have := ob.abstraction (.ann true 1 5) (.ann true 1 6) .cls rfl .transform trivial
  simp [compiler, answer] at this

end Zinc.Annotations
