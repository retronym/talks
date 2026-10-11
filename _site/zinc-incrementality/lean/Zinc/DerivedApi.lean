import Zinc.Tree

/-!
# Derived API: export forwarders and used types' supertypes

A `TCompiler` instance. Units:

* `holder v`: `object B { val x: V }`, the type of `x` being the unit `v`;
* `cls ps`: a class with parents `ps`;
* `member n`: `object A { def f: T }` with signature `n`;
* `exporter a`: `object B { export a.* }`, whose forwarder `f` has `a.f`'s signature;
* `assign b p`: `val p: P = b.x`, which compiles when the type of `b.x` has `p` among its parents;
* `call b`: a client of `b.f`, the forwarder.

Queries: `typeOf` (the unit a value's type is), `parents`, `sig` (a forwarder's or a member's
signature, as clients see it), `baseSig` (the exported member's, as the exporter reads it).

Bridges: `today` records only what a unit names (the exporter, through a wildcard, names no
member; `assign` names `b` and `p`); `fix` adds the exporter's edge to the exported object
(scala/scala3#10182) and the type of the value used (sbt/zinc#87's types in used names).

* `obligations_fix`, `fix_sound`: the fix meets the obligations, so T3a.
* `export_not_coverage`: the exporter's `baseSig` query has no key today.
* `usedType_not_coverage`: `assign`'s `parents` query on the value's type has no key today.
-/

set_option linter.unusedSectionVars false

namespace Zinc.DerivedApi

open Compiler (State Policy)

variable {U : Type} [DecidableEq U]

inductive Src (U : Type)
  | absent
  | holder (v : U)
  | cls (ps : List U)
  | member (n : ℕ)
  | exporter (a : U)
  | assign (b p : U)
  | call (b : U)

inductive Q | typeOf | parents | sig | baseSig
  deriving DecidableEq

abbrev Ans (U : Type) : Q → Type
  | .typeOf => Option U
  | .parents => List U
  | .sig => ℕ
  | .baseSig => ℕ

inductive Iface (U : Type)
  | none
  | holder (v : U)
  | cls (ps : List U)
  | member (n : ℕ)
  | forwarder (n : ℕ)
  | client (r : ℕ)
  deriving DecidableEq

def answer : Iface U → (q : Q) → Ans U q
  | .holder v, .typeOf => some v
  | .cls ps, .parents => ps
  | .member n, .sig => n
  | .member n, .baseSig => n
  | .forwarder n, .sig => n
  | _, .typeOf => none
  | _, .parents => []
  | _, .sig => 0
  | _, .baseSig => 0

structure Out (U : Type) where
  iface : Iface U
  ok : Bool
  /-- The units the unit's source names. -/
  named : List U
  /-- What the fix adds: the exported object, the type of a value used. -/
  derived : List U

abbrev T (U : Type) := Task (U × Q) (fun p => Ans U p.2)
abbrev Env (U : Type) := Task.Env (U × Q) (fun p => Ans U p.2)

def unit : Src U → T U (Out U)
  | .absent => .pure ⟨.none, true, [], []⟩
  | .holder v => .pure ⟨.holder v, true, [], []⟩
  | .cls ps => .pure ⟨.cls ps, true, [], []⟩
  | .member n => .pure ⟨.member n, true, [], []⟩
  | .exporter a => .ask (a, .baseSig) fun n => .pure ⟨.forwarder n, true, [], [a]⟩
  | .assign b p => .ask (b, .typeOf) fun v =>
      match v with
      | none => .pure ⟨.client 0, false, [b, p], []⟩
      | some v => .ask (v, .parents) fun ps => .pure ⟨.client 0, ps.contains p, [b, p], [v]⟩
  | .call b => .ask (b, .sig) fun n => .pure ⟨.client n, true, [b], []⟩

inductive K | cls
  deriving DecidableEq

inductive Rec | today | fix
  deriving DecidableEq

def keysOf : Rec → Out U → Finset (U × K)
  | .today, o => (o.named.map (·, K.cls)).toFinset
  | .fix, o => ((o.named ++ o.derived).map (·, K.cls)).toFinset

/-- What a unit answers to `typeOf`, `parents` and `baseSig`: a function of its source alone. -/
def kindIface : Src U → Iface U
  | .absent => .none
  | .holder v => .holder v
  | .cls ps => .cls ps
  | .member n => .member n
  | .exporter _ => .forwarder 0
  | .assign _ _ => .client 0
  | .call _ => .client 0

def e₁ (G : Finset U) (src : U → Src U) (e : Env U) : Env U :=
  fun p => if p.1 ∈ G then answer (kindIface (src p.1)) p.2 else e p

def e₂ (G : Finset U) (src : U → Src U) (e : Env U) : Env U :=
  fun p => if p.1 ∈ G then answer ((unit (src p.1)).run (e₁ G src e)).iface p.2 else e p

def group (G : Finset U) (src : U → Src U) (e : Env U) : U → Out U :=
  fun u => (unit (src u)).run (e₂ G src e)

def compiler (r : Rec) : TCompiler U (Src U) (Out U) (Iface U) K (Iface U) Q (Ans U) where
  unit := unit
  group := group
  iface := Out.iface
  answer := answer
  π := fun i _ => i
  keysOf := keysOf r
  covers := fun _ _ => True

theorem answer_kind (s : Src U) (e : Env U) (q : Q) (hq : q ≠ .sig) :
    answer ((unit s).run e).iface q = answer (kindIface s) q := by
  cases s with
  | absent => rfl
  | holder v => rfl
  | cls ps => rfl
  | member n => rfl
  | exporter a => simp only [unit, Task.run_ask, Task.run_pure, kindIface]; cases q <;> simp_all [answer]
  | assign b p =>
    simp only [unit, Task.run_ask, kindIface]
    split <;> simp only [Task.run_ask, Task.run_pure] <;> cases q <;> simp_all [answer]
  | call b => simp only [unit, Task.run_ask, Task.run_pure, kindIface]; cases q <;> simp_all [answer]

/-- An exporter asks no `sig`. -/
theorem trace_exporter (a : U) (e : Env U) : ∀ q ∈ (unit (.exporter a)).trace e, q.2 ≠ .sig := by
  intro q hq; simp [unit] at hq; subst hq; simp

theorem sig_stable (s : Src U) (e e' : Env U) (h : ∀ p : U × Q, p.2 ≠ .sig → e p = e' p) :
    answer ((unit s).run e).iface .sig = answer ((unit s).run e').iface .sig := by
  cases s with
  | absent => rfl
  | holder v => rfl
  | cls ps => rfl
  | member n => rfl
  | exporter a => rw [Task.run_congr (unit (.exporter a)) e e' (fun q hq => h q (trace_exporter a e q hq))]
  | assign b p =>
    simp only [unit, Task.run_ask]
    split <;> split <;> simp [answer]
  | call b => simp [unit, answer]

theorem obligations_comp (r : Rec) : ∀ (G : Finset U) (src : U → Src U) (e : Env U),
    ∀ u ∈ G, (compiler r).group G src e u =
      ((compiler r).unit (src u)).run ((compiler r).override e G ((compiler r).iface ∘ (compiler r).group G src e)) := by
  intro G src e u _
  show (unit (src u)).run (e₂ G src e) = (unit (src u)).run _
  congr 1
  funext p
  obtain ⟨v, q⟩ := p
  simp only [TCompiler.override, compiler, Function.comp, group, e₂]
  split
  · by_cases hq : q = .sig
    · subst hq
      apply sig_stable
      intro p hp
      simp only [e₂, e₁]
      split
      · exact (answer_kind _ _ _ hp).symm
      · rfl
    · rw [answer_kind _ _ _ hq, answer_kind _ _ _ hq]
  · rfl

/-- Every unit a compile asks about is among those its output names or derives. -/
theorem trace_units (s : Src U) (e : Env U) :
    ∀ q ∈ (unit s).trace e, q.1 ∈ ((unit s).run e).named ++ ((unit s).run e).derived := by
  intro q hq
  cases s with
  | absent => simp [unit] at hq
  | holder v => simp [unit] at hq
  | cls ps => simp [unit] at hq
  | member n => simp [unit] at hq
  | exporter a => simp [unit] at hq; subst hq; simp [unit]
  | call b => simp [unit] at hq; subst hq; simp [unit]
  | assign b p =>
    simp only [unit, Task.trace_ask, Task.run_ask, List.mem_cons] at hq ⊢
    rcases hq with rfl | hq
    · split <;> simp
    · revert hq
      split
      · simp
      · simp only [Task.trace_ask, Task.run_ask, Task.trace_pure, Task.run_pure, List.mem_cons,
          List.not_mem_nil, or_false]
        rintro rfl
        simp

/-- **The fix meets the obligations**: #10182's export edge and #87's used types. -/
theorem obligations_fix : (compiler .fix (U := U)).Obligations where
  comp := obligations_comp .fix
  coverage := by
    intro s e q hq
    refine ⟨(q.1, .cls), ?_, rfl, trivial⟩
    have := trace_units s e q hq
    show (q.1, K.cls) ∈ keysOf .fix ((unit s).run e)
    simp only [keysOf, List.mem_toFinset, List.mem_map, Prod.mk.injEq, and_true, exists_eq_right]
    exact this
  abstraction := by
    intro i i' _ h _ _
    simp only [compiler] at h
    rw [h]

theorem fix_sound (S : Finset U) (src : U → Src U) (P : Policy U (Out U) K) (hP : P.Sound S)
    (fuel n : ℕ) (R : Finset U) (s : State U (Out U) K) (D : Finset U) (hD : D ⊆ R)
    (hInv : (compiler .fix).Inv S src s D) (s' : State U (Out U) K)
    (h : (compiler .fix).zinc S src P fuel n R s = some s') :
    (compiler .fix).Inv S src s' ∅ :=
  (compiler .fix).zinc_sound obligations_fix S src P hP fuel n R s D hD hInv s' h

/-- **Export, no edge** (before scala/scala3#10182): `object B { export a.* }` asks `a`'s member's
signature and records nothing on `a`. -/
theorem export_not_coverage : ¬ (compiler .today (U := Fin 3)).Obligations := by
  intro ob
  obtain ⟨k, hk, _, _⟩ := ob.coverage (.exporter 0) (fun p => answer (Iface.member 1) p.2)
    (0, .baseSig) (by simp [compiler, unit])
  simp [compiler, unit, keysOf] at hk

/-- **Used types** (before sbt/zinc#87): `val p: P = B.x` with `B.x : A1` asks `A1`'s parents, and
names only `B` and `P`. -/
theorem usedType_not_coverage : ¬ (compiler .today (U := Fin 3)).Obligations := by
  intro ob
  let ifc : Fin 3 → Iface (Fin 3) := fun u => if u = 0 then .holder 2 else if u = 2 then .cls [1] else .cls []
  obtain ⟨k, hk, h1, _⟩ := ob.coverage (.assign 0 1) (fun p => answer (ifc p.1) p.2)
    (2, .parents) (by simp [compiler, unit, ifc, answer])
  simp [compiler, unit, keysOf, ifc, answer] at hk
  rcases hk with rfl | rfl <;> simp at h1

end Zinc.DerivedApi
