import Zinc.Tree
import Mathlib.Data.Fintype.Basic

/-!
# Scala 3 macro dependencies as a specification

A `TCompiler` instance (`Tree.lean`) on the shape of `InlineOpaqueSpec.lean`, for what a macro
expansion reads and when dotc records it (`PLAN-macros.md`).

**The language.** Units (with a static project assignment `proj`) declare public members (a
signature), macro defs (`macroDef impl f`: an inline def whose body splices `impl.f`),
implementations (`impl code`: what the implementation generates), macro annotations (`annot code`:
the annotation class with its `transform`), and private members. A client's code calls a macro,
with an optional type argument, or applies an annotation.

**The task is dotc's.** A macro call asks `macroBody` of the macro's owner, then `implCode` of the
implementation (its behaviour: bytecode, run by the compiler); running it, the expansion's generated
code asks `sig` of each class it references, and the implementation's reads of the type argument
ask `reflect` (members, private ones included). An annotation asks `implCode` of its `transform`.

**Keys.** `name n` (Zinc's name hash: a signature, a macro def's body, an implementation's
signature but not its code), `api` (`DependencyByMacroExpansion`: the public API), `bytecode` (the
transitive bytecode hash: the unit's whole interface). Designs: `pre23900`, `pre24969`, `today`
(3.9 with Zinc `develop`), `earlyAnalysis` (the analysis written before `Inlining` sends the dependencies,
scala/scala3#27125), `fix`.

**Results.** Witnesses (kernel `decide`), each a failed obligation of the design that has the bug:
`gen_pre24969` (scala/scala3#23852, coverage), `targ_pre23900` (coverage), `private_today`
(abstraction: the `api` hash misses a private member the macro reflects), `annot_today`
(scala/scala3#22999, coverage), `crossProject_today` (sbt/zinc#1478, coverage), `early_violates`
(scala/scala3#27125, coverage of the analysis handed on). `fix` meets the obligations
(`obligations_fix`) and so T3a (`fix_sound`). Cost: `bytecode_coarse` and `private_coarse`.
-/

set_option linter.unusedSectionVars false

namespace Zinc.MacroDeps

open Compiler (State Policy)

abbrev Name := ℕ

/-- What an implementation generates: a literal, a reference to a member, or a read of the type
argument. -/
inductive Gen (U : Type) | lit (v : ℕ) | ref (c : U) (n : Name) | targ
  deriving DecidableEq, Repr

inductive Def (U : Type)
  | member (t : ℕ)
  | macroDef (impl : U) (f : Name)
  | impl (code : List (Gen U))
  | annot (code : List (Gen U))
  deriving DecidableEq, Repr

structure Iface (U : Type) where
  pub : List (Name × Def U) := []
  priv : List (Name × ℕ) := []
  deriving DecidableEq, Repr

inductive Item (U : Type)
  | call (m : U) (n : Name) (targ : Option U)
  | annotated (a : U)
  deriving DecidableEq, Repr

structure Src (U : Type) where
  iface : Iface U := {}
  code : List (Item U) := []

inductive Q | sig (n : Name) | macroBody (n : Name) | implCode (n : Name) | reflect
  deriving DecidableEq, Repr

/-- Where a reference ends up: the client's own code (typer); an implementation read for a macro,
`internal` if it is in the macro's project; an annotation's implementation; a reference in the
generated code; a read of the type argument. -/
inductive Cat | code | impl (internal : Bool) | annot | gen | targ
  deriving DecidableEq, Repr

inductive Emit (U : Type) | v (n : ℕ) | ref (c : Cat) (u : U) (q : Q)
  deriving DecidableEq, Repr

structure Out (U : Type) where
  iface : Iface U
  tree : List (Emit U)
  deriving DecidableEq, Repr

variable {U : Type}

def Def.isMember : Def U → Bool | .member _ => true | _ => false
def Def.isMacro : Def U → Bool | .macroDef _ _ => true | _ => false
def Def.isCode : Def U → Bool | .impl _ => true | .annot _ => true | _ => false

/-- Answers are slices of the interface. `implCode` reads an implementation's code; `reflect`
reads every member, private ones included. -/
def answer (i : Iface U) : Q → Iface U
  | .sig n => ⟨i.pub.filter fun d => d.1 == n && d.2.isMember, []⟩
  | .macroBody n => ⟨i.pub.filter fun d => d.1 == n && d.2.isMacro, []⟩
  | .implCode n => ⟨i.pub.filter fun d => d.1 == n && d.2.isCode, []⟩
  | .reflect => ⟨i.pub.filter fun d => d.2.isMember, i.priv⟩

abbrev Ans (_ : Q) : Type := Iface U

def macroOf (a : Iface U) : Option (U × Name) :=
  match a.pub with
  | (_, .macroDef c f) :: _ => some (c, f)
  | _ => none

def codeOf (a : Iface U) : List (Gen U) :=
  match a.pub with
  | (_, .impl code) :: _ => code
  | (_, .annot code) :: _ => code
  | _ => []

def sigOf (a : Iface U) : ℕ :=
  match a.pub with
  | (_, .member t) :: _ => t
  | _ => 0

def shape (a : Iface U) : List ℕ := a.pub.map (fun d => match d.2 with | .member t => t | _ => 0) ++ a.priv.map (·.2)

/-! ## The task -/

abbrev T (U : Type) := Task (U × Q) (fun p => Ans (U := U) p.2)
abbrev Env (U : Type) := Task.Env (U × Q) (fun p => Ans (U := U) p.2)

def askR (c : Cat) (u : U) (q : Q) (k : Iface U → T U (List (Emit U))) : T U (List (Emit U)) :=
  .ask (u, q) fun a => (k a).bind fun es => .pure (.ref c u q :: es)

def seqT : List (T U (List (Emit U))) → T U (List (Emit U))
  | [] => .pure []
  | t :: ts => t.bind fun x => (seqT ts).bind fun xs => .pure (x ++ xs)

/-- Run an implementation's code: the generated references and the type argument reads. -/
def gen (targ : Option U) : Gen U → T U (List (Emit U))
  | .lit v => .pure [.v v]
  | .ref c n => askR .gen c (.sig n) fun a => .pure [.v (sigOf a)]
  | .targ => match targ with
    | some t => askR .targ t .reflect fun a => .pure ((shape a).map .v)
    | none => .pure []

variable (proj : U → ℕ)

def item : Item U → T U (List (Emit U))
  | .call m n targ => askR .code m (.macroBody n) fun a =>
      match macroOf a with
      | some (c, f) => askR (.impl (proj c == proj m)) c (.implCode f) fun b =>
          seqT ((codeOf b).map (gen targ))
      | none => .pure []
  | .annotated a => askR .annot a (.implCode 0) fun b => seqT ((codeOf b).map (gen none))

def unit (s : Src U) : T U (Out U) :=
  (seqT (s.code.map (item proj))).bind fun es => .pure ⟨s.iface, es⟩

theorem iface_unit (s : Src U) (e : Env U) : ((unit proj s).run e).iface = s.iface := by
  simp [unit]

/-! ## The trace is the tree -/

def Faithful (e : Env U) (t : T U (List (Emit U))) : Prop :=
  ∀ u q, (u, q) ∈ t.trace e ↔ ∃ c, Emit.ref c u q ∈ t.run e

theorem faithful_vals (e : Env U) (l : List (Emit U)) (hl : ∀ c u q, Emit.ref c u q ∉ l) :
    Faithful e (.pure l) := by
  intro u q; simp [hl]

theorem faithful_askR (e : Env U) (c : Cat) (u : U) (q : Q)
    (k : Iface U → T U (List (Emit U))) (hk : ∀ a, Faithful e (k a)) :
    Faithful e (askR c u q k) := by
  intro u' q'
  have := hk (e (u, q)) u' q'
  simp only [askR, Task.trace_ask, Task.trace_bind, Task.trace_pure, List.append_nil,
    Task.run_ask, Task.run_bind, Task.run_pure, List.mem_cons, Prod.mk.injEq, Emit.ref.injEq]
  constructor
  · rintro (⟨rfl, rfl⟩ | h)
    · exact ⟨_, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · obtain ⟨c', hc'⟩ := this.1 h; exact ⟨c', Or.inr hc'⟩
  · rintro ⟨c', ⟨_, rfl, rfl⟩ | h⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (this.2 ⟨c', h⟩)

theorem run_seqT (e : Env U) (ts : List (T U (List (Emit U)))) :
    (seqT ts).run e = ts.flatMap fun t => t.run e := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [seqT, Task.run_bind, ih]

theorem trace_seqT (e : Env U) (ts : List (T U (List (Emit U)))) :
    (seqT ts).trace e = ts.flatMap fun t => t.trace e := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [seqT, Task.trace_bind, ih]

theorem faithful_seqT (e : Env U) (ts : List (T U (List (Emit U)))) (h : ∀ t ∈ ts, Faithful e t) :
    Faithful e (seqT ts) := by
  intro u q
  simp only [run_seqT, trace_seqT, List.mem_flatMap]
  constructor
  · rintro ⟨t, ht, hq⟩
    obtain ⟨c, hc⟩ := (h t ht u q).1 hq
    exact ⟨c, t, ht, hc⟩
  · rintro ⟨c, t, ht, hc⟩
    exact ⟨t, ht, (h t ht u q).2 ⟨c, hc⟩⟩

theorem faithful_gen (e : Env U) (targ : Option U) (g : Gen U) : Faithful e (gen targ g) := by
  cases g with
  | lit v => exact faithful_vals e _ (by simp)
  | ref c n => exact faithful_askR e _ _ _ _ fun _ => faithful_vals e _ (by simp)
  | targ =>
    cases targ with
    | none => exact faithful_vals e _ (by simp)
    | some t => exact faithful_askR e _ _ _ _ fun _ => faithful_vals e _ (by simp)

theorem faithful_codes (e : Env U) (targ : Option U) (b : Iface U) :
    Faithful e (seqT ((codeOf b).map (gen targ))) :=
  faithful_seqT e _ fun t ht => by
    obtain ⟨g, _, rfl⟩ := List.mem_map.1 ht
    exact faithful_gen e targ g

theorem faithful_item (e : Env U) (it : Item U) : Faithful e (item proj it) := by
  cases it with
  | call m n targ =>
    refine faithful_askR e _ _ _ _ fun a => ?_
    split
    · exact faithful_askR e _ _ _ _ fun b => faithful_codes e targ b
    · exact faithful_vals e _ (by simp)
  | annotated a => exact faithful_askR e _ _ _ _ fun b => faithful_codes e none b

theorem faithful (e : Env U) (s : Src U) :
    ∀ u q, (u, q) ∈ (unit proj s).trace e ↔ ∃ c, Emit.ref c u q ∈ ((unit proj s).run e).tree := by
  have h : Faithful e (seqT (s.code.map (item proj))) :=
    faithful_seqT e _ fun t ht => by
      obtain ⟨it, _, rfl⟩ := List.mem_map.1 ht
      exact faithful_item proj e it
  intro u q
  simp only [unit, Task.trace_bind, Task.trace_pure, List.append_nil, Task.run_bind, Task.run_pure]
  exact h u q

/-! ## Keys -/

inductive K | name (n : Name) | api | bytecode
  deriving DecidableEq, Repr

def keyOf : Q → K
  | .sig n | .macroBody n => .name n
  | .implCode _ => .bytecode
  | .reflect => .api

/-- A bridge with Zinc's rules: which references it records, and what the `api` hash holds. -/
structure Design where
  /-- Generated references recorded (scala/scala3#24969). -/
  gen : Bool
  /-- Type arguments recorded as `DependencyByMacroExpansion` (scala/scala3#23900). -/
  targ : Bool
  /-- The `api` hash includes private members. -/
  priv : Bool
  /-- An implementation in another project is tracked (sbt/zinc#1478). -/
  cross : Bool
  /-- A macro annotation's `transform` is tracked (scala/scala3#22999). -/
  annot : Bool
  /-- The analysis is written before the dependencies are sent (scala/scala3#27125). -/
  early : Bool
  deriving DecidableEq, Repr

def Design.pre23900 : Design := ⟨false, false, false, false, false, false⟩
def Design.pre24969 : Design := ⟨false, true, false, false, false, false⟩
def Design.today : Design := ⟨true, true, false, false, false, false⟩
def Design.earlyAnalysis : Design := ⟨true, true, false, false, false, true⟩
def Design.fix : Design := ⟨true, true, true, true, true, false⟩

def Design.records (d : Design) : Cat → Bool
  | .code => !d.early
  | .impl internal => !d.early && (internal || d.cross)
  | .annot => !d.early && d.annot
  | .gen => !d.early && d.gen
  | .targ => !d.early && d.targ

def keysOf [DecidableEq U] (d : Design) (o : Out U) : Finset (U × K) :=
  (o.tree.filterMap fun e => match e with
    | .ref c u q => if d.records c then some (u, keyOf q) else none
    | .v _ => none).toFinset

def covers (q : Q) (k : K) : Prop := keyOf q = k

instance (q : Q) (k : K) : Decidable (covers q k) := by unfold covers; infer_instance

/-- An implementation's name hash is its signature, not its code. -/
def render : Def U → Def U
  | .impl _ => .impl []
  | .annot _ => .annot []
  | d => d

def π (d : Design) (i : Iface U) : K → Iface U
  | .name n => ⟨(i.pub.filter fun x => x.1 == n).map fun x => (x.1, render x.2), []⟩
  | .api => ⟨(i.pub.map fun x => (x.1, render x.2)), if d.priv then i.priv else []⟩
  | .bytecode => i

def group [DecidableEq U] (G : Finset U) (src : U → Src U) (e : Env U) : U → Out U :=
  fun u => (unit proj (src u)).run fun p => if p.1 ∈ G then answer (src p.1).iface p.2 else e p

def compiler [DecidableEq U] (d : Design) :
    TCompiler U (Src U) (Out U) (Iface U) K (Iface U) Q (Ans (U := U)) where
  unit := unit proj
  group := group proj
  iface := Out.iface
  answer := answer
  π := π d
  keysOf := keysOf d
  covers := covers

/-! ## Obligations of the fix -/

variable [DecidableEq U]

theorem obligations_comp (d : Design) :
    ∀ (G : Finset U) (src : U → Src U) (e : Env U), ∀ u ∈ G,
      (compiler proj d).group G src e u =
        ((compiler proj d).unit (src u)).run
          ((compiler proj d).override e G ((compiler proj d).iface ∘ (compiler proj d).group G src e)) := by
  intro G src e u _
  show (unit proj (src u)).run _ = (unit proj (src u)).run _
  congr 1
  funext p
  simp only [TCompiler.override, compiler, Function.comp]
  split
  · rw [group, iface_unit]
  · rfl

theorem filter_member (l : List (Name × Def U)) :
    ((l.map fun x => (x.1, render x.2)).filter fun y => y.2.isMember) = l.filter fun y => y.2.isMember := by
  induction l with
  | nil => rfl
  | cons x xs ih => obtain ⟨a, b⟩ := x; cases b <;> simp_all [render, Def.isMember]

theorem filter_macro (l : List (Name × Def U)) :
    ((l.map fun x => (x.1, render x.2)).filter fun y => y.2.isMacro) = l.filter fun y => y.2.isMacro := by
  induction l with
  | nil => rfl
  | cons x xs ih => obtain ⟨a, b⟩ := x; cases b <;> simp_all [render, Def.isMacro]

/-- Abstraction holds when the `api` hash includes private members. -/
theorem obligations_abstraction (d : Design) (hd : d.priv = true) :
    ∀ (i i' : Iface U) (k : K), π d i k = π d i' k → ∀ q, covers q k → answer i q = answer i' q := by
  intro i i' k h q hq
  simp only [covers] at hq
  subst hq
  cases q with
  | sig n =>
    have := congrArg (fun x : Iface U => x.pub.filter fun y => y.2.isMember) h
    simp only [keyOf, π, filter_member, List.filter_filter] at this
    simp only [answer]; congr 1; simpa [Bool.and_comm] using this
  | macroBody n =>
    have := congrArg (fun x : Iface U => x.pub.filter fun y => y.2.isMacro) h
    simp only [keyOf, π, filter_macro, List.filter_filter] at this
    simp only [answer]; congr 1; simpa [Bool.and_comm] using this
  | implCode n => simp only [keyOf, π] at h; rw [h]
  | reflect =>
    have hp := congrArg (fun x : Iface U => x.pub.filter fun y => y.2.isMember) h
    have hv := congrArg Iface.priv h
    simp only [keyOf, π, filter_member] at hp
    simp only [keyOf, π, hd, ite_true] at hv
    simp only [answer, hp, hv]

theorem mem_keysOf (d : Design) (o : Out U) (c : Cat) (u : U) (q : Q) (hr : d.records c = true)
    (h : Emit.ref c u q ∈ o.tree) : (u, keyOf q) ∈ keysOf d o := by
  simp only [keysOf, List.mem_toFinset, List.mem_filterMap]
  exact ⟨_, h, by simp [hr]⟩

theorem fix_records : ∀ c, Design.fix.records c = true := by
  intro c; cases c <;> simp [Design.records, Design.fix]

theorem obligations_coverage :
    ∀ (s : Src U) (e : Env U), ∀ q ∈ (unit proj s).trace e,
      ∃ k ∈ keysOf .fix ((unit proj s).run e), q.1 = k.1 ∧ covers q.2 k.2 := by
  intro s e ⟨u, q⟩ hq
  obtain ⟨c, hc⟩ := (faithful proj e s u q).1 hq
  exact ⟨_, mem_keysOf .fix _ c u q (fix_records c) hc, rfl, rfl⟩

/-- **The fix meets the obligations**: generated references and type arguments recorded, private
members in the `api` hash, implementations tracked across projects and for annotations, and the
analysis written after the dependencies are sent. -/
theorem obligations_fix : (compiler (U := U) proj .fix).Obligations where
  comp := obligations_comp proj .fix
  coverage := obligations_coverage proj
  abstraction := obligations_abstraction .fix rfl

/-- **T3a for the fix**, for any program, edit, project assignment and sound policy. -/
theorem fix_sound (S : Finset U) (src : U → Src U) (P : Policy U (Out U) K) (hP : P.Sound S)
    (fuel n : ℕ) (R : Finset U) (s : State U (Out U) K) (D : Finset U) (hD : D ⊆ R)
    (hInv : (compiler proj .fix).Inv S src s D) (s' : State U (Out U) K)
    (h : (compiler proj .fix).zinc S src P fuel n R s = some s') :
    (compiler proj .fix).Inv S src s' ∅ :=
  (compiler proj .fix).zinc_sound (obligations_fix proj) S src P hP fuel n R s D hD hInv s' h

end Zinc.MacroDeps

/-! ## Witnesses -/

namespace Zinc.MacroDeps.Ex

open Zinc.MacroDeps

/-- `M` owns the macro `m` (name 1); `I` the implementation `f` (name 2); `D` a class the generated
code references (`d`, name 3); `Tp` a type argument; `A` a macro annotation. -/
inductive Cls | M | I | D | Tp | A | Client
  deriving DecidableEq, Repr

open Cls

def envI (I' : Cls → Iface Cls) : Env Cls := fun p => answer (I' p.1) p.2

/-- One project; and a split one, the implementation upstream of everything else. -/
def one : Cls → ℕ := fun _ => 0
def split : Cls → ℕ | I => 1 | _ => 0

def prog (code : List (Gen Cls)) (priv : List (Name × ℕ) := []) : Cls → Iface Cls
  | M => { pub := [(1, .macroDef I 2)] }
  | I => { pub := [(2, .impl code)] }
  | D => { pub := [(3, .member 0)] }
  | Tp => { pub := [(4, .member 0)], priv := priv }
  | A => { pub := [(0, .annot [.lit 1])] }
  | Client => {}

def client (targ : Option Cls := none) : Src Cls := { code := [.call M 1 targ] }

/-- **scala/scala3#23852** (≤ 3.8.2): the generated code calls `D.d`; no recorded key covers the
`sig` query, since dependencies were collected before the expansion existed. -/
theorem gen_pre24969 : ¬ (compiler (U := Cls) one .pre24969).Obligations := by
  intro ob
  have := ob.coverage (client) (envI (prog [.ref D 3])) (D, .sig 3) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- Before scala/scala3#23900: the implementation reads the type argument `Tp`; nothing records it. -/
theorem targ_pre23900 : ¬ (compiler (U := Cls) one .pre23900).Obligations := by
  intro ob
  have := ob.coverage (client (some Tp)) (envI (prog [.targ])) (Tp, .reflect) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- **A private member the macro reflects** (today): the `api` key covers `reflect`, but its hash
has public members only, so an edit to a private member keeps the hash and changes the answer:
an abstraction failure. -/
theorem private_today : ¬ (compiler (U := Cls) one .today).Obligations := by
  intro ob
  have := ob.abstraction (prog [.targ] [(5, 0)] Tp) (prog [.targ] [(5, 1)] Tp) .api
    (by simp only [compiler]; decide) .reflect rfl
  simp only [compiler] at this
  revert this; decide

/-- **scala/scala3#22999**: a macro annotation's `transform` is read, and nothing records it. -/
theorem annot_today : ¬ (compiler (U := Cls) one .today).Obligations := by
  intro ob
  have := ob.coverage { code := [.annotated A] } (envI (prog [])) (A, .implCode 0) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- **sbt/zinc#1478**: the implementation lives in another project; the transitive bytecode hash
of the macro's owner covers its own project only. -/
theorem crossProject_today : ¬ (compiler (U := Cls) split .today).Obligations := by
  intro ob
  have := ob.coverage (client) (envI (prog [.lit 1])) (I, .implCode 2) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- Today (after scala/scala3#24969 and #23900) the generated reference and the type argument read
are covered. -/
example : ∃ k ∈ keysOf .today ((unit one (client)).run (envI (prog [.ref D 3]))),
    (D, Q.sig 3).1 = k.1 ∧ covers (Q.sig 3) k.2 := by decide

example : ∃ k ∈ keysOf .today ((unit one (client (some Tp))).run (envI (prog [.targ]))),
    (Tp, Q.reflect).1 = k.1 ∧ covers Q.reflect k.2 := by decide

/-- In one project the same read is covered (sbt/zinc#1282). -/
example : ∃ k ∈ keysOf .today ((unit one (client)).run (envI (prog [.lit 1]))),
    (I, Q.implCode 2).1 = k.1 ∧ covers (Q.implCode 2) k.2 := by decide

/-- **scala/scala3#27125**: the analysis written before `Inlining` sends the dependencies has no
key, so even the call itself is uncovered in what Zinc hands on. -/
theorem early_violates : ¬ (compiler (U := Cls) one .earlyAnalysis).Obligations := by
  intro ob
  have := ob.coverage (client) (envI (prog [.lit 1])) (M, .macroBody 1) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- **The bytecode key is coarse.** An edit to an implementation the client's macro does not call
(another method of `I`) moves `I`'s bytecode key, which the client records: Zinc recompiles the
call site for nothing (sbt/zinc#1282's choice, #1333). -/
theorem bytecode_coarse :
    let i₀ : Iface Cls := { pub := [(2, .impl [.lit 1]), (7, .impl [.lit 1])] }
    let i₁ : Iface Cls := { pub := [(2, .impl [.lit 1]), (7, .impl [.lit 2])] }
    answer i₀ (.implCode 2) = answer i₁ (.implCode 2) ∧ π .fix i₀ .bytecode ≠ π .fix i₁ .bytecode := by
  decide

/-- **Private members in the `api` hash cost.** A private edit the macro does not read (the
implementation never reflects) still moves `Tp`'s `api` key. -/
theorem private_coarse :
    π .fix (prog [] [(5, 0)] Tp) .api ≠ π .fix (prog [] [(5, 1)] Tp) .api := by decide

end Zinc.MacroDeps.Ex
