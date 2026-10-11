import Zinc.Tree
import Mathlib.Data.Fintype.Basic

/-!
# Scala 3 `inline` and opaque types as a specification

A `TCompiler` instance (`Tree.lean`: keys are read off the output) over any set of units and any
program of the language below; the shape of `JavaSpec.lean`, and the design of `DESIGN-spec.md`.

**The language.** A unit declares, by name: a member with a signature (`member t`, a primitive
erasure or an opaque type `c.n`), a constant (`final val`/`inline val`), a type alias read at the
type level (`typeAlias`), an `inline` or `transparent inline` def whose body is a list of items, an
opaque type (`opq rhs`), a concrete trait method (`meth t`) that descendants forward. Its code is a
list of items: a literal, a call, a constant through `this` or through a path, an alias read
(`constValue[D.N]`), a signature mentioning a type, an inline call.

**Queries** (to the unit that declares the symbol): `sig n`, `constant n`, `aliasRhs n`,
`inlineBody n`, `erasure n` (the erasure of opaque type `n`, its right-hand side), `meths` (a
trait's inherited signatures).

**The task is dotc's.** An inline call asks `inlineBody` and expands the body in the client, asking
inside it what the inliner reads: `constant` for a constant, `aliasRhs` for a type-level read,
`sig` for a call, `inlineBody` for a nested inline call. Erasing a signature asks `erasure` for an
opaque type. A class emits, for each parent trait's method, a forwarder: `meths`, then `erasure`
for each opaque type in the inherited signature.

**The output** is the interface and the typed tree after inlining: the values emitted, and the
references in it, each marked by where it ended up (`Cat`): the unit's own code; a reference that
survives in a plain expansion (`Inlining` records it); one the inliner folded into a literal (a
constant through a path, a type-level alias read); one inside a transparent expansion (typer
expanded it; its dependency phase records only the call); one read only to erase a forwarder (no
tree has it).

**Keys** (`Design`): today's bridge (Scala 3.9.0) records the references of the first two kinds,
as `(owner, name)`, with an opaque type's right-hand side hashed into the owner (`cls`, its self
type). The fixes are keys: recording folded and transparent references (`inl`), recording the
erased types of a forwarder (`opq`), both (`fix`), and both with the right-hand side in the type's
own name key (`refine`).

**Results.**

* `today` fails coverage, with one witness per family: `I1_today` (a constant through a path),
  `I2_today` (an alias read at the type level), `I3_today` (a transparent expansion), `O1_today`
  (an opaque type in an inherited signature). `inl` still fails `O1` and `opq` still fails `I1`.
  All four are coverage failures: the client issued a query and no recorded key covers it. I1
  reads as an abstraction failure (equal hashes, different answers) only if the inline def's key is
  credited with covering what its body reads; that covering depends on the interface (which body,
  which reads), so it is an `NCompiler` statement: `InlineOpaqueSound.Ex.I1_abstraction`.
* `fix` and `refine` meet the obligations (`obligations_fix`, `obligations_refine`) and inherit
  T3a (`fix_sound`, `refine_sound`). Coverage rests on `faithful`: a query is in the trace exactly
  when its reference is in the output tree.
* Precision: every key a design records covers a query the unit asked (`keys_traced`); a name key
  moves only if an answer it covers changed (`name_exact`); the owner's `cls` key moves on any of
  its opaque types (`cls_coarse`: a client of `O.other` alone), which `refine` avoids.
-/

set_option linter.unusedSectionVars false

namespace Zinc.InlineOpaqueSpec

open Compiler (State Policy)

abbrev Name := ℕ

inductive TyRef (U : Type) | prim (t : ℕ) | opq (c : U) (n : Name)
  deriving DecidableEq, Repr

inductive Item (U : Type)
  | lit (v : ℕ)
  | call (c : U) (n : Name)
  | constThis (c : U) (n : Name)
  | constPath (c : U) (n : Name)
  | aliasRead (c : U) (n : Name)
  | inl (c : U) (n : Name)
  | sig (t : TyRef U)
  deriving DecidableEq, Repr

inductive Def (U : Type)
  | member (t : TyRef U)
  | const (v : ℕ)
  | typeAlias (v : ℕ)
  | inl (trans : Bool) (body : List (Item U))
  | opq (rhs : ℕ)
  | meth (t : TyRef U)
  deriving DecidableEq, Repr

abbrev Iface (U : Type) := List (Name × Def U)

structure Src (U : Type) where
  defs : Iface U := []
  parents : List U := []
  code : List (Item U) := []

inductive Q | sig (n : Name) | constant (n : Name) | aliasRhs (n : Name) | inlineBody (n : Name)
  | erasure (n : Name) | meths
  deriving DecidableEq, Repr

/-- Where a reference ends up in the typed tree after inlining. -/
inductive Cat | code | exp | folded | trans | fwd
  deriving DecidableEq, Repr

inductive Emit (U : Type) | v (n : ℕ) | ref (c : Cat) (u : U) (q : Q)
  deriving DecidableEq, Repr

structure Out (U : Type) where
  iface : Iface U
  tree : List (Emit U)
  deriving DecidableEq, Repr

variable {U : Type}

def Def.isSig : Def U → Bool | .member _ => true | .meth _ => true | _ => false
def Def.isConst : Def U → Bool | .const _ => true | _ => false
def Def.isAlias : Def U → Bool | .typeAlias _ => true | _ => false
def Def.isInl : Def U → Bool | .inl _ _ => true | _ => false
def Def.isOpq : Def U → Bool | .opq _ => true | _ => false
def Def.isMeth : Def U → Bool | .meth _ => true | _ => false

abbrev Ans (_ : Q) : Type := Iface U

/-- An answer is the slice of the interface the query reads. -/
def answer (i : Iface U) : (q : Q) → Ans (U := U) q
  | .sig n => i.filter fun d => d.1 == n && d.2.isSig
  | .constant n => i.filter fun d => d.1 == n && d.2.isConst
  | .aliasRhs n => i.filter fun d => d.1 == n && d.2.isAlias
  | .inlineBody n => i.filter fun d => d.1 == n && d.2.isInl
  | .erasure n => i.filter fun d => d.1 == n && d.2.isOpq
  | .meths => i.filter fun d => d.2.isMeth

def sigOf : Iface U → Option (TyRef U)
  | (_, .member t) :: _ => some t
  | (_, .meth t) :: _ => some t
  | _ => none

def valOf : Iface U → ℕ
  | (_, .const v) :: _ => v
  | (_, .typeAlias v) :: _ => v
  | (_, .opq v) :: _ => v
  | _ => 0

def bodyOf : Iface U → Option (Bool × List (Item U))
  | (_, .inl tr b) :: _ => some (tr, b)
  | _ => none

def methsOf (a : Iface U) : List (TyRef U) :=
  a.filterMap fun d => match d.2 with | .meth t => some t | _ => none

/-! ## The task -/

abbrev T (U : Type) := Task (U × Q) (fun p => Ans (U := U) p.2)
abbrev Env (U : Type) := Task.Env (U × Q) (fun p => Ans (U := U) p.2)

/-- Where an expansion's code is: the unit's own, a plain expansion, a transparent one, a
forwarder's erasure. -/
inductive Ctx | code | exp | trans | fwd
  deriving DecidableEq, Repr

def Ctx.enter : Ctx → Bool → Ctx
  | .code, tr => if tr then .trans else .exp
  | c, _ => c

/-- Where a reference read in context `ctx` ends up; `folds` for what the inliner folds. -/
def Ctx.cat : Ctx → Bool → Cat
  | .code, _ => .code
  | .exp, f => if f then .folded else .exp
  | .trans, _ => .trans
  | .fwd, _ => .fwd

/-- Ask `q` of unit `c`, and mark the reference in the tree. -/
def askR (ctx : Ctx) (folds : Bool) (c : U) (q : Q) (k : Iface U → T U (List (Emit U))) :
    T U (List (Emit U)) :=
  .ask (c, q) fun a => (k a).bind fun es => .pure (.ref (ctx.cat folds) c q :: es)

def seqT : List (T U (List (Emit U))) → T U (List (Emit U))
  | [] => .pure []
  | t :: ts => t.bind fun x => (seqT ts).bind fun xs => .pure (x ++ xs)

def erase (ctx : Ctx) : TyRef U → T U (List (Emit U))
  | .prim t => .pure [.v t]
  | .opq c n => askR ctx false c (.erasure n) fun a => .pure [.v (valOf a)]

def item (rec : Ctx → List (Item U) → T U (List (Emit U))) (ctx : Ctx) : Item U → T U (List (Emit U))
  | .lit v => .pure [.v v]
  | .call c n => askR ctx false c (.sig n) fun a =>
      match sigOf a with
      | some t => erase ctx t
      | none => .pure []
  | .constThis c n => askR ctx false c (.constant n) fun a => .pure [.v (valOf a)]
  | .constPath c n => askR ctx true c (.constant n) fun a => .pure [.v (valOf a)]
  | .aliasRead c n => askR ctx true c (.aliasRhs n) fun a => .pure [.v (valOf a)]
  | .sig t => erase ctx t
  | .inl c n => askR ctx false c (.inlineBody n) fun a =>
      match bodyOf a with
      | some (tr, b) => rec (ctx.enter tr) b
      | none => .pure []

/-- Compile items; an inline call expands its body with one level of nesting less. -/
def expand : ℕ → Ctx → List (Item U) → T U (List (Emit U))
  | 0, ctx, is => seqT (is.map (item (fun _ _ => .pure []) ctx))
  | f + 1, ctx, is => seqT (is.map (item (expand f) ctx))

def ownDescs (ds : Iface U) : T U (List (Emit U)) :=
  seqT (ds.map fun d => match d.2 with
    | .member t => erase .code t
    | .meth t => erase .code t
    | .const v => .pure [.v v]
    | _ => .pure [])

def fwds (ps : List U) : T U (List (Emit U)) :=
  seqT (ps.map fun p => askR .code false p .meths fun a => seqT ((methsOf a).map (erase .fwd)))

variable (depth : ℕ)

def unit (s : Src U) : T U (Out U) :=
  (seqT [expand (depth + 1) .code s.code, ownDescs s.defs, fwds s.parents]).bind fun es =>
    .pure ⟨s.defs, es⟩

theorem iface_unit (s : Src U) (e : Env U) : ((unit depth s).run e).iface = s.defs := by
  simp [unit]

/-! ## The trace is the tree's references -/

/-- A task is faithful if the queries it asks are exactly the references it puts in the tree. -/
def Faithful (e : Env U) (t : T U (List (Emit U))) : Prop :=
  ∀ u q, (u, q) ∈ t.trace e ↔ ∃ c, Emit.ref c u q ∈ t.run e

theorem faithful_vals (e : Env U) (l : List (Emit U)) (hl : ∀ c u q, Emit.ref c u q ∉ l) :
    Faithful e (.pure l) := by
  intro u q; simp [hl]

theorem faithful_askR (e : Env U) (ctx : Ctx) (f : Bool) (c : U) (q : Q)
    (k : Iface U → T U (List (Emit U))) (hk : ∀ a, Faithful e (k a)) :
    Faithful e (askR ctx f c q k) := by
  intro u q'
  have := hk (e (c, q)) u q'
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

theorem faithful_erase (e : Env U) (ctx : Ctx) (t : TyRef U) : Faithful e (erase ctx t) := by
  cases t with
  | prim t => exact faithful_vals e _ (by simp)
  | opq c n => exact faithful_askR e _ _ _ _ _ fun _ => faithful_vals e _ (by simp)

theorem faithful_item (e : Env U) (rec : Ctx → List (Item U) → T U (List (Emit U)))
    (hrec : ∀ ctx b, Faithful e (rec ctx b)) (ctx : Ctx) (it : Item U) :
    Faithful e (item rec ctx it) := by
  cases it with
  | lit v => exact faithful_vals e _ (by simp)
  | call c n =>
    refine faithful_askR e _ _ _ _ _ fun a => ?_
    split
    · exact faithful_erase e _ _
    · exact faithful_vals e _ (by simp)
  | constThis c n => exact faithful_askR e _ _ _ _ _ fun _ => faithful_vals e _ (by simp)
  | constPath c n => exact faithful_askR e _ _ _ _ _ fun _ => faithful_vals e _ (by simp)
  | aliasRead c n => exact faithful_askR e _ _ _ _ _ fun _ => faithful_vals e _ (by simp)
  | sig t => exact faithful_erase e _ _
  | inl c n =>
    refine faithful_askR e _ _ _ _ _ fun a => ?_
    split
    · exact hrec _ _
    · exact faithful_vals e _ (by simp)

theorem faithful_expand (e : Env U) : ∀ f ctx (is : List (Item U)), Faithful e (expand f ctx is)
  | 0, ctx, is => faithful_seqT e _ fun t ht => by
      obtain ⟨it, _, rfl⟩ := List.mem_map.1 ht
      exact faithful_item e _ (fun _ _ => faithful_vals e _ (by simp)) ctx it
  | f + 1, ctx, is => faithful_seqT e _ fun t ht => by
      obtain ⟨it, _, rfl⟩ := List.mem_map.1 ht
      exact faithful_item e _ (faithful_expand e f) ctx it

/-- **The trace is the tree.** A unit's compilation asks exactly the queries whose references are
in its output tree. -/
theorem faithful (e : Env U) (s : Src U) :
    ∀ u q, (u, q) ∈ (unit depth s).trace e ↔ ∃ c, Emit.ref c u q ∈ ((unit depth s).run e).tree := by
  have h : Faithful e (seqT [expand (depth + 1) .code s.code, ownDescs s.defs, fwds s.parents]) := by
    apply faithful_seqT
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro t (rfl | rfl | rfl)
    · exact faithful_expand e _ _ _
    · apply faithful_seqT
      intro t ht
      obtain ⟨d, _, rfl⟩ := List.mem_map.1 ht
      split
      · exact faithful_erase e _ _
      · exact faithful_erase e _ _
      · exact faithful_vals e _ (by simp)
      · exact faithful_vals e _ (by simp)
    · apply faithful_seqT
      intro t ht
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 ht
      exact faithful_askR e _ _ _ _ _ fun a => faithful_seqT e _ fun t ht => by
        obtain ⟨ty, _, rfl⟩ := List.mem_map.1 ht
        exact faithful_erase e _ _
  intro u q
  simp only [unit, Task.trace_bind, Task.trace_pure, List.append_nil, Task.run_bind, Task.run_pure]
  exact h u q

/-! ## Keys -/

inductive K | name (n : Name) | cls
  deriving DecidableEq, Repr

/-- A bridge: which references it records, and where an opaque right-hand side is hashed. -/
structure Design where
  folded : Bool
  trans : Bool
  fwd : Bool
  refine : Bool
  deriving DecidableEq, Repr

def Design.today : Design := ⟨false, false, false, false⟩
def Design.inl : Design := ⟨true, true, false, false⟩
def Design.opq : Design := ⟨false, false, true, false⟩
def Design.fix : Design := ⟨true, true, true, false⟩
def Design.refined : Design := ⟨true, true, true, true⟩

def Design.records (d : Design) : Cat → Bool
  | .code | .exp => true
  | .folded => d.folded
  | .trans => d.trans
  | .fwd => d.fwd

def keyOf (d : Design) : Q → K
  | .sig n | .constant n | .aliasRhs n | .inlineBody n => .name n
  | .erasure n => if d.refine then .name n else .cls
  | .meths => .cls

/-- The keys a design reads off the tree: for each recorded reference, its key, and the owner's own
name (Zinc records the qualifier `O` of `O.m` as a used name, whose hash is the owner's `cls`). -/
def keysOf [DecidableEq U] (d : Design) (o : Out U) : Finset (U × K) :=
  (o.tree.flatMap fun e => match e with
    | .ref c u q => if d.records c then [(u, keyOf d q), (u, .cls)] else []
    | .v _ => []).toFinset

def covers (d : Design) (q : Q) (k : K) : Prop := keyOf d q = k

instance (d : Design) (q : Q) (k : K) : Decidable (covers d q k) := by unfold covers; infer_instance

/-- A name's hash: what each kind of query about the name reads. Today an opaque type's
right-hand side is not in it (the name renders as a type declaration; the right-hand side is in
the owner's self type, `cls`). -/
def π (d : Design) (i : Iface U) : K → List (Iface U)
  | .name n => [answer i (.sig n), answer i (.constant n), answer i (.aliasRhs n),
      answer i (.inlineBody n),
      if d.refine then answer i (.erasure n) else (answer i (.erasure n)).map fun x => (x.1, .opq 0)]
  | .cls => [if d.refine then [] else i.filter fun x => x.2.isOpq, answer i .meths]

def group [DecidableEq U] (G : Finset U) (src : U → Src U) (e : Env U) : U → Out U :=
  fun u => (unit depth (src u)).run fun p => if p.1 ∈ G then answer (src p.1).defs p.2 else e p

def compiler [DecidableEq U] (d : Design) :
    TCompiler U (Src U) (Out U) (Iface U) K (List (Iface U)) Q (Ans (U := U)) where
  unit := unit depth
  group := group depth
  iface := Out.iface
  answer := answer
  π := π d
  keysOf := keysOf d
  covers := covers d

/-! ## Obligations -/

variable [DecidableEq U]

theorem obligations_comp (d : Design) :
    ∀ (G : Finset U) (src : U → Src U) (e : Env U), ∀ u ∈ G,
      (compiler depth d).group G src e u =
        ((compiler depth d).unit (src u)).run
          ((compiler depth d).override e G ((compiler depth d).iface ∘ (compiler depth d).group G src e)) := by
  intro G src e u _
  show (unit depth (src u)).run _ = (unit depth (src u)).run _
  congr 1
  funext p
  simp only [TCompiler.override, compiler, Function.comp]
  split
  · rw [group, iface_unit]
  · rfl

theorem obligations_abstraction (d : Design) :
    ∀ (i i' : Iface U) (k : K), π d i k = π d i' k → ∀ q, covers d q k → answer i q = answer i' q := by
  intro i i' k h q hq
  simp only [covers] at hq
  subst hq
  cases q with
  | sig n =>
    have := congrArg (·[0]?) h
    simpa [π, keyOf] using this
  | constant n =>
    have := congrArg (·[1]?) h
    simpa [π, keyOf] using this
  | aliasRhs n =>
    have := congrArg (·[2]?) h
    simpa [π, keyOf] using this
  | inlineBody n =>
    have := congrArg (·[3]?) h
    simpa [π, keyOf] using this
  | erasure n =>
    cases hr : d.refine
    · have := congrArg (fun l => (l[0]?).map (List.filter fun x => x.1 == n)) h
      simp only [keyOf, hr, π, ite_false, Bool.false_eq_true] at this
      simpa [answer, List.filter_filter, Bool.and_comm] using this
    · have := congrArg (·[4]?) h
      simpa [keyOf, hr, π] using this
  | meths =>
    have := congrArg (·[1]?) h
    simpa [π, keyOf] using this

theorem mem_keysOf (d : Design) (o : Out U) (c : Cat) (u : U) (q : Q) (hr : d.records c = true)
    (h : Emit.ref c u q ∈ o.tree) : (u, keyOf d q) ∈ keysOf d o := by
  simp only [keysOf, List.mem_toFinset, List.mem_flatMap]
  exact ⟨_, h, by simp [hr]⟩

/-- A design that records every kind of reference covers every query. -/
theorem obligations_coverage (d : Design) (hd : ∀ c, d.records c = true) :
    ∀ (s : Src U) (e : Env U), ∀ q ∈ (unit depth s).trace e,
      ∃ k ∈ keysOf d ((unit depth s).run e), q.1 = k.1 ∧ covers d q.2 k.2 := by
  intro s e ⟨u, q⟩ hq
  obtain ⟨c, hc⟩ := (faithful depth e s u q).1 hq
  exact ⟨_, mem_keysOf d _ c u q (hd c) hc, rfl, rfl⟩

theorem fix_records : ∀ c, Design.fix.records c = true := by intro c; cases c <;> rfl
theorem refined_records : ∀ c, Design.refined.records c = true := by intro c; cases c <;> rfl

/-- **The fix meets the obligations**: record folded and transparent references and a forwarder's
erased types, the right-hand side in the owner. -/
theorem obligations_fix : (compiler (U := U) depth .fix).Obligations where
  comp := obligations_comp depth .fix
  coverage := obligations_coverage depth .fix fix_records
  abstraction := obligations_abstraction .fix

/-- The same with the right-hand side in the opaque type's own name key. -/
theorem obligations_refine : (compiler (U := U) depth .refined).Obligations where
  comp := obligations_comp depth .refined
  coverage := obligations_coverage depth .refined refined_records
  abstraction := obligations_abstraction .refined

/-- **T3a for the fix.** When Zinc's loop stops, every unit is up to date, for any program, edit and
sound policy. -/
theorem fix_sound (S : Finset U) (src : U → Src U) (P : Policy U (Out U) K) (hP : P.Sound S)
    (fuel n : ℕ) (R : Finset U) (s : State U (Out U) K) (D : Finset U) (hD : D ⊆ R)
    (hInv : (compiler depth .fix).Inv S src s D) (s' : State U (Out U) K)
    (h : (compiler depth .fix).zinc S src P fuel n R s = some s') :
    (compiler depth .fix).Inv S src s' ∅ :=
  (compiler depth .fix).zinc_sound (obligations_fix depth) S src P hP fuel n R s D hD hInv s' h

theorem refine_sound (S : Finset U) (src : U → Src U) (P : Policy U (Out U) K) (hP : P.Sound S)
    (fuel n : ℕ) (R : Finset U) (s : State U (Out U) K) (D : Finset U) (hD : D ⊆ R)
    (hInv : (compiler depth .refined).Inv S src s D) (s' : State U (Out U) K)
    (h : (compiler depth .refined).zinc S src P fuel n R s = some s') :
    (compiler depth .refined).Inv S src s' ∅ :=
  (compiler depth .refined).zinc_sound (obligations_refine depth) S src P hP fuel n R s D hD hInv s' h

/-! ## Precision -/

/-- **No name key without a read.** Every name key a design records covers a query the unit
asked. (The owner's `cls` key is recorded with every reference through it, read or not: its
over-approximation, `cls_coarse`.) -/
theorem keys_traced (d : Design) (s : Src U) (e : Env U) (u : U) (n : Name) :
    (u, K.name n) ∈ keysOf d ((unit depth s).run e) →
      ∃ q ∈ (unit depth s).trace e, q.1 = u ∧ covers d q.2 (.name n) := by
  intro hk
  simp only [keysOf, List.mem_toFinset, List.mem_flatMap] at hk
  obtain ⟨x, hx, hk⟩ := hk
  cases x with
  | v _ => simp at hk
  | ref c u' q =>
    simp only at hk
    split at hk
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
      rcases hk with ⟨hu, hq⟩ | ⟨_, h⟩
      · subst hu
        exact ⟨(u, q), (faithful depth e s u q).2 ⟨c, hx⟩, rfl, hq.symm⟩
      · cases h
    · simp at hk

/-- **A name key is exact.** It moves only if an answer it covers changed: today for a name that
is not an opaque type (whose right-hand side is hashed into the owner instead), with `refine` for
every name. -/
theorem name_exact (d : Design) (i i' : Iface U) (n : Name)
    (hno : d.refine = false → answer i (.erasure n) = [] ∧ answer i' (.erasure n) = [])
    (h : ∀ q, covers d q (.name n) → answer i q = answer i' q) : π d i (.name n) = π d i' (.name n) := by
  have hs := h (.sig n) rfl
  have hc := h (.constant n) rfl
  have ha := h (.aliasRhs n) rfl
  have hb := h (.inlineBody n) rfl
  simp only [π, hs, hc, ha, hb]
  cases hr : d.refine
  · obtain ⟨h1, h2⟩ := hno hr
    simp [h1, h2]
  · simp only [ite_true]
    rw [h (.erasure n) (by simp [covers, keyOf, hr])]

end Zinc.InlineOpaqueSpec

/-! ## Families and precision, as witnesses -/

namespace Zinc.InlineOpaqueSpec.Ex

open Zinc.InlineOpaqueSpec

inductive Cls | L | D | O | Tr | K | Client
  deriving DecidableEq, Repr

open Cls

def envI (I : Cls → Iface Cls) : Env Cls := fun p => answer (I p.1) p.2

def client : Src Cls := { code := [.inl L 1] }

/-- `inline def inl = D.K` (`K` is name 0, `inl` name 1). -/
def ifI1 : Cls → Iface Cls
  | L => [(1, .inl false [.constPath D 0])]
  | D => [(0, .const 1)]
  | _ => []

/-- **I1.** The client asks `D` for the constant `K`; the inliner folded it, so no recorded key
covers the query (a coverage failure). -/
theorem I1_today : ¬ (compiler (U := Cls) 1 .today).Obligations := by
  intro ob
  have := ob.coverage client (envI ifI1) (D, .constant 0) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- `inline def inl = constValue[D.N]` (`N` is name 7). -/
def ifI2 : Cls → Iface Cls
  | L => [(1, .inl false [.aliasRead D 7])]
  | D => [(7, .typeAlias 1)]
  | _ => []

/-- **I2.** The client asks `D` for the alias `N`'s right-hand side, read at the type level and
folded: no recorded key covers it. -/
theorem I2_today : ¬ (compiler (U := Cls) 1 .today).Obligations := by
  intro ob
  have := ob.coverage client (envI ifI2) (D, .aliasRhs 7) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- `transparent inline def inl = h` with `def h: Int` (name 2). -/
def ifI3 : Cls → Iface Cls
  | L => [(2, .member (.prim 0)), (1, .inl true [.call L 2])]
  | _ => []

/-- **I3.** Inside the transparent expansion the client asks `L` for `h`'s signature; typer's
dependency phase recorded only the call of `inl`. -/
theorem I3_today : ¬ (compiler (U := Cls) 1 .today).Obligations := by
  intro ob
  have := ob.coverage client (envI ifI3) (L, .sig 2) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- `opaque type T` (name 4) in `O`, `Tr.h(t: O.T)` (name 6), `class K extends Tr`. -/
def ifO1 : Cls → Iface Cls
  | O => [(4, .opq 0)]
  | Tr => [(6, .meth (.opq O 4))]
  | _ => []

def k : Src Cls := { parents := [Tr] }

/-- **O1.** Erasing the inherited `h` for its forwarder, `K` asks `O` for `T`'s erasure; no tree has
the reference, so no key covers it. -/
theorem O1_today : ¬ (compiler (U := Cls) 1 .today).Obligations := by
  intro ob
  have := ob.coverage k (envI ifO1) (O, .erasure 4) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- Each key fixes its own family only: recording folded and transparent references leaves `O1`. -/
theorem O1_inl : ¬ (compiler (U := Cls) 1 .inl).Obligations := by
  intro ob
  have := ob.coverage k (envI ifO1) (O, .erasure 4) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- ... and recording a forwarder's erased types leaves `I1`. -/
theorem I1_opq : ¬ (compiler (U := Cls) 1 .opq).Obligations := by
  intro ob
  have := ob.coverage client (envI ifI1) (D, .constant 0) (by decide)
  simp only [compiler] at this
  revert this; decide

/-- `O.other` (name 5) beside `opaque type T = rhs`. -/
def ifOther (rhs : ℕ) : Cls → Iface Cls
  | O => [(4, .opq rhs), (5, .member (.prim 0))]
  | _ => []

def otherClient : Src Cls := { code := [.call O 5] }

/-- **`cls` is coarse.** A client that calls only `O.other` asks the same answers whatever `T`'s
right-hand side, yet a key it records (`O`'s own name) moves under the fix: Zinc recompiles it for
nothing. With `refine`, no key it records moves. -/
theorem cls_coarse :
    (∀ q ∈ (unit 1 otherClient).trace (envI (ifOther 0)), envI (ifOther 0) q = envI (ifOther 1) q) ∧
    (∃ p ∈ keysOf .fix ((unit 1 otherClient).run (envI (ifOther 0))),
      π .fix (ifOther 0 p.1) p.2 ≠ π .fix (ifOther 1 p.1) p.2) ∧
    (∀ p ∈ keysOf .refined ((unit 1 otherClient).run (envI (ifOther 0))),
      π .refined (ifOther 0 p.1) p.2 = π .refined (ifOther 1 p.1) p.2) := by
  decide

end Zinc.InlineOpaqueSpec.Ex
