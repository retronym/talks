import Zinc.Uniqueness
import Zinc.Termination

/-!
# Inferred types in a cycle: T3a holds, T3 fails

`Uniqueness.lean` proves that a per-unit fixed point is the clean build when traced dependencies
are acyclic (`fixpoint_unique_of_wf`) or interfaces are explicit (`fixpoint_unique_of_explicit`).
Here is the case that has neither. Two members infer their types from each other:

```scala
object A { def x = B.y }      // was: def x: Int = B.y
object B { def y = A.x }
```

A clean build compiles both together and reports the cycle ("recursive method x needs result
type"). An incremental build that recompiles `A` alone reads `B.y : Int` from `B`'s classfile,
infers `x : Int`, sees no API change, and stops: it succeeds where the clean build fails. Nothing is
stale. Both outcomes are per-unit fixed points of separate compilation (`two_fixpoints`); joint
compilation picks the least one (no type: the error), and Zinc's loop, whose result is always a
per-unit fixed point (T3a), stays at the one it started from.

**The instance.** Units `a`, `b`; a unit's interface is its member's type, `none` for an error.
Source `ann t r`: `def x: t = r.y`, which type-checks iff `r.y : t`. Source `inf r`: `def x = r.y`,
whose type is `r.y`'s. Joint compilation follows the reads inside the round and gives `none` to a
cycle of inferred members (scalac's cyclic-reference error); a member annotated anywhere on the
cycle fixes the type for the rest. The compiler meets the obligations (`obligations`).

**Results.**

* `zinc_stops_at_old`, `clean_fails`, `zinc_ne_clean`: from the clean build of the annotated
  version, removing the annotation, Zinc's loop recompiles `A` and stops with both types `Int`;
  the clean build of the same sources has both in error.
* `two_fixpoints`: both are per-unit fixed points of the edited sources.
* `annotated_eq_clean`: with every member annotated, Zinc's result is the clean build, for every
  program, edit and sound policy (T3 from `zinc_eq_clean_of_explicit`).

**Pragmatics.** No key fixes this: Zinc's keys are sound (the obligations hold and the incremental
state is a fixed point); what differs is *which* fixed point, and that is decided by what is
compiled jointly. The remedies are joint recompilation of the cycle (a round that holds every
member of the cycle whenever one of them changes from annotated to inferred, which is what
`transitiveStep`'s brute-force round does eventually, see `PingPong.lean`), or annotations. The
cheap rule for Zinc: when a recompiled member's type became inferred and its traced reads reach
back to it, recompile the cycle jointly; it fires only on an edit that removes an annotation in a
cycle.
-/

namespace Zinc.Cycles

open Compiler (State Policy)

inductive U | a | b
  deriving DecidableEq, Repr

instance : Fintype U := ⟨{.a, .b}, by intro x; cases x <;> decide⟩

inductive Ty | int | long
  deriving DecidableEq, Repr

inductive Q | ty
  deriving DecidableEq, Repr

abbrev Ans (_ : Q) : Type := Option Ty

inductive K | ty
  deriving DecidableEq, Repr

inductive Src
  /-- `def x: t = r.y` -/
  | ann (t : Ty) (r : U)
  /-- `def x = r.y` -/
  | inf (r : U)
  deriving DecidableEq, Repr

def Src.reads : Src → U
  | .ann _ r => r
  | .inf r => r

structure Out where
  ty : Option Ty
  ok : Bool
  deriving DecidableEq, Repr

abbrev Env := Task.Env (U × Q) (fun p => Ans p.2)

/-- `v` conforms to `t`: equal, or Scala's numeric widening `Int` to `Long`. -/
def conforms (v : Option Ty) (t : Ty) : Bool := v == some t || (v == some .int && t == .long)

def unit : Src → Task (U × Q) (fun p => Ans p.2) Out
  | .ann t r => .ask (r, .ty) fun v => .pure ⟨some t, conforms v t⟩
  | .inf r => .ask (r, .ty) fun v => .pure ⟨v, v.isSome⟩

/-- The types of a round's members: follow the reads inside the round from the types outside it; a
cycle of inferred members inside the round has none. -/
def jt (G : Finset U) (src : U → Src) (ext : U → Option Ty) : ℕ → U → Option Ty
  | 0, u => match src u with
    | .ann t _ => some t
    | .inf r => if r ∈ G then none else ext r
  | k + 1, u => match src u with
    | .ann t _ => some t
    | .inf r => if r ∈ G then jt G src ext k r else ext r

/-- With two units, one step along the reads is as good as two. -/
theorem jt_stable (G : Finset U) (src : U → Src) (ext : U → Option Ty) (r : U) :
    jt G src ext 1 r = jt G src ext 2 r := by
  cases r <;> rcases ha : src .a with ⟨t1, r1⟩ | r1 <;> rcases hb : src .b with ⟨t2, r2⟩ | r2 <;>
    (try cases r1) <;> (try cases r2) <;>
    by_cases a : U.a ∈ G <;> by_cases b : U.b ∈ G <;> simp [jt, ha, hb, a, b]

def group (G : Finset U) (src : U → Src) (e : Env) : U → Out :=
  fun u => (unit (src u)).run fun p => if p.1 ∈ G then jt G src (fun x => e (x, .ty)) 2 p.1 else e p

/-- The compiler, on sources `S` (all of them, or a subtype) through `val`. -/
def compiler (S : Type) (val : S → Src) : Compiler U S Out (Option Ty) K (Option Ty) Q Ans where
  unit := fun s => unit (val s)
  group := fun G src e => group G (val ∘ src) e
  iface := Out.ty
  answer := fun i _ => i
  π := fun i _ => i
  keys := fun tr => (tr.map fun p => (p.1, K.ty)).toFinset
  covers := fun _ _ => True

theorem ty_group (G : Finset U) (src : U → Src) (e : Env) (v : U) :
    (group G src e v).ty = jt G src (fun x => e (x, .ty)) 2 v := by
  simp only [group]
  cases h : src v with
  | ann t r => simp [unit, jt, h]
  | inf r =>
    simp only [unit, Task.run_ask, Task.run_pure, jt, h]
    by_cases hr : r ∈ G
    · simp only [hr, ite_true]; exact (jt_stable G src _ r).symm
    · simp [hr]

theorem obligations (S : Type) (val : S → Src) : (compiler S val).Obligations where
  comp := by
    intro G src e d _
    show group G (val ∘ src) e d = (unit (val (src d))).run _
    simp only [group]
    congr 1
    funext p
    obtain ⟨u, q⟩ := p
    cases q
    simp only [Compiler.override, compiler, Function.comp]
    split
    · rename_i hu; rw [ty_group]
    · rfl
  coverage := by
    intro tr q hq
    refine ⟨(q.1, K.ty), ?_, rfl, trivial⟩
    show (q.1, K.ty) ∈ (tr.map fun p => (p.1, K.ty)).toFinset
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, rfl⟩
  abstraction := by
    intro i i' _ h _ _
    exact h

/-! ## The witness -/

abbrev C := compiler Src id
abbrev S : Finset U := {U.a, U.b}

/-- `A.x: Int = B.y`, `B.y = A.x`. -/
def srcOld : U → Src
  | .a => .ann .int .b
  | .b => .inf .a

/-- The annotation removed: `A.x = B.y`, `B.y = A.x`. -/
def srcNew : U → Src
  | .a => .inf .b
  | .b => .inf .a

def none₀ : Env := fun _ => none

/-- The clean build of the annotated version, with the keys each unit records. -/
def s₀ : State U Out K :=
  { out := C.group S srcOld none₀
    U := fun u => C.keys ((C.unit (srcOld u)).trace (C.envOf (C.iface ∘ C.group S srcOld none₀))) }

theorem s₀_out : ∀ u, s₀.out u = ⟨some .int, true⟩ := by decide

/-- Zinc recompiles `A` (its source changed), finds `x : Int` against `B`'s classfile, sees no API
change, and stops. -/
theorem zinc_stops_at_old :
    (C.zinc S srcNew Policy.plain 3 0 {U.a} s₀).map (·.out) = some (fun _ => ⟨some .int, true⟩) := by
  decide

/-- The clean build of the same sources reports the cycle. -/
theorem clean_fails : ∀ u, C.cleanFrom S srcNew s₀ u = ⟨none, false⟩ := by decide

theorem zinc_ne_clean :
    (C.zinc S srcNew Policy.plain 3 0 {U.a} s₀).map (·.out) ≠ some (C.cleanFrom S srcNew s₀) := by
  decide

/-- Both outcomes are per-unit fixed points of the edited sources. -/
theorem two_fixpoints :
    C.Fixpoint S srcNew (fun _ => ⟨some .int, true⟩) ∧ C.Fixpoint S srcNew (fun _ => ⟨none, false⟩) := by
  constructor <;> intro u _ <;> cases u <;> rfl

/-! ## Annotations restore T3 -/

def Src.isAnn : Src → Prop
  | .ann _ _ => True
  | .inf _ => False

abbrev Ann := { s : Src // s.isAnn }

def annTy : Ann → Option Ty
  | ⟨.ann t _, _⟩ => some t
  | ⟨.inf _, h⟩ => absurd h id

theorem iface_ann (s : Ann) (e : Env) : ((unit s.val).run e).ty = annTy s := by
  obtain ⟨s, h⟩ := s
  cases s with
  | ann t r => rfl
  | inf r => exact absurd h id

/-- **T3 with annotations**: when every member's type is written, Zinc's result is the clean build,
for every program, edit and sound policy that stays in the project. -/
theorem annotated_eq_clean [DecidableEq K] (Sp : Finset U) (src : U → Ann)
    (P : Policy U Out K) (hP : P.Sound Sp) (hPS : Compiler.Policy.InS Sp P)
    (fuel n : ℕ) (R : Finset U) (s : State U Out K) (D : Finset U)
    (hD : D ⊆ R) (hR : R ⊆ Sp) (hInv : (compiler Ann Subtype.val).Inv Sp src s D)
    (s' : State U Out K) (h : (compiler Ann Subtype.val).zinc Sp src P fuel n R s = some s') :
    s'.out = (compiler Ann Subtype.val).cleanFrom Sp src s :=
  (compiler Ann Subtype.val).zinc_eq_clean_of_explicit (obligations _ _) Sp src P hP hPS annTy
    (fun sr e => iface_ann sr e) fuel n R s D hD hR hInv s' h

/-! ## Zinc's loop as it runs, and the program space

Zinc's next round is the invalidated units and the units whose API changed (`PingPong.zincPolicy`);
a round with a compile error stops the build. The modes are Zinc today; sbt/zinc#1284 (reverted by
#1462): add to the first round every unit with a member-ref edge both to and from a changed unit;
and the precise rule proposed here: add the units of a cycle through a changed unit only when the
edit changes whether, or how, the unit's type is written (a body-only edit adds nothing). -/

inductive Mode | today | mutual | precise
  deriving DecidableEq, Repr

/-- A source, and whether its text changed beyond its `Src` (a body-only edit). -/
structure Prog where
  src : U → Src
  touched : U → Bool

def other : U → U | .a => .b | .b => .a

/-- The outcome of a build: every unit's type, or a compile error. -/
inductive Result | ok (a b : Option Ty) | error
  deriving DecidableEq, Repr

def resultOf (o : U → Out) (G : Finset U) : Result :=
  if ∀ u ∈ G, (o u).ok = true then .ok (o .a).ty (o .b).ty else .error

def cleanResult (src : U → Src) : Result := resultOf (C.group S src none₀) S

def zincPolicy : Policy U Out K := fun _ R s s' I => I ∪ R.filter fun u => s.out u ≠ s'.out u

/-- The rounds of Zinc's loop from `R`, at most `fuel`; `none` on an error. -/
def loop (src : U → Src) : ℕ → Finset U → State U Out K → Option ((U → Out) × List (Finset U))
  | 0, _, s => some (s.out, [])
  | fuel + 1, R, s =>
    let s' := C.round src R s
    if ∃ u ∈ R, (s'.out u).ok = false then none
    else
      let I := C.invalidated S R s s'
      if I ⊆ R then some (s'.out, [R])
      else (loop src fuel (zincPolicy 0 R s s' I) s').map fun (o, rs) => (o, R :: rs)

/-- The first round: the edited units, and the units the mode adds. -/
def firstRound (m : Mode) (p p' : Prog) : Finset U :=
  let edited := S.filter fun u => p.src u != p'.src u || p'.touched u
  let cyc := S.filter fun u => (p.src u).reads ∈ edited ∧ (p.src ((p.src u).reads)).reads = u
  match m with
  | .today => edited
  | .mutual => edited ∪ cyc
  | .precise => edited ∪ cyc.filter fun _ => (S.filter fun v => p.src v != p'.src v).Nonempty

def initial (src : U → Src) : State U Out K :=
  { out := C.group S src none₀
    U := fun u => C.keys ((C.unit (src u)).trace (C.envOf (C.iface ∘ C.group S src none₀))) }

structure Verdict where
  clean : Result
  incr : Result
  rounds : List (Finset U)
  same : Bool
  deriving DecidableEq

def verdict (m : Mode) (p p' : Prog) : Verdict :=
  let cl := cleanResult p'.src
  match loop p'.src 4 (firstRound m p p') (initial p.src) with
  | none => ⟨cl, .error, [], cl == .error⟩
  | some (o, rs) => ⟨cl, resultOf o S, rs, resultOf o S == cl⟩

def uStr : U → String | .a => "A" | .b => "B"

def srcs : List Src := [.ann .int .b, .ann .long .b, .inf .b]

/-- `a`'s and `b`'s sources over the three choices, each reading the other. -/
def progs : List Prog :=
  srcs.flatMap fun sa => srcs.map fun sb =>
    ⟨fun u => match u with | .a => sa | .b => match sb with
        | .ann t _ => .ann t .a | .inf _ => .inf .a, fun _ => false⟩

def bases : List Prog := progs.filter fun p => cleanResult p.src != .error

/-- Single edits: another source for one unit, or a body-only edit. -/
def edits (p : Prog) : List (String × Prog) :=
  [U.a, U.b].flatMap fun u =>
    ((srcs.map fun x => match u, x with
        | .b, .ann t _ => Src.ann t .a | .b, .inf _ => .inf .a | _, x => x).filter (· != p.src u)).map
      (fun x => ("set " ++ uStr u ++ " " ++ (match x with | .ann .int _ => "Int" | .ann .long _ => "Long" | .inf _ => "inf"),
        { p with src := fun v => if v = u then x else p.src v })) ++
    [("touch " ++ uStr u, { p with touched := fun v => v = u })]

/-- **C1, an annotation removed in a cycle**: the incremental build keeps the old type, the clean
build reports the cycle. -/
example : (verdict .today ⟨srcOld, fun _ => false⟩ ⟨srcNew, fun _ => false⟩).same = false := by decide

/-- **C2, an annotation changed in a cycle**: `A.x: Long = B.y` to `A.x: Int = B.y`, `B.y = A.x`;
`A` compiled alone against `B.y : Long` fails, the clean build infers `B.y : Int`. -/
example : (verdict .today ⟨fun u => match u with | .a => .ann .long .b | .b => .inf .a, fun _ => false⟩
    ⟨srcOld, fun _ => false⟩) = ⟨.ok (some .int) (some .int), .error, [], false⟩ := by decide

end Zinc.Cycles
