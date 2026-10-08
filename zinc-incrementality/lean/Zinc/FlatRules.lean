import Zinc.Flat

/-!
# The PoC's descendant rules as a policy, checked exhaustively

`Flat.lean` records the descendant's refchecks as keys. The PoC (decision 3) does not: Zinc keeps
recording only client `memberRef`s (dropping self-references), and decides which descendants to
recompile from a table of rules evaluated on its stored view (decl stubs, linearizations, headers).
Here that table is a `Policy`, the refchecks queries go unrecorded, and every run over a small
program space is compared with the clean build.
-/

namespace Zinc.Flat

open Zinc.Hier (Cls Name Ty)
open Zinc.Hier.Cls Zinc.Hier.Name

inductive Rule | uses | overrides | conflicts | abstract | header
  deriving DecidableEq, Repr

def ifc (s : St) (c : Cls) : Iface := (s.out c).iface

/-- `N`: the names whose decls-only hash changed on `p`. -/
def changedNames (s s' : St) (p : Cls) : List Name :=
  names.filter fun n => own (ifc s p) n != own (ifc s' p) n

def declares (s : St) (q : Cls) (n : Name) : Bool := (own (ifc s q) n).isSome

def deferredIn (s : St) (q : Cls) (n : Name) : Bool :=
  (own (ifc s q) n).map (·.deferred) == some true

/-- `d`'s parents with their stored linearizations. -/
def sides (s : St) (d : Cls) : List Lin :=
  (ifc s d).decl.parents.map fun e => e :: (ifc s e.1).lin

/-- Does rule `r` say that descendant `d` must recompile after `p` was recompiled? The PoC's
table, with `U(d)` the names `d`'s source selects. `abstractAll` widens `abstract` to names
deferred in *any* ancestor of `d` (see below). -/
def fires (src : Cls → Src) (abstractAll : Bool) (s s' : St) (p d : Cls) : Rule → Bool
  | .uses => (changedNames s s' p).any fun n => (src d).body.any (·.2 == n)
  | .overrides => (changedNames s s' p).any fun n => declares s' d n
  | .conflicts => (changedNames s s' p).any fun n =>
      (ifc s' d).lin.any fun e => e.1 != p && !sameSide (sides s' d) p e.1 && declares s' e.1 n
  | .abstract => !(ifc s' d).decl.abstract && (changedNames s s' p).any fun n =>
      deferredIn s p n || deferredIn s' p n ||
        (abstractAll && (ifc s' d).lin.any fun e => deferredIn s' e.1 n)
  | .header => headerChanged s s' p

/-- The rule set as a policy over `inheritance.reverse*` of each recompiled class. -/
def rulePolicy (src : Cls → Src) (abstractAll : Bool) (rs : List Rule) : Compiler.Policy Cls Out K :=
  fun _ R s s' I => I ∪ Finset.univ.filter fun d =>
    ∃ p ∈ R, d ≠ p ∧ d ∈ descendants s' {p} ∧ ∃ r ∈ rs, fires src abstractAll s s' p d r = true

/-- Zinc's keys: client `memberRef`s only. -/
def clientOnly : Kind → Bool := (· == .client)

def allRules : List Rule := [.uses, .overrides, .conflicts, .abstract, .header]

/-! ## The program space

`A[T]` (abstract) optionally `extends M[t]`; trait `M[T]`; `B extends A[t]`; `C extends B with M`;
each of `A B M C` declares `m` or not (`Int`, `String`, `T`, or deferred `Int`); `B` optionally
selects its own `m`; clients `X (B.m)`, `Y (C.m)`, `Z (A.m)`. An edit changes one class. -/

inductive Opt | none | int | str | par | dfr
  deriving DecidableEq, Repr

def Opt.decls : Opt → List (Name × Mem)
  | .none => []
  | .int => [(m, Flat.int)]
  | .str => [(m, Flat.str)]
  | .par => [(m, Flat.par)]
  | .dfr => [(m, intD)]

def opts : List Opt := [.none, .int, .str, .par, .dfr]

structure Cfg where
  oA : Opt
  oB : Opt
  oM : Opt
  oC : Opt
  aPar : Option Ty
  bArg : Ty
  bUses : Bool
  deriving DecidableEq, Repr

def Cfg.aParents (k : Cfg) : List (Cls × Ty) :=
  match k.aPar with
  | some t => [(M, t)]
  | none => []

def Cfg.bBody (k : Cfg) : List (Cls × Name) := if k.bUses then [(B, m)] else []

def Cfg.src (k : Cfg) : Cls → Src
  | A => { decl := { parents := k.aParents, decls := k.oA.decls, abstract := true } }
  | M => { decl := { decls := k.oM.decls, abstract := true } }
  | B => { decl := { parents := [(A, k.bArg)], decls := k.oB.decls }, body := k.bBody }
  | C => { decl := { parents := [(B, .int), (M, .int)], decls := k.oC.decls } }
  | X => { decl := {}, body := [(B, m)] }
  | Y => { decl := {}, body := [(C, m)] }
  | Z => { decl := {}, body := [(A, m)] }

def cfgs : List Cfg := do
  let a ← opts; let b ← opts; let mm ← opts; let c ← opts
  let aPar ← [none, some .int, some .string]
  let bArg ← [Ty.int, .string]
  let bUses ← [false, true]
  pure ⟨a, b, mm, c, aPar, bArg, bUses⟩

/-- Single-class edits, with the class edited. -/
def edits (k : Cfg) : List (Cfg × Cls) :=
  (opts.filter (· != k.oA)).map (fun o => ({ k with oA := o }, A)) ++
  (opts.filter (· != k.oB)).map (fun o => ({ k with oB := o }, B)) ++
  (opts.filter (· != k.oM)).map (fun o => ({ k with oM := o }, M)) ++
  (opts.filter (· != k.oC)).map (fun o => ({ k with oC := o }, C)) ++
  ([none, some .int, some .string].filter (· != k.aPar)).map (fun t => ({ k with aPar := t }, A)) ++
  ([Ty.int, .string].filter (· != k.bArg)).map (fun t => ({ k with bArg := t }, B))

def Cfg.size (k : Cfg) : ℕ :=
  ([k.oA, k.oB, k.oM, k.oC].filter (· != .none)).length + (if k.aPar.isSome then 1 else 0) +
    (if k.bArg != .int then 1 else 0) + (if k.bUses then 1 else 0)

/-- Is the run from `k` after edit `k'` of class `e` clean, under keys `E` and the rule policy? -/
def cleanRun (E : Kind → Bool) (abstractAll : Bool) (rs : List Rule) (s₀ : St) (k' : Cfg) (e : Cls) :
    Bool :=
  match runF E .zinc k'.src (rulePolicy k'.src abstractAll rs) 9 0 ∅ {e} s₀ with
  | some r =>
    let cl := memo { out := clean k'.src, U := fun _ => ∅ }
    all.all fun c => r.state.out c == cl.out c
  | none => false

/-- Every unclean (base, edit) pair. -/
def unclean (E : Kind → Bool) (abstractAll : Bool) (rs : List Rule) : List (Cfg × Cfg × Cls) :=
  cfgs.flatMap fun k =>
    let s₀ := init E k.src
    (edits k).filterMap fun (k', e) =>
      if cleanRun E abstractAll rs s₀ k' e then none else some (k, k', e)

/-- The smallest unclean pair, by the size of the base and then of the edited program. -/
def minimal (l : List (Cfg × Cfg × Cls)) : Option (Cfg × Cfg × Cls) :=
  l.foldl (fun acc x => match acc with
    | none => some x
    | some y => if x.1.size < y.1.size || (x.1.size == y.1.size && x.2.1.size < y.2.1.size) then some x else some y) none

/-! ## Results

Over the 7,500 bases and 142,500 single-class edits (`lake exe exhaustive`, compiled; a
`native_decide` over the whole space is too slow for the build), the default rules as stated
leave 672 runs unclean; widening `abstract` to names deferred in any ancestor of `d` leaves none.
The minimal counterexamples, as checked examples, follow. -/

def reportR (E : Kind → Bool) (abstractAll : Bool) (rs : List Rule) (src₀ src₁ : Cls → Src)
    (R₀ : Finset Cls) : Option Report :=
  report E .zinc (rulePolicy src₁ abstractAll rs) src₀ src₁ R₀

/-- `abstract class A { def m: Int }`, `abstract class B extends A { def m = 1 }`,
`class C extends B`. -/
def baseImpl : Cls → Src
  | A => { decl := { decls := [(m, intD)], abstract := true } }
  | B => { decl := { parents := [(A, .int)], decls := [(m, int)], abstract := true } }
  | C => { decl := { parents := [(B, .int)] } }
  | _ => { decl := {} }

/-- Delete `B.m`: `C` no longer implements `m`. -/
def editImpl : Cls → Src
  | B => { decl := { parents := [(A, .int)], abstract := true } }
  | c => baseImpl c

/-- **The `abstract` rule as stated is unsound.** `m` changed on `B`, but is deferred in neither
the old nor the new `B`; it is deferred in `A`. `C` is not recompiled and misses its error. -/
example : reportR clientOnly false allRules baseImpl editImpl {B} = some ⟨[], 1, false⟩ := by
  native_decide

/-- Widened: `C` is concrete and `m` is deferred in some ancestor of `C`. -/
example : reportR clientOnly true allRules baseImpl editImpl {B} = some ⟨[C], 2, true⟩ := by
  native_decide

/-! ### Minimal counterexample per rule, against the widened default

Each pair is clean under the widened default and unclean with that one rule dropped (counts of
unclean pairs over the whole space in brackets). They are the candidate scripted tests. -/

def k₀ : Cfg := ⟨.none, .none, .none, .none, none, .int, false⟩

def cleanUnder (rs : List Rule) (k k' : Cfg) (e : Cls) : Bool :=
  ((reportR clientOnly true rs k.src k'.src {e}).map (·.clean)).getD false

def without' (r : Rule) : List Rule := allRules.filter (· != r)

/-- `uses` (1320): `B` selects `this.m`; `A` gains `m: T`. -/
example : cleanUnder allRules { k₀ with bUses := true } { k₀ with oA := .par, bUses := true } A ∧
    !cleanUnder (without' .uses) { k₀ with bUses := true } { k₀ with oA := .par, bUses := true } A := by
  native_decide

/-- …and recording the self-selection as a key instead makes the rule unnecessary (0). -/
example : ((reportR (fun k => k == .client || k == .uses) true (without' .uses)
    ({ k₀ with bUses := true }).src ({ k₀ with oA := .par, bUses := true }).src {A}).map (·.clean)) =
    some true := by native_decide

/-- `overrides` (20650): `B` declares `def m: Int`; `A` gains `m: String`. -/
example : cleanUnder allRules { k₀ with oB := .dfr } { k₀ with oA := .str, oB := .dfr } A ∧
    !cleanUnder (without' .overrides) { k₀ with oB := .dfr } { k₀ with oA := .str, oB := .dfr } A := by
  native_decide

/-- `conflicts` (504): `A.m: T` reaches `C` through `B`; the mixin `M` gains a concrete `m: T`. -/
example : cleanUnder allRules { k₀ with oA := .par } { k₀ with oA := .par, oM := .par } M ∧
    !cleanUnder (without' .conflicts) { k₀ with oA := .par } { k₀ with oA := .par, oM := .par } M := by
  native_decide

/-- `abstract` (2272): the trait `M` gains a deferred `m`; the concrete `C` must implement it. -/
example : cleanUnder allRules k₀ { k₀ with oM := .dfr } M ∧
    !cleanUnder (without' .abstract) k₀ { k₀ with oM := .dfr } M := by
  native_decide

/-- `header` (22500): `B extends A[Int]` → `A[String]` with no members at all: `C`'s stored
linearization still says `A[Int]`. Only a reader of stored linearizations (cross-project
composition) can observe it. -/
example : cleanUnder allRules k₀ { k₀ with bArg := .string } B ∧
    !cleanUnder (without' .header) k₀ { k₀ with bArg := .string } B := by
  native_decide

end Zinc.Flat
