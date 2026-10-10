import Zinc.InlineOpaque
import Zinc.ExtraHash

/-!
# Companion pairs in a hierarchy (Phase 25)

Phase 23 (`ExtraHash.lean`) models a companion pair as two units under one name, the type half and
the term half. This phase puts such pairs in a program space for the conformance harness: a class
`A` (a plain class, a case class or a trait) with a companion `object A` (none, a case class's
synthetic one, or explicit, written before or after the class), either half extending a trait
(`P` for the class, `Q` for the object), with readers of each half: `UseM.u(a: A) = a.m` (the
class half's own member), `UseX.u = A.x` (the object half's), `UseP`/`UseQ` (members the halves
inherit) and a descendant `class D extends A { def k = m }`, whose mixin forwarders read the
members of a trait `A`. Edits change the type of a member of
either half or of a parent, or add a member to either half.

The model is the key loop of `InlineOpaque.lean` (`verdict`): the pair is one Zinc class, `A`,
whose keys are the names of both halves, each covering its half's atoms. Two bridges:

* `today`: both halves are reported, so each key moves with its half (develop, and the Merkle
  PoC since retronym/zinc#56).
* `pre56`: the Merkle PoC's Scala 2 bridge kept the extracted classes in a map keyed by name, and a
  class and its companion share it: the half extracted last replaced the other, and Zinc stored
  an empty placeholder for it. Its keys never move. The class half is extracted before its
  companion (a case class's synthetic companion, or an explicit object written after the class),
  so the class half is lost; an object written before its class loses the object half.

Checked by `decide` below: under `today` every edit is clean; under `pre56` exactly the edits to
the lost half's members that a reader reads are unclean (`check_pre56_exact`). This is
`ExtraHash.qualified_sound` failing its hypothesis for the lost half: its hash is constant, so it
determines nothing. The earlier spaces had no companion in an edited hierarchy, so no run reached
this case.
-/

namespace Zinc.Companions

open Zinc.InlineOpaque (Key Cls Verdict verdict uniq ancestors)

/-- The type half. -/
inductive Kind | cls | caseCls | trait
  deriving DecidableEq, Repr

def Kind.str : Kind → String | .cls => "class" | .caseCls => "case" | .trait => "trait"

/-- The term half: none, the case class's synthetic companion, or an explicit object, written
before or after the class. -/
inductive Obj | none | synthetic | before | after
  deriving DecidableEq, Repr

def Obj.str : Obj → String
  | .none => "none" | .synthetic => "synthetic" | .before => "before" | .after => "after"

def Obj.explicit : Obj → Bool | .before | .after => true | _ => false

/-- `today`: develop, both halves stored, every descendant of a changed class recompiles.
`merkle`: the Merkle PoC since retronym/zinc#56, both halves stored, a descendant recompiles only
when its own compilation reads the change (the descendant rules). `pre56`: the Merkle PoC before
#56, which lost one half. -/
inductive Mode | today | merkle | pre56
  deriving DecidableEq, Repr

def Mode.parse : String → Option Mode
  | "today" => some .today | "merkle" => some .merkle | "pre56" => some .pre56 | _ => none

/-- A member's result type, the slot an edit changes. -/
inductive Ty | int | str
  deriving DecidableEq, Repr

def Ty.scala : Ty → String | .int => "Int" | .str => "String"
def Ty.lit : Ty → String | .int => "1" | .str => "\"s\""

structure Prog where
  kind : Kind
  obj : Obj
  /-- The class half extends `P` (`def p`), the object half `Q` (`def q`). -/
  pP : Bool
  pQ : Bool
  m : Ty := .int
  x : Ty := .int
  p : Ty := .int
  q : Ty := .int
  /-- An added member: `n` in the class half, `y` in the object half. -/
  n : Bool := false
  y : Bool := false
  deriving DecidableEq, Repr

def Prog.hasObj (p : Prog) : Bool := p.obj != .none

/-- A case class always has a companion; only a case class has a synthetic one; `Q` is a parent of
an explicit object. -/
def Prog.wellFormed (p : Prog) : Bool :=
  (match p.kind, p.obj with
    | .caseCls, .none => false
    | .caseCls, _ => true
    | _, .synthetic => false
    | _, _ => true) &&
    (!p.pQ || p.obj.explicit)

def bases : List Prog := Id.run do
  let mut out := []
  for k in [Kind.cls, .caseCls, .trait] do
    for o in [Obj.none, .synthetic, .before, .after] do
      for pP in [false, true] do
        for pQ in [false, true] do
          let p : Prog := { kind := k, obj := o, pP, pQ }
          if p.wellFormed then out := out ++ [p]
  return out

inductive Edit | m | x | p | q | n | y
  deriving DecidableEq, Repr

def Edit.str : Edit → String
  | .m => "m" | .x => "x" | .p => "p" | .q => "q" | .n => "add n" | .y => "add y"

def Edit.apply (p : Prog) : Edit → Option Prog
  | .m => some { p with m := .str }
  | .x => if p.obj.explicit then some { p with x := .str } else none
  | .p => if p.pP then some { p with p := .str } else none
  | .q => if p.pQ then some { p with q := .str } else none
  | .n => some { p with n := true }
  | .y => if p.obj.explicit then some { p with y := true } else none

def edits (p : Prog) : List (Edit × Prog) :=
  [Edit.m, .x, .p, .q, .n, .y].filterMap fun e => (e.apply p).map (e, ·)

/-! ## Sources -/

def classSrc (p : Prog) : String :=
  let ext := if p.pP then " extends P" else ""
  let n := if p.n then "\n  def n: Int = 1" else ""
  let head := match p.kind with
    | .cls => "class A(val i: Int)" ++ ext
    | .caseCls => "case class A(i: Int)" ++ ext
    | .trait => "trait A" ++ ext
  head ++ " {\n  def m: " ++ p.m.scala ++ " = " ++ p.m.lit ++ n ++ "\n}\n"

def objectSrc (p : Prog) : String :=
  let ext := if p.pQ then " extends Q" else ""
  let y := if p.y then "\n  def y: Int = 1" else ""
  "object A" ++ ext ++ " {\n  def x: " ++ p.x.scala ++ " = " ++ p.x.lit ++ y ++ "\n}\n"

def aSrc (p : Prog) : String :=
  "package c\n\n" ++
    match p.obj with
    | .before => objectSrc p ++ "\n" ++ classSrc p
    | .after => classSrc p ++ "\n" ++ objectSrc p
    | _ => classSrc p

def dSrc (p : Prog) : String :=
  let parent := match p.kind with | .trait => "A" | _ => "A(0)"
  "package c\n\nclass D extends " ++ parent ++ " {\n  def k = m\n}\n"

def files (p : Prog) : List (String × String) :=
  [("A.scala", aSrc p), ("D.scala", dSrc p),
    ("UseM.scala", "package c\n\nobject UseM {\n  def u(a: A) = a.m\n}\n")] ++
  (if p.obj.explicit then [("UseX.scala", "package c\n\nobject UseX {\n  def u = A.x\n}\n")] else []) ++
  (if p.pP then [("P.scala", "package c\n\ntrait P {\n  def p: " ++ p.p.scala ++ " = " ++ p.p.lit ++ "\n}\n"),
      ("UseP.scala", "package c\n\nobject UseP {\n  def u(a: A) = a.p\n}\n")] else []) ++
  (if p.pQ then [("Q.scala", "package c\n\ntrait Q {\n  def q: " ++ p.q.scala ++ " = " ++ p.q.lit ++ "\n}\n"),
      ("UseQ.scala", "package c\n\nobject UseQ {\n  def u = A.q\n}\n")] else [])

def tiers (p : Prog) : List (String × ℕ) :=
  (files p).map fun (f, _) => (f, if f.startsWith "Use" || f == "D.scala" then 2 else 1)

def editedFile : Edit → String
  | .m | .x | .n | .y => "A.scala" | .p => "P.scala" | .q => "Q.scala"

def factors (p : Prog) : List (String × String) :=
  [("kind", p.kind.str), ("obj", p.obj.str), ("pP", toString p.pP), ("pQ", toString p.pQ)]

/-! ## The model -/

/-- The half the `pre56` bridge loses: the one extracted first. -/
def lost (p : Prog) : Option ExtraHash.Ns :=
  match p.obj with
  | .none => none
  | .before => some .term
  | .synthetic | .after => some .type

/-- Zinc's view of a program: the pair is one class, `A`; each name's key covers its half's atom,
unless the bridge lost that half. An inherited member's key is its owner's (the Merkle PoC records
a selection on the owner). -/
def zprog (md : Mode) (p : Prog) : List Cls :=
  let keep (n : ExtraHash.Ns) := md != .pre56 || lost p != some n
  let typeKeys := if keep .type then [("m", ["A.m"]), ("n", ["A.n"])] else []
  let termKeys := if keep .term && p.obj.explicit then [("x", ["A.x"]), ("y", ["A.y"])] else []
  let mixesP := p.pP && p.kind == .trait
  [{ name := "A", file := "A.scala", keys := typeKeys ++ termKeys,
      parents := (if p.pP then ["P"] else []) ++ (if p.pQ then ["Q"] else []),
      reads := if p.pP && p.kind != .trait then ["P.p"] else [] },
    { name := "D", file := "D.scala", uses := [⟨"A", "m"⟩], parents := ["A"],
      reads := ["A.m"] ++ (if p.kind == .trait then ["A.n"] else []) ++
        (if mixesP then ["P.p"] else []) },
    { name := "UseM", file := "UseM.scala", uses := [⟨"A", "m"⟩], reads := ["A.m"] }] ++
  (if p.obj.explicit then [{ name := "UseX", file := "UseX.scala", uses := [⟨"A", "x"⟩], reads := ["A.x"] }]
    else []) ++
  (if p.pP then [{ name := "P", file := "P.scala", keys := [("p", ["P.p"])] },
      { name := "UseP", file := "UseP.scala", uses := [⟨"P", "p"⟩], reads := ["P.p"] }] else []) ++
  (if p.pQ then [{ name := "Q", file := "Q.scala", keys := [("q", ["Q.q"])] },
      { name := "UseQ", file := "UseQ.scala", uses := [⟨"Q", "q"⟩], reads := ["Q.q"] }] else [])

def changed : Edit → List String
  | .m => ["A.m"] | .x => ["A.x"] | .p => ["P.p"] | .q => ["Q.q"] | .n => ["A.n"] | .y => ["A.y"]

/-- Where the Merkle PoC's descendant rules fire without the descendant reading the change, because
Zinc keys the pair by one name (Phase 23's merged key): `(descendant, ancestor, atoms)`.
* `mirror`: `object A extends Q` is taken for a top-level object with static forwarders, though
  its companion class means it has none;
* `exports`: the pair's parents are both halves' (#1795), so `D` is a descendant of `Q` whose
  stored parents do not name it;
* `traitDirect`: `D` mixes in the trait half, and a change to the object half moves the pair's
  key (`ExtraHash.merged_spurious`);
* before #56, with the class half lost: its stored parents are empty, so `exports` takes `A` and
  `D` for classes forwarding `P`'s members, and `traitDirect` no longer sees a trait. -/
def mergedFires (md : Mode) (p : Prog) : List (String × String × List String) :=
  let typeLost := md == .pre56 && lost p == some .type
  (if p.pQ then [("A", "Q", ["Q.q"]), ("D", "Q", ["Q.q"])] else []) ++
  (if p.kind == .trait && p.obj.explicit && !typeLost then [("D", "A", ["A.x", "A.y"])] else []) ++
  (if typeLost && p.pP then [("A", "P", ["P.p"]), ("D", "P", ["P.p"])] else [])

/-- The Merkle PoC's cycle: as `InlineOpaque.next`, but a descendant of a class whose API moved
recompiles only when it uses a moved name, reads a changed atom of an ancestor (an override
check, a mixin forwarder: the descendant rules of retronym/zinc#24), or a rule fires through the
merged pair (`mergedFires`). -/
def nextMerkle (fires : List (String × String × List String)) (p : List Cls) (ch : List String)
    (done cur : List String) : List String :=
  let moved := (p.filter (cur.contains ·.name)).flatMap (·.moved ch)
  let movedCls := moved.map (·.cls)
  let inv := p.filter fun d => d.uses.any moved.contains ||
    (d.reads.any ch.contains && (ancestors p d).any movedCls.contains) ||
    fires.any fun (x, a, as) => x == d.name && movedCls.contains a && as.any ch.contains
  (inv.map (·.name)).filter (!done.contains ·)

def runMerkle (fires : List (String × String × List String)) (p : List Cls) (ch : List String)
    (files : List String) : List String :=
  let rec go (fuel : ℕ) (done cur : List String) : List String :=
    match fuel with
    | 0 => done
    | n + 1 =>
      if cur.isEmpty then done
      else
        let done' := uniq (done ++ cur)
        go n done' (uniq (nextMerkle fires p ch done' cur))
  go (p.length + 1) [] ((p.filter (files.contains ·.file)).map (·.name))

def check (md : Mode) (p : Prog) (e : Edit) : Verdict :=
  let zp := zprog md p
  let files := [editedFile e]
  if md == .today then verdict zp (changed e) files
  else
    let r := runMerkle (mergedFires md p) zp (changed e) files
    ⟨r, (zp.filter fun c => c.reads.any (changed e).contains && !r.contains c.name).map (·.name),
      (zp.filter fun c => r.contains c.name && !files.contains c.file &&
        !c.reads.any (changed e).contains).map (·.name)⟩

/-- An edit to a member of the lost half that a class reads: `m` (read by `UseM` and `D`), `x` (by
`UseX`), or a member added to a trait, which `D`'s mixin forwarders read. -/
def readsLost (p : Prog) (e : Edit) : Bool :=
  match lost p, e with
  | some .type, .m => true
  | some .type, .n => p.kind == .trait
  | some .term, .x => true
  | _, _ => false

def check_today_clean : Bool :=
  bases.all fun p => (edits p).all fun (e, _) => (check .today p e).clean

def check_merkle_clean : Bool :=
  bases.all fun p => (edits p).all fun (e, _) => (check .merkle p e).clean

/-- The Merkle PoC recompiles a subset of develop's classes; what it recompiles without reading the
change is what the merged pair makes its rules fire for. -/
def check_merkle_subset : Bool :=
  bases.all fun p => (edits p).all fun (e, _) =>
    let m := check .merkle p e
    m.recompiled.all (check .today p e).recompiled.contains &&
      m.wasted.all fun c => (mergedFires .merkle p).any fun (x, _, as) => x == c && as.any (changed e).contains

def check_pre56_exact : Bool :=
  bases.all fun p => (edits p).all fun (e, _) => (check .pre56 p e).clean == !readsLost p e

set_option maxRecDepth 100000 in
example : check_today_clean = true := by decide +kernel
set_option maxRecDepth 100000 in
example : check_pre56_exact = true := by decide +kernel
set_option maxRecDepth 100000 in
example : check_merkle_clean = true := by decide +kernel
set_option maxRecDepth 100000 in
example : check_merkle_subset = true := by decide +kernel

-- The space has 30 programs.
set_option maxRecDepth 100000 in
example : bases.length = 30 := by decide +kernel

end Zinc.Companions
