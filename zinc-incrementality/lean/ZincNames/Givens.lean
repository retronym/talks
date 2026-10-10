import ZincNames.Names

/-!
# Givens and implicits: resolution by type, where Zinc records the owner only

`Names.lean` with a type instead of a name: the client summons `a.T` (`summon[a.T]` in Scala 3,
`implicitly[a.T]` in Scala 2) and an instance can sit in

* `blk`: object `a.V`, through `{ import a.V.given; ... }` in the client;
* `inh`: trait `a.P`, which the client extends;
* `wild`: object `a.W`, through `import a.W.given` (Scala 2: `import a.W._`);
* `inner`: package `a.b` at the top level, a file of its own (Scala 3);
* `pobj`: `package object b` in `a`;
* `outer`: package `a`: at the top level, a file of its own, in Scala 3; in `package object a` in
  Scala 2;
* `comp`: the companion `object T`, the implicit scope.

Resolution, as both compilers report it (probed with `scala-cli`, 2.13 and 3):

* Scala 2: any two instances in the lexical scope are ambiguous; the companion is searched only
  when the lexical scope has none.
* Scala 3: the innermost nesting level wins: the block, then the inherited member, then the file's
  imports together with the members of the client's own package (two of them are ambiguous), then
  the enclosing package; the companion last.

Zinc records the same edges as for a name, but a changed implicit member invalidates every
member-ref dependent of its class, used names or not (`MemberRefInvalidator`). So the import's edge
charged to the first class suffices here, and the misses are the scopes reached through no edge:
the package object, and an added top-level given (an added source, `T$package`).

The specification is `NamesSpec.lean` (`givens`); this file is the executable model, checked on a
bounded space.
-/

namespace Zinc.Givens

open Zinc.Names (Ver Pkg Rules)

inductive Slot | blk | inh | wild | wpkg | inner | pobj | outer | comp
  deriving DecidableEq, Repr

def Slot.str : Slot → String
  | .blk => "blk" | .inh => "inh" | .wild => "wild" | .wpkg => "wpkg" | .inner => "inner"
  | .pobj => "pobj" | .outer => "outer" | .comp => "comp"

inductive Res | ok (s : Slot) | err (why : String)
  deriving DecidableEq, Repr

def Res.str : Res → String
  | .ok s => s.str | .err w => "error (" ++ w ++ ")"

structure Verdict where
  before : Res
  after : Res
  recompiled : Bool
  clean : Bool
  deriving DecidableEq, Repr

def Slot.all : List Slot := [.blk, .inh, .wild, .wpkg, .inner, .pobj, .outer, .comp]

/-- A top-level given is a file of its own (Scala 3 only). -/
def Slot.topLevel (v : Ver) : Slot → Bool
  | .inner | .outer | .wpkg => v == .s3
  | _ => false

structure Client where
  pkg : Pkg
  blk : Bool
  inh : Bool
  wild : Bool
  first : Bool
  /-- `package object b extends a.PT`: the package object inherits its instance from `a.PT`, which
  the edit changes. -/
  pinh : Bool := false
  /-- `import a.q._` (Scala 3: `import a.q.given`): an instance in `package object q` (Scala 2) or
  at the top level of package `a.q` (Scala 3). The bridge records nothing for a package import. -/
  wpkg : Bool := false
  deriving DecidableEq, Repr

structure Prog where
  cl : Client
  has : Slot → Bool

/-- The slots the client can see, innermost first; the companion is always there. -/
def visible (v : Ver) (c : Client) : List Slot :=
  (if c.blk then [.blk] else []) ++ (if c.inh then [.inh] else []) ++
  (if c.wild then [.wild] else []) ++ (if c.wpkg then [.wpkg] else []) ++
  (if c.pkg != .top && v == .s3 then [.inner] else []) ++
  (if c.pkg != .top then [.pobj] else []) ++
  (if c.pkg != .flat then [.outer] else []) ++ [.comp]

/-- The slots that exist: those in scope. -/
def present (v : Ver) (c : Client) : List Slot := visible v c

/-- Scala 3's nesting level of a slot, for this client. -/
def level (c : Client) : Slot → Nat
  | .blk => 0
  | .inh => 1
  | .wild | .wpkg | .inner | .pobj => 2
  | .outer => if c.pkg == .top then 2 else 3
  | .comp => 4

def resolve (v : Ver) (p : Prog) : Res :=
  let bs := (visible v p.cl).filter p.has
  let lex := bs.filter (· != .comp)
  match v with
  | .s2 =>
    match lex, bs with
    | [s], _ => .ok s
    | [], [s] => .ok s
    | [], _ => .err "not found"
    | _, _ => .err "ambiguous"
  | .s3 =>
    match bs with
    | [] => .err "not found"
    | s :: rest =>
      if rest.any (fun t => level p.cl t == level p.cl s) then .err "ambiguous" else .ok s

/-- Does Zinc invalidate the client's file when slot `s` changed, given what it resolved before?
-/
def invalidates (v : Ver) (p : Prog) (r : Res) (s : Slot) : Bool :=
  match s with
  -- an edge to the class (the import's edge goes to the first class), and the change is implicit
  | .blk | .inh | .wild | .comp => true
  -- a package object, or an added or removed top-level given
  | .pobj | .inner | .outer | .wpkg => r == .ok s && (!s.topLevel v || p.has s)

def changed (v : Ver) (p p' : Prog) : List Slot :=
  (present v p.cl).filter fun s => p.has s != p'.has s

/-- The simple names of the top-level classes an edit adds: a top-level given's file `Inner.scala`
holds class `Inner$package` (Scala 3); Scala 2's `package object a` exists before and after. -/
def addedClasses (v : Ver) (p p' : Prog) : List String :=
  (present v p.cl).filterMap fun s =>
    if s.topLevel v && !p.has s && p'.has s then
      some (if s == .inner then "Inner$package" else if s == .wpkg then "Q$package" else "Outer$package")
    else none

/-- Does the client use a name? It never names a `$package` class: it summons by type. -/
def clientUses (n : String) : Bool := !n.endsWith "$package"

/-- The packages that hold implicits at the top level: `a.b`, `a`, and the imported `a.q`. -/
inductive Where | ab | a | aq
  deriving DecidableEq, Repr

def Slot.where? : Slot → Option Where
  | .pobj | .inner => some .ab
  | .outer => some .a
  | .wpkg => some .aq
  | _ => none

/-- The packages whose package object or `$package` class gains or loses an implicit, as a rule
diffing their names sees it: `package object b` (an inherited instance as `Rules.seesInherited`
says), `package object q` and Scala 2's `package object a`, and Scala 3's `$package` classes (a new
or deleted class has all its names added or removed). -/
def implicitPkgs (rs : Rules) (v : Ver) (p p' : Prog) : List Where :=
  (changed v p p').filterMap fun s =>
    if s == .pobj && p.cl.pinh && !rs.seesInherited then none else s.where?

/-- Does the G rule, for an implicit changed in package `w`, reach a class of package clause `c`
that imports `a.q` (`wpkg`)? Global: every class. Narrowed: the classes of `w` and of the packages
nested in it, and those that record a wildcard import of `w` (with `imports`). -/
def reachesG (rs : Rules) (c : Pkg) (wpkg : Bool) : Where → Bool
  | .a => true
  | .ab => rs.reach == .global || c != .top
  | .aq => rs.reach == .global || (rs.imports && wpkg)

def recompiles (m : Zinc.Names.Mode) (v : Ver) (p p' : Prog) : Bool :=
  match m with
  | .searched => !(changed v p p').isEmpty
  | .names => !(changed v p p').isEmpty
  | m =>
    let rs := m.toRules
    (changed v p p').any (invalidates v p (resolve v p)) ||
      (rs.cheap && (addedClasses v p p').any clientUses) ||
      (rs.g && (implicitPkgs rs v p p').any (reachesG rs p.cl.pkg p.cl.wpkg))

/-- Scala 3 compiles a class that extends a trait whose members are all lazy (a given alias is a
lazy val) differently alone than with the trait: read from TASTy, the trait has no initialiser, and
the class's static initialiser omits the call to `P.$init$` that a joint compile emits. Zinc
recompiles the client in a later round than `P`, or without it, unless the companion of `T` changed
(both `P` and the client depend on `T`, and a changed implicit invalidates them together); a clean
build compiles them together. Here the trait's `$init$` is empty, so only the classfiles differ.
But the client's behaviour now depends on how it was compiled: a statement later added to the
trait is not API, Zinc recompiles the trait alone, and a client compiled apart never runs it
(`Names.separateInit`; pending scripted test `trait-initialiser-skipped-scala3`). -/
def separateInit (v : Ver) (p p' : Prog) (rc : Bool) : Bool :=
  v == .s3 && p'.cl.inh && p'.has .inh && rc && p.has .comp == p'.has .comp

def verdict (m : Zinc.Names.Mode) (v : Ver) (p p' : Prog) : Verdict :=
  let r := resolve v p
  let r' := resolve v p'
  let rc := recompiles m v p p'
  ⟨r, r', rc, (rc || r == r') && !separateInit v p p' rc⟩

def Prog.set (p : Prog) (s : Slot) (x : Bool) : Prog :=
  { p with has := fun t => if t == s then x else p.has t }

def clients : List Client := Id.run do
  let mut out := []
  for pkg in [Pkg.nested, .flat, .top] do
    for blk in [false, true] do
      for inh in [false, true] do
        for wild in [false, true] do
          for first in [false, true] do
            if !first || wild then
              for pinh in [false, true] do
                if !pinh || pkg != .top then
                  for wpkg in [false, true] do
                    out := out ++ [⟨pkg, blk, inh, wild, first, pinh, wpkg⟩]
  return out

def subsets : List Slot → List (List Slot)
  | [] => [[]]
  | s :: ss => (subsets ss).flatMap fun t => [t, s :: t]

/-- Bases: every client, and every set of at most two instances, that resolves in this version. -/
def bases (v : Ver) : List Prog :=
  clients.flatMap fun c =>
    ((subsets (present v c)).filter (·.length ≤ 2)).filterMap fun ss =>
      let p : Prog := ⟨c, fun s => ss.contains s⟩
      if resolve v p matches .ok _ then some p else none

inductive Edit | add (s : Slot) | delete (s : Slot) | move (s t : Slot)
  deriving DecidableEq, Repr

def Edit.str : Edit → String
  | .add s => "add " ++ s.str | .delete s => "delete " ++ s.str
  | .move s t => "move " ++ s.str ++ " " ++ t.str

def edits (v : Ver) (p : Prog) : List (Edit × Prog) :=
  let ss := present v p.cl
  let one := ss.map fun s => if p.has s then (.delete s, p.set s false) else (.add s, p.set s true)
  let tops := ss.filter (·.topLevel v)
  let moves := tops.flatMap fun s => tops.filterMap fun t =>
    if s != t && p.has s && !p.has t then some (.move s t, (p.set s false).set t true) else none
  one ++ moves

/-! ## Families -/

def cl0 : Client := ⟨.nested, false, false, false, false, false, false⟩

/-- `pobj_added_today_s2`: **Package object, Scala 2**: an implicit added to `package object b` over the companion's. -/
example :
    verdict .today .s2 ⟨cl0, (· == .comp)⟩ ⟨cl0, fun s => s == .comp || s == .pobj⟩ =
      ⟨.ok .comp, .ok .pobj, false, false⟩ := by native_decide

/-- `inner_added_today_s3`: **Top-level given, Scala 3**: a file with `given a.T` added to package `a.b`, over the
companion's. -/
example :
    verdict .today .s3 ⟨cl0, (· == .comp)⟩ ⟨cl0, fun s => s == .comp || s == .inner⟩ =
      ⟨.ok .comp, .ok .inner, false, false⟩ := by native_decide

/-- `wild_first_clean`: An import's edge is enough for an implicit: the first class is invalidated whatever it uses. -/
example :
    (verdict .today .s3 ⟨{ cl0 with wild := true, first := true }, (· == .comp)⟩
      ⟨{ cl0 with wild := true, first := true }, fun s => s == .comp || s == .wild⟩).clean = true := by
  native_decide

/-! ## The package rule (G) -/

/-- Is every edit of the space clean in both versions under a mode, but for the trait initialiser? -/
def cleanOn (m : Zinc.Names.Mode) : Bool := [Ver.s2, .s3].all fun v => (bases v).all fun p =>
  (edits v p).all fun (_, p') => (verdict m v p p').clean || separateInit v p p' (recompiles m v p p')

/-- `package object b extends a.PT`, and `a.PT` gains an instance over the companion's. -/
def pinhBase : Prog := ⟨{ cl0 with pinh := true }, (· == .comp)⟩

/-- `pobj_inherited_today`. -/
example :
    verdict .today .s2 pinhBase (pinhBase.set .pobj true) = ⟨.ok .comp, .ok .pobj, false, false⟩ := by
  native_decide

/-- `pobj_inherited_decls`. -/
example :
    verdict (.rules { Zinc.Names.allRules with api := .decls }) .s2 pinhBase (pinhBase.set .pobj true) =
      ⟨.ok .comp, .ok .pobj, false, false⟩ := by native_decide

/-- The family of an unclean edit: G3 the trait initialiser; G1 an instance in a package object
(Scala 2's `package object a` included); G2 a top-level given (Scala 3). -/
def family (m : Zinc.Names.Mode) (v : Ver) (p p' : Prog) : String :=
  if (verdict m v p p').clean then "-"
  else if separateInit v p p' (recompiles m v p p') then "G3"
  else if (changed v p p').any (fun s => s.topLevel v) then "G2"
  else if (changed v p p').any (fun s => s == .pobj || s == .outer) then "G1" else "?"

/-! ## Cost

Beyond the edited files and their heirs: the client's file, and two classes that summon nothing,
`a.b.Near` and `a.Mid`, standing for the other classes of package `a.b` and of package `a`. -/

def necessary (v : Ver) (p p' : Prog) : Bool := resolve v p != resolve v p'

/-- `Near` (in `a.b`), `Mid` (in `a`), `Far` (in `c`): does the mode recompile them? -/
def bystanders (m : Zinc.Names.Mode) (v : Ver) (p p' : Prog) : Bool × Bool × Bool :=
  match m with
  | .searched | .names => (false, false, false)
  | m =>
    let rs := m.toRules
    let ws := if rs.g then implicitPkgs rs v p p' else []
    (ws.any (reachesG rs .flat false), ws.any (reachesG rs .top false),
      rs.reach == .global && !ws.isEmpty)

structure Cost where
  edits : Nat
  wrong : Nat
  client : Nat
  near : Nat
  mid : Nat
  far : Nat
  deriving Repr

def cost (m : Zinc.Names.Mode) (v : Ver) : Cost := Id.run do
  let mut c : Cost := ⟨0, 0, 0, 0, 0, 0⟩
  for p in bases v do
    for (_, p') in edits v p do
      let rc := recompiles m v p p'
      let (n, d, f) := bystanders m v p p'
      c := ⟨c.edits + 1,
        c.wrong + (if !(verdict m v p p').clean && !separateInit v p p' rc then 1 else 0),
        c.client + (if rc && !necessary v p p' then 1 else 0),
        c.near + (if n then 1 else 0), c.mid + (if d then 1 else 0), c.far + (if f then 1 else 0)⟩
  return c

/-! ## Rendering -/

def gname : Slot → String
  | .blk => "gBlk" | .inh => "gInh" | .wild => "gWild" | .wpkg => "gWpkg" | .inner => "gInner" | .pobj => "gPobj"
  | .outer => "gOuter" | .comp => "gComp"

def instance_ (v : Ver) (s : Slot) : String :=
  match v with
  | .s3 => "given " ++ gname s ++ ": a.T = new a.T"
  | .s2 => "implicit val " ++ gname s ++ ": a.T = new a.T"

def body (v : Ver) (p : Prog) (s : Slot) : String :=
  if p.has s then " {\n  " ++ instance_ v s ++ "\n}\n" else "\n"

def slotFile (p : Prog) : Slot → String
  | .pobj => if p.cl.pinh then "PT.scala" else "PObj.scala"
  | .blk => "V.scala" | .inh => "P.scala" | .wild => "W.scala" | .inner => "Inner.scala"
  | .outer => "Outer.scala" | .comp => "T.scala" | .wpkg => "Q.scala"

def slotSrc (v : Ver) (p : Prog) : Slot → Option String
  | .blk => some ("package a\n\nobject V" ++ body v p .blk)
  | .inh => some ("package a\n\ntrait P" ++ body v p .inh)
  | .wild => some ("package a\n\nobject W" ++ body v p .wild)
  | .pobj => some ((if p.cl.pinh then "package a\n\ntrait PT" else "package a\n\npackage object b") ++
      body v p .pobj)
  | .comp => some ("package a\n\nclass T\nobject T" ++ body v p .comp)
  | .inner => if p.has .inner then some ("package a.b\n\n" ++ instance_ v .inner ++ "\n") else none
  | .wpkg => match v with
    | .s3 => if p.has .wpkg then some ("package a.q\n\n" ++ instance_ v .wpkg ++ "\n") else none
    | .s2 => some ("package a\n\npackage object q" ++ body v p .wpkg)
  | .outer => match v with
    | .s3 => if p.has .outer then some ("package a\n\n" ++ instance_ v .outer ++ "\n") else none
    | .s2 => some ("package object a" ++ body v p .outer)

def clientSrc (v : Ver) (p : Prog) : String :=
  let c := p.cl
  let pkg := match c.pkg with
    | .nested => "package a\npackage b\n" | .flat => "package a.b\n" | .top => "package a\n"
  let sel := if v == .s3 then "given" else "_"
  let summ := if v == .s3 then "summon[a.T]" else "implicitly[a.T]"
  let imps := (if c.wild then "import a.W." ++ sel ++ "\n" else "") ++
    (if c.wpkg then "import a.q." ++ sel ++ "\n" else "")
  let imps := if imps.isEmpty then "" else imps ++ "\n"
  let first := if c.first then "object First\n\n" else ""
  let ext := if c.inh then " extends a.P" else ""
  let use := if c.blk then "{ import a.V." ++ sel ++ "; " ++ summ ++ " }" else summ
  pkg ++ "\n" ++ imps ++ first ++ "object Client" ++ ext ++ " {\n  val use: Any = " ++ use ++ "\n}\n"

/-- The program's files: the client, the bystanders `a.b.Near`, `a.Mid` and `c.Far`, the package
object that inherits its instance, `a.q.Other` (package `a.q` exists without its given), and the
slots'. -/
def files (v : Ver) (p : Prog) : List (String × String) :=
  [("Client.scala", clientSrc v p), ("Near.scala", "package a.b\n\nobject Near\n"),
   ("Mid.scala", "package a\n\nobject Mid\n"), ("Far.scala", "package c\n\nobject Far\n")] ++
  (if p.cl.wpkg then [("Other.scala", "package a.q\n\nobject Other\n")] else []) ++
  (if p.cl.pinh then [("PObj.scala", "package a\n\npackage object b extends a.PT\n")] else []) ++
  (present v p.cl).filterMap fun s => (slotSrc v p s).map (slotFile p s, ·)

def fileEdits (v : Ver) (p p' : Prog) : List (String × Option String) :=
  (present v p.cl).filterMap fun s =>
    if slotSrc v p s == slotSrc v p' s then none else some (slotFile p s, slotSrc v p' s)

end Zinc.Givens
