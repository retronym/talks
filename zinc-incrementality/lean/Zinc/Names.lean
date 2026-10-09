import Mathlib.Data.List.Basic

/-!
# Name resolution: where a simple name can be bound, and what Zinc records

`Added.lean` has one client and two scopes. Here the client's simple name `Foo` (or `Option`, with
`scala.Option` as the last resort) can be bound in any of the scopes Scala searches, and an edit
adds, deletes, renames or moves a binding. The model resolves the name before and after the edit
with Scala's rules, predicts what Zinc recompiles from the dependencies its extractors record
(`ExtractDependencies`, `ExtractUsedNames`) and the invalidation rules of `IncrementalCommon`, and
says whether the incremental build equals the clean one.

The binding sites (`Slot`), innermost first, for

```scala
package a; package b              // or `package a.b`, or `package a`
import a.W._; import a.q._        // optional
import a.X.Foo                    // optional
object First                      // optional: another class, charged with the imports (Scala 3: `object Last`, after)
object Client extends a.P {       // `extends` optional
  val use: Any = { import a.V._; Foo }   // the block import optional
}
```

* `blk`: a member of `a.V`, through the import in the block;
* `inh`: a member of trait `a.P`, inherited;
* `expl`: a member of `a.X`, through the explicit import;
* `wild`: a member of object `a.W`, through the wildcard import;
* `wpkg`: a class in package `a.q`, through the wildcard import;
* `inner`: a class in package `a.b`, in another file;
* `pobj`: a member of `package object b` in `a`;
* `outer`: a class in package `a`;
* `lib`: `scala.Option`.

Zinc's dependencies, read off the bridges (`Dependency.scala`, Scala 3's `ExtractDependencies`):

* a reference records a member-ref edge to the class that owns the symbol it resolved to, and to
  the classes of its qualifier; the used name `Foo` goes to the enclosing class;
* an import records an edge to its qualifier (a package records nothing), and an explicit
  selector's name; a top-level import is charged to one class of the file: the first in Scala 2
  (`Dependency.firstClassOrModuleClass`), the last in Scala 3 (`responsibleForImports` folds over
  the file and keeps the last `TypeDef` it meets, though its comment says first);
* `extends` records an inheritance edge.

Zinc's invalidation (`IncrementalCommon`, `MemberRefInvalidator`): a recompiled class whose API
changed invalidates its inheritance dependents and the member-ref dependents that use a changed
name; a deleted source invalidates the member-ref dependents of its classes; an added source
invalidates nothing (`invalidateInitial` schedules only the added source; its classes have no
dependents yet). Zinc recompiles whole files.

So a change of resolution is missed when the client's file records no edge to the scope that
changed. The fixed extractor records every scope the lookup searched, misses included (`Added.lean`'s
`fixed`); the coarse fix invalidates the users of a name whenever a binding of it is added or
removed.
-/

namespace Zinc.Names

inductive Ver | s2 | s3
  deriving DecidableEq, Repr

inductive Slot | blk | inh | expl | wild | wpkg | inner | pobj | outer | lib
  deriving DecidableEq, Repr

/-- Top-level classes: a binding is a file of its own, so adding one adds a source. -/
def Slot.topLevel : Slot → Bool
  | .wpkg | .inner | .outer => true
  | _ => false

def Slot.str : Slot → String
  | .blk => "blk" | .inh => "inh" | .expl => "expl" | .wild => "wild" | .wpkg => "wpkg"
  | .inner => "inner" | .pobj => "pobj" | .outer => "outer" | .lib => "lib"

/-- The client's package clause: `package a; package b`, `package a.b`, `package a`. -/
inductive Pkg | nested | flat | top
  deriving DecidableEq, Repr

def Pkg.str : Pkg → String
  | .nested => "a;b" | .flat => "a.b" | .top => "a"

structure Client where
  pkg : Pkg
  blk : Bool
  inh : Bool
  expl : Bool
  wild : Bool
  wpkg : Bool
  /-- Another class shares the client's file and is charged with the top-level imports: before the
  client in Scala 2 (`object First`), after it in Scala 3 (`object Last`). -/
  first : Bool
  /-- The name is `Option`, so `scala.Option` binds it when nothing else does. -/
  opt : Bool
  /-- Scala 3 only: `W` and package `a.b` get their member through a wildcard `export` of another
  object (`object W { export a.U.* }`, and `export a.U2.*` at the top level of `a.b`), whose
  member the edit adds or removes. -/
  exp : Bool := false
  deriving DecidableEq, Repr

/-- What a slot holds: nothing, the name, or (top-level slots) a class `Bar`, to rename. -/
inductive St | none | foo | bar
  deriving DecidableEq, Repr

structure Prog where
  cl : Client
  st : Slot → St

/-- The slots in scope for the client, innermost first. -/
def visible (c : Client) : List Slot :=
  (if c.blk then [.blk] else []) ++ (if c.inh then [.inh] else []) ++
  (if c.expl then [.expl] else []) ++ (if c.wild then [.wild] else []) ++
  (if c.wpkg then [.wpkg] else []) ++
  (if c.pkg != .top then [.inner, .pobj] else []) ++
  (if c.pkg != .flat then [.outer] else []) ++ (if c.opt then [.lib] else [])

/-- The slots that exist: those in scope, and `a.Foo`, which a class can move to. -/
def present (c : Client) : List Slot :=
  let v := visible c
  if v.contains .outer then v else v ++ [.outer]

def Prog.binds (p : Prog) (s : Slot) : Bool := s == .lib || p.st s == .foo

inductive Res
  | ok (s : Slot)
  /-- The client does not compile. -/
  | err (why : String)
  /-- Another file does not compile: `a.b.Foo` and the package object's `Foo` clash (Scala 3). -/
  | clash
  deriving DecidableEq, Repr

def Res.str : Res → String
  | .ok s => s.str | .err w => "error (" ++ w ++ ")" | .clash => "clash"

/-- Scala's resolution of the client's name. The order of `visible` is the search order; the
exceptions are the ambiguities, which both compilers report:

* the block import against an inherited member (an import does not shadow an outer definition);
* the block's wildcard import against the explicit import outside it;
* two wildcard imports at one level.

An import beats a package member from another file in both (Scala 2's `lookupSymbol`:
"imported symbols take precedence over package-owned symbols in different compilation units");
an inherited member beats a package member without an ambiguity (Scala 3's `checkNoOuterDefs`
skips package owners). -/
def resolve (v : Ver) (p : Prog) : Res :=
  let vis := visible p.cl
  let b := fun s => vis.contains s && p.binds s
  if v == .s3 && p.st .inner == .foo && p.st .pobj == .foo then .clash
  else if p.cl.expl && !b .expl then .err "import"
  else if b .blk && b .inh then .err "ambiguous"
  else if b .blk && b .expl then .err "ambiguous"
  else if !b .blk && !b .inh && !b .expl && b .wild && b .wpkg then .err "ambiguous"
  else
    -- Scala 2 looks in the package object before the package's own classes
    let vis := if v == .s2 then
        (vis.filter (· != .inner)).flatMap fun s => if s == .pobj then [.pobj, .inner] else [s]
      else vis
    match vis.find? b with
    | some s => .ok s
    | none => .err "not found"

/-- Which extractor or invalidation rule. -/
inductive Mode
  /-- Zinc today. -/
  | today
  /-- Record every scope the lookup searched, misses included. -/
  | searched
  /-- When a binding of a name is added or removed, invalidate the users of the name. -/
  | names
  deriving DecidableEq, Repr

/-- The slots whose binding of the name changed. -/
def changed (p p' : Prog) : List Slot :=
  (present p.cl).filter fun s => p.binds s != p'.binds s

/-- Does Zinc invalidate the client's file when slot `s` changed, given what the client resolved
before (`r`)? -/
def invalidates (p : Prog) (r : Res) (s : Slot) : Bool :=
  match s with
  -- inheritance edge
  | .inh => true
  -- `V` is the block import's qualifier: an edge from `Client`, which uses `Foo`
  | .blk => true
  -- `X` and the selector's name `Foo`, both charged to the first class of the file
  | .expl => true
  -- `W` is charged to the first class (Scala 3: the last); it uses `Foo` if it is the client, or if
  -- the explicit import's selector is charged to it too; otherwise only a client that resolved
  -- through `W` has its own edge to `W`
  | .wild => !p.cl.first || p.cl.expl || r == .ok .wild
  -- the package object is reached only through the resolved symbol
  | .pobj => r == .ok .pobj
  -- a top-level class: only a deleted class's dependents are invalidated
  | .wpkg | .inner | .outer => r == .ok s && p.st s == .foo
  | .lib => false

def recompiles (m : Mode) (v : Ver) (p p' : Prog) : Bool :=
  let r := resolve v p
  match m with
  | .today => (changed p p').any (invalidates p r)
  | .searched => (changed p p').any (visible p.cl).contains
  | .names => !(changed p p').isEmpty

/-- The verdict of an edit: the client's resolution before, after, whether Zinc recompiles it,
and whether the incremental build equals the clean one. -/
structure Verdict where
  before : Res
  after : Res
  recompiled : Bool
  clean : Bool
  deriving DecidableEq, Repr

/-- Scala 2 lets `package object b` hold an `object Foo` beside a class `a.b.Foo`, and the class's
mirror (`a/b/Foo.class`, its static forwarders) comes out differently when the package object's
member is compiled with it. Adding the member leaves the class's file alone, and its old mirror. -/
def staleMirror (v : Ver) (p p' : Prog) : Bool :=
  v == .s2 && p.st .pobj != .foo && p'.st .pobj == .foo && p.st .inner == .foo && p'.st .inner == .foo

/-- Scala 3 reports the clash of a class `a.b.Foo` with a member `Foo` of package `a.b`'s package
object (or a top-level export) only when it compiles both files together. An edit changes one of
them, and nothing in Zinc connects the other (Zinc names the member `a.b.package$.Foo`), so the
incremental build misses the error. -/
def missedClash (v : Ver) (p' : Prog) : Bool := resolve v p' == .clash

/-- Scala 3 compiles a class that extends a trait whose members are all lazy (here `object Foo`)
differently alone than with the trait: read from TASTy, the trait has no initialiser, and the
class's static initialiser omits the call to `P.$init$`. Zinc compiles the client in a later round
than `P`, or without it; a clean build compiles them together. In this space the trait's `$init$`
is empty and only the classfiles differ (`Givens.lean` has the same with a given). It is a separate
compilation bug all the same: once a client has been compiled apart, a statement added to the trait
(not API, so Zinc recompiles the trait alone) never runs for it, where a clean build runs it
(pending scripted test `trait-initialiser-skipped-scala3`). -/
def separateInit (v : Ver) (p' : Prog) (rc : Bool) : Bool := v == .s3 && p'.cl.inh && p'.st .inh == .foo && rc

/-- The divergences that are not about the client's resolution. -/
def besideResolution (v : Ver) (p p' : Prog) : Bool := staleMirror v p p' || missedClash v p'

def verdict (m : Mode) (v : Ver) (p p' : Prog) : Verdict :=
  let r := resolve v p
  let r' := resolve v p'
  let rc := recompiles m v p p'
  let bytes := separateInit v p' rc && r' matches .ok _
  ⟨r, r', rc, (rc || r == r') && !besideResolution v p p' && !bytes⟩

/-! ## The program space -/

def Prog.set (p : Prog) (s : Slot) (x : St) : Prog :=
  { p with st := fun t => if t == s then x else p.st t }

def states (s : Slot) : List St :=
  if s.topLevel then [.none, .foo, .bar] else [.none, .foo]

def clients : List Client := Id.run do
  let mut out := []
  for pkg in [Pkg.nested, .flat, .top] do
    for blk in [false, true] do
      for inh in [false, true] do
        for expl in [false, true] do
          for wild in [false, true] do
            for wpkg in [false, true] do
              for first in [false, true] do
                for opt in [false, true] do
                  -- `First` matters only for the wildcard import's edge
                  if !first || wild then
                    for exp in [false, true] do
                      -- the export matters only where `W` or package `a.b` is in scope
                      if !exp || wild || pkg != .top then
                        out := out ++ [⟨pkg, blk, inh, expl, wild, wpkg, first, opt, exp⟩]
  return out

/-- Assignments of states to the given slots, with at most `k` slots holding the name. -/
def assigns : List Slot → ℕ → List (List (Slot × St))
  | [], _ => [[]]
  | s :: ss, k =>
    (states s).flatMap fun x =>
      if x == .foo then
        match k with
        | 0 => []
        | k + 1 => (assigns ss k).map ((s, x) :: ·)
      else (assigns ss k).map ((s, x) :: ·)

def mkProg (c : Client) (a : List (Slot × St)) : Prog :=
  ⟨c, fun s => ((a.find? (·.1 == s)).map (·.2)).getD .none⟩

/-- The bases: every client, and every assignment with at most two bindings (besides
`scala.Option`) and an explicit import that compiles, whose resolution compiles in both versions. -/
def bases : List Prog :=
  clients.flatMap fun c =>
    let ss := (present c).filter (· != .lib)
    (assigns ss 2).filterMap fun a =>
      let p := mkProg c a
      if (resolve .s2 p matches .ok _) && (resolve .s3 p matches .ok _) then some p else none

inductive Edit
  | add (s : Slot)
  | delete (s : Slot)
  | rename (s : Slot)
  | unrename (s : Slot)
  | move (s t : Slot)
  deriving DecidableEq, Repr

def Edit.str : Edit → String
  | .add s => "add " ++ s.str | .delete s => "delete " ++ s.str
  | .rename s => "rename " ++ s.str | .unrename s => "unrename " ++ s.str
  | .move s t => "move " ++ s.str ++ " " ++ t.str

/-- Single edits: add or delete a binding, rename a top-level class to or from `Bar`, and move a
top-level class between packages. -/
def edits (p : Prog) : List (Edit × Prog) :=
  let ss := (present p.cl).filter (· != .lib)
  let one := ss.flatMap fun s =>
    match p.st s with
    | .none => [(.add s, p.set s .foo)]
    | .foo => [(.delete s, p.set s .none)] ++ (if s.topLevel then [(.rename s, p.set s .bar)] else [])
    | .bar => [(.unrename s, p.set s .foo)]
  let tops := ss.filter (·.topLevel)
  let moves := tops.flatMap fun s => tops.filterMap fun t =>
    if s != t && p.st s == .foo && p.st t == .none then
      some (.move s t, (p.set s .none).set t .foo)
    else none
  one ++ moves

/-! ## Families, as checked examples -/

def cl0 : Client := ⟨.nested, false, false, false, false, false, false, false, false⟩

/-- **Inner package** (retronym/zinc#32): `a.b.Foo` added over `a.Foo`. -/
def innerBase : Prog := mkProg cl0 [(.outer, .foo)]

theorem inner_added_today :
    verdict .today .s2 innerBase (innerBase.set .inner .foo) = ⟨.ok .outer, .ok .inner, false, false⟩ := by
  native_decide

theorem inner_added_searched :
    (verdict .searched .s2 innerBase (innerBase.set .inner .foo)).clean = true := by native_decide

/-- **Package object**: `Foo` added to `package object b` over `a.Foo`. The client reached the
package object through no symbol. -/
theorem pobj_added_today :
    verdict .today .s3 innerBase (innerBase.set .pobj .foo) = ⟨.ok .outer, .ok .pobj, false, false⟩ := by
  native_decide

/-- **Top-level export** (Scala 3): `export a.U2.*` in package `a.b`, and `a.U2` gains `Foo`. Zinc
recompiles the exporting file (the wildcard export records an inheritance edge), whose new
forwarder shadows `a.Foo`, but the client has no edge to it: the package object's case. -/
def expBase : Prog := mkProg { cl0 with exp := true } [(.outer, .foo)]

theorem export_added_today :
    verdict .today .s3 expBase (expBase.set .pobj .foo) = ⟨.ok .outer, .ok .pobj, false, false⟩ := by
  native_decide

/-- **Wildcard import, another class**: `Foo` added to `object W` over `a.Foo`, the import charged to
`First`, which does not use `Foo`. -/
def wildBase : Prog := mkProg { cl0 with wild := true, first := true } [(.outer, .foo)]

theorem wild_first_today :
    verdict .today .s2 wildBase (wildBase.set .wild .foo) = ⟨.ok .outer, .ok .wild, false, false⟩ := by
  native_decide

/-- Without `First` the client is charged with the import, and uses `Foo`. -/
theorem wild_client_today :
    (verdict .today .s2 { wildBase with cl := { wildBase.cl with first := false } }
      (({ wildBase with cl := { wildBase.cl with first := false } }).set .wild .foo)).clean = true := by
  native_decide

/-- Every edit of the space, both versions, is clean when the lookup's misses are recorded, and
when the users of a name are invalidated on every added or removed binding; the stale mirror, the
missed clash and the trait initialiser are not about the client's resolution, and neither fix
touches them. -/
theorem searched_clean : (bases.all fun p => (edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => (verdict .searched v p p').clean || besideResolution v p p' ||
      separateInit v p' (recompiles .searched v p p')) = true := by
  native_decide

theorem names_clean : (bases.all fun p => (edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => (verdict .names v p p').clean || besideResolution v p p' ||
      separateInit v p' (recompiles .names v p p')) = true := by
  native_decide

end Zinc.Names

/-! ## Rendering as Scala sources -/

namespace Zinc.Names

def Prog.name (p : Prog) : String := if p.cl.opt then "Option" else "Foo"

/-- The file of each slot, and its source; `none` when the file does not exist. -/
def slotFile (p : Prog) : Slot → String
  | .blk => "V.scala" | .inh => "P.scala" | .expl => "X.scala"
  | .wild => if p.cl.exp then "U.scala" else "W.scala"
  | .wpkg => "Q.scala" | .inner => "Inner.scala"
  | .pobj => if p.cl.exp then "U2.scala" else "PObj.scala"
  | .outer => "Outer.scala"
  | .lib => ""

def member (p : Prog) (s : Slot) : String :=
  if p.st s == .foo then " {\n  object " ++ p.name ++ "\n}\n" else "\n"

def topClass (p : Prog) (s : Slot) (pkg : String) : Option String :=
  match p.st s with
  | .none => none
  | .foo => some ("package " ++ pkg ++ "\n\nobject " ++ p.name ++ "\n")
  | .bar => some ("package " ++ pkg ++ "\n\nobject Bar\n")

def slotSrc (p : Prog) : Slot → Option String
  | .blk => some ("package a\n\nobject V" ++ member p .blk)
  | .inh => some ("package a\n\ntrait P" ++ member p .inh)
  | .expl => some ("package a\n\nobject X" ++ member p .expl)
  | .wild => some ((if p.cl.exp then "package a\n\nobject U" else "package a\n\nobject W") ++ member p .wild)
  | .pobj => some ((if p.cl.exp then "package a\n\nobject U2" else "package a\n\npackage object b") ++
      member p .pobj)
  | .wpkg => topClass p .wpkg "a.q"
  | .inner => topClass p .inner "a.b"
  | .outer => topClass p .outer "a"
  | .lib => none

def clientSrc (v : Ver) (p : Prog) : String :=
  let c := p.cl
  let pkg := match c.pkg with
    | .nested => "package a\npackage b\n" | .flat => "package a.b\n" | .top => "package a\n"
  let imps := (if c.wild then "import a.W._\n" else "") ++ (if c.wpkg then "import a.q._\n" else "") ++
    (if c.expl then "import a.X." ++ p.name ++ "\n" else "")
  let first := if c.first && v == .s2 then "object First\n\n" else ""
  let last := if c.first && v == .s3 then "\nobject Last\n" else ""
  let ext := if c.inh then " extends a.P" else ""
  let use := if c.blk then "{ import a.V._; " ++ p.name ++ " }" else p.name
  pkg ++ "\n" ++ imps ++ (if imps.isEmpty then "" else "\n") ++ first ++
    "object Client" ++ ext ++ " {\n  val use: Any = " ++ use ++ "\n}\n" ++ last

/-- The client's classfile, where the harness reads what the name resolved to. -/
def clientClass (p : Prog) : String := if p.cl.pkg == .top then "a/Client$" else "a/b/Client$"

/-- The program's files. `Other.scala` keeps package `a.q` in existence for its import. -/
def files (v : Ver) (p : Prog) : List (String × String) :=
  [("Client.scala", clientSrc v p)] ++
  (if p.cl.wpkg then [("Other.scala", "package a.q\n\nobject Other\n")] else []) ++
  (if p.cl.exp && p.cl.wild then [("W.scala", "package a\n\nobject W {\n  export a.U.*\n}\n")] else []) ++
  (if p.cl.exp && p.cl.pkg != .top then [("PObj.scala", "package a.b\n\nexport a.U2.*\n")] else []) ++
  ((present p.cl).filter (· != .lib)).filterMap fun s => (slotSrc p s).map (slotFile p s, ·)

/-- The files an edit changes: a new source, or `none` to delete it. -/
def fileEdits (p p' : Prog) : List (String × Option String) :=
  ((present p.cl).filter (· != .lib)).filterMap fun s =>
    if slotSrc p s == slotSrc p' s then none else some (slotFile p s, slotSrc p' s)

end Zinc.Names
