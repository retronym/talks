
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

The specification is `NamesSpec.lean`: the lookup as a `TCompiler` instance, today's bridge and the
fixes as keys, with the obligations proved for every program. This file is the executable model
checked against the compilers and Zinc on a bounded space; its results are `example`s.
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
  /-- The package object inherits its member: `package object b extends a.PT`, and the edit adds or
  removes `Foo` in trait `a.PT`. -/
  pinh : Bool := false
  /-- `W` inherits its member: `object W extends a.WT`, and the edit adds or removes `Foo` in trait
  `a.WT`. -/
  winh : Bool := false
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
skips package owners). Scala 3 reports the clash of a class `a.b.Foo` with a member of package `a.b`'s
package object only when the package object declares it; one it inherits clashes with nothing, and
the class wins. Scala 2 treats an inherited member of the package object as no package member at all
(`isPackageOwnedInDifferentUnit` looks at its owner, the trait): it beats the file's imports, even two
binding wildcards, and is ambiguous with the block import, like the client's own inherited member,
which it loses to (probed with `scala-cli`, 2.13 and 3.3, and on the harness). -/
def resolve (v : Ver) (p : Prog) : Res :=
  let vis := visible p.cl
  let b := fun s => vis.contains s && p.binds s
  let pin := v == .s2 && p.cl.pinh && b .pobj
  if v == .s3 && p.st .inner == .foo && p.st .pobj == .foo && !p.cl.pinh then .clash
  else if p.cl.expl && !b .expl then .err "import"
  else if b .blk && b .inh then .err "ambiguous"
  else if b .blk && b .expl then .err "ambiguous"
  else if b .blk && pin then .err "ambiguous"
  else if pin then .ok (if b .inh then .inh else .pobj)
  else if !b .blk && !b .inh && !b .expl && b .wild && b .wpkg then .err "ambiguous"
  else
    -- Scala 2 looks in the package object before the package's own classes
    let vis := if v == .s2 then
        (vis.filter (· != .inner)).flatMap fun s => if s == .pobj then [.pobj, .inner] else [s]
      else vis
    match vis.find? b with
    | some s => .ok s
    | none => .err "not found"

/-- What Zinc stores of a class's API, for the rules that diff a class's names: develop's, with
the inherited members (`mkStructureWithInherited`; Scala 3's bridge takes all bases); retronym/zinc#24's
(Merkle), declarations only; or #24's with each class's names composed from its own and its
ancestors' stored names (`MerkleHashes.composed`, over the stored linearization). Today's member-ref
invalidation is the same under all three: #24 walks the descendants of a changed class and checks
their member-ref dependents' used names against the ancestor's changed names. -/
inductive Api | full | decls | composed
  deriving DecidableEq, Repr

/-- How far a rule on names or implicits reaches: every user of the name, or every class
(`global`, as #34 does); or only the classes of the package where the binding changed and of the
packages nested in it, and (with `imports`, a bridge change) those that record a wildcard import of
that package (`narrowed`). `NamesSpec.lean` proves the narrowed rules sound only with the recorded
import. -/
inductive Reach | global | narrowed
  deriving DecidableEq, Repr

/-- The extensions of retronym/zinc#34, each a rule run after every cycle.

* `cheap`: #34, the users of the simple name of an added top-level class.
* `f2`: the users of a name that a package object (`a.b.package`, Scala 3's `F$package`) gained.
* `f3`: an import's change checked against the used names of every class of the importing file,
  not only the class it is charged to.
* `g`: when a package object or `$package` class gains or loses an implicit (or is a new class with
  one), the classes of its package and the packages nested in it (`Givens.lean`). -/
structure Rules where
  api : Api := .full
  reach : Reach := .global
  imports : Bool := false
  cheap : Bool := false
  f2 : Bool := false
  f3 : Bool := false
  g : Bool := false
  deriving DecidableEq, Repr

/-- Does a name diff of a package object see a member it inherits? Develop stores it; #24 stores
declarations only, so without composition it never appears (`NamesSpec.decls_violates_abstraction`). -/
def Rules.seesInherited (r : Rules) : Bool := r.api != .decls

/-- Does a package-scoped rule, for a binding changed in slot `s`'s package, reach the client? The
enclosing packages always; package `a.q` only through the wildcard import, when recorded. -/
def Rules.reachesClient (r : Rules) (c : Client) (s : Slot) : Bool :=
  r.reach == .global || s != .wpkg || r.imports

/-- Which extractor or invalidation rule. -/
inductive Mode
  /-- Zinc today. -/
  | today
  /-- Record every scope the lookup searched, misses included. -/
  | searched
  /-- When a binding of a name is added or removed, invalidate the users of the name. -/
  | names
  /-- Zinc today, and after each cycle the users of the simple name of a top-level class the cycle
  added (`invalidateByAddedClasses`, retronym/zinc#34). -/
  | cheap
  /-- Zinc today, with the extensions of #34 that `Rules` selects. -/
  | rules (r : Rules)
  deriving DecidableEq, Repr

/-- A mode from `+`-separated tokens: `today`, `cheap`, `searched`, `names`, or rules from `cheap`,
`f2`, `f3`, `g` (`all` for the four), `decls` or `composed` for #24's API, `narrowed` and
`imports` for the narrowed rules with recorded package imports; e.g. `all+narrowed+imports`. -/
def Mode.parse (s : String) : Option Mode :=
  let ts := s.splitOn "+"
  match ts with
  | ["today"] => some .today
  | ["cheap"] => some .cheap
  | ["searched"] => some .searched
  | ["names"] => some .names
  | _ => ts.foldlM (init := .rules {}) fun m t =>
    match m, t with
    | .rules r, "cheap" => some (.rules { r with cheap := true })
    | .rules r, "f2" => some (.rules { r with f2 := true })
    | .rules r, "f3" => some (.rules { r with f3 := true })
    | .rules r, "g" => some (.rules { r with g := true })
    | .rules r, "all" => some (.rules { r with cheap := true, f2 := true, f3 := true, g := true })
    | .rules r, "decls" => some (.rules { r with api := .decls })
    | .rules r, "composed" => some (.rules { r with api := .composed })
    | .rules r, "narrowed" => some (.rules { r with reach := .narrowed })
    | .rules r, "imports" => some (.rules { r with imports := true })
    | _, _ => none

/-- The rules of a mode built on Zinc's invalidation (`searched` and `names` are not). -/
def Mode.toRules : Mode → Rules
  | .cheap => { cheap := true }
  | .rules r => r
  | _ => {}

/-- The slots whose binding of the name changed. -/
def changed (p p' : Prog) : List Slot :=
  (present p.cl).filter fun s => p.binds s != p'.binds s

/-- Scala 2's bridge names a class by `fullName`, which skips `package`: to Zinc, `package object b`'s
declared `object Foo` and the class `a.b.Foo` have one class name, `a.b.Foo`. A client that resolved
either depends on that name, so a change to either file's `Foo` invalidates it; and a class `a.b.Foo`
added beside the member is no new class name to #34 (seen on the harness). -/
def aliased (v : Ver) (p : Prog) : Bool := v == .s2 && !p.cl.pinh && (present p.cl).contains .pobj

/-- Does Zinc invalidate the client's file when slot `s` changed, given what the client resolved
before (`r`)? -/
def invalidates (rs : Rules) (v : Ver) (p : Prog) (r : Res) (s : Slot) : Bool :=
  match s with
  -- inheritance edge
  | .inh => true
  -- `V` is the block import's qualifier: an edge from `Client`, which uses `Foo`
  | .blk => true
  -- `X` and the selector's name `Foo`, both charged to the first class of the file
  | .expl => true
  -- `W` is charged to the first class (Scala 3: the last); it uses `Foo` if it is the client, or if
  -- the explicit import's selector is charged to it too; otherwise only a client that resolved
  -- through `W` has its own edge to `W`; with `f3`, the client's file has a class that uses it.
  -- `W`'s changed names include an inherited one (develop stores it; #24 walks `WT`'s descendants)
  | .wild => rs.f3 || !p.cl.first || p.cl.expl || r == .ok .wild
  -- the package object is reached only through the resolved symbol, or the name it shares with
  -- `a.b.Foo` (Scala 2); Scala 3 records a dependency on an inherited member it saw and passed over
  -- for the class `a.b.Foo` (seen on the harness)
  | .pobj => r == .ok .pobj || (aliased v p && r == .ok .inner) ||
      (v == .s3 && p.cl.pinh && r == .ok .inner && p.st .pobj == .foo)
  -- a top-level class: only a deleted class's dependents are invalidated
  | .inner => r == .ok .inner && p.st .inner == .foo || (aliased v p && r == .ok .pobj)
  | .wpkg | .outer => r == .ok s && p.st s == .foo
  | .lib => false

/-- Does the edit add a top-level class named as the client's name? A class is added when its
fully qualified name is new: added, renamed to the name (`unrename`), or moved to another package.
A package object is never one (`invalidateByAddedClasses` drops the name `package`), nor is a
member of an object. The client uses its name, so `invalidateByAddedClasses` invalidates it. -/
def addsClass (rs : Rules) (v : Ver) (p p' : Prog) : Bool :=
  (present p.cl).any fun s => s.topLevel && p.st s != .foo && p'.st s == .foo &&
    !(s == .inner && aliased v p && p.st .pobj == .foo) && rs.reachesClient p.cl s

/-- Does a rule diffing the package object's names see it gain the client's name? Scala 2's
`package object b`, Scala 3's `package object b` or the `PObj$package` class holding the top-level
export (its forwarder is a declaration, recompiled in the cycle after `a.U2`). -/
def pobjGains (rs : Rules) (p p' : Prog) : Bool :=
  (present p.cl).contains .pobj && p.st .pobj != .foo && p'.st .pobj == .foo &&
    (!p.cl.pinh || rs.seesInherited)

def recompiles (m : Mode) (v : Ver) (p p' : Prog) : Bool :=
  let r := resolve v p
  match m with
  | .searched => (changed p p').any (visible p.cl).contains
  | .names => !(changed p p').isEmpty
  | m =>
    let rs := m.toRules
    (changed p p').any (invalidates rs v p r) || (rs.cheap && addsClass rs v p p') ||
      (rs.f2 && pobjGains rs p p')

/-- The verdict of an edit: the client's resolution before, after, whether Zinc recompiles it,
and whether the incremental build equals the clean one. -/
structure Verdict where
  before : Res
  after : Res
  recompiled : Bool
  clean : Bool
  deriving DecidableEq, Repr

/-- Scala 2 lets `package object b` hold an `object Foo` (declared or inherited) beside a class
`a.b.Foo`, and the class's mirror (`a/b/Foo.class`) comes out without its `ScalaSignature` when the
package object's member is compiled with it. An edit of the member leaves the class's file alone,
and its mirror as it was. Adding the member leaves a mirror with the signature (bytes only);
removing it leaves one without, and a client that now resolves `a.b.Foo` fails to compile
(`not found: value Foo`) where a clean build succeeds. In this space only an inherited member
reaches the removal (a declared one clashes in Scala 3, so no base has both), but a declared one
fails the same way (probed with `scalac`). -/
def staleMirror (v : Ver) (p p' : Prog) : Bool :=
  v == .s2 && (p.st .pobj == .foo) != (p'.st .pobj == .foo) && p.st .inner == .foo && p'.st .inner == .foo

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

/-- F6 for `W` (Scala 3): `object W extends a.WT`, and `WT` gains `object Foo`, its only member.
Zinc recompiles `W` in the cycle after `WT`, apart from it, and `W` loses the call to `WT.$init$`
that a clean build emits (seen on the harness). -/
def heirInit (v : Ver) (p p' : Prog) : Bool :=
  v == .s3 && p.cl.winh && p.st .wild != .foo && p'.st .wild == .foo

/-- Scala 3 compiles `object a.b.Foo` jointly with `package object b extends a.PT`, where `PT` has an
`object Foo`, into a `writeReplace` that serialises `a.PT$Foo$`, the inherited member, instead of
`a.b.Foo$`; compiled apart, it is right (probed with `scala-cli`, 3.3). The incremental build keeps the
base's `Foo$.class` unless the edit is to `Inner.scala`, which it then compiles alone. -/
def staleModule (v : Ver) (p p' : Prog) : Bool :=
  let wrong (q : Prog) := q.st .pobj == .foo && q.st .inner == .foo
  let incWrong := p.st .inner == p'.st .inner && wrong p
  v == .s3 && p.cl.pinh && incWrong != wrong p'

/-- The divergences that are not about the client's resolution. -/
def besideResolution (v : Ver) (p p' : Prog) : Bool :=
  staleMirror v p p' || missedClash v p' ||
    ((heirInit v p p' || staleModule v p p') && resolve v p' matches .ok _)

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
                        -- inherited members: in the package object (when the client sees it) or in
                        -- `W`; the export already gets them from elsewhere
                        for pinh in [false, true] do
                          if !pinh || (pkg != .top && !exp) then
                            for winh in [false, true] do
                              if !winh || (wild && !exp) then
                                out := out ++ [⟨pkg, blk, inh, expl, wild, wpkg, first, opt, exp, pinh, winh⟩]
  return out

/-- Assignments of states to the given slots, with at most `k` slots holding the name. -/
def assigns : List Slot → Nat → List (List (Slot × St))
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

def cl0 : Client := ⟨.nested, false, false, false, false, false, false, false, false, false, false⟩

/-- **Inner package** (retronym/zinc#32): `a.b.Foo` added over `a.Foo`. -/
def innerBase : Prog := mkProg cl0 [(.outer, .foo)]

/-- `inner_added_today`. -/
example :
    verdict .today .s2 innerBase (innerBase.set .inner .foo) = ⟨.ok .outer, .ok .inner, false, false⟩ := by
  native_decide

/-- `inner_added_searched`. -/
example :
    (verdict .searched .s2 innerBase (innerBase.set .inner .foo)).clean = true := by native_decide

/-- `pobj_added_today`: **Package object**: `Foo` added to `package object b` over `a.Foo`. The client reached the
package object through no symbol. -/
example :
    verdict .today .s3 innerBase (innerBase.set .pobj .foo) = ⟨.ok .outer, .ok .pobj, false, false⟩ := by
  native_decide

/-- **Top-level export** (Scala 3): `export a.U2.*` in package `a.b`, and `a.U2` gains `Foo`. Zinc
recompiles the exporting file (the wildcard export records an inheritance edge), whose new
forwarder shadows `a.Foo`, but the client has no edge to it: the package object's case. -/
def expBase : Prog := mkProg { cl0 with exp := true } [(.outer, .foo)]

/-- `export_added_today`. -/
example :
    verdict .today .s3 expBase (expBase.set .pobj .foo) = ⟨.ok .outer, .ok .pobj, false, false⟩ := by
  native_decide

/-- **Wildcard import, another class**: `Foo` added to `object W` over `a.Foo`, the import charged to
`First`, which does not use `Foo`. -/
def wildBase : Prog := mkProg { cl0 with wild := true, first := true } [(.outer, .foo)]

/-- `wild_first_today`. -/
example :
    verdict .today .s2 wildBase (wildBase.set .wild .foo) = ⟨.ok .outer, .ok .wild, false, false⟩ := by
  native_decide

/-- `wild_client_today`: Without `First` the client is charged with the import, and uses `Foo`. -/
example :
    (verdict .today .s2 { wildBase with cl := { wildBase.cl with first := false } }
      (({ wildBase with cl := { wildBase.cl with first := false } }).set .wild .foo)).clean = true := by
  native_decide

/-- `inner_added_cheap`: The cheap fix (retronym/zinc#34) on the inner package: the added `a.b.Foo` invalidates the
client, which uses `Foo`. -/
example :
    verdict .cheap .s2 innerBase (innerBase.set .inner .foo) = ⟨.ok .outer, .ok .inner, true, true⟩ := by
  native_decide

/-- `pobj_added_cheap`: It misses the package object and the wildcard-imported object: neither adds a class. -/
example :
    verdict .cheap .s3 innerBase (innerBase.set .pobj .foo) = ⟨.ok .outer, .ok .pobj, false, false⟩ := by
  native_decide

/-- `export_added_cheap`. -/
example :
    verdict .cheap .s3 expBase (expBase.set .pobj .foo) = ⟨.ok .outer, .ok .pobj, false, false⟩ := by
  native_decide

/-- `wild_first_cheap`. -/
example :
    verdict .cheap .s2 wildBase (wildBase.set .wild .foo) = ⟨.ok .outer, .ok .wild, false, false⟩ := by
  native_decide

/-- Is every edit of the space clean in both versions under a mode, but for the divergences beside
the client's resolution (the stale mirror, the missed clash) and the trait initialiser? -/
def cleanOn (m : Mode) : Bool := bases.all fun p => (edits p).all fun (_, p') =>
  [Ver.s2, .s3].all fun v => (verdict m v p p').clean || besideResolution v p p' ||
    separateInit v p' (recompiles m v p p')

/-! ## Extending #34: a rule per family

Each rule closes its family and nothing else; together, on develop's API, they are clean on the
whole space. -/

/-- The edits a mode gets wrong, but for the divergences beside resolution and the trait initialiser. -/
def wrong (m : Mode) (v : Ver) (p p' : Prog) : Bool :=
  !(verdict m v p p').clean && !besideResolution v p p' && !separateInit v p' (recompiles m v p p')

/-- The families by edit: F1 adds a top-level class, F2 a member of the package object (or the
export's forwarder), F3 a member of `W` (or the forwarder `W` exports). -/
def f1 (p p' : Prog) : Bool := (present p.cl).any fun s => s.topLevel && p.st s != .foo && p'.st s == .foo
def f2 (p p' : Prog) : Bool := (present p.cl).contains .pobj && p.st .pobj != .foo && p'.st .pobj == .foo
def f3 (p p' : Prog) : Bool := p.cl.wild && p.st .wild != .foo && p'.st .wild == .foo

/-- #34 with both: clean on the whole space, on develop's API. -/
def allRules : Rules := { cheap := true, f2 := true, f3 := true, g := true }

/-- The family of an unclean edit, as the dump reports it: the divergences beside resolution first. -/
def family (m : Mode) (v : Ver) (p p' : Prog) : String :=
  if (verdict m v p p').clean then "-"
  else if staleMirror v p p' then "F4"
  else if missedClash v p' then "F5"
  else if separateInit v p' (recompiles m v p p') || besideResolution v p p' && heirInit v p p' then "F6"
  else if staleModule v p p' then "F7"
  else if f1 p p' then "F1" else if f2 p p' then "F2" else if f3 p p' then "F3" else "?"

/-! ### Declarations only (retronym/zinc#24) -/

/-- `package object b extends a.PT`, over `a.Foo`, and `a.PT` gains `Foo`. -/
def pinhBase : Prog := mkProg { cl0 with pinh := true } [(.outer, .foo)]

/-- `pobj_inherited_today`: Today misses it as it misses a declared member. -/
example :
    verdict .today .s2 pinhBase (pinhBase.set .pobj .foo) = ⟨.ok .outer, .ok .pobj, false, false⟩ := by
  native_decide

/-- `pobj_inherited_f2`: On develop the F2 rule sees the inherited member in the package object's stored API. -/
example :
    (verdict (.rules allRules) .s2 pinhBase (pinhBase.set .pobj .foo)).clean = true := by native_decide

/-- `pobj_inherited_decls`: #24 stores the package object's declarations only, and it declares nothing: the rule sees no
new name. -/
example :
    verdict (.rules { allRules with api := .decls }) .s2 pinhBase (pinhBase.set .pobj .foo) =
      ⟨.ok .outer, .ok .pobj, false, false⟩ := by native_decide

/-- `pobj_inherited_composed`: Composed from the ancestors, against the run's baseline: clean. -/
example :
    (verdict (.rules { allRules with api := .composed }) .s2 pinhBase (pinhBase.set .pobj .foo)).clean = true := by
  native_decide

/-! ## Cost

What a mode recompiles beyond the edited files and the classes that inherit from them (which every
mode recompiles): the client's file, and a class elsewhere that uses the name, `c.User`
(`a.Y.Foo`), standing for every user of the name in the build. The client's file is necessary
when its resolution changes or it extends the edited trait; `User` never is. -/

def necessary (v : Ver) (p p' : Prog) : Bool := resolve v p != resolve v p'

/-- Does the mode recompile `c.User`? The rules on names reach every user of the name. -/
def userRecompiled (m : Mode) (v : Ver) (p p' : Prog) : Bool :=
  match m with
  | .searched => false
  | .names => !(changed p p').isEmpty
  | m =>
    let rs := m.toRules
    rs.reach == .global && ((rs.cheap && addsClass rs v p p') || (rs.f2 && pobjGains rs p p'))

/-- Counts over the space: edits, wrong edits, the client recompiled though not necessary, and
`User` recompiled. -/
structure Cost where
  edits : Nat
  wrong : Nat
  client : Nat
  user : Nat
  deriving Repr

def cost (m : Mode) (v : Ver) : Cost := Id.run do
  let mut c : Cost := ⟨0, 0, 0, 0⟩
  for p in bases.filter (fun p => v == .s3 || !p.cl.exp) do
    for (_, p') in edits p do
      let rc := recompiles m v p p'
      c := ⟨c.edits + 1, c.wrong + (if wrong m v p p' then 1 else 0),
        c.client + (if rc && !necessary v p p' then 1 else 0),
        c.user + (if userRecompiled m v p p' then 1 else 0)⟩
  return c

end Zinc.Names

/-! ## Rendering as Scala sources -/

namespace Zinc.Names

def Prog.name (p : Prog) : String := if p.cl.opt then "Option" else "Foo"

/-- The file of each slot, and its source; `none` when the file does not exist. -/
def slotFile (p : Prog) : Slot → String
  | .blk => "V.scala" | .inh => "P.scala" | .expl => "X.scala"
  | .wild => if p.cl.exp then "U.scala" else if p.cl.winh then "WT.scala" else "W.scala"
  | .wpkg => "Q.scala" | .inner => "Inner.scala"
  | .pobj => if p.cl.exp then "U2.scala" else if p.cl.pinh then "PT.scala" else "PObj.scala"
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
  | .wild => some ((if p.cl.exp then "package a\n\nobject U" else if p.cl.winh then "package a\n\ntrait WT"
      else "package a\n\nobject W") ++ member p .wild)
  | .pobj => some ((if p.cl.exp then "package a\n\nobject U2" else if p.cl.pinh then "package a\n\ntrait PT"
      else "package a\n\npackage object b") ++ member p .pobj)
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

/-- The program's files. `Other.scala` keeps package `a.q` in existence for its import; `c.User`
uses the name elsewhere, through `a.Y`, which no edit touches. -/
def files (v : Ver) (p : Prog) : List (String × String) :=
  [("Client.scala", clientSrc v p),
   ("Y.scala", "package a\n\nobject Y {\n  object " ++ p.name ++ "\n}\n"),
   ("User.scala", "package c\n\nobject User {\n  val use: Any = a.Y." ++ p.name ++ "\n}\n")] ++
  (if p.cl.winh then [("W.scala", "package a\n\nobject W extends a.WT\n")] else []) ++
  (if p.cl.pinh then [("PObj.scala", "package a\n\npackage object b extends a.PT\n")] else []) ++
  (if p.cl.wpkg then [("Other.scala", "package a.q\n\nobject Other\n")] else []) ++
  (if p.cl.exp && p.cl.wild then [("W.scala", "package a\n\nobject W {\n  export a.U.*\n}\n")] else []) ++
  (if p.cl.exp && p.cl.pkg != .top then [("PObj.scala", "package a.b\n\nexport a.U2.*\n")] else []) ++
  ((present p.cl).filter (· != .lib)).filterMap fun s => (slotSrc p s).map (slotFile p s, ·)

/-- The files an edit changes: a new source, or `none` to delete it. -/
def fileEdits (p p' : Prog) : List (String × Option String) :=
  ((present p.cl).filter (· != .lib)).filterMap fun s =>
    if slotSrc p s == slotSrc p' s then none else some (slotFile p s, slotSrc p' s)

end Zinc.Names
