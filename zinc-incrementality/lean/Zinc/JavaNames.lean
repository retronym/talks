import Mathlib.Data.List.Basic

/-!
# Name resolution with Java sources

`Names.lean` with every binding a Java source, and the client in Java or in Scala. The client's
simple name `Foo` (or `Process`, with `java.lang.Process` as the last resort) can be bound by

```java
package a.b;                      // or `package a;`
import static a.W.*;              // optional (Scala: `import a.W._`)
import a.q.*;                     // optional (Scala: `import a.q._`)
import static a.X.Foo;            // optional (Scala: `import a.X.Foo`); `X` always has a static method `Foo`
public class Client implements a.P {   // `implements` optional, Java only
  public static Object use() { return Foo.class; }   // Scala: `object Client { val use: Any = classOf[Foo] }`
}
```

* `inh`: a member class of interface `a.P` (Java only: Scala does not inherit Java member classes);
* `expl`: a static member class of `a.X`, through the single-static import;
* `wild`: a static member class of `a.W`, through the static on-demand import;
* `wpkg`: a class in package `a.q`, through the on-demand import;
* `inner`: a class in package `a.b`, `outer`: a class in package `a` (the client's package, or not
  visible: Java has no nesting of packages, and Scala's `package a.b` does not see `a`);
* `lib`: `java.lang.Process`.

Java's rules (JLS 6.4.1, 7.5), probed with javac 21: member types of the class and its supertypes,
then the single imports, then the package's types, then the on-demand imports and `java.lang`
together, where two bindings are an ambiguity error. Scala's are `Names.lean`'s, over Java statics
as companion members: the explicit import, then the wildcard imports (two that bind are ambiguous),
then the package, then the root imports. An import of `X.Foo` binds no type when `X` has only the
method `Foo`, in both languages.

Zinc's Java side (`JavaAnalyze`, `ClassToAPI`): a member-ref edge to every class in the classfile's
constant pool and to their ancestors (sbt/zinc#148), an inheritance edge to each parent. An import
leaves nothing in the classfile, so it records nothing; a member class the client resolved brings
its outer class into the constant pool (`InnerClasses`). A Java class has no used names, so it is
invalidated by any API change of a class it depends on, and retronym/zinc#34 (the users of an added
class's simple name) never reaches it. With `pipelining` on, Zinc compiles every Java source in
every cycle, which hides every Java client's miss.
-/

namespace Zinc.JavaNames

inductive Lang | java | s2 | s3
  deriving DecidableEq, Repr

inductive Slot | inh | expl | wild | wpkg | inner | outer | lib
  deriving DecidableEq, Repr

def Slot.topLevel : Slot → Bool
  | .wpkg | .inner | .outer => true
  | _ => false

def Slot.str : Slot → String
  | .inh => "inh" | .expl => "expl" | .wild => "wild" | .wpkg => "wpkg" | .inner => "inner"
  | .outer => "outer" | .lib => "lib"

/-- The client's package: `a.b` or `a`. -/
inductive Pkg | sub | top
  deriving DecidableEq, Repr

def Pkg.str : Pkg → String | .sub => "a.b" | .top => "a"

structure Client where
  pkg : Pkg
  inh : Bool
  expl : Bool
  wild : Bool
  wpkg : Bool
  /-- The name is `Process`, so `java.lang.Process` binds it when nothing else does. -/
  opt : Bool
  deriving DecidableEq, Repr

inductive St | none | foo | bar
  deriving DecidableEq, Repr

structure Prog where
  cl : Client
  st : Slot → St

/-- The client's own package. -/
def same (c : Client) : Slot := if c.pkg == .sub then .inner else .outer

/-- The slots in scope for a client, innermost first. -/
def visible (l : Lang) (c : Client) : List Slot :=
  (if c.inh && l == .java then [.inh] else []) ++ (if c.expl then [.expl] else []) ++
  (if l == .java then [same c] else []) ++
  (if c.wild then [.wild] else []) ++ (if c.wpkg then [.wpkg] else []) ++
  (if l == .java then [] else [same c]) ++ (if c.opt then [.lib] else [])

/-- The slots that exist: every one the client could see, and both packages, for moves. -/
def present (c : Client) : List Slot :=
  (if c.inh then [.inh] else []) ++ (if c.expl then [.expl] else []) ++
  (if c.wild then [.wild] else []) ++ (if c.wpkg then [.wpkg] else []) ++ [.inner, .outer] ++
  (if c.opt then [.lib] else [])

def Prog.binds (p : Prog) (s : Slot) : Bool := s == .lib || p.st s == .foo

inductive Res
  | ok (s : Slot)
  | err (why : String)
  deriving DecidableEq, Repr

def Res.str : Res → String | .ok s => s.str | .err w => "error (" ++ w ++ ")"

def resolve (l : Lang) (p : Prog) : Res :=
  let c := p.cl
  let b := fun s => (visible l c).contains s && p.binds s
  if l == .java then
    if b .inh then .ok .inh
    else if b .expl then .ok .expl
    else if b (same c) then .ok (same c)
    else
      match [Slot.wpkg, .wild, .lib].filter b with
      | [] => .err "not found"
      | [s] => .ok s
      | _ => .err "ambiguous"
  else
    if b .expl then .ok .expl
    else if b .wild && b .wpkg then .err "ambiguous"
    else match [Slot.wild, .wpkg, same c, .lib].find? b with
      | some s => .ok s
      | none => .err "not found"

inductive Mode
  /-- Zinc today. -/
  | today
  /-- retronym/zinc#34: after each cycle, the users of an added top-level class's simple name. -/
  | cheap
  /-- #34, with a Java class's used names recorded (so #34 reaches Java clients) and an edge from a
  static import to its class. -/
  | fix
  deriving DecidableEq, Repr

/-- Does the client record the used name `Foo`? Scala 2's bridge records no used name for the type
in `classOf[Foo]` (`ExtractUsedNames` skips the literal; `Dependency` records the class), so only the
explicit import's selector names it. Scala 3 and the Java fix record it. -/
def usesName (l : Lang) (c : Client) : Bool := l != .s2 || c.expl

def changed (p p' : Prog) : List Slot :=
  (present p.cl).filter fun s => p.binds s != p'.binds s

/-- Does Zinc invalidate the client when slot `s` changed, given what it resolved before? -/
def invalidates (m : Mode) (l : Lang) (p : Prog) (r : Res) (s : Slot) : Bool :=
  match s with
  -- the inheritance edge to `P`, whose API has `Foo` as a member class
  | .inh => true
  -- Scala: the import's qualifier, charged to the client, filtered by the used name. Java: no edge
  -- from an import; the outer class of a resolved member class is in the constant pool, and a Java
  -- dependent is not filtered by name.
  | .expl | .wild => if l == .java then m == .fix || r == .ok s else usesName l p.cl
  -- the dependents of a deleted class
  | .wpkg | .inner | .outer => r == .ok s && p.st s == .foo
  | .lib => false

def addsClass (p p' : Prog) : Bool :=
  (present p.cl).any fun s => s.topLevel && p.st s != .foo && p'.st s == .foo

def recompiles (m : Mode) (pipe : Bool) (l : Lang) (p p' : Prog) : Bool :=
  let r := resolve l p
  (pipe && l == .java) || (changed p p').any (invalidates m l p r) ||
    (m != .today && (l != .java || m == .fix) && usesName l p.cl && addsClass p p')

structure Verdict where
  before : Res
  after : Res
  recompiled : Bool
  clean : Bool
  deriving DecidableEq, Repr

def verdict (m : Mode) (pipe : Bool) (l : Lang) (p p' : Prog) : Verdict :=
  let r := resolve l p
  let r' := resolve l p'
  let rc := recompiles m pipe l p p'
  ⟨r, r', rc, rc || r == r'⟩

/-! ## The program space -/

def Prog.set (p : Prog) (s : Slot) (x : St) : Prog :=
  { p with st := fun t => if t == s then x else p.st t }

def states (s : Slot) : List St := if s.topLevel then [.none, .foo, .bar] else [.none, .foo]

def clients (l : Lang) : List Client := Id.run do
  let mut out := []
  for pkg in [Pkg.sub, .top] do
    for inh in (if l == .java then [false, true] else [false]) do
      for expl in [false, true] do
        for wild in [false, true] do
          for wpkg in [false, true] do
            for opt in [false, true] do
              out := out ++ [⟨pkg, inh, expl, wild, wpkg, opt⟩]
  return out

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

/-- Every client and every assignment with at most two bindings (besides `java.lang`) whose
resolution compiles. -/
def bases (l : Lang) : List Prog :=
  (clients l).flatMap fun c =>
    (assigns ((present c).filter (· != .lib)) 2).filterMap fun a =>
      let p := mkProg c a
      if resolve l p matches .ok _ then some p else none

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

def cl0 : Client := ⟨.sub, false, false, false, false, false⟩

/-- **J1, a class added to the client's package** over an on-demand import: `a.b.Foo` shadows
`a.q.Foo` for a Java client. Zinc compiles the new source alone. -/
def j1Base : Prog := mkProg { cl0 with wpkg := true } [(.wpkg, .foo)]

theorem j1_today :
    verdict .today false .java j1Base (j1Base.set .inner .foo) = ⟨.ok .wpkg, .ok .inner, false, false⟩ := by
  native_decide

/-- The same for a Scala client, where the wildcard import wins: `a.q.Foo` added over `a.b.Foo`. -/
def j1sBase : Prog := mkProg { cl0 with wpkg := true } [(.inner, .foo)]

theorem j1s_today : [Lang.s2, .s3].all (fun l =>
    verdict .today false l j1sBase (j1sBase.set .wpkg .foo) == ⟨.ok .inner, .ok .wpkg, false, false⟩) := by
  native_decide

/-- #34 fires for a class added in a Java source, so a Scala client is invalidated (it uses `Foo`);
a Java client records no used names, and #34 does not reach it. -/
theorem j1_cheap :
    verdict .cheap false .java j1Base (j1Base.set .inner .foo) = ⟨.ok .wpkg, .ok .inner, false, false⟩ ∧
    verdict .cheap false .s3 j1sBase (j1sBase.set .wpkg .foo) = ⟨.ok .inner, .ok .wpkg, true, true⟩ := by
  native_decide

/-- **N1, Scala 2's `classOf`**: the bridge records the class of `classOf[Foo]` but not the name, so
a name-filtered invalidation skips the client: here #34, and `W.Foo` deleted from a wildcard-imported
object the client resolved through. -/
def n1Base : Prog := mkProg { cl0 with wild := true } [(.wild, .foo), (.inner, .foo)]

theorem n1 :
    verdict .cheap false .s2 j1sBase (j1sBase.set .wpkg .foo) = ⟨.ok .inner, .ok .wpkg, false, false⟩ ∧
    verdict .today false .s2 n1Base (n1Base.set .wild .none) = ⟨.ok .wild, .ok .inner, false, false⟩ ∧
    (verdict .today false .s3 n1Base (n1Base.set .wild .none)).clean = true := by
  native_decide

/-- With pipelining, Zinc compiles every Java source in every cycle. -/
theorem j1_pipe : (verdict .today true .java j1Base (j1Base.set .inner .foo)).clean = true := by
  native_decide

/-- **J2, a member class added behind a static import**: `X.Foo` over `a.b.Foo`, through
`import static a.X.Foo` (`X` had only the method `Foo`). The import leaves no trace in the Java
client's classfile; a Scala client's import records `X` and the name. -/
def j2Base : Prog := mkProg { cl0 with expl := true } [(.inner, .foo)]

theorem j2 :
    verdict .today false .java j2Base (j2Base.set .expl .foo) = ⟨.ok .inner, .ok .expl, false, false⟩ ∧
    verdict .cheap false .java j2Base (j2Base.set .expl .foo) = ⟨.ok .inner, .ok .expl, false, false⟩ ∧
    verdict .today false .s2 j2Base (j2Base.set .expl .foo) = ⟨.ok .inner, .ok .expl, true, true⟩ := by
  native_decide

/-- **J3, an ambiguity added by an on-demand import**: `W.Foo` added beside `a.q.Foo`, or `a.q.Process`
beside `java.lang.Process`. Java reports an ambiguity; Zinc compiles `W` or the new source alone. -/
def j3Base : Prog := mkProg { cl0 with wild := true, wpkg := true } [(.wpkg, .foo)]

theorem j3 :
    verdict .today false .java j3Base (j3Base.set .wild .foo) = ⟨.ok .wpkg, .err "ambiguous", false, false⟩ := by
  native_decide

def j3libBase : Prog := mkProg { cl0 with wpkg := true, opt := true } []

theorem j3_lib :
    verdict .cheap false .java j3libBase (j3libBase.set .wpkg .foo) =
      ⟨.ok .lib, .err "ambiguous", false, false⟩ := by
  native_decide

/-- A member class added to `P` reaches a Java client through its inheritance edge. -/
theorem inh_today :
    (verdict .today false .java (mkProg { cl0 with inh := true } [(.inner, .foo)])
      ((mkProg { cl0 with inh := true } [(.inner, .foo)]).set .inh .foo)).clean = true := by
  native_decide

/-- The fix (Java used names for #34, an edge from a static import to its class) is clean on the
whole space for Java and Scala 3 clients; #34 alone is clean for Scala 3 clients. Scala 2's are clean
when they name `Foo` in a way the bridge records (here, with the explicit import). -/
theorem fix_clean : [Lang.java, .s3].all (fun l => (bases l).all fun p => (edits p).all fun (_, p') =>
    (verdict .fix false l p p').clean) = true := by
  native_decide

theorem cheap_clean_scala : [Lang.s2, .s3].all (fun l => (bases l).all fun p => (edits p).all fun (_, p') =>
    !usesName l p.cl || (verdict .cheap false l p p').clean) = true := by
  native_decide

end Zinc.JavaNames

/-! ## Rendering as Java and Scala sources -/

namespace Zinc.JavaNames

def Prog.name (p : Prog) : String := if p.cl.opt then "Process" else "Foo"

def jdir : String := "src/main/java/"

def member (p : Prog) (s : Slot) (mods : String) : String :=
  if p.st s == .foo then "  " ++ mods ++ "class " ++ p.name ++ " {}\n" else ""

def pkgDir : Slot → String | .wpkg => "a/q/" | .inner => "a/b/" | _ => "a/"

def pkgName : Slot → String | .wpkg => "a.q" | .inner => "a.b" | _ => "a"

/-- The files of each slot: a member class's container, or a top-level class in a file of its
name. -/
def slotFiles (p : Prog) : Slot → List (String × String)
  | .inh => [(jdir ++ "a/P.java", "package a;\n\npublic interface P {\n" ++ member p .inh "" ++ "}\n")]
  | .expl => [(jdir ++ "a/X.java", "package a;\n\npublic class X {\n  public static void " ++ p.name ++
      "() {}\n" ++ member p .expl "public static " ++ "}\n")]
  | .wild => [(jdir ++ "a/W.java", "package a;\n\npublic class W {\n" ++ member p .wild "public static " ++ "}\n")]
  | .lib => []
  | s => match p.st s with
    | .none => []
    | .foo => [(jdir ++ pkgDir s ++ p.name ++ ".java", "package " ++ pkgName s ++ ";\n\npublic class " ++ p.name ++ " {}\n")]
    | .bar => [(jdir ++ pkgDir s ++ "Bar.java", "package " ++ pkgName s ++ ";\n\npublic class Bar {}\n")]

def clientSrc (l : Lang) (p : Prog) : String × String :=
  let c := p.cl
  let pkg := if c.pkg == .sub then "a.b" else "a"
  if l == .java then
    let imps := (if c.wild then "import static a.W.*;\n" else "") ++ (if c.wpkg then "import a.q.*;\n" else "") ++
      (if c.expl then "import static a.X." ++ p.name ++ ";\n" else "")
    (jdir ++ (if c.pkg == .sub then "a/b/" else "a/") ++ "Client.java",
      "package " ++ pkg ++ ";\n\n" ++ imps ++ (if imps.isEmpty then "" else "\n") ++
      "public class Client" ++ (if c.inh then " implements a.P" else "") ++
      " {\n  public static Object use() { return " ++ p.name ++ ".class; }\n}\n")
  else
    let imps := (if c.wild then "import a.W._\n" else "") ++ (if c.wpkg then "import a.q._\n" else "") ++
      (if c.expl then "import a.X." ++ p.name ++ "\n" else "")
    ("Client.scala", "package " ++ pkg ++ "\n\n" ++ imps ++ (if imps.isEmpty then "" else "\n") ++
      "object Client {\n  val use: Any = classOf[" ++ p.name ++ "]\n}\n")

def clientClass (l : Lang) (p : Prog) : String :=
  (if p.cl.pkg == .sub then "a/b/Client" else "a/Client") ++ (if l == .java then "" else "$")

def bindingFiles (p : Prog) : List (String × String) :=
  ((present p.cl).filter (· != .lib)).flatMap (slotFiles p)

def files (l : Lang) (p : Prog) : List (String × String) :=
  [clientSrc l p] ++
  (if p.cl.wpkg then [(jdir ++ "a/q/Other.java", "package a.q;\n\npublic class Other {}\n")] else []) ++
  bindingFiles p

/-- The files an edit changes: a new source, or `none` to delete it. -/
def fileEdits (p p' : Prog) : List (String × Option String) :=
  let before := bindingFiles p
  let after := bindingFiles p'
  (after.filter (fun f => !before.contains f)).map (fun (n, s) => (n, some s)) ++
  (before.filter (fun (n, _) => !(after.any (·.1 == n)))).map (fun (n, _) => (n, none))

end Zinc.JavaNames
