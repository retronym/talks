import Zinc.JavaNames

/-!
# Exhaustivity against a Java sealed hierarchy

`Sealed.lean` showed that a hash without the children fails abstraction. Here the hierarchy is
Java source in a mixed build, one level (`S permits A, B`) or two (`S permits A, T`, `T permits B`),
with `permits` written out (a file per class) or inferred from the compilation unit (all in
`S.java`); a Scala hierarchy in one file is the control. The client covers exactly the leaves: a
Java pattern `switch` without `default` (javac: an error when not exhaustive), or a Scala match
compiled with `-Werror` (scalac's warning made an error). Both compilers read the children from the
Java source. An edit adds a leaf `C` under `S` or `T`, or deletes it.

What Zinc sees (develop):

* The Scala bridge hashes a sealed class's *descendants* (`sealedDescendants`, transitively), so a
  leaf added under `T` changes `S`'s API too, and a Scala client, which records the scrutinee's type
  `S` (`PatMatTarget`) and its patterns' classes `A` and `B` but not `T`, is invalidated.
* Without pipelining, a Java class's API is `ClassToAPI`'s, which lists sealed children only for
  enums, so adding `C` changes no API. retronym/zinc#21 reads `getPermittedSubclasses`: the direct
  children only, so a leaf added under `T` changes `T` and not `S`, and a Scala client is missed.
  With pipelining, the API is scalac's view of the Java source (descendants included), and every
  Java source is compiled in every cycle.
* A Java client depends on the classes in its constant pool (`S`, `A`, `B`) and on their ancestors
  (sbt/zinc#148), so on `T`.
-/

namespace Zinc.JavaSealed

open Zinc.JavaNames (Lang)

/-- How the hierarchy is written. -/
inductive Defn
  /-- Java, a file per class, `permits` written out. -/
  | jPermits
  /-- Java, all in `S.java`, `permits` inferred. -/
  | jUnit
  /-- Scala, all in `S.scala`. -/
  | scala
  deriving DecidableEq, Repr

def Defn.str : Defn → String | .jPermits => "permits" | .jUnit => "unit" | .scala => "scala"

/-- `C`'s parent. -/
inductive Par | s | t
  deriving DecidableEq, Repr

def Par.str : Par → String | .s => "S" | .t => "T"

structure Prog where
  defn : Defn
  /-- `S permits A, T; T permits B` rather than `S permits A, B`. -/
  two : Bool
  c : Option Par
  deriving DecidableEq, Repr

inductive Edit
  | add (p : Par)
  | delete
  deriving DecidableEq, Repr

def Edit.str : Edit → String | .add p => "add C " ++ p.str | .delete => "delete C"

inductive Mode
  /-- Zinc today. -/
  | today
  /-- retronym/zinc#21: a Java class's permitted subclasses are its children. -/
  | permits
  /-- #21 with the transitive permitted subclasses, as the Scala bridge hashes descendants. -/
  | desc
  /-- #21, and a change to a sealed class's children also invalidates the users (`PatMatTarget`)
  of its sealed ancestors. -/
  | fix
  deriving DecidableEq, Repr

/-- Java clients only over a Java hierarchy: javac knows no Scala sealed classes. -/
def bases (l : Lang) : List Prog := Id.run do
  let mut out := []
  for defn in (if l == .java then [Defn.jPermits, .jUnit] else [Defn.jPermits, .jUnit, .scala]) do
    for two in [false, true] do
      for c in ([none, some Par.s] ++ (if two then [some Par.t] else [])) do
        out := out ++ [⟨defn, two, c⟩]
  return out

def edits (p : Prog) : List (Edit × Prog) :=
  match p.c with
  | some _ => [(.delete, { p with c := none })]
  | none => ([Par.s] ++ (if p.two then [Par.t] else [])).map fun q => (.add q, { p with c := some q })

/-- Is `S`'s file edited, so that Zinc recompiles `S` and compares its API? -/
def sEdited (p : Prog) (q : Par) : Bool := p.defn != .jPermits || q == .s

/-- Does a parent's API list its children: Scala's always, Java's with pipelining (scalac's view of
the source) or #21. Scala's and scalac's list the descendants, #21's the direct children. -/
def children (m : Mode) (pipe : Bool) (p : Prog) : Bool := p.defn == .scala || pipe || m != .today

def descendants (m : Mode) (pipe : Bool) (p : Prog) : Bool := p.defn == .scala || pipe || m == .desc

/-- Does Zinc recompile the client? -/
def recompiles (m : Mode) (pipe : Bool) (l : Lang) (p : Prog) : Edit → Bool
  -- the client's cases name `C`: the dependents of a removed class
  | .delete => true
  | .add q =>
    -- every client depends on `S`
    let sChanged := sEdited p q && children m pipe p && (q == .s || descendants m pipe p)
    let tChanged := q == .t && children m pipe p
    (l == .java && pipe) || sChanged ||
    -- a Java client depends on `T`, an ancestor of a case's class (sbt/zinc#148)
    (tChanged && (l == .java || m == .fix))

/-- The client covers the leaves it was written against, so after an edit it never compiles (a
case too few, or a case for the deleted `C`), and the incremental build is right iff it recompiles
the client. -/
def clean (m : Mode) (pipe : Bool) (l : Lang) (p : Prog) (e : Edit) : Bool := recompiles m pipe l p e

/-! ## Families, as checked examples -/

/-- **S1** (retronym/zinc#21): a leaf added to a Java `permits`, no pipelining: no API changes. -/
theorem s1 : [Lang.java, .s2, .s3].all (fun l =>
    !clean .today false l ⟨.jPermits, false, none⟩ (.add .s) && clean .permits false l ⟨.jPermits, false, none⟩ (.add .s)) := by
  native_decide

/-- Pipelining hides it: every Java source is compiled, and the API is scalac's, with children. -/
theorem s1_pipe : [Lang.java, .s2, .s3].all (fun l => clean .today true l ⟨.jPermits, false, none⟩ (.add .s)) := by
  native_decide

/-- **S2**: a leaf added under the inner sealed `T`, in a file of its own, misses a Scala client
whatever the mode but the fix: `S`'s file is not edited, so its API is not recomputed, and the client
depends on `S`, not `T`. A Java client depends on `T` as an ancestor of `B`. With `T` in `S`'s file
(Java's inferred `permits`, or a Scala hierarchy) `S`'s API changes when it lists the descendants. -/
theorem s2 :
    [Mode.today, .permits, .desc].all (fun m => [Lang.s2, .s3].all fun l => [false, true].all fun pipe =>
      !clean m pipe l ⟨.jPermits, true, none⟩ (.add .t)) ∧
    clean .permits false .java ⟨.jPermits, true, none⟩ (.add .t) ∧
    !clean .permits false .s2 ⟨.jUnit, true, none⟩ (.add .t) ∧
    clean .desc false .s2 ⟨.jUnit, true, none⟩ (.add .t) ∧
    clean .today false .s2 ⟨.scala, true, none⟩ (.add .t) := by
  native_decide

theorem fix_clean : [Lang.java, .s2, .s3].all (fun l => (bases l).all fun p => (edits p).all fun (e, _) =>
    [false, true].all fun pipe => clean .fix pipe l p e) := by
  native_decide

end Zinc.JavaSealed

/-! ## Rendering -/

namespace Zinc.JavaSealed

open Zinc.JavaNames (Lang)

def jdir : String := "src/main/java/a/"

def leaves (p : Prog) : List String := ["A", "B"] ++ (if p.c.isSome then ["C"] else [])

/-- The leaves under each parent. -/
def under (p : Prog) (q : Par) : List String :=
  (if q == .s then ["A"] ++ (if p.two then [] else ["B"]) else (if p.two then ["B"] else [])) ++
  (if p.c == some q then ["C"] else [])

def parentOf (p : Prog) (x : String) : String :=
  if x == "A" || (x == "B" && !p.two) || (x == "C" && p.c == some .s) then "S" else "T"

def files (p : Prog) : List (String × String) :=
  match p.defn with
  | .jPermits =>
    let sKids := under p .s ++ (if p.two then ["T"] else [])
    [(jdir ++ "S.java", "package a;\n\npublic sealed interface S permits " ++ ", ".intercalate sKids ++ " {}\n")] ++
    (if p.two then [(jdir ++ "T.java", "package a;\n\npublic sealed interface T extends S permits " ++
      ", ".intercalate (under p .t) ++ " {}\n")] else []) ++
    (leaves p).map fun x => (jdir ++ x ++ ".java", "package a;\n\npublic final class " ++ x ++
      " implements " ++ parentOf p x ++ " {}\n")
  | .jUnit =>
    [(jdir ++ "S.java", "package a;\n\npublic sealed interface S {}\n" ++
      (if p.two then "\nsealed interface T extends S {}\n" else "") ++
      String.join ((leaves p).map fun x => "\nfinal class " ++ x ++ " implements " ++ parentOf p x ++ " {}\n"))]
  | .scala =>
    [("S.scala", "package a\n\nsealed trait S\n" ++ (if p.two then "sealed trait T extends S\n" else "") ++
      String.join ((leaves p).map fun x => "final class " ++ x ++ " extends " ++ parentOf p x ++ "\n"))]

def clientSrc (l : Lang) (p : Prog) : String × String :=
  if l == .java then
    (jdir ++ "Client.java", "package a;\n\npublic class Client {\n  public static int f(S s) {\n    return switch (s) {\n" ++
      String.join ((leaves p).zipIdx.map fun (x, i) => "      case " ++ x ++ " x -> " ++ toString i ++ ";\n") ++
      "    };\n  }\n}\n")
  else
    ("Client.scala", "package a\n\nobject Client {\n  def f(s: S): Int = s match {\n" ++
      String.join ((leaves p).zipIdx.map fun (x, i) => "    case _: " ++ x ++ " => " ++ toString i ++ "\n") ++
      "  }\n}\n")

def allFiles (l : Lang) (p : Prog) : List (String × String) := [clientSrc l p] ++ files p

/-- The files an edit changes; the client is written against the base and stays. -/
def fileEdits (p p' : Prog) : List (String × Option String) :=
  let before := files p
  let after := files p'
  (after.filter (fun f => !before.contains f)).map (fun (n, s) => (n, some s)) ++
  (before.filter (fun (n, _) => !(after.any (·.1 == n)))).map (fun (n, _) => (n, none))

end Zinc.JavaSealed
