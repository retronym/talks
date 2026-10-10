/-!
# A typed Scala subset, as the back end sees it

Lowering runs after the typer, so the source is resolved: parents are definitions by name,
applied to at most one type argument, and members carry their signatures. Bodies are opaque;
lowering only needs to know whether a member is concrete. Overloading is out of scope, so a
member is identified by its name.
-/

namespace Scala

/-- scalac 2.12, 2.13, and Scala 3. -/
inductive Dialect | s212 | s213 | s3
  deriving DecidableEq, Repr

/-- Types: base types, a definition's own type parameter `X`, another definition by name. -/
inductive Ty | int | bool | unit | str | obj | tp | ref (d : String)
  deriving DecidableEq, Repr

/-- `X ↦ a`. -/
def Ty.subst (a : Ty) : Ty → Ty
  | .tp => a
  | t => t

inductive Kind | cls | trt | obj | vcls
  deriving DecidableEq, Repr

structure Mem where
  name : String
  params : List Ty := []
  res : Ty
  isVal : Bool := false
  abs : Bool := false
  final : Bool := false
  /-- `lazy val`. -/
  lzy : Bool := false
  /-- Scala 3 `@static`, in an object. -/
  static : Bool := false
  /-- Scala 3 `extension (x: T) def …`: the receiver, an extra first parameter. -/
  ext : Option Ty := none
  deriving DecidableEq, Repr

def Mem.allParams (m : Mem) : List Ty := m.ext.toList ++ m.params

/-- A parent: a definition, applied to a type argument if it has a type parameter. -/
abbrev Parent := String × Option Ty

structure Decl where
  name : String
  kind : Kind := .cls
  abs : Bool := false
  final : Bool := false
  /-- One type parameter `X`. -/
  tparam : Bool := false
  super : Option Parent := none
  traits : List Parent := []
  members : List Mem := []
  /-- A value class's parameter, `class V(val x: U) extends AnyVal`. -/
  under : Option (String × Ty) := none
  deriving DecidableEq, Repr

def Decl.parents (d : Decl) : List Parent := d.super.toList ++ d.traits

/-- A compilation unit: a class or trait and its companion object, either optional. Both have the
unit's name; the object's class is `name$`. -/
structure Src where
  name : String
  cls : Option Decl := none
  obj : Option Decl := none
  deriving DecidableEq, Repr

abbrev Program := List Src

/-! ## Printing as Scala source -/

def Ty.show : Ty → String
  | .int => "Int"
  | .bool => "Boolean"
  | .unit => "Unit"
  | .str => "String"
  | .obj => "Object"
  | .tp => "X"
  | .ref d => d

def Parent.show : Parent → String
  | (p, none) => p
  | (p, some a) => s!"{p}[{a.show}]"

def body : Ty → String
  | .int => "0"
  | .bool => "false"
  | .unit => "()"
  | .str => "\"\""
  | .obj => "null"
  | .tp => "null.asInstanceOf[X]"
  | .ref _ => "???"

def Mem.show (ov : Bool) (m : Mem) : String :=
  let mods := (match m.ext with | some t => s!"extension (self: {t.show}) " | none => "") ++
    (if m.static then "@static " else "") ++ (if ov then "override " else "") ++
    (if m.final then "final " else "") ++ (if m.lzy then "lazy " else "")
  let kw := if m.isVal then "val" else "def"
  let ps := if m.params.isEmpty && m.isVal then ""
    else "(" ++ ", ".intercalate ((m.params.zipIdx.map fun (t, i) => s!"x{i}: {t.show}")) ++ ")"
  let rhs := if m.abs then "" else s!" = {body m.res}"
  s!"{mods}{kw} {m.name}{ps}: {m.res.show}{rhs}"

/-- Print a definition; `ov n` says whether member `n` overrides an inherited one. -/
def Decl.show (ov : String → Bool) (d : Decl) : String :=
  let kw := match d.kind with
    | .trt => "trait" | .obj => "object" | _ => "class"
  let mods := (if d.abs && d.kind == .cls then "abstract " else "") ++ (if d.final then "final " else "")
  let tps := if d.tparam then "[X]" else ""
  let ctor := match d.under with
    | some (x, t) => s!"(val {x}: {t.show})"
    | none => ""
  let ps := (match d.kind with | .vcls => ["AnyVal"] | _ => []) ++ d.parents.map Parent.show
  let ext := match ps with
    | [] => ""
    | p :: rest => " extends " ++ " with ".intercalate (p :: rest)
  let ms := d.members.map fun m => "  " ++ m.show (ov m.name) ++ "\n"
  s!"{mods}{kw} {d.name}{tps}{ctor}{ext} \{\n{String.join ms}}\n"

end Scala
