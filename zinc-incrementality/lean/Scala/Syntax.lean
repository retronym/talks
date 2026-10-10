import Scala.AsSeenFrom

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

/-- Types: base types, another definition by name, a this-type `D.this`, and the `i`-th type
parameter of a definition `D`. Classes are owner paths, innermost first, as in `AsSeenFrom`; a
top-level definition `D` is `[D]`. -/
inductive Ty
  | int | bool | unit | str | obj | any
  | ref (d : String)
  /-- `Array[d]`, of a definition. -/
  | arr (d : String)
  | this (c : List String)
  | tp (c : List String) (i : Nat)
  deriving DecidableEq, Repr

/-- `X`, the type parameter of the top-level definition `d`. -/
def Ty.X (d : String) : Ty := .tp [d] 0

/-! `Ty` is a type language for `AsSeenFrom`: its leaves are `this` and `tp`. -/

open AsSeenFrom in
def Ty.bind : Ty → (Leaf String → Ty) → Ty
  | .this c, f => f (.this c)
  | .tp c i, f => f (.param c i)
  | t, _ => t

open AsSeenFrom in
instance : Subst Ty (AsSeenFrom.Leaf String) where
  leaf | .this c => .this c | .param c i => .tp c i
  bind := Ty.bind
  leaves | .this c => [.this c] | .tp c i => [.param c i] | _ => []

open AsSeenFrom in
instance : LawfulSubst Ty (AsSeenFrom.Leaf String) where
  bind_leaf l f := by cases l <;> rfl
  bind_bind t f g := by cases t <;> rfl
  bind_congr t f g h := by
    cases t <;> first | rfl | exact h _ (by simp [Subst.leaves])

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
  /-- The `override` modifier, when written explicitly; `none`: printed iff it overrides. -/
  ov : Option Bool := none
  priv : Bool := false
  /-- A `def` without parameters is written `def m: T`, not `def m(): T`. -/
  nullary : Bool := false
  /-- The body, when the source must say which definition ran. -/
  rhs : Option String := none
  /-- A field without accessors (an enum case in its companion), private if `priv`. -/
  fieldOnly : Bool := false
  deriving DecidableEq, Repr

def Mem.allParams (m : Mem) : List Ty := m.ext.toList ++ m.params

/-- A parent: a definition, applied to type arguments if it has type parameters. -/
abbrev Parent := String × List Ty

/-- An enum case: a singleton (`case A`, or `case A extends E(1)` with the arguments), or a class
case with fields (`case B(x: Int)`). -/
structure EnumCase where
  name : String
  fields : List (String × Ty) := []
  args : List String := []
  deriving DecidableEq, Repr

structure Decl where
  name : String
  kind : Kind := .cls
  abs : Bool := false
  final : Bool := false
  /-- The number of type parameters (`X`, `X1`, …; `Ty.tp [d] i`). -/
  tparams : Nat := 0
  super : Option Parent := none
  traits : List Parent := []
  members : List Mem := []
  /-- A value class's parameter, `class V(val x: U) extends AnyVal`. -/
  under : Option (String × Ty) := none
  /-- `case class` or `case object`; a case class's parameters are `cparams`. -/
  isCase : Bool := false
  cparams : List (String × Ty) := []
  /-- The constructor's parameter types (after desugaring). -/
  ctor : List Ty := []
  /-- A Scala 3 `enum`'s cases (the definition is the enum class). -/
  cases : List EnumCase := []
  sealed : Bool := false
  deriving DecidableEq, Repr

def Decl.parents (d : Decl) : List Parent := d.super.toList ++ d.traits

/-- A compilation unit: a class or trait and its companion object, either optional. Both have the
unit's name; the object's class is `name$`. -/
structure Src where
  name : String
  cls : Option Decl := none
  obj : Option Decl := none
  /-- The enclosing unit, for a nested definition: its name is `outer$Simple`. -/
  outer : Option String := none
  /-- Nested in the enclosing unit's object (static), rather than in its class or trait (inner). -/
  inObj : Bool := false
  /-- An anonymous class created in the object of this unit (an enum's singleton cases). -/
  anonIn : Option String := none
  deriving DecidableEq, Repr

/-- The name a nested definition has in source. -/
def Src.simple (s : Src) : String :=
  match s.outer with
  | some o => String.ofList (s.name.toList.drop (o.length + 1))
  | none => s.name

abbrev Program := List Src

/-! ## Printing as Scala source -/

def Ty.show : Ty → String
  | .int => "Int"
  | .bool => "Boolean"
  | .unit => "Unit"
  | .str => "String"
  | .obj => "Object"
  | .any => "Any"
  | .tp _ 0 => "X"
  | .tp _ i => s!"X{i}"
  | .this c => s!"{c.headD ""}.this.type"
  | .ref d => d
  | .arr d => s!"Array[{d}]"

def Parent.show : Parent → String
  | (p, []) => p
  | (p, as) => s!"{p}[{", ".intercalate (as.map Ty.show)}]"

def body : Ty → String
  | .int => "0"
  | .bool => "false"
  | .unit => "()"
  | .str => "\"\""
  | .obj => "null"
  | .any => "null"
  | .tp _ _ => "null.asInstanceOf[X]"
  | .this _ => "this"
  | .ref _ | .arr _ => "???"

def Mem.show (ov : Bool) (m : Mem) : String :=
  let mods := (match m.ext with | some t => s!"extension (self: {t.show}) " | none => "") ++
    (if m.static then "@static " else "") ++ (if m.ov.getD ov then "override " else "") ++
    (if m.priv then "private " else "") ++
    (if m.final then "final " else "") ++ (if m.lzy then "lazy " else "")
  let kw := if m.isVal then "val" else "def"
  let ps := if m.params.isEmpty && (m.isVal || m.nullary) then ""
    else "(" ++ ", ".intercalate ((m.params.zipIdx.map fun (t, i) => s!"x{i}: {t.show}")) ++ ")"
  let rhs := if m.abs then "" else s!" = {m.rhs.getD (body m.res)}"
  s!"{mods}{kw} {m.name}{ps}: {m.res.show}{rhs}"

/-- Print a definition, named `name` in source, with nested definitions `inner` in its body; `ov n`
says whether member `n` overrides an inherited one. -/
def Decl.show (ov : String → Bool) (d : Decl) (name : String := d.name) (inner : String := "") : String :=
  let kw := if !d.cases.isEmpty then "enum" else match d.kind with
    | .trt => "trait" | .obj => "object" | _ => "class"
  let mods := (if d.abs && d.kind == .cls then "abstract " else "") ++ (if d.final then "final " else "") ++
    (if d.sealed then "sealed " else "") ++ (if d.isCase then "case " else "")
  let tps := if d.tparams == 0 then "" else "[" ++ ", ".intercalate ((List.range d.tparams).map fun i => (Ty.tp [d.name] i).show) ++ "]"
  let ctor := match d.under with
    | some (x, t) => s!"(val {x}: {t.show})"
    | none => if !d.cases.isEmpty && !d.cparams.isEmpty then
        "(" ++ ", ".intercalate (d.cparams.map fun (p : String × Ty) => s!"val {p.1}: {p.2.show}") ++ ")"
      else if d.isCase && d.kind != Kind.obj then
        "(" ++ ", ".intercalate (d.cparams.map fun (p : String × Ty) => s!"{p.1}: {p.2.show}") ++ ")" else ""
  let ps := (match d.kind with | .vcls => ["AnyVal"] | _ => []) ++ d.parents.map Parent.show
  let ext := match ps with
    | [] => ""
    | p :: rest => " extends " ++ " with ".intercalate (p :: rest)
  let caseLines := d.cases.map fun c =>
    let fs := if c.fields.isEmpty then "" else
      "(" ++ ", ".intercalate (c.fields.map fun (p : String × Ty) => s!"{p.1}: {p.2.show}") ++ ")"
    let ext := if c.args.isEmpty then "" else s!" extends {name}(" ++ ", ".intercalate c.args ++ ")"
    s!"  case {c.name}{fs}{ext}\n"
  let ms := caseLines ++ d.members.map fun m => "  " ++ m.show (ov m.name) ++ "\n"
  s!"{mods}{kw} {name}{tps}{ctor}{ext} \{\n{String.join ms}{inner}}\n"

end Scala
