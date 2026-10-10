/-!
# An attributed Java subset, as javac's back end sees it

javac lowers after attribution, so the source is resolved: supertypes are types by name, applied
to at most one type argument, and members carry their signatures. Method bodies are opaque, except
for one thing lowering reads: a method may return an expression over other types' fields, whose
constants javac folds (JLS §15.29) and whose other fields it reads with `getstatic`.

A program is a list of compilation units (files); a unit's first type is public, the rest are
package-private (they share the file, which is how `permits` is inferred).
-/

namespace Java

/-- javac's `--release`. The probe has found no difference between 17, 21 and 25 on the space, so
lowering does not take it yet. -/
inductive Release | r17 | r21 | r25
  deriving DecidableEq, Repr

/-- Types: base types, the type's own type parameter `T`, another type by name. -/
inductive Ty | int | bool | void | str | obj | tp | ref (n : String)
  deriving DecidableEq, Repr

def Ty.subst (a : Ty) : Ty → Ty
  | .tp => a
  | t => t

/-- An expression a field is initialised with or a method returns: literals, other fields, `+`
and `<<`. -/
inductive Expr
  | int (n : Int)
  | str (s : String)
  | field (owner name : String)
  | add (a b : Expr)
  | shl (a b : Expr)
  /-- `Integer.parseInt("1")`: never a constant expression. -/
  | call
  deriving DecidableEq, Repr

inductive Kind | cls | iface | enum | record
  deriving DecidableEq, Repr

structure Meth where
  name : String
  params : List Ty := []
  res : Ty
  abs : Bool := false
  static : Bool := false
  final : Bool := false
  priv : Bool := false
  /-- The returned expression; otherwise a default body (`return 0;`, `return null;`, nothing). -/
  ret : Option Expr := none
  deriving DecidableEq, Repr

structure Field where
  name : String
  ty : Ty
  static : Bool := true
  final : Bool := true
  init : Option Expr := none
  deriving DecidableEq, Repr

/-- `sealed` with `permits` written out, or inferred from the compilation unit. -/
inductive Sealing | none | explicit (ps : List String) | inferred | nonSealed
  deriving DecidableEq, Repr

/-- A supertype applied to a type argument when it has a type parameter. -/
abbrev Parent := String × Option Ty

structure Decl where
  name : String
  kind : Kind := .cls
  abs : Bool := false
  final : Bool := false
  sealing : Sealing := .none
  tparam : Bool := false
  super : Option Parent := none
  ifaces : List Parent := []
  methods : List Meth := []
  fields : List Field := []
  /-- An enum's constants. -/
  consts : List String := []
  /-- A record's components. -/
  comps : List (String × Ty) := []
  deriving DecidableEq, Repr

/-- A compilation unit: its types, the first public. -/
abbrev CUnit := List Decl

abbrev Program := List CUnit

def Program.decls (p : Program) : List Decl := p.flatten

def Program.find (p : Program) (n : String) : Option Decl := p.decls.find? (·.name == n)

/-- The types sharing `n`'s compilation unit. -/
def Program.unitOf (p : Program) (n : String) : List Decl :=
  (p.find? fun u => u.any (·.name == n)).getD []

/-! ## Printing as Java source -/

def Ty.show : Ty → String
  | .int => "int"
  | .bool => "boolean"
  | .void => "void"
  | .str => "String"
  | .obj => "Object"
  | .tp => "T"
  | .ref n => n

def Parent.show : Parent → String
  | (p, none) => p
  | (p, some a) => s!"{p}<{a.show}>"

def Expr.show : Expr → String
  | .int n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .field o n => s!"{o}.{n}"
  | .add a b => s!"({a.show} + {b.show})"
  | .shl a b => s!"({a.show} << {b.show})"
  | .call => "Integer.parseInt(\"1\")"

def defaultBody : Ty → String
  | .int => "return 0;"
  | .bool => "return false;"
  | .void => ""
  | _ => "return null;"

def Meth.show (inIface : Bool) (m : Meth) : String :=
  let mods := (if m.priv then "private " else if inIface then "" else "public ") ++
    (if m.static then "static " else "") ++
    (if inIface && !m.abs && !m.static && !m.priv then "default " else "") ++
    (if m.abs && !inIface then "abstract " else "") ++ (if m.final then "final " else "")
  let ps := ", ".intercalate (m.params.zipIdx.map fun (t, i) => s!"{t.show} x{i}")
  let body := if m.abs then ";" else
    " { " ++ (match m.ret with | some e => s!"return {e.show};" | none => defaultBody m.res) ++ " }"
  s!"{mods}{m.res.show} {m.name}({ps}){body}"

def Field.show (inIface : Bool) (f : Field) : String :=
  let mods := (if inIface then "" else "public ") ++ (if f.static && !inIface then "static " else "") ++
    (if f.final && !inIface then "final " else "")
  let init := match f.init with | some e => s!" = {e.show}" | none => ""
  s!"{mods}{f.ty.show} {f.name}{init};"

def Decl.show (isPublic : Bool) (d : Decl) : String :=
  let pub := if isPublic then "public " else ""
  let sl := match d.sealing with
    | .none => "" | .nonSealed => "non-sealed " | _ => "sealed "
  let mods := pub ++ (if d.abs && d.kind == .cls then "abstract " else "") ++
    (if d.final && d.kind == .cls then "final " else "") ++ sl
  let kw := match d.kind with
    | .cls => "class" | .iface => "interface" | .enum => "enum" | .record => "record"
  let tps := if d.tparam then "<T>" else ""
  let comps := if d.kind == .record then
      "(" ++ ", ".intercalate (d.comps.map fun (n, t) => s!"{t.show} {n}") ++ ")" else ""
  let ext := match d.super with
    | some p => s!" extends {p.show}"
    | none => ""
  let impl := if d.ifaces.isEmpty then "" else
    (if d.kind == .iface then " extends " else " implements ") ++ ", ".intercalate (d.ifaces.map Parent.show)
  let permits := match d.sealing with
    | .explicit ps => " permits " ++ ", ".intercalate ps
    | _ => ""
  let consts := if d.kind == .enum then "  " ++ ", ".intercalate d.consts ++ ";\n" else ""
  let inIface := d.kind == .iface
  let fs := d.fields.map fun f => "  " ++ f.show inIface ++ "\n"
  let ms := d.methods.map fun m => "  " ++ m.show inIface ++ "\n"
  s!"{mods}{kw} {d.name}{tps}{comps}{ext}{impl}{permits} \{\n{consts}{String.join fs}{String.join ms}}\n"

def CUnit.show (pkg : String) (u : CUnit) : String :=
  s!"package {pkg};\n\n" ++ String.join (u.zipIdx.map fun (d, i) => d.show (i == 0))

end Java
