import Scala.Syntax

/-!
# Desugaring onto a library prelude

Features whose lowering is mostly synthesized members are written as a desugaring into the core
AST, which `Lower` already handles (forwarders, bridges, static forwarders, erasure). What the
compiler inherits from the standard library enters as a *prelude*: the interfaces of the library
classes a desugared definition extends, read through `Q.decl` like any other parent. So the mixin
forwarders for `Product`'s concrete methods and the static forwarders for
`AbstractFunction2.tupled` come from the rules calibrated in S1-S3.

**Case classes.** `case class P(x: A, y: B)` becomes:
- a class with the fields, `copy` and its default getters, `Product`'s abstract members,
  `productPrefix`, `canEqual`, `equals`/`hashCode`/`toString` (and `productElementName` from 2.13,
  `_1`, `_2` in Scala 3), extending `Product` and `Serializable`;
- a companion with `apply` and `unapply`. Scala 2: `unapply` returns `Option` (`Boolean` for no
  fields), and a companion the compiler synthesizes extends `AbstractFunctionN` and overrides
  `toString`. Scala 3: the companion extends `Mirror.Product` with `fromProduct`, `unapply` is the
  identity (`Boolean` for no fields), and a synthesized companion overrides `toString`.

`case object O` is an object extending `Product` and `Serializable` (and `Mirror.Singleton` in
Scala 3) with `Product`'s members, `canEqual`, `hashCode`, `toString`.
-/

namespace Scala

/-! ## The prelude: library interfaces -/

def lib (n : String) : Ty := .ref n

def abs (n : String) (ps : List Ty) (r : Ty) : Mem := { name := n, params := ps, res := r, abs := true, nullary := ps.isEmpty }
def conc (n : String) (ps : List Ty) (r : Ty) : Mem := { name := n, params := ps, res := r, nullary := ps.isEmpty }

def iterator : Ty := lib "scala/collection/Iterator"

/-- `scala.Serializable` (2.12) or `java.io.Serializable`. -/
def serializable (dl : Dialect) : String :=
  if dl == .s212 then "scala/Serializable" else "java/io/Serializable"

def functionN (n : Nat) : String := s!"scala/Function{n}"
def abstractFunctionN (n : Nat) : String := s!"scala/runtime/AbstractFunction{n}"

/-- The library classes the desugarings extend, as interfaces. -/
def prelude (dl : Dialect) : Program :=
  let trt (n : String) (ms : List Mem) (ps : List Parent := []) (tps : Nat := 0) : Src :=
    { name := n, cls := some { name := n, kind := .trt, members := ms, traits := ps, tparams := tps } }
  let product : List Mem :=
    [abs "productArity" [] .int, abs "productElement" [.int] .obj, conc "productIterator" [] iterator,
     conc "productPrefix" [] .str] ++
    (if dl == .s212 then [] else [conc "productElementName" [.int] .str, conc "productElementNames" [] iterator])
  -- `FunctionN[T1, …, Tn, R]`: `apply`, and the concrete members a companion inherits
  let fn (n : Nat) : Src :=
    let x (i : Nat) : Ty := .tp [functionN n] i
    let extra : List Mem := match n with
      | 1 => [conc "compose" [lib "scala/Function1"] (lib "scala/Function1"),
              conc "andThen" [lib "scala/Function1"] (lib "scala/Function1")]
      | 2 => [conc "curried" [] (lib "scala/Function1"), conc "tupled" [] (lib "scala/Function1")]
      | _ => []
    trt (functionN n) ([abs "apply" ((List.range n).map x) (x n), conc "toString" [] .str] ++ extra) [] (n + 1)
  let afn (n : Nat) : Src :=
    { name := abstractFunctionN n,
      cls := some { name := abstractFunctionN n, abs := true, tparams := n + 1,
                    traits := [(functionN n, (List.range (n + 1)).map (Ty.tp [abstractFunctionN n]))] } }
  [trt "java/io/Serializable" [],
   trt "scala/Equals" [abs "canEqual" [.any] .bool, abs "equals" [.any] .bool],
   trt "scala/Product" product [("scala/Equals", [])]] ++
  (if dl == .s212 then [trt "scala/Serializable" [] [("java/io/Serializable", [])]] else []) ++
  (if dl == .s3 then
    [trt "scala/reflect/Enum" [abs "ordinal" [] .int] [("scala/Product", []), ("java/io/Serializable", [])],
     trt "scala/runtime/EnumValue" [],
     trt "scala/deriving/Mirror$Sum" [abs "ordinal" [.tp ["scala/deriving/Mirror$Sum"] 0] .int] [] 1,
     trt "scala/deriving/Mirror$Product" [abs "fromProduct" [lib "scala/Product"] .obj],
     trt "scala/deriving/Mirror$Singleton"
       [conc "fromProduct" [lib "scala/Product"] (lib "scala/deriving/Mirror$Singleton")]
       [("scala/deriving/Mirror$Product", [])]]
  else ([0, 1, 2].map fn) ++ ([0, 1, 2].map afn))

/-! ## Case classes and case objects -/

/-- The superclasses of `d` in `p` (not traits, not the library's). -/
def superclasses (p : Program) (d : Decl) : List Decl :=
  go 8 d
where
  go : Nat → Decl → List Decl
    | 0, _ => []
    | k + 1, d => match d.super with
      | some (s, _) => match (p.find? (·.name == s)).bind (·.cls) with
        | some c => c :: go k c
        | none => []
      | none => []

/-- The members of a case class. `copy`, `toString`, `hashCode`, `equals` and `canEqual` are not
synthesized when a superclass already defines one concretely (a trait's does not count); Scala 2
then also drops `copy`'s default getters, Scala 3 keeps them. -/
def caseClassMembers (dl : Dialect) (p : Program) (d : Decl) : List Mem :=
  let ps := d.cparams
  let self : Ty := .ref d.name
  let inherited (n : String) : Bool :=
    (superclasses p d).any fun c => c.members.any fun m => m.name == n && !m.abs
  let unlessInherited (ms : List Mem) : List Mem := ms.filter fun m => !inherited m.name
  (ps.map fun (x, t) => { name := x, res := t, isVal := true }) ++
  (if inherited "copy" then [] else [conc "copy" (ps.map (·.2)) self]) ++
  -- (Scala 3 keeps `copy`'s default getters when a superclass's `copy` replaces it)
  (if inherited "copy" && dl != .s3 then []
   else ps.zipIdx.map fun ((_, t), i) => conc s!"copy$default${i + 1}" [] t) ++
  [conc "productPrefix" [] .str, conc "productArity" [] .int, conc "productElement" [.int] .obj] ++
  (if dl == .s212 then [] else [conc "productElementName" [.int] .str]) ++
  unlessInherited [conc "canEqual" [.any] .bool, conc "hashCode" [] .int, conc "toString" [] .str,
   conc "equals" [.any] .bool] ++
  (if dl == .s3 then (ps.zipIdx.map fun ((_, t), i) => conc s!"_{i + 1}" [] t) else [])

/-- The companion of a case class: the explicit object, or a synthesized one. -/
def caseCompanion (dl : Dialect) (d : Decl) (explicit : Option Decl) : Decl :=
  let ps := d.cparams
  let n := ps.length
  let self : Ty := .ref d.name
  let unapplyRes : Ty :=
    if n == 0 then .bool else if dl == .s3 then self else lib "scala/Option"
  let members : List Mem :=
    [conc "apply" (ps.map (·.2)) self, conc "unapply" [self] unapplyRes] ++
    (if dl == .s3 then [conc "fromProduct" [lib "scala/Product"] self] else [])
  let synthesized := explicit.isNone
  let toStr : List Mem := if synthesized then [{ conc "toString" [] .str with final := dl != .s3 }] else []
  let base : Decl := explicit.getD { name := d.name, kind := .obj }
  let parents : Option Parent × List Parent :=
    if dl == .s3 then (base.super, base.traits ++ [("scala/deriving/Mirror$Product", [])])
    else if synthesized && n ≤ 2 then
      (some (abstractFunctionN n, ps.map (·.2) ++ [self]), base.traits ++ [(serializable dl, [])])
    else (base.super, base.traits ++ [(serializable dl, [])])
  { base with super := parents.1, traits := parents.2, members := base.members ++ members ++ toStr }

def caseObject (dl : Dialect) (o : Decl) : Decl :=
  let ms : List Mem :=
    [conc "productPrefix" [] .str, conc "productArity" [] .int, conc "productElement" [.int] .obj,
     conc "canEqual" [.any] .bool, conc "hashCode" [] .int, conc "toString" [] .str]
  { o with isCase := false, members := o.members ++ ms,
           traits := o.traits ++ [("scala/Product", []), (serializable dl, [])] ++
             (if dl == .s3 then [("scala/deriving/Mirror$Singleton", [])] else []) }

/-! ## Scala 3 enums

`enum E { case A, B; case C(x: Int) }` becomes:
- the abstract class `E` implementing `scala.reflect.Enum`, with the enum's parameters as fields;
- its companion implementing `Mirror.Sum[E]`: each singleton case a static field; `values`,
  `valueOf` and the array `$values` when every case is a singleton; `$new` when singletons share
  one class; `fromOrdinal` and `ordinal`;
- an anonymous class for the singletons: one shared `E$$anon$1(name, ordinal)` for cases written
  without arguments, else one per case (`case A extends E(1)`);
- a nested case class `E$C extends E` for each case with fields, with an `ordinal`.
-/

def enumSrcs (s : Src) : List Src :=
  match s.cls with
  | none => [s]
  | some d =>
    if d.cases.isEmpty then [s] else
    let e := d.name
    let self : Ty := .ref e
    let singles := d.cases.filter (·.fields.isEmpty)
    let classCases := d.cases.filter (!·.fields.isEmpty)
    let shared := singles.filter (·.args.isEmpty)
    let perCase := singles.filter (!·.args.isEmpty)
    let fieldVals : List Mem := d.cparams.map fun (x, t) => { name := x, res := t, isVal := true }
    let enumTraits : List Parent := d.traits ++ [("scala/reflect/Enum", [])]
    let cls : Decl := { d with cases := [], abs := true, cparams := [], ctor := d.cparams.map (·.2),
                               members := fieldVals ++ d.members, traits := enumTraits }
    let field (n : String) (t : Ty) (priv : Bool := false) : Mem := { name := n, res := t, fieldOnly := true, priv := priv }
    let compMembers : List Mem :=
      (singles.map fun c => field c.name self) ++
      (if classCases.isEmpty then
        [field "$values" (.arr e) true, conc "values" [] (.arr e), conc "valueOf" [.str] self] else []) ++
      (if shared.isEmpty then [] else [{ conc "$new" [.int, .str] self with priv := true }]) ++
      [conc "fromOrdinal" [.int] self, conc "ordinal" [self] .int]
    let base : Decl := s.obj.getD { name := e, kind := .obj }
    let compTraits : List Parent := base.traits ++ [("scala/deriving/Mirror$Sum", [self])]
    let comp : Decl := { base with members := base.members ++ compMembers, traits := compTraits }
    let anonMembers : List Mem :=
      [conc "canEqual" [.any] .bool, conc "productArity" [] .int, conc "productElement" [.int] .obj,
       conc "productElementName" [.int] .str, { conc "readResolve" [] .obj with priv := true },
       conc "productPrefix" [] .str, conc "toString" [] .str, conc "ordinal" [] .int, conc "hashCode" [] .int]
    let anon (k : Nat) (sharedFields : Bool) : Src :=
      let n := s!"{e}$$anon${k}"
      let ts : List Parent := [("scala/runtime/EnumValue", []), ("scala/deriving/Mirror$Singleton", [])]
      let fs : List Mem := if sharedFields then [field "$name$1" .str true, field "_$ordinal$1" .int true] else []
      let c : Decl := { name := n, final := true, super := some (e, []), traits := ts,
                        ctor := (if sharedFields then [.str, .int] else []), members := fs ++ anonMembers }
      { name := n, cls := some c, anonIn := some e }
    let anons : List Src :=
      (if shared.isEmpty then [] else [anon 1 true]) ++
      (perCase.zipIdx.map fun (_, i) => anon (i + 1 + (if shared.isEmpty then 0 else 1)) false)
    let caseClasses : List Src := classCases.map fun c =>
      let n := s!"{e}${c.name}"
      let cd : Decl := { name := n, isCase := true, final := true, cparams := c.fields, super := some (e, []),
                         members := [conc "ordinal" [] .int] }
      { name := n, outer := some e, inObj := true, cls := some cd }
    [{ s with cls := some cls, obj := some comp }] ++ anons ++ caseClasses

def desugarSrc (dl : Dialect) (p : Program) (s : Src) : Src :=
  match s.cls with
  | some d =>
    if d.isCase then
      let c : Decl := { d with isCase := false, cparams := [], ctor := d.cparams.map (·.2),
                               members := d.members ++ caseClassMembers dl p d,
                               traits := d.traits ++ [("scala/Product", []), (serializable dl, [])] }
      { s with cls := some c, obj := some (caseCompanion dl d s.obj) }
    else s
  | none =>
    match s.obj with
    | some o => if o.isCase then { s with obj := some (caseObject dl o) } else s
    | none => s

/-- The program the back end sees: desugared, after the prelude. -/
def Program.desugar (dl : Dialect) (p : Program) : Program :=
  let q := p.flatMap enumSrcs
  q.map (desugarSrc dl q)

end Scala
