import Scala.Members

/-!
# Bounded program spaces for calibrating lowering against scalac

Enumeration here is testing (`DESIGN-spec.md`): `ScalaProbe` prints each program as Scala source
and its lowered classfiles, and `probes/scala/probe.py` diffs those against scalac's.

* `mixinSpace`: a trait `T`, a second trait `U` (extending `T` or not), a superclass `B`, a class
  `C` mixing them, and an object: a companion of `C` or a standalone `O` with `C`'s parents.
  Covers default methods, `m$`, `$init$`, mixin forwarders, trait fields, static forwarders,
  bridges from a narrowed result type.
* `genericSpace`: a generic class or trait `G[X]` and a subclass or subtrait at `G[String]`:
  bridges for erasure.
* `vclsSpace`: value classes, their companions, and erasure in a client's signature.
* `traitCompanionSpace`: static forwarders for a trait's companion.
* `miscSpace`: `final` members, fields of classes and objects.
* `initProgram`: trait initialisers, with the trait compiled in the same run as its subclasses
  and in a run of its own (F6).
* `scala3Space`: `@static` members and extension methods.
-/

namespace Scala

/-- Run lowering's linearization against a program, for the space's own legality checks. -/
def linIn (p : Program) (d : Decl) : List Anc :=
  match ((lin fuel d).run.run p.env) with
  | .ok l => l
  | .error _ => []

/-- Does member `n` of `d` override an inherited one, by `memberType`? (Printed as `override`.) -/
def overrides (p : Program) (d : Decl) (n : String) : Bool :=
  let l := linIn p d
  match (hits l n).head? with
  | some h => (hitsAbove l n).any (overridesIn d.name l h)
  | none => false

def Src.show (p : Program) (s : Src) : String :=
  let one (d : Decl) := d.show (overrides p d)
  String.join (s.cls.toList.map one ++ s.obj.toList.map one)

def Program.show (pkg : String) (p : Program) : String :=
  let static := p.any fun s => (s.obj.map fun o => o.members.any (·.static)).getD false
  s!"package {pkg}\n\n" ++ (if static then "import scala.annotation.static\n\n" else "") ++
    String.join (p.map (Src.show p))

/-! ## Mixins -/

inductive TM | none | abs | conc
  deriving DecidableEq, Repr
inductive UK | none | sub | sib
  deriving DecidableEq, Repr
inductive BK | none | abs | conc | extT
  deriving DecidableEq, Repr
inductive OK | none | comp | compClash | standalone
  deriving DecidableEq, Repr

def mem (n : String) (r : Ty) (abs : Bool) : Mem := { name := n, res := r, abs := abs }

def mixinProgram (tm : TM) (tv : Bool) (u : UK) (b : BK) (cm : Option Bool) (r : Ty) (o : OK) :
    Option Program := do
  let tms := match tm with
    | .none => [] | .abs => [mem "m" r true] | .conc => [mem "m" r false]
  let t : Decl := { name := "T", kind := .trt,
                    members := tms ++ (if tv then [{ name := "v", res := .int, isVal := true }] else []) }
  let uD : Option Decl := match u with
    | .none => none
    | .sub => some { name := "U", kind := .trt, traits := [("T", [])], members := [mem "m" r false] }
    | .sib => some { name := "U", kind := .trt, members := [mem "m" r false] }
  let bD : Option Decl := match b with
    | .none => none
    | .abs => some { name := "B", abs := true, members := [mem "m" r true] }
    | .conc => some { name := "B", members := [mem "m" r false] }
    | .extT => some { name := "B", abs := tm == .abs, traits := [("T", [])] }
  let cms := match cm with
    | none => []
    | some narrow => [mem "m" (if narrow then .str else r) false]
  let parents : Option Parent × List Parent :=
    (bD.map fun _ => ("B", []), [("T", [])] ++ (uD.toList.map fun _ => ("U", [])))
  let c0 : Decl := { name := "C", super := parents.1, traits := parents.2, members := cms }
  let lib : Program := [{ name := "T", cls := some t }] ++ (uD.toList.map fun d => { name := "U", cls := some d }) ++
    (bD.toList.map fun d => { name := "B", cls := some d })
  let base := lib ++ [{ name := "C", cls := some c0 }]
  -- legal by the membership model (`Members`), made abstract if it must be
  let es := match Members.errors .s213 base with
    | .ok es => es
    | .error _ => [{ cls := "C", kind := .conflicting }]
  if es.any (·.kind != .needsAbstract) then failure
  let c := { c0 with abs := es.any (·.kind == .needsAbstract) }
  let f : Mem := { name := "f", params := [.int], res := .int }
  let cSrc : Src := match o with
    | .comp => { name := "C", cls := some c, obj := some { name := "C", kind := .obj, members := [f] } }
    | .compClash => { name := "C", cls := some c,
                      obj := some { name := "C", kind := .obj, members := [f, mem "m" r false] } }
    | _ => { name := "C", cls := some c }
  let oSrc : List Src := match o with
    | .standalone =>
      let om := if c.abs then [mem "m" r false] else cms
      [{ name := "O", obj := some { name := "O", kind := .obj, super := parents.1, traits := parents.2,
                                     members := om ++ [f] } }]
    | _ => []
  pure (lib ++ [cSrc] ++ oSrc)

def mixinSpace : List Program :=
  [TM.none, .abs, .conc].flatMap fun tm => [false, true].flatMap fun tv =>
  [UK.none, .sub, .sib].flatMap fun u => [BK.none, .abs, .conc, .extT].flatMap fun b =>
  [Ty.int, .obj].flatMap fun r =>
  (if r == .obj then [none, some false, some true] else [none, some false]).flatMap fun cm =>
  [OK.none, .comp, .compClash, .standalone].filterMap fun o => mixinProgram tm tv u b cm r o

/-! ## Generics -/

def genericProgram (gTrait : Bool) (gAbs : Bool) (hTrait : Bool) (hOv : Bool) (k : Bool) :
    Option Program := do
  let g : Mem := { name := "g", params := [Ty.X "G"], res := Ty.X "G", abs := gAbs }
  let gD : Decl := { name := "G", kind := (if gTrait then .trt else .cls), abs := gAbs && !gTrait,
                     tparams := 1, members := [g] }
  let hm := if hOv then [{ name := "g", params := [.str], res := .str : Mem }] else []
  let hParents : Option Parent × List Parent :=
    if gTrait then (none, [("G", [.str])]) else (some ("G", [.str]), [])
  if hTrait && !gTrait then failure
  let hD : Decl := { name := "H", kind := (if hTrait then .trt else .cls), abs := gAbs && !hOv && !hTrait,
                     super := hParents.1, traits := hParents.2, members := hm }
  let kDecl : Decl := { name := "K", abs := gAbs && !hOv,
                        super := (if hTrait then none else some ("H", [])), traits := (if hTrait then [("H", [])] else []) }
  let kD : List Src := if k || hTrait then [{ name := "K", cls := some kDecl }] else []
  pure ([{ name := "G", cls := some gD }, { name := "H", cls := some hD }] ++ kD)

def genericSpace : List Program :=
  [false, true].flatMap fun gTrait => [false, true].flatMap fun gAbs =>
  [false, true].flatMap fun hTrait => [false, true].flatMap fun hOv =>
  [false, true].filterMap fun k => genericProgram gTrait gAbs hTrait hOv k

/-! ## Value classes -/

def vclsProgram (u : Ty) (comp : Bool) : Program :=
  let v : Decl := { name := "V", kind := .vcls, under := some ("x", u),
                    members := [{ name := "plus", params := [.int], res := .int }] }
  let w : Decl := { name := "W", members := [{ name := "use", params := [.ref "V"], res := .ref "V" }] }
  [{ name := "V", cls := some v,
     obj := (if comp then some { name := "V", kind := .obj, members := [{ name := "f", res := .int }] } else none) },
   { name := "W", cls := some w }]

def vclsSpace : List Program :=
  [Ty.int, .str].flatMap fun u => [false, true].map fun c => vclsProgram u c

/-! ## A trait's companion -/

def traitCompanionSpace : List Program :=
  [false, true].map fun conc =>
    [{ name := "T", cls := some { name := "T", kind := .trt, members := [mem "m" .int !conc] },
       obj := some { name := "T", kind := .obj, members := [{ name := "f", params := [.int], res := .int }] } }]

/-! ## `final` members and fields of classes and objects -/

def miscSpace : List Program :=
  let fm : Mem := { name := "m", res := .int, final := true }
  let k (n : String) : Mem := { name := n, res := .int, isVal := true }
  let fobj : Mem := { name := "f", params := [.int], res := .int, final := true }
  [ [{ name := "T", cls := some { name := "T", kind := .trt, members := [fm] } },
     { name := "C", cls := some { name := "C", traits := [("T", [])] } }],
    [{ name := "B", cls := some { name := "B", members := [fm] } },
     { name := "C", cls := some { name := "C", super := some ("B", []) } }],
    [{ name := "C", cls := some { name := "C", members := [k "k"] },
       obj := some { name := "C", kind := .obj, members := [k "k2", fobj] } },
     { name := "O", obj := some { name := "O", kind := .obj, members := [k "k", fobj] } }],
    [{ name := "T", cls := some { name := "T", kind := .trt, members := [fm, k "v"] } },
     { name := "O", obj := some { name := "O", kind := .obj, traits := [("T", [])] } }] ]

/-! ## Trait initialisers, compiled together and apart -/

/-- A trait with one member (a concrete `def`, `val` or `lazy val`, or an abstract extension
method), a class and an object extending it. As a `Case` with `lib := ["T"]`, the trait is compiled in a run of its own. -/
def initProgram (k : Nat) : Program :=
  let m : Mem := match k with
    | 0 => { name := "m", res := .int }
    | 1 => { name := "v", res := .int, isVal := true }
    | 2 => { name := "z", res := .int, isVal := true, lzy := true }
    | _ => { name := "e", res := .int, ext := some .int, abs := true }
  let cms : List Mem := if k == 3 then [{ m with abs := false }] else []
  [{ name := "T", cls := some { name := "T", kind := .trt, members := [m] } },
   { name := "C", cls := some { name := "C", traits := [("T", [])], members := cms } },
   { name := "O", obj := some { name := "O", kind := .obj, traits := [("T", [])], members := cms } }]

/-! ## Scala 3: `@static` and extension methods -/

def scala3Space : List Program :=
  let sv : Mem := { name := "sv", res := .int, isVal := true, static := true }
  let sf : Mem := { name := "sf", params := [.int], res := .int, static := true }
  let g : Mem := { name := "g", res := .int }
  let twice : Mem := { name := "twice", res := .int, ext := some .int }
  let len : Mem := { name := "len", params := [.int], res := .int, ext := some .str }
  [ [{ name := "S", cls := some { name := "S" }, obj := some { name := "S", kind := .obj, members := [sv, sf, g] } }],
    [{ name := "S", cls := some { name := "S" }, obj := some { name := "S", kind := .obj, members := [sf, g] } }],
    [{ name := "E", obj := some { name := "E", kind := .obj, members := [twice, len] } }],
    [{ name := "TE", cls := some { name := "TE", kind := .trt, members := [twice, { len with abs := true }] } },
     { name := "CE", cls := some { name := "CE", traits := [("TE", [])],
                                   members := [{ len with }] } }] ]

/-! ## Type arguments through several parents, value-class arguments, overloads

Programs where a member's type must be viewed from the class (`memberType`) to decide overriding
and bridges: a parameter passed through an intermediate generic class or trait, a value class as
the argument, and an overload that a name-only rule would take for an override. -/

def asfSpace : List Program :=
  let g (o : String) (abs : Bool := false) : Mem := { name := "g", params := [Ty.X o], res := Ty.X o, abs := abs }
  let gAt (t : Ty) : Mem := { name := "g", params := [t], res := t }
  let cG : Src := { name := "G", cls := some { name := "G", tparams := 1, members := [g "G"] } }
  let tG : Src := { name := "G", cls := some { name := "G", kind := .trt, tparams := 1, members := [g "G"] } }
  let hOf (trt : Bool) : Src :=
    let gx : Parent := ("G", [(Ty.X "H")])
    let d : Decl := { name := "H", kind := (if trt then .trt else .cls), tparams := 1,
                      super := (if trt then none else some gx), traits := (if trt then [gx] else []) }
    { name := "H", cls := some d }
  let v : Src := { name := "V", cls := some { name := "V", kind := .vcls, under := some ("x", .int) } }
  let k (sup : Option Parent) (ts : List Parent) (ms : List Mem) : Src :=
    { name := "K", cls := some { name := "K", super := sup, traits := ts, members := ms } }
  let o (sup : Option Parent) (ts : List Parent) (ms : List Mem) : Src :=
    { name := "O", obj := some { name := "O", kind := .obj, super := sup, traits := ts, members := ms } }
  -- through an intermediate generic class, with and without an override
  [ [cG, hOf false, k (some ("H", [.str])) [] [gAt .str]],
    [cG, hOf false, k (some ("H", [.str])) [] []],
    [cG, hOf false, k (some ("H", [.int])) [] [gAt .int]],
  -- through an intermediate generic trait
    [tG, hOf true, k none [("H", [.str])] []],
    [tG, hOf true, k none [("H", [.int])] [gAt .int]],
    [tG, hOf true, k none [("H", [.str])] [gAt .str], o none [("H", [.str])] [gAt .str]],
  -- a value class as the argument
    [cG, v, k (some ("G", [(.ref "V")])) [] [gAt (.ref "V")]],
    [tG, v, k none [("G", [(.ref "V")])] [], o none [("G", [(.ref "V")])] [gAt (.ref "V")]],
  -- an overload, not an override: no bridge
    [cG, k (some ("G", [.str])) [] [gAt .int]],
    [tG, k none [("G", [.str])] [gAt .int]] ]

structure Case where
  fam : String
  prog : Program
  /-- Scala 3 syntax only. -/
  only3 : Bool := false
  /-- Compile these units in a run of their own, then the rest against them. -/
  lib : List String := []

def space : List Case :=
  (mixinSpace.map ({ fam := "mixin", prog := · })) ++ (genericSpace.map ({ fam := "generic", prog := · })) ++
  (vclsSpace.map ({ fam := "vcls", prog := · })) ++ (traitCompanionSpace.map ({ fam := "tcomp", prog := · })) ++
  (miscSpace.map ({ fam := "misc", prog := · })) ++ (asfSpace.map ({ fam := "asf", prog := · })) ++
  ([0, 1, 2].map fun k => { fam := "init", prog := initProgram k }) ++
  ([0, 1, 2].map fun k => { fam := "initSep", prog := initProgram k, lib := ["T"] }) ++
  [{ fam := "init", prog := initProgram 3, only3 := true },
   { fam := "initSep", prog := initProgram 3, lib := ["T"], only3 := true }] ++
  (scala3Space.map ({ fam := "scala3", prog := ·, only3 := true }))

def Case.lower (dl : Dialect) (c : Case) : Except String (List ClassOut) :=
  if c.lib.isEmpty then lowerProgram dl c.prog else lowerSeparately dl c.prog c.lib

/-! ## Dumping classfiles in the probe's format -/

def flags (ws : List (String × Bool)) : String := " ".intercalate (ws.filter (·.2) |>.map (·.1))

def Insn.show (i : Insn) : String := s!"{i.op} {i.owner}.{i.name}:{i.desc}"

def ClassOut.dump (pid : String) (c : ClassOut) : List String :=
  let pre := s!"{pid}\t{c.name}\t"
  (if c.partly then [pre ++ "partly"] else []) ++
  [pre ++ s!"class\t{flags [("interface", c.itf), ("abstract", c.abs), ("final", c.final)]}\t" ++
     s!"super={c.super.getD "java/lang/Object"};ifaces={",".intercalate c.ifaces}"] ++
  c.fields.map (fun f => pre ++ s!"field {f.name} {f.desc}\t" ++
    flags [(if f.priv then "private" else "public", true), ("static", f.static), ("final", f.final)]) ++
  c.methods.map fun m => pre ++ s!"method {m.name} {m.desc}\t" ++
    flags [(if m.priv then "private" else "public", true), ("static", m.static), ("final", m.final),
           ("abstract", m.abs), ("bridge", m.bridge)] ++ "\t" ++
    (match m.calls with | none => "*" | some cs => "; ".intercalate (cs.map Insn.show))

end Scala
