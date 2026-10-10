import Scala.Lower

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
-/

namespace Scala

/-- Run lowering's linearization against a program, for the space's own legality checks. -/
def linIn (p : Program) (d : Decl) : List Anc :=
  match ((lin fuel d none).run.run p.env) with
  | .ok l => l
  | .error _ => []

/-- Does member `n` of `d` override an inherited one? (Printed as `override`.) -/
def overrides (p : Program) (d : Decl) (n : String) : Bool :=
  !(hits (linIn p d).tail n).isEmpty

/-- Scala's rule for inherited concrete members: the winner must override every other concrete
member, which here means its owner must have the other's owner as an ancestor. -/
def conflictFree (p : Program) (d : Decl) (n : String) : Bool :=
  let l := linIn p d
  match (hits l n).filter (!·.2.abs) with
  | [] => true
  | ((w, _), _) :: rest =>
    let lw := linIn p w
    rest.all fun ((o, _), _) => lw.any (·.1.name == o.name)

def needsAbstract (p : Program) (d : Decl) (n : String) : Bool :=
  let hs := hits (linIn p d) n
  !hs.isEmpty && hs.all (·.2.abs)

def Src.show (p : Program) (s : Src) : String :=
  let one (d : Decl) := d.show (overrides p d)
  String.join (s.cls.toList.map one ++ s.obj.toList.map one)

def Program.show (pkg : String) (p : Program) : String :=
  s!"package {pkg}\n\n" ++ String.join (p.map (Src.show p))

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
    | .sub => some { name := "U", kind := .trt, traits := [("T", none)], members := [mem "m" r false] }
    | .sib => some { name := "U", kind := .trt, members := [mem "m" r false] }
  let bD : Option Decl := match b with
    | .none => none
    | .abs => some { name := "B", abs := true, members := [mem "m" r true] }
    | .conc => some { name := "B", members := [mem "m" r false] }
    | .extT => some { name := "B", abs := tm == .abs, traits := [("T", none)] }
  let cms := match cm with
    | none => []
    | some narrow => [mem "m" (if narrow then .str else r) false]
  let parents : Option Parent × List Parent :=
    (bD.map fun _ => ("B", none), [("T", none)] ++ (uD.toList.map fun _ => ("U", none)))
  let c0 : Decl := { name := "C", super := parents.1, traits := parents.2, members := cms }
  let lib : Program := [{ name := "T", cls := some t }] ++ (uD.toList.map fun d => { name := "U", cls := some d }) ++
    (bD.toList.map fun d => { name := "B", cls := some d })
  let base := lib ++ [{ name := "C", cls := some c0 }]
  if !conflictFree base c0 "m" then failure
  let c := { c0 with abs := needsAbstract base c0 "m" }
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
  let g : Mem := { name := "g", params := [.tp], res := .tp, abs := gAbs }
  let gD : Decl := { name := "G", kind := (if gTrait then .trt else .cls), abs := gAbs && !gTrait,
                     tparam := true, members := [g] }
  let hm := if hOv then [{ name := "g", params := [.str], res := .str : Mem }] else []
  let hParents : Option Parent × List Parent :=
    if gTrait then (none, [("G", some .str)]) else (some ("G", some .str), [])
  if hTrait && !gTrait then failure
  let hD : Decl := { name := "H", kind := (if hTrait then .trt else .cls), abs := gAbs && !hOv && !hTrait,
                     super := hParents.1, traits := hParents.2, members := hm }
  let kDecl : Decl := { name := "K", abs := gAbs && !hOv,
                        super := (if hTrait then none else some ("H", none)), traits := (if hTrait then [("H", none)] else []) }
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
     { name := "C", cls := some { name := "C", traits := [("T", none)] } }],
    [{ name := "B", cls := some { name := "B", members := [fm] } },
     { name := "C", cls := some { name := "C", super := some ("B", none) } }],
    [{ name := "C", cls := some { name := "C", members := [k "k"] },
       obj := some { name := "C", kind := .obj, members := [k "k2", fobj] } },
     { name := "O", obj := some { name := "O", kind := .obj, members := [k "k", fobj] } }],
    [{ name := "T", cls := some { name := "T", kind := .trt, members := [fm, k "v"] } },
     { name := "O", obj := some { name := "O", kind := .obj, traits := [("T", none)] } }] ]

def space : List (String × Program) :=
  (mixinSpace.map ("mixin", ·)) ++ (genericSpace.map ("generic", ·)) ++ (vclsSpace.map ("vcls", ·)) ++
    (traitCompanionSpace.map ("tcomp", ·)) ++ (miscSpace.map ("misc", ·))

/-! ## Dumping classfiles in the probe's format -/

def flags (ws : List (String × Bool)) : String := " ".intercalate (ws.filter (·.2) |>.map (·.1))

def Insn.show (i : Insn) : String := s!"{i.op} {i.owner}.{i.name}:{i.desc}"

def ClassOut.dump (pid : String) (c : ClassOut) : List String :=
  let pre := s!"{pid}\t{c.name}\t"
  [pre ++ s!"class\t{flags [("interface", c.itf), ("abstract", c.abs), ("final", c.final)]}\t" ++
     s!"super={c.super.getD "java/lang/Object"};ifaces={",".intercalate c.ifaces}"] ++
  c.fields.map (fun f => pre ++ s!"field {f.name} {f.desc}\t" ++
    flags [(if f.priv then "private" else "public", true), ("static", f.static), ("final", f.final)]) ++
  c.methods.map fun m => pre ++ s!"method {m.name} {m.desc}\t" ++
    flags [(if m.priv then "private" else "public", true), ("static", m.static), ("final", m.final),
           ("abstract", m.abs), ("bridge", m.bridge)] ++ "\t" ++
    (match m.calls with | none => "*" | some cs => "; ".intercalate (cs.map Insn.show))

end Scala
