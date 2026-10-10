import Java.Lower

/-!
# Bounded program spaces for calibrating lowering against javac

Enumeration here is testing (`DESIGN-spec.md`): `JavaProbe` prints each program as Java source
and its lowered classfiles, and `probes/java/probe.py` diffs those against javac's.

* `ifaceSpace`: an interface with abstract, default, static and private methods and a constant,
  implemented by a class or an abstract class.
* `bridgeSpace`: a supertype (class or interface, generic or not) with `get` and `put`, a subtype at
  `String` overriding them (narrowed result, substituted parameter) or not, and a third level.
* `constSpace`: constants (literals, `<<`, string concatenation, a non-constant), constants in an
  interface read from another type, a client whose methods return them.
* `enumSpace`: enums with zero to two constants, an interface, a static constant.
* `recordSpace`: records with zero to two components, an interface the accessor implements.
* `sealedSpace`: sealed interfaces and classes, `permits` written out or inferred, final,
  non-sealed, record and sealed subtypes.
-/

namespace Java

structure Case where
  fam : String
  prog : Program

def meth (n : String) (ps : List Ty) (r : Ty) (abs : Bool := false) : Meth :=
  { name := n, params := ps, res := r, abs := abs }

/-! ## Interfaces -/

def ifaceSpace : List Case := Id.run do
  let mut out := []
  for b in [false, true] do
    for st in [false, true] do
      for pr in [false, true] do
        for k in [false, true] do
          for cAbs in [false, true] do
            let i : Decl := { name := "I", kind := .iface,
                                methods := [meth "a" [] .int true] ++
                                (if b then [meth "b" [] .int] else []) ++
                                (if st then [{ (meth "s" [] .int) with static := true }] else []) ++
                                (if pr then [{ (meth "c" [] .int) with priv := true }, { (meth "d" [] .str) with priv := true, static := true }] else []),
                                fields := if k then [{ name := "K", ty := .int, init := some (.int 7) }] else [] }
            let c : Decl := { name := "C", abs := cAbs, ifaces := [("I", none)],
                                methods := if cAbs then [] else [meth "a" [] .int] }
            out := out ++ [⟨"iface", [[i], [c]]⟩]
  return out

/-! ## Bridges -/

def bridgeSpace : List Case := Id.run do
  let mut out := []
  for pIface in [false, true] do
    for gen in [false, true] do
      for qIface in (if pIface then [false, true] else [false]) do
        for ovGet in [false, true] do
          for ovPut in (if gen then [false, true] else [false]) do
            for third in (if qIface then [false] else [false, true]) do
              let t : Ty := if gen then .tp else .obj
              let pAbs := pIface
              let p : Decl := { name := "P", kind := (if pIface then .iface else .cls), tparam := gen,
                                  methods := [meth "get" [] t pAbs, meth "put" [t] .void pAbs] }
              let arg : Option Ty := if gen then some .str else none
              let qAbs := qIface
              let q : Decl := { name := "Q", kind := (if qIface then .iface else .cls),
                                  super := (if pIface then none else some ("P", arg)),
                                  ifaces := if pIface then [("P", arg)] else [],
                                  abs := pIface && !qIface && (!ovGet || !ovPut),
                                  methods := (if ovGet then [meth "get" [] .str qAbs] else []) ++
                                  (if ovPut then [meth "put" [.str] .void qAbs] else []) }
              let r : List Decl := if third then
                [{ name := "R", super := some ("Q", none), methods := [meth "get" [] .str] ++
                     (if q.abs then [meth "put" [if gen then .str else .obj] .void] ++
                      (if gen && !ovPut then [] else []) else []) }]
                else []
              -- an abstract `Q` leaves a method unimplemented; `R` implements both
              let r := r.map fun d =>
                if q.abs then { d with methods := [meth "get" [] .str, meth "put" [if gen then .str else .obj] .void] } else d
              out := out ++ [⟨"bridge", [[p], [q]] ++ r.map ([·])⟩]
  return out

/-! ## Constants -/

def constSpace : List Case := Id.run do
  let mut out := []
  for kE in [Expr.int 8, .shl (.int 1) (.int 3)] do
    for withN in [false, true] do
      for iface in [false, true] do
        let a : Decl := { name := "A",
                            fields := [{ name := "K", ty := .int, init := some kE },
                            { name := "S", ty := .str, init := some (.add (.str "s") (.field "A" "K")) }] ++
                            (if withN then [{ name := "N", ty := .int, init := some .call }] else []) ++
                            [{ name := "F", ty := .int, static := false, final := false }] }
        let j : List Decl := if iface then
          [{ name := "J", kind := .iface, fields := [{ name := "L", ty := .int, init := some (.add (.field "A" "K") (.int 1)) }] ++
               (if withN then [{ name := "M", ty := .int, init := some (.add (.field "A" "N") (.int 1)) }] else []) }] else []
        let c : Decl := { name := "C", methods :=
                            [{ (meth "k" [] .int) with ret := some (.field "A" "K") },
                            { (meth "s" [] .str) with ret := some (.field "A" "S") }] ++
                            (if withN then [{ (meth "n" [] .int) with ret := some (.field "A" "N") }] else []) ++
                            (if iface then [{ (meth "l" [] .int) with ret := some (.field "J" "L") }] else []) ++
                            (if iface && withN then [{ (meth "m" [] .int) with ret := some (.field "J" "M") }] else []) }
        out := out ++ [⟨"const", [[a]] ++ j.map ([·]) ++ [[c]]⟩]
  return out

/-! ## Enums -/

def enumSpace : List Case := Id.run do
  let mut out := []
  for n in [0, 1, 2] do
    for iface in [false, true] do
      for k in [false, true] do
        let consts := (["X", "Y"].take n)
        let i : List Decl := if iface then [{ name := "I", kind := .iface, methods := [meth "m" [] .int true] }] else []
        let e : Decl := { name := "E", kind := .enum, consts := consts,
                            ifaces := if iface then [("I", none)] else [],
                            methods := (if iface then [meth "m" [] .int] else []),
                            fields := if k then [{ name := "K", ty := .int, init := some (.int 3) }] else [] }
        out := out ++ [⟨"enum", i.map ([·]) ++ [[e]]⟩]
  return out

/-! ## Records -/

def recordSpace : List Case := Id.run do
  let mut out := []
  for comps in [[], [("x", Ty.int)], [("x", .int), ("y", .str)]] do
    for iface in [false, true] do
      if iface && comps.isEmpty then continue
      let i : List Decl := if iface then [{ name := "I", kind := .iface, methods := [meth "x" [] .int true] }] else []
      let r : Decl := { name := "R", kind := .record, comps := comps,
                          ifaces := if iface then [("I", none)] else [] }
      out := out ++ [⟨"record", i.map ([·]) ++ [[r]]⟩]
  return out

/-! ## Sealed hierarchies -/

def sealedSpace : List Case := Id.run do
  let mut out := []
  for sIface in [false, true] do
    for inferred in [false, true] do
      for withRec in (if sIface then [false, true] else [false]) do
        for two in [false, true] do
          let ext := fun (n : String) (d : Decl) =>
            if sIface then { d with ifaces := [(n, none)] } else { d with super := some (n, none) }
          let subs : List Decl :=
            [ext "S" { name := "F", final := true }, ext "S" { name := "NS", sealing := .nonSealed }] ++
            (if withRec then [ext "S" { name := "Rr", kind := .record }] else []) ++
            (if two then [ext "S" { name := "T", abs := !sIface, kind := (if sIface then .iface else .cls),
                                      sealing := if inferred then .inferred else .explicit ["G"] }] else [])
          let grand : List Decl := if two then
            [if sIface then { name := "G", final := true, ifaces := [("T", none)] }
             else { name := "G", final := true, super := some ("T", none) }] else []
          let s : Decl := { name := "S", kind := (if sIface then .iface else .cls), abs := !sIface,
                              sealing := if inferred then .inferred else .explicit (subs.map (·.name)) }
          let prog : Program := if inferred then
              -- `permits` inferred: the subtypes share `S`'s compilation unit; `T`'s share it too
              [[s] ++ subs ++ grand]
            else [[s]] ++ subs.map ([·]) ++ grand.map ([·])
          out := out ++ [⟨"sealed", prog⟩]
  return out

def space : List Case :=
  ifaceSpace ++ bridgeSpace ++ constSpace ++ enumSpace ++ recordSpace ++ sealedSpace

/-! ## Dumping -/

def flags (ws : List (String × Bool)) : String := " ".intercalate ((ws.filter (·.2)).map (·.1))

def Acc.show : Acc → String | .pub => "public" | .priv => "private" | .pkg => "package"

def Insn.show (i : Insn) : String := s!"{i.op} {i.owner}.{i.name}:{i.desc}"

def ClassOut.dump (pid : String) (c : ClassOut) : List String :=
  let pre := s!"{pid}\t{c.name}\t"
  [pre ++ s!"class\t{flags [("public", c.pub), ("interface", c.itf), ("abstract", c.abs), ("final", c.final), ("enum", c.enum)]}\t" ++
     s!"super={if c.itf then "java/lang/Object" else c.super};ifaces={",".intercalate c.ifaces};permits={",".intercalate c.permitted}" ++
     (match c.record with
      | some cs => ";record=" ++ ",".intercalate (cs.map fun (n, d) => s!"{n}:{d}")
      | none => "")] ++
  c.fields.map (fun f => pre ++ s!"field {f.name} {f.desc}\t" ++
    flags [(f.acc.show, true), ("static", f.static), ("final", f.final), ("synthetic", f.synthetic), ("enum", f.enum)] ++
    "\t" ++ (match f.const with | some v => v.show | none => "-")) ++
  c.methods.map fun m => pre ++ s!"method {m.name} {m.desc}\t" ++
    flags [(m.acc.show, true), ("static", m.static), ("final", m.final), ("abstract", m.abs),
           ("bridge", m.bridge), ("synthetic", m.synthetic)] ++ "\t" ++
    "; ".intercalate (m.calls.map Insn.show) ++
    (if m.pushes.isEmpty then "" else " | " ++ ", ".intercalate (m.pushes.map CVal.show))

end Java
