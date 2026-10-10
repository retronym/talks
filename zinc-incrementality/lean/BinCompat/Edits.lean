import BinCompat.Mima
import Jvm.Clients

/-!
# A space of library edits, and the clients they could break

Single edits to two base libraries in package `p1`: one header change to a class (abstract,
final, interface, public, superclass, superinterfaces), or one member slot (`m()V`, `m()I`, the
field `m`) set to absent or to any combination of flags. Edits that give a classfile the JVM
would reject (`ClassFormatError`: a final interface method, a protected interface member, a
non-constant interface field, an abstract static method, …) or a cyclic hierarchy are left out.

Clients are `Jvm.Clients.space3` with `X` also implementing `J` and `I, J`, and the `m()I` call
sites of `Jvm.Clients.space`. This is the space MiMa's verdicts are compared on; enumeration
here is testing, per `DESIGN-spec.md`.
-/

namespace BinCompat

open Jvm Jvm.Catalogue Jvm.Clients

def pub1 : Header C := { pkg := 1 }
def itf1 : Header C := { pkg := 1, isInterface := true }

/-- A sparse base: `A` with a method and a field, `B extends A`, `I` with a default, `J` empty. -/
def base1 : Lib :=
  [(.A, { header := pub1, methods := [(.m, .v, {})], fields := [(.m, .s, {})] }),
   (.B, { header := { pub1 with super := some .A } }),
   (.I, { header := itf1, methods := [(.m, .v, {})] }),
   (.J, { header := itf1 })]

/-- A dense base: overrides, an abstract interface method implemented by a class, a constant. -/
def base2 : Lib :=
  [(.A, { header := pub1, methods := [(.m, .v, {})], fields := [(.m, .s, {})] }),
   (.B, { header := { pub1 with super := some .A, ifaces := [.I] }, methods := [(.m, .v, {})],
          fields := [(.m, .s, { isStatic := true })] }),
   (.I, { header := itf1, methods := [(.m, .v, { isAbstract := true })],
          fields := [(.m, .s, { isStatic := true, isFinal := true })] }),
   (.J, { header := { itf1 with ifaces := [.I] }, methods := [(.m, .v, {})] })]

def bools : List Bool := [false, true]
def accesses : List Access := [.pub, .prot, .pkg, .priv]

def methodInfos : List MethodInfo := do
  let s ← bools; let a ← bools; let f ← bools; let acc ← accesses
  pure { isStatic := s, isAbstract := a, isFinal := f, access := acc }

def fieldInfos : List FieldInfo := do
  let s ← bools; let f ← bools; let acc ← accesses
  pure { isStatic := s, isFinal := f, access := acc }

def wfMethod (itf : Bool) (m : MethodInfo) : Bool :=
  !(m.isAbstract && (m.isStatic || m.isFinal || m.access == .priv)) &&
  (!itf || (!m.isFinal && (m.access == .pub || m.access == .priv) &&
            !(m.access == .priv && m.isAbstract)))

def wfField (itf : Bool) (f : FieldInfo) : Bool :=
  !itf || (f.isStatic && f.isFinal && f.access == .pub)

/-- The JVM's format checks, and an acyclic hierarchy. -/
def wf (l : Lib) : Bool :=
  l.all fun (c, cf) =>
    let h := cf.header
    let itf := h.isInterface
    (!itf || (h.super.isNone && !h.isFinal)) && !(h.isAbstract && h.isFinal) &&
    h.super != some c && !h.ifaces.contains c &&
    !(supers l fuel c).contains c && !(allIfaces l fuel c).contains c &&
    cf.methods.all (fun m => wfMethod itf m.2.2) && cf.fields.all (fun f => wfField itf f.2.2)

def setMethod (cf : Classfile C N D) (d : D) (m : Option MethodInfo) : Classfile C N D :=
  { cf with methods := (cf.methods.filter (·.2.1 != d)) ++ (m.map fun i => (N.m, d, i)).toList }

def setField (cf : Classfile C N D) (f : Option FieldInfo) : Classfile C N D :=
  { cf with fields := f.map (fun i => [(N.m, D.s, i)]) |>.getD [] }

def headers (c : C) (h : Header C) : List (Header C) :=
  [{ h with isAbstract := !h.isAbstract }, { h with isFinal := !h.isFinal },
   { h with isInterface := !h.isInterface, super := none }, { h with isPublic := !h.isPublic }] ++
  ([none, some C.A, some C.B].filter (· != h.super) |>.filter (· != some c) |>.map fun s =>
    { h with super := s }) ++
  ([[], [C.I], [C.J], [C.I, C.J]].filter (· != h.ifaces) |>.map fun is => { h with ifaces := is })

def variants (c : C) (cf : Classfile C N D) : List (Classfile C N D) :=
  (headers c cf.header).map (fun h => { cf with header := h }) ++
  ([D.v, D.i].flatMap fun d => (none :: methodInfos.map some).map (setMethod cf d)) ++
  ((none :: fieldInfos.map some).map (setField cf))

def replace (l : Lib) (c : C) (cf : Classfile C N D) : Lib :=
  l.map fun p => if p.1 = c then (c, cf) else p

/-- Single edits of a base: well-formed, and different from it. -/
def editsOf (l : Lib) : List Lib :=
  (l.flatMap fun (c, cf) => (variants c cf).map (replace l c)).filter fun l' =>
    wf l' && !(l'.map (·.2.header) = l.map (·.2.header) &&
               l'.map (·.2.methods) = l.map (·.2.methods) && l'.map (·.2.fields) = l.map (·.2.fields))

structure Edit where
  name : String
  v0 : Lib
  v1 : Lib

def edits : List Edit :=
  ((editsOf base1).zipIdx.map fun (l, i) => { name := s!"b1-{i}", v0 := base1, v1 := l }) ++
  ((editsOf base2).zipIdx.map fun (l, i) => { name := s!"b2-{i}", v0 := base2, v1 := l })

def Edit.case (e : Edit) : Case := { name := e.name, mima := none, v0 := e.v0, v1 := e.v1, prog := {} }

/-! ## Clients -/

def xClassesB : List (Classfile C N D) := do
  let s ← [none, some C.A, some C.B]
  let is ← [[], [C.I], [C.J], [C.I, C.J]]
  let ms ← [[], [(N.m, D.v, ({} : MethodInfo))]]
  pure { header := { super := s, ifaces := is }, methods := ms }

def sitesB : List (Site C N D) :=
  sites3 ++ ([C.A, C.B, C.I, C.J].flatMap fun c =>
    [.invokestatic c .m .i, .invokestaticIface c .m .i] ++
    ([C.A, C.B, C.X].flatMap fun r => [.invokevirtual c .m .i r, .invokeinterface c .m .i r]))

def spaceB : List Client :=
  (sitesB.map fun s => ([], { sites := [s] })) ++
  (xClassesB.flatMap fun x => sitesB.map fun s => ([(.X, x)], { loads := [.X], sites := [s] }))

end BinCompat
