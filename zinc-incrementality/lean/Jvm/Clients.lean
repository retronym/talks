import Jvm.Catalogue

/-!
# Client spaces: does an edit break *some* client?

MiMa reports a problem for an edit without naming a client; its claim is that some client compiled
against `v0` fails to link against `v1`. The model's version of that claim quantifies over a bounded
space of clients over the catalogue's universe:

- an optional client class `X`: superclass none, `A` or `B`; superinterfaces a subset of `I`, `J`;
  declares nothing, `m()V` or `m()I`;
- one call site: `invokestatic`, `invokevirtual`, `invokeinterface` of `m` with either descriptor on
  any owner, or `new` of any class; the receiver is a class whose static type is the owner in `v0`
  (`isSub`), as a compiler would emit it.

One site suffices: linking is lazy and per site, so a client fails on `v1` iff one of its sites
(or its loads) does. `breaksSomeClient` is the model's verdict for a MiMa problem; `changesSomeClient`
adds "links on both, and runs a different method" (the J4 verdict for `overrideAdded`, `pulledUp`).
Checked per catalogue case by kernel `decide`.

Not in the space: clients with more than one class, fields, `invokespecial`; and the verifier's
assignability checks, which a real client's `v1` receivers also face (`superclassRemoved` breaks
`B b; b.m()` compiled as `invokevirtual A.m` by a `VerifyError`).
-/

namespace Jvm.Clients

open Jvm.Catalogue

/-- `r` is `c` or a subtype of `c` in `w`, by superclasses and superinterfaces, with fuel. -/
def isSub (w : W) : ℕ → C → C → Bool
  | 0, _, _ => false
  | k + 1, r, c =>
    r == c ||
      match w r with
      | none => false
      | some cf => (cf.header.super.toList ++ cf.header.ifaces).any fun s => isSub w k s c

def allC : List C := [.A, .B, .I, .J, .X]
def allD : List D := [.v, .i]

def xClasses : List (Classfile C N D) := do
  let s ← [none, some .A, some .B]
  let is ← [[], [.I], [.J], [.I, .J]]
  let ms ← [[], [(.m, .v, inst)], [(.m, .i, inst)]]
  pure { header := { super := s, ifaces := is }, methods := ms }

def sites : List (Site C N D) :=
  (allC.flatMap fun c => allD.map fun d => .invokestatic c .m d) ++
  (allC.flatMap fun c => allD.flatMap fun d => [.A, .B, .X].map fun r => .invokevirtual c .m d r) ++
  (allC.flatMap fun c => allD.flatMap fun d => [.A, .B, .X].map fun r => .invokeinterface c .m d r) ++
  allC.map .new

/-- A client: its classes and its program. -/
abbrev Client := List (C × Classfile C N D) × P

def space : List Client :=
  (sites.map fun s => ([], { sites := [s] })) ++
  (xClasses.flatMap fun x => sites.map fun s => ([(.X, x)], { loads := [.X], sites := [s] }))

/-- The J3 space: `X` in the unnamed package, superclass none, `A` or `B`, implementing `I` or not,
declaring nothing or a public `m()V`; one site of any kind (methods `m()V`, fields `m:String`), run
from a class of its own or from `X` (`invokespecial` only from `X`). -/
def xClasses3 : List (Classfile C N D) := do
  let s ← [none, some .A, some .B]
  let is ← [[], [.I]]
  let ms ← [[], [(.m, .v, inst)]]
  pure { header := { super := s, ifaces := is }, methods := ms }

def sites3 : List (Site C N D) :=
  let rs : List C := [.A, .B, .X]
  let direct : List (Site C N D) :=
    (allC.flatMap fun c => rs.flatMap fun r =>
      [.invokevirtual c .m .v r, .invokeinterface c .m .v r, .getfield c .m .s r, .putfield c .m .s r]) ++
    (allC.flatMap fun c =>
      [.invokestatic c .m .v, .invokestaticIface c .m .v, .getstatic c .m .s, .putstatic c .m .s, .new c])
  direct ++ direct.map (.within .X) ++
    (allC.flatMap fun c => [true, false].map fun i => .within .X (.invokespecial c .m .v i))

def space3 : List Client :=
  (sites3.map fun s => ([], { sites := [s] })) ++
  (xClasses3.flatMap fun x => sites3.map fun s => ([(.X, x)], { loads := [.X], sites := [s] }))

def recvOf : Site C N D → Option (C × C)
  | .invokevirtual c _ _ r => some (r, c)
  | .invokeinterface c _ _ r => some (r, c)
  | .getfield c _ _ r => some (r, c)
  | .putfield c _ _ r => some (r, c)
  | .within _ s => recvOf s
  | _ => none

/-- The client is one a compiler could emit against `w₀`: each receiver's class is a subtype of the
site's owner. -/
def wellTyped (w₀ : W) (p : P) : Bool :=
  p.sites.all fun s => match recvOf s with
    | some (r, c) => isSub w₀ depth r c
    | none => true

def _root_.Jvm.Catalogue.Case.withClient (k : Case) (cl : Client) : Case := { k with client := cl.1, prog := cl.2 }

def links (w : W) (p : P) : Bool := (outcome w p).toBool

/-- The first client in the space that links on `v0` and fails on `v1`. -/
def breaking (k : Case) (sp : List Client := space) : Option Client :=
  sp.find? fun (cl, p) =>
    let k' := k.withClient (cl, p)
    wellTyped k'.w0 p && links k'.w0 p && !links k'.w1 p

def breaksSomeClient (k : Case) (sp : List Client := space) : Bool := (breaking k sp).isSome

/-- The first client that links on both and runs a different method. -/
def changing (k : Case) (sp : List Client := space) : Option Client :=
  sp.find? fun (cl, p) =>
    let k' := k.withClient (cl, p)
    wellTyped k'.w0 p && links k'.w0 p && links k'.w1 p && k'.before != k'.after

def changesSomeClient (k : Case) (sp : List Client := space) : Bool := (changing k sp).isSome

/-! ## Verdicts per catalogue case -/

example : breaksSomeClient methodRemoved = true := by decide +kernel
example : breaksSomeClient resultTypeChanged = true := by decide +kernel
example : breaksSomeClient classBecomesInterface = true := by decide +kernel
example : breaksSomeClient becomesStatic = true := by decide +kernel
example : breaksSomeClient becomesAbstract = true := by decide +kernel
example : breaksSomeClient becomesFinal = true := by decide +kernel
example : breaksSomeClient methodBecomesFinal = true := by decide +kernel
example : breaksSomeClient superclassRemoved = true := by decide +kernel
example : breaksSomeClient defaultRemoved = true := by decide +kernel
example : breaksSomeClient defaultConflict = true := by decide +kernel
example : breaksSomeClient overrideAdded = false ∧ changesSomeClient overrideAdded = true := by
  decide +kernel
example : breaksSomeClient pulledUp = false ∧ changesSomeClient pulledUp = true := by decide +kernel

/-! ## J3 verdicts, over `space3` -/

example : breaksSomeClient methodBecomesPrivate space3 = true := by decide +kernel
example : breaksSomeClient methodBecomesPackagePrivate space3 = true := by decide +kernel
example : breaksSomeClient classBecomesPackagePrivate space3 = true := by decide +kernel
example : breaksSomeClient methodBecomesProtected space3 = true := by decide +kernel
/-- Breaks `invokevirtual B.m`: resolution finds the private `B.m` before the inherited `A.m`. -/
example : breaksSomeClient overrideBecomesPrivate space3 = true ∧
    changesSomeClient overrideBecomesPrivate space3 = true := by decide +kernel
example : breaksSomeClient superCallPulledUp space3 = false ∧
    changesSomeClient superCallPulledUp space3 = true := by decide +kernel
example : breaksSomeClient superCallRemoved space3 = true := by decide +kernel
example : breaksSomeClient superCallAbstract space3 = true := by decide +kernel
example : breaksSomeClient defaultSuperCallAbstract space3 = true := by decide +kernel
example : breaksSomeClient staticIfaceMethodRemoved space3 = true := by decide +kernel
example : breaksSomeClient staticMovedToIface space3 = true := by decide +kernel
example : breaksSomeClient defaultBecomesStatic space3 = true := by decide +kernel
example : breaksSomeClient defaultBecomesPrivate space3 = true := by decide +kernel
example : breaksSomeClient fieldRemoved space3 = true := by decide +kernel
example : breaksSomeClient fieldBecomesStatic space3 = true := by decide +kernel
example : breaksSomeClient fieldBecomesFinal space3 = true := by decide +kernel
example : breaksSomeClient fieldBecomesPrivate space3 = true := by decide +kernel
example : breaksSomeClient fieldShadowed space3 = false ∧
    changesSomeClient fieldShadowed space3 = true := by decide +kernel
/-- Breaks `putstatic B.m`: it now resolves to the interface's field, which is final. -/
example : breaksSomeClient fieldIfaceBeforeSuper space3 = true ∧
    changesSomeClient fieldIfaceBeforeSuper space3 = true := by decide +kernel
example : breaksSomeClient putstaticBecomesFinal space3 = true := by decide +kernel

end Jvm.Clients
