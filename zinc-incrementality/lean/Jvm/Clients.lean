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

def recvOf : Site C N D → Option (C × C)
  | .invokevirtual c _ _ r => some (r, c)
  | .invokeinterface c _ _ r => some (r, c)
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
def breaking (k : Case) : Option Client :=
  space.find? fun (cl, p) =>
    let k' := k.withClient (cl, p)
    wellTyped k'.w0 p && links k'.w0 p && !links k'.w1 p

def breaksSomeClient (k : Case) : Bool := (breaking k).isSome

/-- The first client that links on both and runs a different method. -/
def changing (k : Case) : Option Client :=
  space.find? fun (cl, p) =>
    let k' := k.withClient (cl, p)
    wellTyped k'.w0 p && links k'.w0 p && links k'.w1 p && k'.before != k'.after

def changesSomeClient (k : Case) : Bool := (changing k).isSome

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

end Jvm.Clients
