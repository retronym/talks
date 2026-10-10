import BinCompat.Keys

/-!
# A corrected rule set

MiMa's keys plus four, one per gap in `BinCompat/Keys.lean`:

* `resolveMethod c n d`, `resolveField c n d`: for a public class `c` of the old library and every
  name and descriptor, the member a client's reference *through `c`* resolves to (JVMS §5.4.3.2–4,
  private members and superinterfaces included), compared by access, `static`, `abstract` and
  `final`. MiMa compares only the members `c` declares, looked up without private members or
  (for fields) interfaces: gaps M1 and F1.
* `ifaceField t n d`: an interface that sees a field it did not see before, which a client class
  extending a public class and implementing `t` would resolve before the class's field (F2).
* `defaults t n d`: an interface gaining a default method that another public interface, unrelated
  to it, also has (D1). In general a client's own interface can have a default of any name, so any
  new default can conflict; in the model's client space, clients implement only library interfaces.

Soundness on the space: every edit in `BinCompat.edits` that breaks a client of `spaceB` is
reported. Checked by kernel `decide` (enumeration as testing, per `DESIGN-spec.md`; not a proof for
all libraries).
-/

namespace BinCompat

open Jvm Jvm.Catalogue Jvm.Clients

inductive Extra
  | resolvedMethodChanged
  | resolvedFieldChanged
  | ifaceFieldShadows
  | defaultConflict
  deriving DecidableEq, Repr

def Extra.name : Extra → String
  | .resolvedMethodChanged => "ResolvedMethodChanged"
  | .resolvedFieldChanged => "ResolvedFieldChanged"
  | .ifaceFieldShadows => "InterfaceFieldShadows"
  | .defaultConflict => "DefaultConflict"

def rank : Access → ℕ | .pub => 3 | .prot => 2 | .pkg => 1 | .priv => 0

/-- Method resolution through `c`, without the access check (§5.4.3.3, §5.4.3.4). -/
def rawResolve (c : C) (n : N) (d : D) : M C N D (C × MethodInfo) := do
  let h ← hdr c
  if h.isInterface then
    match ← askMethod c n d with
    | some i => pure (c, i)
    | none => fromIfaces c n d
  else
    match ← chain false n d depth c with
    | some r => pure r
    | none => fromIfaces c n d

def runIn {α : Type} (l : Lib) (t : M C N D α) : Except LinkError α := t.run.run (answer (world l))

def resolveMethodCheck (o n : Lib) (c : C) (mn : N) (md : D) : Bool :=
  match runIn o (rawResolve c mn md) with
  | .error _ => false
  | .ok (_, i0) =>
    if rank i0.access < 2 then false
    else match runIn n (rawResolve c mn md) with
      | .error _ => true
      | .ok (_, i1) =>
        rank i1.access < rank i0.access || i0.isStatic != i1.isStatic ||
          (!i0.isAbstract && i1.isAbstract) || (!i0.isFinal && i1.isFinal)

def resolveFieldCheck (o n : Lib) (c : C) (fn : N) (fd : D) : Bool :=
  match runIn o (lookupField fn fd depth c) with
  | .error _ | .ok none => false
  | .ok (some (_, f0)) =>
    if rank f0.access < 2 then false
    else match runIn n (lookupField fn fd depth c) with
      | .error _ | .ok none => true
      | .ok (some (_, f1)) =>
        rank f1.access < rank f0.access || f0.isStatic != f1.isStatic || (!f0.isFinal && f1.isFinal)

def declaresField (l : Lib) (t : C) (fn : N) (fd : D) : Bool :=
  (((get l t).map (·.fields)).getD []).any fun f => f.1 = fn ∧ f.2.1 = fd

def isIface (l : Lib) (t : C) : Bool := ((get l t).map (·.header.isInterface)).getD false

/-- `t` is an interface that sees a field `fn` now and saw none before. -/
def ifaceFieldCheck (o n : Lib) (t : C) (fn : N) (fd : D) : Bool :=
  isIface o t && isIface n t && declaresField n t fn fd &&
    (match runIn o (lookupField fn fd depth t) with | .ok (some _) => false | _ => true) &&
    n.any fun (c, cf) =>
      cf.header.isPublic && !cf.header.isInterface && !cf.header.isFinal &&
        !(allIfaces n fuel c).contains t &&
        match runIn n (lookupField fn fd depth c) with
        | .ok (some _) => true
        | _ => false

def isDefault (l : Lib) (t : C) (mn : N) (md : D) : Bool :=
  (meths l t).any fun m => m.1 = mn ∧ m.2.1 = md ∧ !m.2.2.isAbstract ∧ !m.2.2.isStatic

def defaultsCheck (o n : Lib) (t : C) (mn : N) (md : D) : Bool :=
  isIface n t && isDefault n t mn md && !(isIface o t && isDefault o t mn md) &&
    n.any fun (u, cf) =>
      u != t && cf.header.isPublic && cf.header.isInterface && isDefault n u mn md &&
        !(allIfaces n fuel u).contains t && !(allIfaces n fuel t).contains u

def allN : List N := [.m]
def allMD : List D := [.v, .i]
def allFD : List D := [.s]

/-- The extra problems, per class public in the old library. -/
def extra (o n : Lib) : List Extra :=
  o.flatMap fun (c, cf) =>
    if !cf.header.isPublic then []
    else
      (allN.flatMap fun mn => allMD.filterMap fun md =>
        if resolveMethodCheck o n c mn md then some .resolvedMethodChanged else none) ++
      (allN.flatMap fun fn => allFD.filterMap fun fd =>
        if resolveFieldCheck o n c fn fd then some .resolvedFieldChanged else none) ++
      (allN.flatMap fun fn => allFD.filterMap fun fd =>
        if ifaceFieldCheck o n c fn fd then some .ifaceFieldShadows else none) ++
      (allN.flatMap fun mn => allMD.filterMap fun md =>
        if defaultsCheck o n c mn md then some .defaultConflict else none)

/-- The corrected rule set reports something. -/
def fixedReports (o n : Lib) : Bool := mima o n != [] || extra o n != []

/-- Each witness of a MiMa gap is reported by the corrected rules. -/
example : [finalField, shadowStatic, shadowField, overridePrivate, ifaceField, defaultConflict].all
    (fun x => fixedReports x.o x.n) = true := by decide +kernel

/-! ## The edit space, indexed for `BinCompat/Sound.lean` -/


def baseOf : ℕ → Lib | 1 => base1 | _ => base2

/-- The `i`-th variant of class `c` in base `b`. -/
def variant (b : ℕ) (c : C) (i : ℕ) : Lib :=
  let l := baseOf b
  match get l c with
  | some cf => match (variants c cf)[i]? with
    | some cf' => replace l c cf'
    | none => l
  | none => l

/-- The same library: not an edit. -/
def same (o n : Lib) : Bool :=
  o.map (·.2.header) == n.map (·.2.header) && o.map (·.2.methods) == n.map (·.2.methods) &&
    o.map (·.2.fields) == n.map (·.2.fields)

/-- The variant is not a well-formed edit, or the corrected rules report it, or no client breaks. -/
def sound (b : ℕ) (c : C) (i : ℕ) : Bool :=
  let o := baseOf b
  let n := variant b c i
  !wf n || same o n || fixedReports o n ||
    !breaksSomeClient { name := "", mima := none, v0 := o, v1 := n, prog := {} } spaceB

/-- How many variants a class has. -/
def nVariants (b : ℕ) (c : C) : ℕ := ((get (baseOf b) c).map (variants c ·)).getD [] |>.length

/-- The variants that are well-formed edits the corrected rules do not report: these are run
against every client, one `example` each; the rest are sound without running a client. -/
def unreported (b : ℕ) (c : C) : List ℕ :=
  (List.range (nVariants b c)).filter fun i =>
    let n := variant b c i
    wf n && !same (baseOf b) n && !fixedReports (baseOf b) n

end BinCompat
