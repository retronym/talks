import Scala.Lower

/-!
# A catalogue of Scala library edits, lowered and linked

The source-level counterpart of `Jvm/Catalogue.lean`, and the input track B needs for source-level
spaces (B3). Each case is a library edit (`v0` → `v1`, Scala sources), client units compiled
against `v0`, and a JVM program (the classes the client loads and the call sites it executes).
Library and client are lowered with `Scala.lower`, then linked with `Jvm.outcome`:

* `before`: the client against `v0`;
* `after`: the same client classfiles against `v1` (what MiMa asks about);
* `fresh`: the client recompiled against `v1` (what a clean build runs, and what Zinc must reach).

`after ≠ fresh` with both linking is "links, but runs different code than a clean build": binary
compatible, yet Zinc must recompile the client. `widenedToValueClass` shows the other gap: the
edited unit is `V`, but the classfile that changes is `W`'s, because lowering `W` read `V`.

Sites that would run a trait method's body through `invokestatic T.m$` or `T.$init$` are left
out: `Jvm` does not model static interface methods yet (J3).
-/

namespace Scala.Catalogue

open Jvm (LinkError)

abbrev S := Jvm.Site String String String

structure Case where
  name : String
  /-- The MiMa problem expected to report the edit, if any (to be checked by track B). -/
  mima : Option String
  dl : Dialect := .s213
  v0 : Program
  v1 : Program
  client : Program := []
  loads : List String := []
  sites : List S := []

/-- Lower the library alone, and the client against the library; both link against the standard
library (the prelude's classfiles). -/
def build (dl : Dialect) (lib client : Program) : Except String (List ClassOut) := do
  let l ← lowerProgram dl lib
  let env := (prelude dl ++ (lib ++ client).desugar dl).env
  let c ← (client.desugar dl).mapM fun s => lower dl s env
  pure (c.flatten ++ l ++ (← preludeClasses dl))

def Case.prog (k : Case) : Jvm.Program String String String := { loads := k.loads, sites := k.sites }

def run (cs : Except String (List ClassOut)) (p : Jvm.Program String String String) :
    Except String (Except LinkError (List String)) :=
  cs.map fun cs => Jvm.outcome (toWorld cs) p

def Case.before (k : Case) := run (build k.dl k.v0 k.client) k.prog

def Case.after (k : Case) := run (do
  let c ← build k.dl k.v0 k.client
  let l1 := (← lowerProgram k.dl k.v1) ++ (← preludeClasses k.dl)
  let l0 ← lowerProgram k.dl k.v0
  -- the client's classfiles, compiled against v0, next to v1's library
  pure ((c.filter fun x => !l0.any (·.name == x.name)) ++ l1)) k.prog

def Case.fresh (k : Case) := run (build k.dl k.v1 k.client) k.prog

open Jvm.Site

def trt (n : String) (ms : List Mem) (ps : List Parent := []) : Src :=
  { name := n, cls := some { name := n, kind := .trt, members := ms, traits := ps } }
def cls (n : String) (ms : List Mem) (sup : Option Parent := none) (ts : List Parent := []) : Src :=
  { name := n, cls := some { name := n, members := ms, super := sup, traits := ts } }
def dfn (n : String) (abs : Bool := false) : Mem := { name := n, res := .int, abs := abs }

/-- A concrete method added to a trait: a default method, so a client class compiled before it
(without a mixin forwarder) still links and selects it. -/
def concreteAddedToTrait : Case where
  name := "concreteAddedToTrait"
  mima := none
  v0 := [trt "T" [dfn "a"]]
  v1 := [trt "T" [dfn "a", dfn "b"]]
  client := [cls "X" [] none [("T", [])]]
  loads := ["X"]
  sites := [new "X", invokevirtual "X" "a" "()I" "X", invokeinterface "T" "b" "()I" "X"]

/-- An abstract method added to a trait: a caller compiled against `v1` hits the old client
class, which does not implement it. -/
def abstractAddedToTrait : Case where
  name := "abstractAddedToTrait"
  mima := some "ReversedMissingMethodProblem"
  v0 := [trt "T" [dfn "a"]]
  v1 := [trt "T" [dfn "a", dfn "b" true]]
  client := [cls "X" [] none [("T", [])]]
  loads := ["X"]
  sites := [invokeinterface "T" "b" "()I" "X"]

/-- A `val` added to a trait: its getter is abstract in the interface and implemented in each
class that mixes the trait in, so an old client class lacks it. On HotSpot (2.13.18) the failure
comes earlier, at `new X`: `T.$init$` calls the setter the old class lacks. -/
def valAddedToTrait : Case where
  name := "valAddedToTrait"
  mima := some "ReversedMissingMethodProblem"
  v0 := [trt "T" [dfn "a"]]
  v1 := [trt "T" [dfn "a", { name := "v", res := .int, isVal := true }]]
  client := [cls "X" [] none [("T", [])]]
  loads := ["X"]
  sites := [invokeinterface "T" "v" "()I" "X"]

/-- A class becomes a trait: the client's subclass now extends an interface. -/
def classBecomesTrait : Case where
  name := "classBecomesTrait"
  mima := some "IncompatibleTemplateDefProblem"
  v0 := [cls "C" [dfn "m"]]
  v1 := [trt "C" [dfn "m"]]
  client := [cls "X" [] (some ("C", []))]
  loads := ["X"]

/-- A parameter with a default added to an object's method: the descriptor changes (plus a
`f$default$2` getter, not modelled), so the old call site finds nothing. -/
def paramWithDefaultAdded : Case where
  name := "paramWithDefaultAdded"
  mima := some "DirectMissingMethodProblem"
  v0 := [{ name := "O", obj := some { name := "O", kind := .obj, members := [{ name := "f", params := [.int], res := .int }] } }]
  v1 := [{ name := "O", obj := some { name := "O", kind := .obj, members := [{ name := "f", params := [.int, .int], res := .int }] } }]
  sites := [invokevirtual "O$" "f" "(I)I" "O$", invokestatic "O" "f" "(I)I"]

/-- A concrete method added to a trait, overriding a method the client's superclass already has.
The old client class has no forwarder, so the JVM selects the superclass's method; a fresh
compile adds a forwarder and runs the trait's. Links either way; MiMa has nothing to report;
Zinc must recompile the client. Confirmed on HotSpot with 2.13.18. -/
def traitOverrideAdded : Case where
  name := "traitOverrideAdded"
  mima := none
  v0 := [trt "R" [dfn "m" true], cls "B" [dfn "m"] none [("R", [])], trt "T" [] [("R", [])]]
  v1 := [trt "R" [dfn "m" true], cls "B" [dfn "m"] none [("R", [])], trt "T" [dfn "m"] [("R", [])]]
  client := [cls "X" [] (some ("B", [])) [("T", [])]]
  loads := ["X"]
  sites := [invokevirtual "X" "m" "()I" "X"]

/-- A class becomes a value class. `W`'s source is unchanged, but its method's descriptor is
lowered through `V`'s erasure, so `W`'s classfile changes and the old call site breaks. -/
def widenedToValueClass : Case where
  name := "widenedToValueClass"
  mima := some "IncompatibleMethTypeProblem"
  v0 := [cls "V" [], cls "W" [{ name := "use", params := [.ref "V"], res := .int }]]
  v1 := [{ name := "V", cls := some { name := "V", kind := .vcls, under := some ("x", .int) } },
         cls "W" [{ name := "use", params := [.ref "V"], res := .int }]]
  sites := [invokevirtual "W" "use" "(LV;)I" "W"]

def caseClass (ps : List Ty) : Src :=
  { name := "P", cls := some { name := "P", isCase := true, cparams := ps.zipIdx.map fun (t, i) => (s!"x{i}", t) } }

/-- A field added to a case class: the accessor of the old field still links, but the constructor,
`apply` (the companion's and its static forwarder) and `copy` change descriptor, so a client
that builds or copies values breaks (and MiMa reports each). -/
def caseFieldAdded : Case where
  name := "caseFieldAdded"
  mima := some "DirectMissingMethodProblem"
  v0 := [caseClass [.int]]
  v1 := [caseClass [.int, .int]]
  sites := [invokevirtual "P" "x0" "()I" "P", invokevirtual "P" "copy" "(I)LP;" "P",
            invokestatic "P" "apply" "(I)LP;"]

def all : List Case :=
  [concreteAddedToTrait, abstractAddedToTrait, valAddedToTrait, classBecomesTrait,
   paramWithDefaultAdded, traitOverrideAdded, widenedToValueClass, caseFieldAdded]

example : caseFieldAdded.before = .ok (.ok ["P", "P", "P"]) ∧
    caseFieldAdded.after = .ok (.error .noSuchMethod) := by decide +kernel

example : concreteAddedToTrait.after = .ok (.ok ["X", "X", "T"]) := by decide +kernel
example : abstractAddedToTrait.after = .ok (.error .abstractMethod) := by decide +kernel
example : valAddedToTrait.after = .ok (.error .abstractMethod) ∧
    valAddedToTrait.fresh = .ok (.ok ["X"]) := by decide +kernel
example : classBecomesTrait.before = .ok (.ok []) ∧
    classBecomesTrait.after = .ok (.error .incompatibleClassChange) := by decide +kernel
example : paramWithDefaultAdded.before = .ok (.ok ["O$", "O"]) ∧
    paramWithDefaultAdded.after = .ok (.error .noSuchMethod) := by decide +kernel
example : traitOverrideAdded.before = .ok (.ok ["B"]) ∧ traitOverrideAdded.after = .ok (.ok ["B"]) ∧
    traitOverrideAdded.fresh = .ok (.ok ["X"]) := by decide +kernel
example : widenedToValueClass.before = .ok (.ok ["W"]) ∧
    widenedToValueClass.after = .ok (.error .noSuchMethod) := by decide +kernel

/-- `W` is the unit whose classfile changes, and its lowering trace shows why: it asked for `V`. -/
example : (trace .s213 (cls "W" [{ name := "use", params := [.ref "V"], res := .int }])
    widenedToValueClass.v0.env).contains (.decl "V" false) = true := by decide +kernel

end Scala.Catalogue
