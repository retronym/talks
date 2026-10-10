import Java.Lower

/-!
# A catalogue of Java library edits, lowered and linked

The Java counterpart of `Scala/Catalogue.lean`, and input for track B's source-level spaces. Each
case is a library edit (`v0` → `v1`, Java declarations), client units compiled against `v0`, and
a JVM program: the classes the client loads, the sites it executes directly, and client methods
whose bodies it runs (their `getstatic`s and invokes, read off the client's lowered classfile).

* `before`: the client against `v0`;
* `after`: the same client classfiles against `v1` (what MiMa asks about);
* `fresh`: the client recompiled against `v1` (what a clean build runs, and what Zinc must reach).

Only the bodies in `runs` change between `after` and `fresh`; hand-written `sites` are the same
call sites in both, so `fresh` is meaningful only for cases whose client calls are in `runs`.
`recompiles` says whether a clean build changes the client's classfiles at all: a constant edit
changes them although every outcome is the same (JLS §13.4.9).

`Java/Jls13.lean` checks the cases against JLS chapter 13.
-/

namespace Java.Catalogue

open Jvm (LinkError)

abbrev S := Jvm.Site String String String

structure Case where
  name : String
  /-- The MiMa problem expected to report the edit, if any (to be checked by track B). -/
  mima : Option String
  v0 : Program
  v1 : Program
  client : Program := []
  loads : List String := []
  sites : List S := []
  /-- Client methods `(class, method)` whose bodies run after `sites`. -/
  runs : List (String × String) := []

/-- The client's classfiles, compiled against `lib`. -/
def clientOf (lib client : Program) : Except String (List ClassOut) := do
  let c ← client.mapM fun u => lower u (lib ++ client).env
  pure c.flatten

def Insn.site : Insn → Option S
  | ⟨"getstatic", o, n, d⟩ => some (.getstatic o n d)
  | ⟨"invokestatic", o, n, d⟩ => some (.invokestatic o n d)
  | ⟨"invokevirtual", o, n, d⟩ => some (.invokevirtual o n d o)
  | ⟨"invokeinterface", o, n, d⟩ => some (.invokeinterface o n d o)
  | _ => none

/-- The sites of the bodies of `runs`, as compiled into `client`. -/
def bodySites (client : List ClassOut) (runs : List (String × String)) : List S :=
  runs.flatMap fun (c, m) => match client.find? (·.name == c) with
    | some k => (k.methods.filter (·.name == m)).flatMap fun mo =>
        mo.calls.filterMap fun i => (Insn.site i).map (.within c)
    | none => []

def Case.prog (k : Case) (client : List ClassOut) : Jvm.Program String String String :=
  { loads := k.loads, sites := k.sites ++ bodySites client k.runs }

def Case.world (client : Except String (List ClassOut)) (lib : Program) :
    Except String (List ClassOut × Jvm.World String String String) := do
  let c ← client
  let l ← lowerProgram lib
  pure (c, toWorld (c ++ l))

def Case.run (k : Case) (client : Except String (List ClassOut)) (lib : Program) :
    Except String (Except LinkError (List String)) :=
  (Case.world client lib).map fun (c, w) => Jvm.outcome w (k.prog c)

def Case.before (k : Case) := k.run (clientOf k.v0 k.client) k.v0
def Case.after (k : Case) := k.run (clientOf k.v0 k.client) k.v1
def Case.fresh (k : Case) := k.run (clientOf k.v1 k.client) k.v1

/-- Does a clean build against `v1` change the client's classfiles? -/
def Case.recompiles (k : Case) : Bool :=
  match clientOf k.v0 k.client, clientOf k.v1 k.client with
  | .ok a, .ok b => a != b
  | _, _ => true

/-- The class tables `before` and `after` link in (empty if lowering fails). -/
def Case.w0 (k : Case) : Jvm.World String String String :=
  match Case.world (clientOf k.v0 k.client) k.v0 with | .ok (_, w) => w | .error _ => fun _ => none
def Case.w1 (k : Case) : Jvm.World String String String :=
  match Case.world (clientOf k.v0 k.client) k.v1 with | .ok (_, w) => w | .error _ => fun _ => none
def Case.p0 (k : Case) : Jvm.Program String String String :=
  match clientOf k.v0 k.client with | .ok c => k.prog c | .error _ => k.prog []

/-- `compatible_of_footprint`, with agreement on the footprint decided query by query. -/
theorem compatible_of_agrees (w₀ w₁ : Jvm.World String String String) (p : Jvm.Program String String String)
    (h : (Jvm.footprint w₀ p).all (Jvm.agrees w₀ w₁) = true) : Jvm.Compatible w₀ w₁ p :=
  Jvm.compatible_of_footprint w₀ w₁ p fun q hq => (Jvm.agrees_iff w₀ w₁ q).1 (List.all_eq_true.1 h q hq)

open Jvm.Site

def cls (n : String) (ms : List Meth := []) (sup : Option Parent := none) (ifs : List Parent := [])
    (fs : List Field := []) : CUnit :=
  [{ name := n, methods := ms, super := sup, ifaces := ifs, fields := fs }]
def itf (n : String) (ms : List Meth := []) (fs : List Field := []) : CUnit :=
  [{ name := n, kind := .iface, methods := ms, fields := fs }]
def dfn (n : String) (abs : Bool := false) : Meth := { name := n, res := .int, abs := abs }
def konst (n : String) (e : Expr) : Field := { name := n, ty := .int, init := some e }
def returns (n : String) (e : Expr) : Meth := { name := n, res := .int, ret := some e }

/-! ## Constants (§13.4.9) -/

/-- A constant's value changes. The client's copy is folded in, so it never touches `A`: it links
before and after, MiMa has nothing to report, yet a clean build changes its classfile. -/
def constantValueChanged : Case where
  name := "constantValueChanged"
  mima := none
  v0 := [cls "A" (fs := [konst "K" (.int 1)])]
  v1 := [cls "A" (fs := [konst "K" (.int 2)])]
  client := [cls "X" [returns "k" (.field "A" "K")]]
  loads := ["X"]
  sites := [new "X", invokevirtual "X" "k" "()I" "X"]
  runs := [("X", "k")]

/-- The same, through an interface's constant that folds `A`'s: the client names only `J`, yet
its classfile changes with `A.K`. -/
def constantThroughInterface : Case where
  name := "constantThroughInterface"
  mima := none
  v0 := [cls "A" (fs := [konst "K" (.int 1)]), itf "J" (fs := [konst "L" (.add (.field "A" "K") (.int 1))])]
  v1 := [cls "A" (fs := [konst "K" (.int 2)]), itf "J" (fs := [konst "L" (.add (.field "A" "K") (.int 1))])]
  client := [cls "X" [returns "l" (.field "J" "L")]]
  loads := ["X"]
  sites := [new "X", invokevirtual "X" "l" "()I" "X"]
  runs := [("X", "l")]

/-- A constant stops being one (its initialiser becomes a call). The old client still has the old
value folded in and does not read the field; a fresh one reads it with `getstatic`. -/
def constantBecomesNonConstant : Case where
  name := "constantBecomesNonConstant"
  mima := none
  v0 := [cls "A" (fs := [konst "K" (.int 1)])]
  v1 := [cls "A" (fs := [konst "K" .call])]
  client := [cls "X" [returns "k" (.field "A" "K")]]
  loads := ["X"]
  sites := [new "X", invokevirtual "X" "k" "()I" "X"]
  runs := [("X", "k")]

/-- A non-constant field is removed: the client reads it, so it no longer links. -/
def nonConstantRemoved : Case where
  name := "nonConstantRemoved"
  mima := some "MissingFieldProblem"
  v0 := [cls "A" (fs := [konst "N" .call])]
  v1 := [cls "A"]
  client := [cls "X" [returns "n" (.field "A" "N")]]
  loads := ["X"]
  sites := [new "X", invokevirtual "X" "n" "()I" "X"]
  runs := [("X", "n")]

/-- A constant is removed: the client folded it, so it still links (and still returns `1`). -/
def constantRemoved : Case where
  name := "constantRemoved"
  mima := some "MissingFieldProblem"
  v0 := [cls "A" (fs := [konst "K" (.int 1)])]
  v1 := [cls "A"]
  client := [cls "X" [returns "k" (.field "A" "K")]]
  loads := ["X"]
  sites := [new "X", invokevirtual "X" "k" "()I" "X"]
  runs := [("X", "k")]

/-! ## Interfaces (§13.5) -/

/-- An abstract method added to an interface: a caller compiled against `v1` hits the old client
class, which does not implement it (§13.5.3). -/
def abstractAddedToInterface : Case where
  name := "abstractAddedToInterface"
  mima := some "ReversedMissingMethodProblem"
  v0 := [itf "I" [dfn "a" true]]
  v1 := [itf "I" [dfn "a" true, dfn "b" true]]
  client := [cls "X" [dfn "a"] none [("I", none)]]
  loads := ["X"]
  sites := [invokeinterface "I" "b" "()I" "X"]

/-- A default method added: the old client class inherits it (§13.5.6). -/
def defaultAddedToInterface : Case where
  name := "defaultAddedToInterface"
  mima := none
  v0 := [itf "I" [dfn "a" true]]
  v1 := [itf "I" [dfn "a" true, dfn "b"]]
  client := [cls "X" [dfn "a"] none [("I", none)]]
  loads := ["X"]
  sites := [invokeinterface "I" "b" "()I" "X"]

/-- A private interface method added: the client links as before, by footprint. -/
def privateAddedToInterface : Case where
  name := "privateAddedToInterface"
  mima := none
  v0 := [itf "I" [dfn "a" true]]
  v1 := [itf "I" [dfn "a" true, { dfn "c" with priv := true }]]
  client := [cls "X" [dfn "a"] none [("I", none)]]
  loads := ["X"]
  sites := [new "X", invokeinterface "I" "a" "()I" "X"]

/-! ## Generics and bridges (§13.4.15) -/

def pGen : CUnit := [{ name := "P", tparam := true, methods := [{ name := "get", res := .tp }] }]
def qNarrow (over : Bool) : CUnit :=
  [{ name := "Q", super := some ("P", some .str),
     methods := if over then [{ name := "get", res := .str }] else [] }]

/-- An override narrowing a generic method's result is removed. The client's call through `Q`
names `get()String`, which only the override declared; the inherited method is `get()Object`. -/
def narrowedOverrideRemoved : Case where
  name := "narrowedOverrideRemoved"
  mima := some "DirectMissingMethodProblem"
  v0 := [pGen, qNarrow true]
  v1 := [pGen, qNarrow false]
  sites := [invokevirtual "Q" "get" "()Ljava/lang/String;" "Q"]

/-- The same edit, called through `P`: `get()Object` is the bridge in `Q` before and `P`'s method
after. Links either way. -/
def narrowedOverrideRemovedViaP : Case where
  name := "narrowedOverrideRemovedViaP"
  mima := some "DirectMissingMethodProblem"
  v0 := [pGen, qNarrow true]
  v1 := [pGen, qNarrow false]
  sites := [invokevirtual "P" "get" "()Ljava/lang/Object;" "Q"]

/-- A narrowing override added: the old call through `Q` names `get()Object` (inherited), which is
now `Q`'s bridge to the override. -/
def narrowedOverrideAdded : Case where
  name := "narrowedOverrideAdded"
  mima := none
  v0 := [pGen, qNarrow false]
  v1 := [pGen, qNarrow true]
  sites := [invokevirtual "Q" "get" "()Ljava/lang/Object;" "Q"]

/-! ## Enums (§13.4.26) and records (§13.4.27) -/

def enm (cs : List String) : CUnit := [{ name := "E", kind := .enum, consts := cs }]

/-- An enum constant added: the client's read of another constant links, by footprint. -/
def enumConstantAdded : Case where
  name := "enumConstantAdded"
  mima := none
  v0 := [enm ["X"]]
  v1 := [enm ["X", "Y"]]
  sites := [getstatic "E" "X" "LE;"]

/-- An enum constant removed: a read of it does not link. -/
def enumConstantRemoved : Case where
  name := "enumConstantRemoved"
  mima := some "MissingFieldProblem"
  v0 := [enm ["X", "Y"]]
  v1 := [enm ["X"]]
  sites := [getstatic "E" "Y" "LE;"]

def rec (cs : List (String × Ty)) : CUnit := [{ name := "R", kind := .record, comps := cs }]

/-- A record component removed: its accessor goes, and a call to it does not link. -/
def recordComponentRemoved : Case where
  name := "recordComponentRemoved"
  mima := some "DirectMissingMethodProblem"
  v0 := [rec [("x", .int), ("y", .int)]]
  v1 := [rec [("x", .int)]]
  sites := [invokevirtual "R" "x" "()I" "R", invokevirtual "R" "y" "()I" "R"]

/-- A record component added: the old accessor still links, by footprint, but the canonical
constructor's descriptor changes, so `new R(1)` compiled against `v0` does not. -/
def recordComponentAdded : Case where
  name := "recordComponentAdded"
  mima := some "DirectMissingMethodProblem"
  v0 := [rec [("x", .int)]]
  v1 := [rec [("x", .int), ("y", .int)]]
  sites := [invokevirtual "R" "x" "()I" "R"]

/-- The same edit, constructing the record. -/
def recordComponentAddedNew : Case where
  name := "recordComponentAddedNew"
  mima := some "DirectMissingMethodProblem"
  v0 := [rec [("x", .int)]]
  v1 := [rec [("x", .int), ("y", .int)]]
  sites := [construct "R" "<init>" "(I)V", invokevirtual "R" "x" "()I" "R"]

/-! ## Sealed classes (§13.4.2.1) -/

/-- A class becomes sealed without permitting the client's subclass: loading the subclass fails
with `IncompatibleClassChangeError` (JVMS §5.3.5). The client no longer compiles either. -/
def classBecomesSealed : Case where
  name := "classBecomesSealed"
  mima := none
  v0 := [cls "A"]
  v1 := [[{ name := "A", sealing := .explicit ["B"] }, { name := "B", final := true, super := some ("A", none) }]]
  client := [cls "X" [] (some ("A", none))]
  loads := ["X"]

def all : List Case :=
  [constantValueChanged, constantThroughInterface, constantBecomesNonConstant, nonConstantRemoved,
   constantRemoved, abstractAddedToInterface, defaultAddedToInterface, privateAddedToInterface,
   narrowedOverrideRemoved, narrowedOverrideRemovedViaP, narrowedOverrideAdded, enumConstantAdded,
   enumConstantRemoved, recordComponentRemoved, recordComponentAdded, recordComponentAddedNew,
   classBecomesSealed]

end Java.Catalogue
