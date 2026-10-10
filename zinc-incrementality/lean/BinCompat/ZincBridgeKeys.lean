import BinCompat.ZincBridge

/-!
# B4 with Zinc's actual keys

`ZincBridge`'s `searched` bridge records a key per query lowering asks. Zinc records less: what
the extractor sees in the typed tree of the unit's own source, before lowering runs.

* **Inheritance** (`ZKey.api` on each parent). On any API change of a class, Zinc invalidates its
  subclasses, transitively over the stored inheritance edges (`invalidateByInheritance`). Here the
  key on a parent `p` is hashed by the declarations of `p` and its ancestors (`ancs`), which is
  what the transitive walk amounts to for one subclass.
* **Member references** (`ZKey.name n` on each class `n` the source names: parents, and the types
  in its members' signatures). Zinc invalidates a member-ref dependent when a name it uses has a
  new name hash. Here the used name is the class's own name, whose hash is the class-level
  declaration (kind, parents, a value class's underlying type: `ExtractAPI` adds it to the
  ancestors, test `value-class-underlying`) and the members of that name.
* The unit's own declarations, recompiled with it (`ZKey.api` on itself).

**Coverage fails for lowering** (`coverage_fails`), even when a name key is let cover every query
on its class (more than its hash justifies). The gap is a value class in the signature of an
*inherited* member. `T` has `def f(v: V): Int`, and `object O extends T`. Lowering `O` erases
`f`'s signature twice: for `O$`'s mixin forwarder and for the static forwarder in the mirror class
`O`. So it asks for `V`. But `O`'s source never names `V`, and `V` is not an ancestor, so `O`
records no key that covers `V`.

**The loop leaves `O` stale, and a clean build's caller fails to link** (`loop_witness`). `V`
becomes a value class. Zinc recompiles `V`, then `T` (`T`'s source names `V`). `T`'s declaration
is unchanged, so its API is too, and the loop stops: `O` was never recompiled. A fresh build of
`O` has the static forwarder `O.f(I)I`; the old `O` has `O.f(LV;)I`, so `invokestatic O.f(I)I`, as
a Java caller compiled against the fresh build does, fails with `NoSuchMethodError`.
The mixin forwarder `O$.f(LV;)I` is stale too.

So B4's hypothesis (the obligations) does not hold for Zinc's keys, and its conclusion fails. The
same shape breaks bridges (a value class in an inherited generic signature) and mixin forwarders of
a class. Fixes: record keys on the value classes in inherited signatures (what `searched` does), or
hash a value class reference in an API by its underlying type, so `T`'s API changes and
inheritance invalidates `O`. This is a prediction of the model; a scripted test is the next step.
-/

namespace BinCompat.ZincBridgeKeys

open Scala ZincBridge

inductive ZKey
  | api
  | name (n : String)
  deriving DecidableEq, Repr

/-- The parents of a unit's class and object. -/
def parentsOf : Iface → List String
  | none => []
  | some (c, o) => (c.toList ++ o.toList).flatMap fun d => d.parents.map (·.1)

/-- A unit and its ancestors, by the interfaces `I`. -/
def ancs (I : String → Iface) : ℕ → String → List String
  | 0, u => [u]
  | k + 1, u => u :: (parentsOf (I u)).flatMap (ancs I k)

def depth : ℕ := 8

/-- The part of a declaration the name hash of `n` covers: the members named `n`, and the
class-level declaration if `n` is the class's own name. -/
def proj (n : String) (d : Decl) : Decl :=
  { (if d.name = n then d else { name := d.name }) with members := d.members.filter (·.name == n) }

def nameHash (n : String) : Iface → Iface
  | none => none
  | some (c, o) => some (c.map (proj n), o.map (proj n))

def π (I : String → Iface) (u : String) : ZKey → List Iface
  | .api => (ancs I depth u).map I
  | .name n => [nameHash n (I u)]

def tyRefs : Ty → List String
  | .ref n => [n]
  | _ => []

/-- The classes a declaration names: its parents and their type arguments, the types in its
members' signatures, a value class's underlying type. -/
def named (d : Decl) : List String :=
  d.parents.flatMap (fun (p, a) => p :: (a.map tyRefs).getD []) ++
    d.members.flatMap (fun m => (m.res :: m.allParams).flatMap tyRefs) ++
    (d.under.map fun (_, t) => tyRefs t).getD []

def decls : Iface → List Decl
  | none => []
  | some (c, o) => c.toList ++ o.toList

/-- Zinc's keys for unit `c`, from its own declarations. -/
def zkeys (c : String) (o : Out) : Finset (String × ZKey) :=
  ((c, ZKey.api) :: (parentsOf o.iface).map (·, ZKey.api) ++
    ((decls o.iface).flatMap named).map fun n => (n, ZKey.name n)).toFinset

/-- An inheritance key covers queries on its class and its ancestors; a name key, generously,
every query on its class. -/
def covers (I : String → Iface) (q : FQ) : String × ZKey → Prop
  | (u, .api) => q.1 ∈ ancs I depth u
  | (u, .name _) => q.1 = u

instance (I : String → Iface) (q : FQ) (k : String × ZKey) : Decidable (covers I q k) := by
  obtain ⟨u, k⟩ := k; cases k <;> (unfold covers; infer_instance)

def compiler (dl : Dialect) :
    Zinc.XCompiler String (Option Scala.Src) Out Iface ZKey (List Iface) Bool (fun _ => Option View) where
  unit := unit dl
  group := group dl
  iface := Out.iface
  answer := answer
  π := π
  hashDeps I u := (ancs I depth u).toFinset
  keys c o _ := zkeys c o
  covers I q k := covers I q k

/-! ## The witness -/

def v0 : Scala.Src := Catalogue.cls "V" []
def v1 : Scala.Src := { name := "V", cls := some { name := "V", kind := .vcls, under := some ("x", .int) } }
def fV : Mem := { name := "f", params := [.ref "V"], res := .int }
def t : Scala.Src := Catalogue.trt "T" [fV]
def o : Scala.Src := { name := "O", obj := some { name := "O", kind := .obj, traits := [("T", none)] } }

def src0 : String → Option Scala.Src := fun u =>
  if u = "V" then some v0 else if u = "T" then some t else if u = "O" then some o else none
def src1 : String → Option Scala.Src := fun u =>
  if u = "V" then some v1 else if u = "T" then some t else if u = "O" then some o else none

def S : Finset String := {"V", "T", "O"}
def us : List String := ["V", "T", "O"]

/-- The old build, with Zinc's keys recorded. -/
def old : String → Out := group .s213 S src0 (fun _ => none)
def s0 : Zinc.Compiler.State String Out ZKey := { out := old, U := fun d => zkeys d (old d) }

/-- The fresh build of the new sources. -/
def fresh : String → Out := group .s213 S src1 (fun _ => none)

/-- Zinc's policy: compile what was invalidated. -/
def P : Zinc.Compiler.Policy String Out ZKey := fun _ _ _ _ I => I

/-- A caller compiled against the fresh build: `O.f(1)` from Java. -/
def caller : Jvm.Program String String String := { sites := [.invokestatic "O" "f" "(I)I"] }


/-- **Coverage fails.** Lowering `O` asks for `V`, and no key `O` records covers that query. -/
theorem coverage_fails :
    ("V", false) ∈ ((compiler .s213).unit (src0 "O")).trace
        ((compiler .s213).answer ((compiler .s213).ifaces s0)) ∧
    ∀ k ∈ zkeys "O" (old "O"), ¬ covers ((compiler .s213).ifaces s0) ("V", false) k := by
  decide +kernel

/-- **The loop.** From the old build, with `V` edited, Zinc recompiles `V` and `T` and stops. `O`
keeps its old classfiles, which differ from a fresh build's, and the fresh build's caller fails
to link against them. -/
theorem loop_witness :
    "V" ∈ (compiler .s213).recompiled S src1 P 4 0 {"V"} s0 ∧
    "T" ∈ (compiler .s213).recompiled S src1 P 4 0 {"V"} s0 ∧
    "O" ∉ (compiler .s213).recompiled S src1 P 4 0 {"V"} s0 ∧
    ((compiler .s213).zinc S src1 P 4 0 {"V"} s0).map (·.out "O") = some (old "O") ∧
    old "O" ≠ fresh "O" ∧
    ((compiler .s213).zinc S src1 P 4 0 {"V"} s0).map
      (fun s' => Jvm.outcome (worldOf us s'.out) caller) = some (.error .noSuchMethod) ∧
    Jvm.outcome (worldOf us fresh) caller = .ok ["O"] := by
  decide +kernel

end BinCompat.ZincBridgeKeys
