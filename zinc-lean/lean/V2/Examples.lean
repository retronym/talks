import V2.Toy

/-!
# Scripted tests for code generation

Each example runs the general loop (`NCompiler.zinc` on `lift`, `Policy.plain`) after an edit and
compares the result with a clean build of the new sources.
-/

namespace V2.Toy

open V1 Cls Name

abbrev S : Finset Cls := {A, B, C, M}

def dummyOut : Out := { iface := {}, descriptors := [], implicits := [], forwarders := [] }

def initial (keys : List (Cls × Q) → Finset (Cls × K)) (src : Cls → Src) : Compiler.State Cls Out K :=
  (compiler keys).round src S { out := fun _ => dummyOut, U := fun _ => ∅ }

/-- Incremental build after editing the classes in `R₀`, by the general loop. -/
def incremental (keys : List (Cls × Q) → Finset (Cls × K)) (R₀ : Finset Cls) (src₀ src₁ : Cls → Src) :
    Option (Compiler.State Cls Out K) :=
  (lift (compiler keys)).zinc S src₁ Compiler.Policy.plain 5 0 R₀ (initial keys src₀)

def cleanBuild (keys : List (Cls × Q) → Finset (Cls × K)) (src₀ src₁ : Cls → Src) : Cls → Out :=
  (compiler keys).cleanFrom S src₁ (initial keys src₀)

def agrees (keys : List (Cls × Q) → Finset (Cls × K)) (R₀ : Finset Cls) (src₀ src₁ : Cls → Src) : Bool :=
  [A, B, C, M].all fun c =>
    (incremental keys R₀ src₀ src₁).map (·.out c) == some (cleanBuild keys src₀ src₁ c)

/-! ## A value class's underlying type changes

```scala
class A(val x: Int) extends AnyVal      // edit: class A(val x: Double) extends AnyVal
object B { def foo: A = new A(0) }
object C { B.foo }                       // descriptor B.foo()I, must become B.foo()D
```
-/

def vc₀ : Cls → Src
  | A => { decl := { members := [⟨x, .int, false⟩], underlying := some .int } }
  | B => { decl := { members := [⟨foo, .ref A, false⟩] } }
  | C => { decl := {}, body := [.select B foo] }
  | M => { decl := {} }

def vc₁ : Cls → Src
  | A => { decl := { members := [⟨x, .double, false⟩], underlying := some .double } }
  | c => vc₀ c

/-- Name-only keys: `C` keeps `B.foo()I`. -/
example : (incremental keysNameOnly {A} vc₀ vc₁).map (·.out C |>.descriptors) = some [.I] := by
  native_decide
example : (cleanBuild keysNameOnly vc₀ vc₁ C).descriptors = [.D] := by native_decide
example : agrees keysNameOnly {A} vc₀ vc₁ = false := by native_decide

/-- Repaired keys: `C` recorded `(A, self)` and is recompiled. -/
example : agrees keysRepaired {A} vc₀ vc₁ = true := by native_decide

/-! ## A trait gains a member

```scala
trait M { def foo: Int }                 // edit: also def y: Int
class C extends M                        // needs a forwarder for y
```
-/

def fw₀ : Cls → Src
  | M => { decl := { members := [⟨foo, .int, false⟩] } }
  | C => { decl := { mixins := [M] } }
  | _ => { decl := {} }

def fw₁ : Cls → Src
  | M => { decl := { members := [⟨foo, .int, false⟩, ⟨y, .int, false⟩] } }
  | c => fw₀ c

/-- Name-only keys: `C` keeps one forwarder. -/
example : (incremental keysNameOnly {M} fw₀ fw₁).map (·.out C |>.forwarders) = some [(M, foo)] := by
  native_decide
example : (cleanBuild keysNameOnly fw₀ fw₁ C).forwarders = [(M, foo), (M, y)] := by native_decide

/-- Repaired keys: `C` recorded `(M, decls)` and is recompiled. -/
example : agrees keysRepaired {M} fw₀ fw₁ = true := by native_decide

/-! ## The general theorems apply -/

/-- T3a″ for the repaired compiler, through the embedding: if the general loop stops, every class
is up to date. -/
theorem repaired_up_to_date (src : Cls → Src) (fuel n : ℕ) (R : Finset Cls)
    (s : Compiler.State Cls Out K) (D : Finset Cls) (hD : D ⊆ R)
    (hInv : (lift (compiler keysRepaired)).Inv S src s D) (s' : Compiler.State Cls Out K)
    (h : (lift (compiler keysRepaired)).zinc S src Compiler.Policy.plain fuel n R s = some s') :
    (lift (compiler keysRepaired)).Inv S src s' ∅ :=
  (lift (compiler keysRepaired)).zinc_sound general_obligations_repaired S src _
    (Compiler.plain_sound S) fuel n R s D hD hInv s' h

/-- And the general loop is V1's loop on this compiler. -/
example (keys) (R₀ : Finset Cls) (src₀ src₁ : Cls → Src) :
    incremental keys R₀ src₀ src₁ =
      (compiler keys).zinc S src₁ Compiler.Policy.plain 5 0 R₀ (initial keys src₀) :=
  zinc_lift _ _ _ _ _ _ _ _

end V2.Toy
