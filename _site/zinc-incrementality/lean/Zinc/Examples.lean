import Zinc.Toy

/-!
# §15 as scripted tests

Each example runs Zinc's loop (`Policy.plain`, from `R₀ = {A}`) on a three-class program after an
edit to `A`, and compares the result with a clean build of the new sources.
-/

namespace Zinc.Toy

open Cls Name

abbrev S : Finset Cls := {A, B, C}

def dummyOut : Out := { iface := {}, descriptors := [], implicits := [] }

/-- The previous build: a clean build of `src` with recorded keys. -/
def initial (keys : List (Cls × Q) → Finset (Cls × K)) (src : Cls → Src) : Compiler.State Cls Out K :=
  (compiler keys).round src S { out := fun _ => dummyOut, U := fun _ => ∅ }

/-- Incremental build after editing `A`. -/
def incremental (keys : List (Cls × Q) → Finset (Cls × K)) (src₀ src₁ : Cls → Src) : Option (Compiler.State Cls Out K) :=
  (compiler keys).zinc S src₁ Compiler.Policy.plain 5 0 {A} (initial keys src₀)

def cleanBuild (keys : List (Cls × Q) → Finset (Cls × K)) (src₀ src₁ : Cls → Src) : Cls → Out :=
  (compiler keys).cleanFrom S src₁ (initial keys src₀)

/-! ## §15b value classes

```scala
class A(val x: Int) extends AnyVal      // → class A(val x: Double) extends AnyVal
object B { def foo: A = new A(0) }
object C { val duck = B.foo }
```
`C`'s output contains the descriptor of `B.foo`, which is `E(A) = E(underlying(A))`.
-/

def vc₀ : Cls → Src
  | A => { decl := { members := [⟨x, .int, false⟩], underlying := some .int } }
  | B => { decl := { members := [⟨foo, .ref A, false⟩] } }
  | C => { decl := { members := [⟨duck, .ref A, false⟩] }, body := [.select B foo] }

def vc₁ : Cls → Src
  | A => { decl := { members := [⟨x, .double, false⟩], underlying := some .double } }
  | c => vc₀ c

/-- Name-only keys: `C` is not recompiled and keeps `B.foo()I`. Undercompilation. -/
example : (incremental keysNameOnly vc₀ vc₁).map (·.out C) ≠ some (cleanBuild keysNameOnly vc₀ vc₁ C) := by
  native_decide

example : (incremental keysNameOnly vc₀ vc₁).map (·.out C |>.descriptors) = some [.I] := by native_decide
example : (cleanBuild keysNameOnly vc₀ vc₁ C).descriptors = [.D] := by native_decide

/-- Repaired keys: `C` recorded `(A, self)`, is invalidated, and the result is the clean build. -/
example : [A, B, C].map (fun c => (incremental keysRepaired vc₀ vc₁).map (·.out c)) =
    [A, B, C].map (fun c => some (cleanBuild keysRepaired vc₀ vc₁ c)) := by
  native_decide

/-! ## §15a implicits

```scala
object B { implicit val x: Int = ... }
object A { }                    // v1: implicit val y: Int   (addition)
                                // v2: val x: Int            (shadowing)
object C { import A._, B._; implicitly[Int] }
```
-/

def imp₀ : Cls → Src
  | A => { decl := {} }
  | B => { decl := { members := [⟨x, .int, true⟩] } }
  | C => { decl := {}, body := [.implicitly .int [A, B]] }

/-- A new, better candidate appears in a class `C` never named a member of. -/
def impAdd : Cls → Src
  | A => { decl := { members := [⟨y, .int, true⟩] } }
  | c => imp₀ c

/-- An unrelated `val x` shadows `B.x` (`source-dependencies/implicit-search`). -/
def impShadow : Cls → Src
  | A => { decl := { members := [⟨x, .int, false⟩] } }
  | c => imp₀ c

/-- Addition, name-only keys: `C` still resolves to `B.x`. Undercompilation (sbt/zinc#945 family). -/
example : (incremental keysNameOnly imp₀ impAdd).map (·.out C |>.implicits) = some [some (B, x)] := by
  native_decide
example : (cleanBuild keysNameOnly imp₀ impAdd C).implicits = [some (A, y)] := by native_decide

/-- Addition, repaired keys: `(A, implicitScope)` changed, `C` recompiles. -/
example : [A, B, C].map (fun c => (incremental keysRepaired imp₀ impAdd).map (·.out c)) =
    [A, B, C].map (fun c => some (cleanBuild keysRepaired imp₀ impAdd c)) := by
  native_decide

/-- Shadowing is caught even by name-only keys: the failed lookup `(A, x)` was recorded, because the
shadowing check is itself a query. "Name hashing happens to model it" (§15a). -/
example : [A, B, C].map (fun c => (incremental keysNameOnly imp₀ impShadow).map (·.out c)) =
    [A, B, C].map (fun c => some (cleanBuild keysNameOnly imp₀ impShadow c)) := by
  native_decide
example : (cleanBuild keysNameOnly imp₀ impShadow C).implicits = [none] := by native_decide

/-! ## The repaired toy compiler is an instance of T3

The abstract theorems apply: for any previous clean build and any edit, the repaired extractor
gives the clean build whenever the loop stops, and it stops within two rounds since interfaces
are explicit. -/

/-- The previous build is a fixed point for its own sources. -/
theorem initial_inv (keys : List (Cls × Q) → Finset (Cls × K)) (ob : (compiler keys).Obligations)
    (src₀ : Cls → Src) : (compiler keys).Inv S src₀ (initial keys src₀) ∅ := by
  have h := (compiler keys).round_preserves ob S src₀
    { out := fun _ => dummyOut, U := fun _ => ∅ } S S (le_refl S) (fun u hu huS => absurd hu huS)
  have hempty : (compiler keys).invalidated S S { out := fun _ => dummyOut, U := fun _ => ∅ }
      ((compiler keys).round src₀ S { out := fun _ => dummyOut, U := fun _ => ∅ }) \ S = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.2 (Finset.filter_subset _ _)
  rwa [hempty] at h

theorem repaired_sound (src₀ src₁ : Cls → Src) (D : Finset Cls)
    (hD : ∀ u, src₀ u ≠ src₁ u → u ∈ D) (hDS : D ⊆ S) (fuel : ℕ)
    (s' : Compiler.State Cls Out K)
    (h : (compiler keysRepaired).zinc S src₁ Compiler.Policy.plain fuel 0 D (initial keysRepaired src₀) = some s') :
    s'.out = cleanBuild keysRepaired src₀ src₁ :=
  (compiler keysRepaired).zinc_eq_clean_of_explicit obligations_repaired S src₁ _
    (Compiler.plain_sound S) (Compiler.plain_inS S) Src.decl (explicit keysRepaired) fuel 0 D _ D
    (le_refl D) hDS
    ((compiler keysRepaired).inv_of_changed S src₀ src₁ _ D hD (initial_inv keysRepaired obligations_repaired src₀))
    s' h

/-- And it always stops within two rounds. -/
theorem repaired_terminates (src₀ src₁ : Cls → Src) (D : Finset Cls)
    (hD : ∀ u, src₀ u ≠ src₁ u → u ∈ D) :
    ((compiler keysRepaired).zinc S src₁ Compiler.Policy.plain 2 0 D (initial keysRepaired src₀)).isSome :=
  (compiler keysRepaired).zinc_some_of_explicit obligations_repaired S src₁ _ (Compiler.plain_inS S)
    Src.decl (explicit keysRepaired) 0 D _ D (le_refl D)
    ((compiler keysRepaired).inv_of_changed S src₀ src₁ _ D hD (initial_inv keysRepaired obligations_repaired src₀))

end Zinc.Toy
