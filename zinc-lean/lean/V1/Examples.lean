import V1.Toy

/-!
# Scripted tests for the typecheck-only toy

Simplified from `zinc-incrementality/lean/Zinc/Examples.lean`. Each example runs Zinc's loop
(`Policy.plain`, from `R₀ = {A}`) on a three-class program after an edit to `A`, and compares the
result with a clean build of the new sources.
-/

namespace V1.Toy

open Cls Name

abbrev S : Finset Cls := {A, B, C}

def dummyOut : Out := { iface := {}, selects := [], implicits := [] }

/-- The previous build: a clean build of `src` with recorded keys. -/
def initial (keys : List (Cls × Q) → Finset (Cls × K)) (src : Cls → Src) : Compiler.State Cls Out K :=
  (compiler keys).round src S { out := fun _ => dummyOut, U := fun _ => ∅ }

/-- Incremental build after editing `A`. -/
def incremental (keys : List (Cls × Q) → Finset (Cls × K)) (src₀ src₁ : Cls → Src) :
    Option (Compiler.State Cls Out K) :=
  (compiler keys).zinc S src₁ Compiler.Policy.plain 5 0 {A} (initial keys src₀)

def cleanBuild (keys : List (Cls × Q) → Finset (Cls × K)) (src₀ src₁ : Cls → Src) : Cls → Out :=
  (compiler keys).cleanFrom S src₁ (initial keys src₀)

/-- Does the incremental build equal the clean build on every class? -/
def agrees (keys : List (Cls × Q) → Finset (Cls × K)) (src₀ src₁ : Cls → Src) : Bool :=
  [A, B, C].all fun c => (incremental keys src₀ src₁).map (·.out c) == some (cleanBuild keys src₀ src₁ c)

/-! ## A member's type changes

```scala
object A { val foo: Int }        // edit: val foo: String
object C { A.foo }
```
`C` recorded `(A, foo)`, so name-only keys suffice. -/

def sel₀ : Cls → Src
  | A => { decl := { members := [⟨foo, .int, false⟩] } }
  | B => { decl := {} }
  | C => { decl := {}, body := [.select A foo] }

def sel₁ : Cls → Src
  | A => { decl := { members := [⟨foo, .str, false⟩] } }
  | c => sel₀ c

example : agrees keysNameOnly sel₀ sel₁ = true := by native_decide
example : (incremental keysNameOnly sel₀ sel₁).map (·.out C |>.selects) = some [some .str] := by
  native_decide

/-! ## Implicits

```scala
object B { implicit val x: Int = 1 }
object A { }                    // edit 1: implicit val y: Int   (addition)
                                // edit 2: val x: Int            (shadowing)
object C { import A._, B._; implicitly[Int] }
```
-/

def imp₀ : Cls → Src
  | A => { decl := {} }
  | B => { decl := { members := [⟨x, .int, true⟩] } }
  | C => { decl := {}, body := [.implicitly .int [A, B]] }

/-- A new candidate appears in a class whose members `C` never named. -/
def impAdd : Cls → Src
  | A => { decl := { members := [⟨y, .int, true⟩] } }
  | c => imp₀ c

/-- An unrelated `val x` shadows `B.x` (`source-dependencies/implicit-search`). -/
def impShadow : Cls → Src
  | A => { decl := { members := [⟨x, .int, false⟩] } }
  | c => imp₀ c

/-- Addition, name-only keys: `C` still resolves to `B.x`, a clean build to `A.y`. -/
example : (incremental keysNameOnly imp₀ impAdd).map (·.out C |>.implicits) = some [some (B, x)] := by
  native_decide
example : (cleanBuild keysNameOnly imp₀ impAdd C).implicits = [some (A, y)] := by native_decide
example : agrees keysNameOnly imp₀ impAdd = false := by native_decide

/-- Addition, repaired keys: `(A, implicitScope)` changed, `C` recompiles. -/
example : agrees keysRepaired imp₀ impAdd = true := by native_decide

/-- Shadowing is caught even by name-only keys: the failed lookup `(A, x)` was recorded, because
the shadowing check is itself a query. -/
example : agrees keysNameOnly imp₀ impShadow = true := by native_decide
example : (cleanBuild keysNameOnly imp₀ impShadow C).implicits = [none] := by native_decide

/-! ## The repaired compiler is an instance of T3 and T4 -/

/-- The previous build is a fixed point for its own sources. -/
theorem initial_inv (keys : List (Cls × Q) → Finset (Cls × K)) (ob : (compiler keys).Obligations)
    (src₀ : Cls → Src) : (compiler keys).Inv S src₀ (initial keys src₀) ∅ := by
  have h := (compiler keys).round_preserves ob S src₀
    { out := fun _ => dummyOut, U := fun _ => ∅ } S S (le_refl S) (fun u hu huS => absurd hu huS)
  have hempty : (compiler keys).invalidated S S { out := fun _ => dummyOut, U := fun _ => ∅ }
      ((compiler keys).round src₀ S { out := fun _ => dummyOut, U := fun _ => ∅ }) \ S = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.2 (Finset.filter_subset _ _)
  rwa [hempty] at h

/-- Whenever the loop stops, the result is the clean build. -/
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

/-- And it stops within two rounds. -/
theorem repaired_terminates (src₀ src₁ : Cls → Src) (D : Finset Cls)
    (hD : ∀ u, src₀ u ≠ src₁ u → u ∈ D) :
    ((compiler keysRepaired).zinc S src₁ Compiler.Policy.plain 2 0 D (initial keysRepaired src₀)).isSome :=
  (compiler keysRepaired).zinc_some_of_explicit obligations_repaired S src₁ _ (Compiler.plain_inS S)
    Src.decl (explicit keysRepaired) 0 D _ D (le_refl D)
    ((compiler keysRepaired).inv_of_changed S src₀ src₁ _ D hD (initial_inv keysRepaired obligations_repaired src₀))

end V1.Toy
