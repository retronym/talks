import Scala.Space

/-!
# Facts about lowering, checked by kernel `decide`

**F6 is a compositionality failure.** Lowering a unit depends on whether its parents are in the
same compiler run (`View.inRun`), not only on their interfaces. Under Scala 3 a class extending a
trait whose only initialisers are a `lazy val` or an extension method calls the trait's `$init$`
when compiled with it and not when compiled apart from it; the trait's classfile has the `$init$`
either way. So the per-unit result is not a function of the interfaces read, which is the
`comp` obligation (`REVIEW-2026-10-11.md`, finding 3), and no key on the trait's API repairs it.
Scala 2 calls `$init$` either way.
-/

namespace Scala

/-- The `$init$` calls in `C`'s constructor, compiled in a run over `run`. -/
def ctorInits (dl : Dialect) (p : Program) (run : List String) : Option (List Insn) := do
  let s ← p.find? (·.name == "C")
  match lower dl s (p.envIn run) with
  | .ok cs => (cs.find? (·.name == "C")).bind fun c => (c.methods.find? (·.name == ctorName)).bind (·.calls)
  | .error _ => none

def tInit : Insn := ⟨"invokestatic", "T", "$init$", "(LT;)V"⟩

/-- A trait with a `lazy val`: joint and separate compilation differ in Scala 3 (F6). -/
example : ctorInits .s3 (initProgram 2) ["T", "C"] = some [tInit] := by decide
example : ctorInits .s3 (initProgram 2) ["C"] = some [] := by decide

/-- A trait with an extension method: the same. -/
example : ctorInits .s3 (initProgram 3) ["T", "C"] = some [tInit] := by decide
example : ctorInits .s3 (initProgram 3) ["C"] = some [] := by decide

/-- A trait with a concrete `val`: no difference. -/
example : ctorInits .s3 (initProgram 1) ["C"] = some [tInit] := by decide

/-- Scala 2.13: no difference. -/
example : ctorInits .s213 (initProgram 2) ["C"] = some [tInit] := by decide

/-! ## `memberType` through the shared `AsSeenFrom`

`K extends H[String]`, `H[X] extends G[X]`, `G[X] { def g(x: X): X }`: `K`'s base type `G` has
argument `String`, computed by viewing `H`'s base type `G[X]` from `K` (scalac's `baseType`), and
`K.this.memberType(g)` takes `X` of `G` to `String`. -/

/-- `info.asSeenFrom(self.this, owner)` in program `p`. -/
def memberTypeIn (p : Program) (self owner : String) (t : Ty) : Option Ty := do
  let s ← p.find? (·.name == self)
  let d ← s.cls
  pure (seenFrom self (linIn p d) owner t)

def throughH : Program := (asfSpace[0]?).getD []

example : memberTypeIn throughH "K" "G" (Ty.X "G") = some .str := by decide
example : memberTypeIn throughH "K" "H" (Ty.X "H") = some .str := by decide
/-- A type parameter of a class that is not a base class is left alone. -/
example : memberTypeIn throughH "H" "G" (Ty.X "G") = some (Ty.X "H") := by decide

/-- An overload is not an override: `K extends G[String] { def g(x: Int): Int }` declares a second
`g`, so lowering keeps two signature groups for `g` and emits no bridge between them. -/
def overload : Program := (asfSpace[8]?).getD []

example : (do
    let d ← ((overload.find? (·.name == "K")).bind (·.cls))
    pure (sigGroups "K" (linIn overload d)).length) = some 2 := by decide

end Scala
