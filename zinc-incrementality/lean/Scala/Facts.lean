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

end Scala
