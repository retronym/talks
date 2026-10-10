import Zinc.Snapshot

/-!
# Pipelining: the downstream compiles against an early output

With pipelining, an upstream run writes an early output (a pickle JAR, and an early Analysis with
its classes' APIs) after the dependency phase, and the downstream starts compiling against it
before the upstream has finished. `downstream_sound` (`Classpath.lean`) is relative to the
classpath the downstream compiled against. Pipelining adds two ways for that classpath to be
wrong, both obligations on the upstream's outputs rather than on the downstream's keys:

* **Early agreement.** Every answer a downstream reads from the early output must equal the answer
  from the final output. `early_agreement` is T1 restated: under agreement on the trace, a unit
  compiles the same against either. Where it fails, a pipelined build and a non-pipelined build
  differ with no source change: a Java `static final` constant is folded from the classfile but
  not from the source view `-Ypickle-java` gives (scala/bug#5333), and Scala 2's optimizer inlines
  from bytecode, which an early output does not have.
* **Published = built.** The early output must describe the upstream's sources as last built
  successfully. Zinc rolls back an upstream's classfiles and Analysis when its compile fails, but
  not the early output it already wrote (`Incremental.withClassfileManager`; `ClassFileManager`
  has no pickle handling). The scenario below runs on `Snapshot`'s compiler: `A` is edited to 2,
  the upstream writes its early output and then fails, the downstream compiles against 2; `A` is
  reverted to 1, the upstream sees no change against its last successful build and writes
  nothing; the downstream still reads 2 (`stale_after_failed_upstream`). Rolling back the early
  output with the rest fixes it (`rollback_after_failed_upstream`). This is Zinc's pending
  `pipelining-failed-upstream-revert`. The upstream's behaviour here is read off the code; the
  model's build steps are a simplification.
-/

namespace Zinc.Pipelining

open Snapshot Compiler

/-- **Early agreement.** A unit compiles the same against two classpaths that agree on every
query it asks. -/
theorem early_agreement {Q : Type} {A : Q → Type} {α : Type} (t : Task Q A α)
    (early final : (q : Q) → A q) (h : ∀ q ∈ t.trace early, early q = final q) :
    t.run early = t.run final :=
  Task.run_congr t early final h

/-! ## A failed upstream compile after its early output -/

/-- The upstream as the downstream sees it: `A`'s number in its last successful build (its
Analysis and final classfiles), and in its early output. -/
structure UpState where
  built : ℕ
  early : ℕ
  deriving DecidableEq, Repr

/-- An upstream run with `A`'s source at `a`. With no change against the last successful build it
does nothing. Otherwise it writes the early output, then either succeeds or fails; on failure the
classfiles and Analysis are rolled back, and the early output too if `rollbackEarly`. -/
def upstreamRun (rollbackEarly : Bool) (u : UpState) (a : ℕ) (fails : Bool) : UpState :=
  if a = u.built then u
  else if fails then { built := u.built, early := if rollbackEarly then u.built else a }
  else { built := a, early := a }

/-- A pipelined downstream build: classpath and API both from the early output; Zinc's refresh
rule is irrelevant here (all hashes local to the class `A` read), so refresh everything. -/
def downstream (u : UpState) (s : State U Out K) (snap : U → Iface) :
    Option (State U Out K × (U → Iface)) :=
  build allRule s snap u.early

/-- Build 1 edits `A` to 2 and the upstream fails; build 2 reverts `A` to 1. What `X` observes. -/
def scenario (rollbackEarly : Bool) : Option (ℕ × ℕ) := do
  let u₀ : UpState := ⟨1, 1⟩
  let u₁ := upstreamRun rollbackEarly u₀ 2 true
  let (s₁, snap₁) ← downstream u₁ s₀ snap₀
  let u₂ := upstreamRun rollbackEarly u₁ 1 false
  let (s₂, _) ← downstream u₂ s₁ snap₁
  pure (s₂.out U.X).2

/-- After the failed edit, the downstream compiled against the early output. -/
example : (upstreamRun false ⟨1, 1⟩ 2 true) = ⟨1, 2⟩ := by native_decide

/-- `stale_after_failed_upstream`: **Stale after the revert**: the sources say `A = 1` and the upstream's last successful build
says 1, but `X` observes 2. -/
example : scenario false = some (2, 5) := by native_decide

/-- `rollback_after_failed_upstream`: Rolling back the early output with the rest: `X` observes 1. -/
example : scenario true = some (1, 5) := by native_decide

end Zinc.Pipelining
