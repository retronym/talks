import BinCompat.ZincBridge

/-!
# B4 for Scala 3: separate compilation

A round of Zinc's loop compiles its units in one compiler run, and reads every other unit from
the classpath (TASTy). The faithful joint compilation of a group `G` (`group3`) therefore answers
`View.inRun := v ∈ G`, where `ZincBridge.group` answers `inRun := true` for everything.

**The obligation that fails is `comp`.** Under Scala 3, lowering a class that mixes in a trait
whose only initialisers are a `lazy val` or an extension method calls the trait's `$init$` when the
trait is in the same run and not when it is read from TASTy (F6, `Scala/Facts.lean`). So the output
of a unit is not a function of the interfaces it reads: `group3 {T, C}` and `group3 {C}` give `C`
different classfiles over the same interfaces (`f6_witness`). No per-unit task and no answer
function can make `comp` hold for `group3` (`not_comp`), whatever the keys.

**The fix, modelled.** retronym/scala3#10 has the TASTy reader compute `NoInits` as the namer does
from source. A trait read from TASTy then gives its subclasses the `$init$` calls the trait would
give them in the same run. In the model `View.inRun` is read only by `Scala.hasInit`, so the fixed
reader is the reader that reports every view as in the run (`readFix`). With it, the faithful
joint compilation is `ZincBridge.group .s3` (`group3Fix_eq`), so `ZincBridge.compiler .s3` meets
the obligations and B4 holds for Scala 3 (`after_eq_fresh_fix`).

**Which is more honest.** The alternative was to restrict the theorem to programs without the F6
shape: no trait whose only initialisers are a `lazy val` or an extension method. That statement is
about today's compiler, but its hypothesis is about every trait the client reads, library traits
included, which the client does not control, and it excludes common code. It would also need a
congruence lemma through all of lowering (an environment differing only in `inRun` on traits
without the shape lowers the same), which the model does not have. The fix states the theorem for
a compiler with one named, reviewable change, and `f6_witness` shows that without the change the
theorem is false. We take the fix.
-/

namespace BinCompat.ZincBridgeScala3

open Scala ZincBridge

/-- The answer of a run over the units `G`: a view is in the run iff its unit is in `G`. -/
def answerIn (G : Finset String) (I : String → Iface) (q : FQ) : FAns q :=
  (side I q).map fun d => { decl := d, inRun := decide (q.1 ∈ G) }

/-- Faithful joint compilation of `G` under Scala 3: the units of `G` read each other from source,
and everything else from TASTy. -/
def group3 (G : Finset String) (src : String → Option Scala.Src) (I : String → Iface) :
    String → Out :=
  fun u => (unit .s3 (src u)).run (answerIn G fun v => if v ∈ G then ifaceSrc (src v) else I v)

theorem iface_group3 (G : Finset String) (src : String → Option Scala.Src) (I : String → Iface)
    (u : String) : (group3 G src I u).iface = ifaceSrc (src u) :=
  iface_unit .s3 (src u) _

/-! ## The witness -/

/-- `T` has only a `lazy val`; `C extends T` (`Scala.initProgram 2`). -/
def lazyZ : Mem := { name := "z", res := .int, isVal := true, lzy := true }
def tz : Scala.Src := { name := "T", cls := some { name := "T", kind := .trt, members := [lazyZ] } }
def cz : Scala.Src := { name := "C", cls := some { name := "C", traits := [("T", none)] } }

def src : String → Option Scala.Src := fun u => if u = "T" then some tz else if u = "C" then some cz else none

/-- The interfaces of the sources, the classpath of both runs. -/
def I : String → Iface := fun v => ifaceSrc (src v)

/-- **F6.** Over the same interfaces, `C` compiled with `T` calls `T.$init$`, and compiled alone
against `T`'s TASTy does not. -/
theorem f6_witness : group3 {"T", "C"} src I "C" ≠ group3 {"C"} src I "C" := by decide +kernel

/-- The interfaces a group's members expose do not depend on the group, here. -/
theorem override_eq (G : Finset String) :
    Zinc.XCompiler.override I G (Out.iface ∘ group3 G src I) = I := by
  funext v
  simp only [Zinc.XCompiler.override, Function.comp, iface_group3]
  split <;> rfl

/-- **`comp` fails for every per-unit task.** Whatever `unit` and `answer` an `XCompiler` with the
faithful Scala 3 joint compilation chooses, the compositionality obligation is false: it would
give `C` one output in both groups. -/
theorem not_comp (unit' : Option Scala.Src → Zinc.Task FQ FAns Out)
    (answer' : (String → Iface) → (q : FQ) → FAns q) :
    ¬ ∀ (G : Finset String) (src : String → Option Scala.Src) (I : String → Iface), ∀ d ∈ G,
      group3 G src I d =
        (unit' (src d)).run (answer' (Zinc.XCompiler.override I G (Out.iface ∘ group3 G src I))) := by
  intro h
  have h₁ := h {"T", "C"} src I "C" (by decide)
  have h₂ := h {"C"} src I "C" (by decide)
  rw [override_eq] at h₁ h₂
  exact f6_witness (h₁.trans h₂.symm)

/-! ## The fix -/

/-- retronym/scala3#10's reader: a view read from TASTy behaves as one read from source. -/
def readFix (v : View) : View := { v with inRun := true }

/-- Joint compilation of `G` with the fixed reader. -/
def group3Fix (G : Finset String) (src : String → Option Scala.Src) (I : String → Iface) :
    String → Out :=
  fun u => (unit .s3 (src u)).run
    (fun q => (answerIn G (fun v => if v ∈ G then ifaceSrc (src v) else I v) q).map readFix)

/-- With the fix, the faithful joint compilation is B4's. -/
theorem group3Fix_eq : group3Fix = group .s3 := by
  funext G src I u
  simp only [group3Fix, group, answerIn, Option.map_map]
  rfl

/-- **B4 for Scala 3, with the fix.** `ZincBridge.after_eq_fresh` at `.s3`, whose compiler is the
faithful one once the reader is fixed (`group3Fix_eq`). Hypotheses as for B4: a sound policy that
stays inside `S`, the edit in the first round, the old build up to date except at the edit. -/
theorem after_eq_fresh_fix (us : List String) (S : Finset String)
    (src : String → Option Scala.Src) (P : Zinc.Compiler.Policy String Out Bool) (hP : P.Sound S)
    (hPS : P.InS S) (fuel : ℕ) (R₀ D : Finset String) (s : Zinc.Compiler.State String Out Bool)
    (hD : D ⊆ R₀) (hR₀ : R₀ ⊆ S) (hInv : (compiler .s3).Inv S src s D)
    (s' : Zinc.Compiler.State String Out Bool) (h : (compiler .s3).zinc S src P fuel 0 R₀ s = some s')
    (c : String) (hc : c ∉ (compiler .s3).recompiled S src P fuel 0 R₀ s)
    (p : Jvm.Program String String String) :
    (compiler .s3).group = group3Fix ∧
    Jvm.outcome (afterWorld us ((compiler .s3).cleanFrom S src s) c (s.out c)) p =
      Jvm.outcome (worldOf us ((compiler .s3).cleanFrom S src s)) p :=
  ⟨group3Fix_eq.symm, after_eq_fresh .s3 us S src P hP hPS fuel R₀ D s hD hR₀ hInv s' h c hc p⟩

end BinCompat.ZincBridgeScala3
