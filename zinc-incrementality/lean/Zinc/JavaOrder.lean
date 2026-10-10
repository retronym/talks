import Zinc.JavaSpec

/-!
# Compile order: a Java class's two views

`JavaSpec.lean` with Scala clients and a second view of each Java class. scalac reads a Java source
in its own batch with its Java parser (the **source view**); javac's classfile is what Zinc analyses
and what every later round and downstream project reads (the **classfile view**). The views should
agree and do not always: scala/scala#11292 (a Java class's `Object` parent typed `ObjectTpeJava`
from source, `ObjectTpe` from the classfile), scala/scala3#27264 (`throws` clauses and constant
expressions, dropped or not folded from source). The model keeps the view abstract: a Java class
`java sv cv` has the member types `sv` from source and `cv` from the classfile, and a query that
tells them apart stands for whichever detail the parsers disagree on.

`group` per strategy (`MixedAnalyzingCompiler.compile`):

* `Mixed`: scalac over the round's Scala and Java sources, the Scala units answered from the round's
  Java classes' **source** views; then javac over the Java units, against the round's Scala outputs
  and the Java classes' classfile views.
* `ScalaThenJava`: scalac over the Scala units only, the round's Java classes answered from the
  state (last round's classfiles); then javac as in `Mixed`.
* `JavaThenScala`: javac first, the round's Scala units answered from the state; then scalac.

Results:

* `Mixed` meets the obligations on the sources whose views agree (`obligations_mixed`), so T3a
  holds there (`mixed_sound`); on a Java class whose views differ, `comp` fails (`mixed_not_comp`):
  the joint compile's Scala output is not what the Scala unit compiles to against the classfile,
  which is what an incremental round that recompiles it alone gives.
* Pipelining's early output (`early_view`): a downstream unit compiled against the source views of
  upstream Java classes (their pickles) agrees with one compiled against the classfiles exactly when
  the views agree on the queries it asks; otherwise it differs (`early_view_differs`).
* `ScalaThenJava` and `JavaThenScala`: `comp` fails as soon as a unit of the first stage asks a unit
  of the second in the same round (`scalaThenJava_not_comp`, `javaThenScala_not_comp`); the clean
  build needs the same direction of dependencies.
-/

set_option linter.unusedSectionVars false

namespace Zinc.JavaOrder

open Compiler (State Policy)
open Zinc.JavaSpec (CU Q Ans Client Out Iface Env K)

variable {Pkg N : Type} [DecidableEq Pkg] [DecidableEq N]

inductive Src (Pkg N : Type)
  | absent
  /-- A Java class: its member types as scalac's Java parser reads them, and as javac's classfile
  has them. -/
  | java (sv cv : List N)
  | jclient (c : Client Pkg N)
  | sclient (c : Client Pkg N)

def Src.scala : Src Pkg N → Bool
  | .sclient _ => true
  | _ => false

def Src.agree : Src Pkg N → Prop
  | .java sv cv => sv = cv
  | _ => True

/-- The interface scalac's batch sees. -/
def srcIface : Src Pkg N → Iface N
  | .absent => none
  | .java sv _ => some sv
  | _ => some []

/-- The interface on the classpath: javac's classfile, scalac's for a Scala unit. -/
def cfIface : Src Pkg N → Iface N
  | .absent => none
  | .java _ cv => some cv
  | _ => some []

variable (javaLang : Pkg)

/-- The `JavaSpec` source a unit compiles as: a Java class to its classfile; a client (either
language) runs `JavaSpec`'s lookup, whose levels here stand for each language's rules. -/
def Src.spec : Src Pkg N → JavaSpec.Src Pkg N
  | .absent => .absent
  | .java _ cv => .cls cv
  | .jclient c => .client c
  | .sclient c => .client c

def unit (s : Src Pkg N) : JavaSpec.T Pkg N (Out Pkg N) := JavaSpec.unit javaLang s.spec

theorem iface_unit (e : Env Pkg N) (s : Src Pkg N) : ((unit javaLang s).run e).iface = cfIface s := by
  rw [unit, JavaSpec.iface_unit]
  cases s <;> rfl

inductive Order | mixed | scalaThenJava | javaThenScala
  deriving DecidableEq

/-- The environment of a stage: the round's units answered from `view` where `see` holds, the rest
from `e`. -/
def stageEnv (G : Finset (CU Pkg N)) (src : CU Pkg N → Src Pkg N) (e : Env Pkg N)
    (see : Src Pkg N → Bool) (view : Src Pkg N → Iface N) : Env Pkg N :=
  fun p => if p.1 ∈ G ∧ see (src p.1) then JavaSpec.answer (view (src p.1)) p.2 else e p

/-- The two-stage joint compilation of a round. -/
def group : Order → Finset (CU Pkg N) → (CU Pkg N → Src Pkg N) → Env Pkg N → CU Pkg N → Out Pkg N
  | .mixed, G, src, e, u =>
    if (src u).scala then (unit javaLang (src u)).run (stageEnv G src e (fun _ => true) srcIface)
    else (unit javaLang (src u)).run (stageEnv G src e (fun _ => true) cfIface)
  | .scalaThenJava, G, src, e, u =>
    if (src u).scala then (unit javaLang (src u)).run (stageEnv G src e Src.scala srcIface)
    else (unit javaLang (src u)).run (stageEnv G src e (fun _ => true) cfIface)
  | .javaThenScala, G, src, e, u =>
    if (src u).scala then (unit javaLang (src u)).run (stageEnv G src e (fun _ => true) cfIface)
    else (unit javaLang (src u)).run (stageEnv G src e (fun s => !s.scala) cfIface)

variable [Fintype Pkg] [Fintype N]

/-- The compiler of a compile order, with the fix's keys (`JavaSpec`). Sources are `S`: all of
them, or a subtype such as the sources whose views agree. -/
def compiler (o : Order) (S : Type) (val : S → Src Pkg N) :
    TCompiler (CU Pkg N) S (Out Pkg N) (Iface N) K (Iface N) (Q N) Ans where
  unit := fun s => unit javaLang (val s)
  group := fun G src e => group javaLang o G (val ∘ src) e
  iface := Out.iface
  answer := JavaSpec.answer
  π := JavaSpec.π
  keysOf := JavaSpec.keysOf .fix
  covers := JavaSpec.covers

theorem iface_group (o : Order) (G : Finset (CU Pkg N)) (src : CU Pkg N → Src Pkg N) (e : Env Pkg N)
    (u : CU Pkg N) : (group javaLang o G src e u).iface = cfIface (src u) := by
  cases o <;> simp only [group] <;> split <;> exact iface_unit javaLang _ _

theorem srcIface_eq (s : Src Pkg N) (h : s.agree) : srcIface s = cfIface s := by
  cases s with
  | java sv cv => simp only [Src.agree] at h; simp [srcIface, cfIface, h]
  | _ => rfl

/-- The sources whose two views agree. -/
abbrev Agree (Pkg N : Type) := { s : Src Pkg N // s.agree }

theorem obligations_coverage (o : Order) (S : Type) (val : S → Src Pkg N) :
    ∀ (s : S) (e : Env Pkg N), ∀ q ∈ ((compiler javaLang o S val).unit s).trace e,
      ∃ k ∈ (compiler javaLang o S val).keysOf (((compiler javaLang o S val).unit s).run e),
        q.1 = k.1 ∧ (compiler javaLang o S val).covers q.2 k.2 :=
  fun s e q hq => JavaSpec.obligations_coverage javaLang (val s).spec e q hq

theorem obligations_abstraction (o : Order) (S : Type) (val : S → Src Pkg N) :
    ∀ (i i' : Iface N) (k : K), (compiler javaLang o S val).π i k = (compiler javaLang o S val).π i' k →
      ∀ q, (compiler javaLang o S val).covers q k →
        (compiler javaLang o S val).answer i q = (compiler javaLang o S val).answer i' q :=
  JavaSpec.obligations_abstraction javaLang .fix

/-- **`Mixed` meets the obligations where the views agree**: the round's Scala units read the Java
classes' source views, and those are the classfiles a later round reads. -/
theorem obligations_mixed :
    (compiler javaLang .mixed (Agree Pkg N) Subtype.val).Obligations where
  comp := by
    intro G src e d _
    show group javaLang .mixed G (Subtype.val ∘ src) e d = (unit javaLang (src d).val).run _
    have henv : (compiler javaLang .mixed (Agree Pkg N) Subtype.val).override e G
        ((compiler javaLang .mixed (Agree Pkg N) Subtype.val).iface ∘
          (compiler javaLang .mixed (Agree Pkg N) Subtype.val).group G src e) =
        stageEnv G (Subtype.val ∘ src) e (fun _ => true) srcIface := by
      funext p
      simp only [TCompiler.override, compiler, Function.comp, iface_group, stageEnv, and_true]
      split
      · rw [srcIface_eq _ (src p.1).property]
      · rfl
    rw [henv]
    have hcf : stageEnv G (Subtype.val ∘ src) e (fun _ => true) cfIface =
        stageEnv G (Subtype.val ∘ src) e (fun _ => true) srcIface := by
      funext p
      simp only [stageEnv, Function.comp]
      split
      · rw [srcIface_eq _ (src p.1).property]
      · rfl
    simp only [group, Function.comp]
    split <;> simp only [hcf]
  coverage := obligations_coverage javaLang .mixed _ _
  abstraction := obligations_abstraction javaLang .mixed _ _

/-- **T3a for `Mixed`**, on sources whose views agree. -/
theorem mixed_sound (S : Finset (CU Pkg N)) (src : CU Pkg N → Agree Pkg N)
    (P : Policy (CU Pkg N) (Out Pkg N) K) (hP : P.Sound S) (fuel n : ℕ) (R : Finset (CU Pkg N))
    (s : State (CU Pkg N) (Out Pkg N) K) (D : Finset (CU Pkg N)) (hD : D ⊆ R)
    (hInv : (compiler javaLang .mixed (Agree Pkg N) Subtype.val).Inv S src s D)
    (s' : State (CU Pkg N) (Out Pkg N) K)
    (h : (compiler javaLang .mixed (Agree Pkg N) Subtype.val).zinc S src P fuel n R s = some s') :
    (compiler javaLang .mixed (Agree Pkg N) Subtype.val).Inv S src s' ∅ :=
  (compiler javaLang .mixed _ _).zinc_sound (obligations_mixed javaLang) S src P hP fuel n R s D hD hInv s' h

/-- **Pipelining's early output.** A downstream unit compiled against the source views of the
upstream Java classes (their pickles) produces what it produces against their classfiles, and asks
the same queries, when the two views answer alike on what it asks (`Task.run_eq_of_trace`). -/
theorem early_view (t : JavaSpec.T Pkg N (Out Pkg N)) (up : CU Pkg N → Src Pkg N)
    (h : ∀ q ∈ t.trace (fun p => JavaSpec.answer (srcIface (up p.1)) p.2),
      JavaSpec.answer (srcIface (up q.1)) q.2 = JavaSpec.answer (cfIface (up q.1)) q.2) :
    t.run (fun p => JavaSpec.answer (srcIface (up p.1)) p.2) =
      t.run (fun p => JavaSpec.answer (cfIface (up p.1)) p.2) :=
  (Task.run_eq_of_trace t _ _ h).1

end Zinc.JavaOrder

/-! ## Zinc's exclusion of passed-in Java classes (pipelining)

Under pipelining Zinc hands every Java source to every scalac cycle (`nextChangedSources`), and the
API it computes for a Java class there is the bridge's, from the source view; the API it stored
after the last run is `ClassToAPI`'s, from javac's classfile. The two are different
representations, so comparing them would report a change for every passed-in class. Zinc therefore
drops from API change detection the passed-in Java classes it did not otherwise schedule
(`IncrementalCommon`: `unchangedJavaClasses = pipelinedJavaSources.flatMap(classNames) --
classesToRecompile`).

**Soundness** (`exclusion_exact`): a unit recompiled in a round although none of its recorded keys
changed recompiles to the output it had. Whatever representation the fresh hash is in, there is no
change to report, so dropping it hides nothing. The argument is T2's (abstraction on the keys, then
trace soundness, then `comp`), for a unit inside the round instead of outside it; it needs the
obligations, and so, for a Java class read by Scala units, view agreement (V1). The exclusion is
exact only because Zinc subtracts `classesToRecompile`: a class it did invalidate keeps its
comparison.

**Precision** (`flip_spurious`): the comparison that remains, for an edited or invalidated Java
class, is between the stored classfile-view hash and the fresh source-view hash. When the two
representations never coincide (Zinc's comment: "never equals the one from scalac"), every such
class reports an API change, also for an edit that changes neither view (a comment), so its
dependents are invalidated: Java dependents always (no name filter), Scala dependents on the names
whose hashes differ. Without pipelining both hashes are `ClassToAPI`'s and the edit invalidates
nothing.

**The two consistent-view policies** (`abstraction_single_view`, `abstraction_both_views`): hashing
a Java class from one view only (scalac's, `-Ypickle-java` in every order; or javac's, deferring
change detection for Java until after javac) makes the comparison meaningful, and the exclusion
unnecessary, but each hash determines the answers of its own view only: a Scala reader of the
source view behind a classfile hash, or a javac reader of the classfile behind a source hash, is
covered only under view agreement. A key per view (hash both) meets abstraction for both readers
without it. Costs: scalac's view needs scalac to parse every Java source of the round in every
order (`JavaThenScala` does not today); javac's view needs javac's output before change detection,
so pipelining's cycles would wait for javac, which is what pipelining avoids; both views need both.
-/

namespace Zinc.TCompiler

open Compiler (State)

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : TCompiler CUnit Src Out Iface K Hash Q A) [DecidableEq CUnit]

/-- **The exclusion is exact.** A unit `u` in the round `R` whose recorded keys (before the round)
all keep their hashes recompiles to its previous output. -/
theorem exclusion_exact (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) (D R : Finset CUnit) (hInv : C.Inv S src s D) (u : CUnit)
    (huS : u ∈ S) (huD : u ∉ D) (huR : u ∈ R)
    (hkeys : ∀ p ∈ s.U u, p.1 ∈ R →
      C.π (C.iface (s.out p.1)) p.2 = C.π (C.iface ((C.round src R s).out p.1)) p.2) :
    (C.round src R s).out u = s.out u := by
  set s' := C.round src R s with hs'
  obtain ⟨hout, hcov⟩ := hInv u huS huD
  have hagree : ∀ q ∈ (C.unit (src u)).trace (C.env s), C.env s q = C.env s' q := by
    intro q hq
    obtain ⟨k, hk, hqk, hcovers⟩ := hcov q hq
    simp only [env, envOf, Function.comp]
    by_cases hqR : q.1 ∈ R
    · have := hkeys k hk (hqk ▸ hqR)
      rw [← hqk] at this
      exact ob.abstraction _ _ k.2 this q.2 hcovers
    · have : s'.out q.1 = s.out q.1 := by simp only [hs', round, hqR, ite_false]
      rw [this]
  have hrun := (Task.run_eq_of_trace _ _ _ hagree).1
  have h2 : s'.out u = C.group R src (C.env s) u := by simp only [hs', round, huR, ite_true]
  rw [h2, ob.comp R src (C.env s) u huR, ← env_round, ← hs', hout, hrun]

end Zinc.TCompiler

namespace Zinc.JavaOrder

/-- **The flip is spurious.** The stored hash of a Java class is `ClassToAPI`'s (`hc`, from the
classfile) and the fresh one in a pipelined cycle is the bridge's (`hs`, from the source); if the
two never coincide, an edit that keeps both views (here: the class unchanged) still reports a
change. -/
theorem flip_spurious {Iv H : Type} (hc hs : Iv → H) (hne : ∀ i, hc i ≠ hs i) (sv cv : Iv)
    (hagree : sv = cv) : hc cv ≠ hs sv := by
  rw [hagree]; exact hne cv

variable {Pkg N : Type} [DecidableEq N]

/-- **One view's hash covers one view's readers.** Equal classfile views give equal classfile
answers, but not equal source-view answers unless the views agree. -/
theorem abstraction_single_view :
    (∀ (sv cv sv' cv' : List N), cv = cv' → ∀ q : JavaSpec.Q N,
      JavaSpec.answer (some cv) q = JavaSpec.answer (some cv') q) ∧
    (∀ (sv cv sv' cv' : List N), sv = cv → sv' = cv' → cv = cv' → ∀ q : JavaSpec.Q N,
      JavaSpec.answer (some sv) q = JavaSpec.answer (some sv') q) := by
  refine ⟨fun _ _ _ _ h _ => by rw [h], fun _ _ _ _ h1 h2 h3 _ => by rw [h1, h2, h3]⟩

/-- A key per view (the pair hashed) determines both readers' answers. -/
theorem abstraction_both_views (sv cv sv' cv' : List N) (h : (sv, cv) = (sv', cv')) (q : JavaSpec.Q N) :
    JavaSpec.answer (some sv) q = JavaSpec.answer (some sv') q ∧
      JavaSpec.answer (some cv) q = JavaSpec.answer (some cv') q := by
  cases h; exact ⟨rfl, rfl⟩

end Zinc.JavaOrder

/-! Witnesses in packages `a.b` (0), `a.q` (1), `java.lang` (2), names `Foo` (0), `Bar` (1). The
Java class `a.q.Bar` (unit `(1, 1)`) has a member `Foo` in its classfile view and not in its source
view; the client `a.b.C` (unit `(0, 1)`) imports `a.q.Bar.Foo` statically and finds `a.b.Foo`
(unit `(0, 0)`) otherwise. -/

namespace Zinc.JavaOrder.Witness

open Zinc.JavaOrder Zinc.JavaSpec

abbrev P := Fin 3
abbrev Nm := Fin 2

def cl : Client P Nm := ⟨0, 0, [], [], [((1, 1), 0)], [], []⟩

def prog (scala : Bool) : CU P Nm → JavaOrder.Src P Nm := fun u =>
  if u = (1, 1) then .java [] [0]
  else if u = (0, 0) then .java [] []
  else if u = (0, 1) then (if scala then .sclient cl else .jclient cl)
  else .absent

def e0 : Env P Nm := fun _ => false

def G : Finset (CU P Nm) := {(0, 0), (0, 1), (1, 1)}

/-- **V1, the views of one Java class differ** (scala/scala#11292, scala/scala3#27264). Under
`Mixed`, the Scala client compiled with `a.q.Bar`'s source resolves `Foo` to `a.b.Foo`; against the
classfile it resolves `a.q.Bar.Foo`. A round that recompiles the client alone gives the second, the
clean build the first: `comp` fails. -/
theorem mixed_not_comp :
    ¬ (compiler (2 : P) .mixed (JavaOrder.Src P Nm) id).Obligations := by
  intro ob
  have h := congrArg Out.res (ob.comp G (prog true) e0 (0, 1) (by decide))
  revert h
  decide

/-- A Java client in the same round reads the classfile in both builds: no difference. -/
example : (group (2 : P) .mixed G (prog false) e0 (0, 1)).res = .ok (.mem (1, 1) 0) := by decide

/-- A classfile hash does not determine the source view: two versions of `a.q.Bar` with the same
classfile view and different source views. -/
theorem single_view_not_abstraction :
    JavaSpec.answer (srcIface (JavaOrder.Src.java [] [0] : JavaOrder.Src P Nm)) (.member 0) ≠
      JavaSpec.answer (srcIface (JavaOrder.Src.java [0] [0] : JavaOrder.Src P Nm)) (.member 0) := by
  decide

/-- **V2, pipelining's early output**: a downstream client compiled against `a.q.Bar`'s pickle
(source view) and one compiled against its classfile resolve differently. -/
theorem early_view_differs :
    ((JavaSpec.unit (2 : P) (.client cl)).run (fun p => JavaSpec.answer (srcIface (prog true p.1)) p.2)).res ≠
    ((JavaSpec.unit (2 : P) (.client cl)).run (fun p => JavaSpec.answer (cfIface (prog true p.1)) p.2)).res := by
  decide

/-- **O1, `ScalaThenJava`**: a Scala unit of the round that asks a Java class of the same round
reads last round's classfile (here: none); the fixed point reads the new one. Agreeing views do not
help. -/
def progAgree : CU P Nm → JavaOrder.Src P Nm := fun u =>
  if u = (1, 1) then .java [0] [0]
  else if u = (0, 0) then .java [] []
  else if u = (0, 1) then .sclient cl
  else .absent

theorem scalaThenJava_not_comp :
    ¬ (compiler (2 : P) .scalaThenJava (JavaOrder.Src P Nm) id).Obligations := by
  intro ob
  have h := congrArg Out.res (ob.comp G progAgree e0 (0, 1) (by decide))
  revert h
  decide

/-- **O2, `JavaThenScala`**: the mirror image, a Java client asking a Scala unit of its round; here
the Scala unit is `a.b.Foo` itself, new in this round. -/
def progJ : CU P Nm → JavaOrder.Src P Nm := fun u =>
  if u = (0, 0) then .sclient ⟨0, 1, [], [], [], [], []⟩
  else if u = (0, 1) then .jclient ⟨0, 0, [], [], [], [], []⟩
  else .absent

theorem javaThenScala_not_comp :
    ¬ (compiler (2 : P) .javaThenScala (JavaOrder.Src P Nm) id).Obligations := by
  intro ob
  have h := congrArg Out.res (ob.comp {(0, 0), (0, 1)} progJ e0 (0, 1) (by decide))
  revert h
  decide

end Zinc.JavaOrder.Witness
