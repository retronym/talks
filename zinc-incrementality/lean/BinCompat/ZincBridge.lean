import Zinc.General
import Scala.Catalogue

/-!
# B4: Zinc-clean implies binary compatible

**The front end.** Scala lowering (`Scala/Lower.lean`) as an `XCompiler` (`General.lean`):

* a unit is a source unit, named;
* its task is `Scala.lowerSrc`, its queries renamed into the framework's shape (`decl n isObj` asks
  unit `n` for one side of its interface);
* its output is the unit's source interface (its class and object declarations) together with
  its lowered classfiles.

The interface is the declaration, so it is source-determined: the explicit-interface case of T3b.

Every query is answered as if the definition were in the same compiler run (`View.inRun = true`).
That is faithful for Scala 2.12 and 2.13, whose lowering ignores `inRun`. For Scala 3, separate
compilation differs (F6: a trait's `$init$`), which is a failure of compositionality
(`Scala/Facts.lean`), not something a key repairs.

**A sound bridge** (`searched`): a key per traced query, its hash the declaration it read. It meets
the obligations (`searched_obligations`), so the hypothesis of the theorem below is satisfiable.

**The theorem**, for any `XCompiler` meeting the obligations whose interfaces are source-determined
(`untouched_eq_clean`). After an edit, if Zinc's loop stops and a unit `c` was never in a round
(`c ∉ recompiled …`), then `c`'s old output equals its output in the clean build of the new sources.
For lowering, the old classfiles of `c` next to the new library link exactly as a fresh build
does (`after_eq_fresh`), so `Jvm.Compatible` holds whenever the fresh build links
(`compatible_of_untouched`).

**The converse fails** (`gap_witness`): a concrete method added to a trait is binary compatible
for a class mixing the trait in (it links, and selects the trait's default method), but the class's
lowered classfile changes (a fresh build adds a mixin forwarder). So every sound bridge must have
Zinc recompile it (`must_recompile`). MiMa reports nothing here: the gap between `Compatible` and
Zinc-clean is exactly such edits.
-/

namespace Zinc.XCompiler

open Compiler (State Policy)

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : XCompiler CUnit Src Out Iface K Hash Q A)
variable [DecidableEq CUnit] [DecidableEq K] [DecidableEq Hash]

/-- The units the loop recompiles: the union of its rounds, by the same recursion as `zinc`. -/
def recompiled (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) :
    ℕ → ℕ → Finset CUnit → State CUnit Out K → Finset CUnit
  | 0, _, R, _ => R
  | fuel + 1, n, R, s =>
    let s' := C.round src R s
    let I := C.invalidated S R s s'
    if I ⊆ R then R else R ∪ recompiled S src P fuel (n + 1) (P n R s s' I) s'

/-- A unit no round recompiles keeps its output. -/
theorem out_of_not_recompiled (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) :
    ∀ (fuel n : ℕ) (R : Finset CUnit) (s s' : State CUnit Out K) (c : CUnit),
      C.zinc S src P fuel n R s = some s' → c ∉ C.recompiled S src P fuel n R s →
        s'.out c = s.out c := by
  intro fuel
  induction fuel with
  | zero => intro n R s s' c h; simp [zinc] at h
  | succ fuel ih =>
    intro n R s s' c h hc
    simp only [zinc] at h
    simp only [recompiled] at hc
    split at h
    · rename_i hsub
      cases h
      rw [if_pos hsub] at hc
      simp [round, hc]
    · rename_i hsub
      rw [if_neg hsub, Finset.mem_union, not_or] at hc
      rw [ih _ _ _ _ c h hc.2]
      simp [round, hc.1]

/-- A per-unit fixed point of separate compilation on `S`. -/
def Fixpoint (S : Finset CUnit) (src : CUnit → Src) (o : CUnit → Out) : Prop :=
  ∀ u ∈ S, o u = (C.unit (src u)).run (C.answer (C.iface ∘ o))

/-- The clean build of `S` against `s`'s outputs for everything else. -/
def cleanFrom (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) : CUnit → Out :=
  fun u => if u ∈ S then C.group S src (C.ifaces s) u else s.out u

omit [DecidableEq K] [DecidableEq Hash] in
theorem cleanFrom_fixpoint (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) : C.Fixpoint S src (C.cleanFrom S src s) := by
  intro u hu
  have h := ob.comp S src (C.ifaces s) u hu
  have hout : C.cleanFrom S src s u = C.group S src (C.ifaces s) u := by simp [cleanFrom, hu]
  rw [hout, h]
  congr 2
  funext v
  simp only [override, cleanFrom, Function.comp, ifaces]
  split <;> rfl

omit [DecidableEq K] [DecidableEq Hash] in
/-- **Uniqueness under explicit interfaces** (T3b), for the general form. -/
theorem fixpoint_unique_of_explicit (S : Finset CUnit) (src : CUnit → Src) (ifaceSrc : Src → Iface)
    (hex : ∀ (sr : Src) (I : CUnit → Iface), C.iface ((C.unit sr).run (C.answer I)) = ifaceSrc sr)
    (o₁ o₂ : CUnit → Out) (h₁ : C.Fixpoint S src o₁) (h₂ : C.Fixpoint S src o₂)
    (hext : ∀ u ∉ S, o₁ u = o₂ u) : o₁ = o₂ := by
  have hi : C.iface ∘ o₁ = C.iface ∘ o₂ := by
    funext p
    simp only [Function.comp]
    by_cases hp : p ∈ S
    · rw [h₁ _ hp, h₂ _ hp, hex, hex]
    · rw [hext _ hp]
  funext u
  by_cases hu : u ∈ S
  · rw [h₁ u hu, h₂ u hu, hi]
  · exact hext u hu

omit [DecidableEq K] [DecidableEq Hash] in
/-- An up-to-date build, edited at `D`: every other unit is still up to date. -/
theorem inv_of_edit (S : Finset CUnit) (src₀ src : CUnit → Src) (s : State CUnit Out K)
    (D : Finset CUnit) (hInv : C.Inv S src₀ s ∅) (hD : ∀ u, src₀ u ≠ src u → u ∈ D) :
    C.Inv S src s D := by
  intro u hu huD
  have h := hInv u hu (Finset.notMem_empty u)
  have : src₀ u = src u := by by_contra hne; exact huD (hD u hne)
  unfold UpToDate at h ⊢
  rw [this] at h
  exact h

/-- **B4.** After an edit (the dirty set `D` ⊆ the first round `R₀`), if Zinc's loop stops and a
unit `c` was in none of its rounds, `c`'s old output is its output in the clean build of the new
sources. Hypotheses: the obligations; interfaces determined by the source; a sound policy that
stays inside `S`. -/
theorem untouched_eq_clean (ob : C.Obligations) (ifaceSrc : Src → Iface)
    (hex : ∀ (sr : Src) (I : CUnit → Iface), C.iface ((C.unit sr).run (C.answer I)) = ifaceSrc sr)
    (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) (hP : P.Sound S)
    (hPS : P.InS S) (fuel : ℕ) (R₀ D : Finset CUnit) (s : State CUnit Out K)
    (hD : D ⊆ R₀) (hR₀ : R₀ ⊆ S) (hInv : C.Inv S src s D)
    (s' : State CUnit Out K) (h : C.zinc S src P fuel 0 R₀ s = some s') (c : CUnit)
    (hc : c ∉ C.recompiled S src P fuel 0 R₀ s) :
    s.out c = C.cleanFrom S src s c := by
  have hfin := C.zinc_sound ob S src P hP fuel 0 R₀ s D hD hInv s' h
  have hfix : C.Fixpoint S src s'.out := fun u hu => (hfin u hu (Finset.notMem_empty u)).1
  have hclean := C.fixpoint_unique_of_explicit S src ifaceSrc hex s'.out (C.cleanFrom S src s)
    hfix (C.cleanFrom_fixpoint ob S src s) (fun u hu => by
      rw [C.zinc_out_outside S src P hPS fuel 0 R₀ s hR₀ s' h u hu]
      simp [cleanFrom, hu])
  rw [← C.out_of_not_recompiled S src P fuel 0 R₀ s s' c h hc, hclean]

/-- Contrapositive: a unit whose old output differs from its clean output is recompiled. -/
theorem must_recompile (ob : C.Obligations) (ifaceSrc : Src → Iface)
    (hex : ∀ (sr : Src) (I : CUnit → Iface), C.iface ((C.unit sr).run (C.answer I)) = ifaceSrc sr)
    (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) (hP : P.Sound S)
    (hPS : P.InS S) (fuel : ℕ) (R₀ D : Finset CUnit) (s : State CUnit Out K)
    (hD : D ⊆ R₀) (hR₀ : R₀ ⊆ S) (hInv : C.Inv S src s D)
    (s' : State CUnit Out K) (h : C.zinc S src P fuel 0 R₀ s = some s') (c : CUnit)
    (hne : s.out c ≠ C.cleanFrom S src s c) : c ∈ C.recompiled S src P fuel 0 R₀ s := by
  by_contra hc
  exact hne (C.untouched_eq_clean ob ifaceSrc hex S src P hP hPS fuel R₀ D s hD hR₀ hInv s' h c hc)

end Zinc.XCompiler

/-! ## Scala lowering as an `XCompiler` -/

namespace BinCompat.ZincBridge

open Scala

/-- The framework's queries: unit `n`, and which side (`true`: the object). -/
abbrev FQ := String × Bool

abbrev FAns : FQ → Type := fun _ => Option View

/-- Rename lowering's queries into the framework's shape. -/
def tr {α : Type} : Zinc.Task Scala.Q Scala.Ans α → Zinc.Task FQ FAns α
  | .pure a => .pure a
  | .ask (.decl n o) k => .ask (n, o) fun v => tr (k v)

/-- An environment in the framework's shape, read by lowering. -/
def back (e : (q : FQ) → FAns q) : (q : Scala.Q) → Scala.Ans q
  | .decl n o => e (n, o)

theorem run_tr {α : Type} (e : (q : FQ) → FAns q) : ∀ t : Zinc.Task Scala.Q Scala.Ans α,
    (tr t).run e = t.run (back e)
  | .pure _ => rfl
  | .ask (.decl n o) k => by simp only [tr, Zinc.Task.run_ask]; exact run_tr e (k (e (n, o)))

def fq : Scala.Q → FQ
  | .decl n o => (n, o)

theorem trace_tr {α : Type} (e : (q : FQ) → FAns q) : ∀ t : Zinc.Task Scala.Q Scala.Ans α,
    (tr t).trace e = (t.trace (back e)).map fq
  | .pure _ => rfl
  | .ask (.decl n o) k => by
    simp only [tr, Zinc.Task.trace_ask, List.map_cons]
    exact congrArg _ (trace_tr e (k (e (n, o))))

/-- A unit's interface: its class and object declarations, if it exists. -/
abbrev Iface := Option (Option Decl × Option Decl)

structure Out where
  iface : Iface
  classes : Except String (List ClassOut)
  deriving DecidableEq

def ifaceSrc : Option Scala.Src → Iface
  | none => none
  | some s => some (s.cls, s.obj)

/-- One side of a unit's interface: the hash of a key, and the answer to a query. -/
def side (I : String → Iface) (q : FQ) : Option Decl :=
  (I q.1).bind fun co => if q.2 then co.2 else co.1

def answer (I : String → Iface) (q : FQ) : FAns q := (side I q).map fun d => { decl := d }

def unit (dl : Dialect) : Option Scala.Src → Zinc.Task FQ FAns Out
  | none => .pure ⟨none, .error "absent"⟩
  | some s => (tr (lowerSrc dl s).run).bind fun r => .pure ⟨some (s.cls, s.obj), r⟩

theorem iface_unit (dl : Dialect) (s : Option Scala.Src) (e : (q : FQ) → FAns q) :
    ((unit dl s).run e).iface = ifaceSrc s := by
  cases s with
  | none => rfl
  | some s => simp [unit, ifaceSrc]

def group (dl : Dialect) (G : Finset String) (src : String → Option Scala.Src) (I : String → Iface) :
    String → Out :=
  fun u => (unit dl (src u)).run (answer fun v => if v ∈ G then ifaceSrc (src v) else I v)

/-- Lowering, with the `searched` bridge: a key per traced query, hashed by the declaration it read. -/
def compiler (dl : Dialect) :
    Zinc.XCompiler String (Option Scala.Src) Out Iface Bool (Option Decl) Bool (fun _ => Option View) where
  unit := unit dl
  group := group dl
  iface := Out.iface
  answer := answer
  π I u k := side I (u, k)
  hashDeps _ u := {u}
  keys _ _ tr := tr.toFinset
  covers _ q k := q = k

theorem searched_obligations (dl : Dialect) : (compiler dl).Obligations where
  comp G src I u _ := by
    show (unit dl (src u)).run (answer _) = (unit dl (src u)).run (answer _)
    congr 2
    funext v
    simp only [Zinc.XCompiler.override, compiler, Function.comp, group, iface_unit]
  coverage I _ s q hq := ⟨q, List.mem_toFinset.2 hq, rfl⟩
  abstraction I I' k h q hc := by
    subst hc
    refine ⟨?_, rfl⟩
    show (side I q).map _ = (side I' q).map _
    have : side I q = side I' q := h
    rw [this]
  locality I I' c h k := by
    show side I (c, k) = side I' (c, k)
    simp only [side, h c (Finset.mem_singleton_self c)]

/-- The interface is the declaration: source-determined. -/
theorem explicit (dl : Dialect) (sr : Option Scala.Src) (I : String → Iface) :
    (compiler dl).iface (((compiler dl).unit sr).run ((compiler dl).answer I)) = ifaceSrc sr :=
  iface_unit dl sr _

/-! ## Linking -/

/-- The classfiles of the units `us`, as a JVM class table. -/
def worldOf (us : List String) (o : String → Out) : Jvm.World String String String :=
  toWorld ((us.filterMap fun u => (o u).classes.toOption).flatten)

/-- The class table after a library edit with `c` not recompiled: `c`'s old classfiles, everything
else from the new build. -/
def afterWorld (us : List String) (clean : String → Out) (c : String) (old : Out) :
    Jvm.World String String String :=
  worldOf us fun u => if u = c then old else clean u

/-- **B4 for lowering.** Under the `searched` bridge (or any bridge meeting the obligations, by
`Zinc.XCompiler.untouched_eq_clean`), a client `c` that Zinc's loop never recompiled links against
the new library exactly as a fresh build does. -/
theorem after_eq_fresh (dl : Dialect) (us : List String) (S : Finset String)
    (src : String → Option Scala.Src) (P : Zinc.Compiler.Policy String Out Bool) (hP : P.Sound S)
    (hPS : P.InS S) (fuel : ℕ) (R₀ D : Finset String) (s : Zinc.Compiler.State String Out Bool)
    (hD : D ⊆ R₀) (hR₀ : R₀ ⊆ S) (hInv : (compiler dl).Inv S src s D)
    (s' : Zinc.Compiler.State String Out Bool) (h : (compiler dl).zinc S src P fuel 0 R₀ s = some s')
    (c : String) (hc : c ∉ (compiler dl).recompiled S src P fuel 0 R₀ s)
    (p : Jvm.Program String String String) :
    Jvm.outcome (afterWorld us ((compiler dl).cleanFrom S src s) c (s.out c)) p =
      Jvm.outcome (worldOf us ((compiler dl).cleanFrom S src s)) p := by
  have := (compiler dl).untouched_eq_clean (searched_obligations dl) ifaceSrc (explicit dl)
    S src P hP hPS fuel R₀ D s hD hR₀ hInv s' h c hc
  unfold afterWorld
  congr 2
  funext u
  split
  · subst_vars; exact this
  · rfl

/-- **Compatible, from Zinc-clean.** If the fresh build links, the old client classfiles link
against the new library. -/
theorem compatible_of_untouched (dl : Dialect) (us : List String) (S : Finset String)
    (src : String → Option Scala.Src) (P : Zinc.Compiler.Policy String Out Bool) (hP : P.Sound S)
    (hPS : P.InS S) (fuel : ℕ) (R₀ D : Finset String) (s : Zinc.Compiler.State String Out Bool)
    (hD : D ⊆ R₀) (hR₀ : R₀ ⊆ S) (hInv : (compiler dl).Inv S src s D)
    (s' : Zinc.Compiler.State String Out Bool) (h : (compiler dl).zinc S src P fuel 0 R₀ s = some s')
    (c : String) (hc : c ∉ (compiler dl).recompiled S src P fuel 0 R₀ s)
    (p : Jvm.Program String String String) (w₀ : Jvm.World String String String)
    (hfresh : (Jvm.outcome (worldOf us ((compiler dl).cleanFrom S src s)) p).toBool = true) :
    Jvm.Compatible w₀ (afterWorld us ((compiler dl).cleanFrom S src s) c (s.out c)) p := by
  intro _
  rw [after_eq_fresh dl us S src P hP hPS fuel R₀ D s hD hR₀ hInv s' h c hc p]
  exact hfresh

/-! ## The converse fails -/

/-- `T` gains a concrete `b`; `X extends T`. -/
def t0 : Scala.Src := Catalogue.trt "T" [Catalogue.dfn "a"]
def t1 : Scala.Src := Catalogue.trt "T" [Catalogue.dfn "a", Catalogue.dfn "b"]
def x : Scala.Src := Catalogue.cls "X" [] none [("T", none)]

def src0 : String → Option Scala.Src := fun u => if u = "T" then some t0 else if u = "X" then some x else none
def src1 : String → Option Scala.Src := fun u => if u = "T" then some t1 else if u = "X" then some x else none

def S : Finset String := {"T", "X"}

/-- The old build: everything compiled against the old sources. -/
def old : String → Out := group .s213 S src0 (fun _ => none)
/-- The fresh build of the new sources. -/
def fresh : String → Out := group .s213 S src1 (fun _ => none)

/-- **The gap.** Adding a concrete method to a trait leaves the old `X` linking against the new `T`
(binary compatible: `X` selects the trait's default `b`), yet `X`'s classfile changes: the fresh
build adds a mixin forwarder. So no sound bridge leaves `X` alone (`must_recompile`), and MiMa,
which compares only the library, reports nothing. -/
theorem gap_witness :
    old "X" ≠ fresh "X" ∧
    Jvm.Compatible (worldOf ["T", "X"] old)
      (worldOf ["T", "X"] fun u => if u = "X" then old "X" else fresh u)
      Catalogue.concreteAddedToTrait.prog := by
  refine ⟨by decide +kernel, ?_⟩
  intro _
  decide +kernel

end BinCompat.ZincBridge
