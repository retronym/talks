import Zinc.Model

/-!
# Hash stability across forms

The bridge extracts a unit's API from whichever form the compiler holds (the typed tree in the
round, unpickled symbols or TASTy or a classfile otherwise), so the hash Zinc compares across runs
is `π f i = h (view f i)`: a function of the form `f` as well as the interface `i`. The formed
compiler's interface is the pair `(f, i)`; its answers read `i`, its hashes `(f, i)`.

* `abstraction_formed_iff`: the framework's abstraction obligation for the formed interface holds
  exactly when no form masks a difference (`NoMasking`).
* `stable_precise`, `unstable_spurious`: with form stability a reported change means the interface
  changed; without it some unchanged interface reports a change (a spurious invalidation).
* `canonical_stable`, `canonical_noMasking`: hashing a canonical form (through a normalisation of
  each form's view) is stable, and inherits abstraction from the canonical form.
* `skip_unsound`, `conservative_sound`, `conservative_spurious`: carrying the form in the key makes
  same-form comparisons exact, but a cross-form comparison cannot be skipped; reporting it as a
  change is sound and spurious whenever the interface did not change.
* Witnesses: `artefact_bugs` (sbt/zinc#1782, #88, scala/scala3#18080, #9133, #9730: an artefact of
  the form in the view), `masking_237` (sbt/zinc#237: annotations dropped in one form).

`JavaOrder.flip_spurious` is the two-form Java case: the classfile view stored, the source view
fresh.
-/

namespace Zinc.HashForms

variable {F I V H Qy : Type} {A : Qy → Type}

/-- How the bridge sees and hashes an interface in each form, and what the interface answers. -/
structure Forms (F I V H Qy : Type) (A : Qy → Type) where
  view : F → I → V
  h : V → H
  answer : I → (q : Qy) → A q

variable (Φ : Forms F I V H Qy A)

def π (f : F) (i : I) : H := Φ.h (Φ.view f i)

/-- **Precision**: a key whose hash changed while every answer stayed. -/
def Spurious (f f' : F) (i i' : I) : Prop := π Φ f i ≠ π Φ f' i' ∧ ∀ q, Φ.answer i q = Φ.answer i' q

def Stable : Prop := ∀ f f' i, π Φ f i = π Φ f' i

def NoMasking : Prop := ∀ f f' i i', π Φ f i = π Φ f' i' → ∀ q, Φ.answer i q = Φ.answer i' q

/-- The abstraction obligation (`Model.lean`) for the formed interface `(f, i)`, every key covering
every query. -/
def FormedAbstraction : Prop :=
  ∀ x x' : F × I, π Φ x.1 x.2 = π Φ x'.1 x'.2 → ∀ q, Φ.answer x.2 q = Φ.answer x'.2 q

theorem abstraction_formed_iff : FormedAbstraction Φ ↔ NoMasking Φ :=
  ⟨fun h f f' i i' e => h (f, i) (f', i') e, fun h x x' e => h x.1 x'.1 x.2 x'.2 e⟩

/-- **Stability is precision across forms**: a change reported between two forms means the
interface changed. -/
theorem stable_precise (hs : Stable Φ) (f f' : F) (i i' : I) (hne : π Φ f i ≠ π Φ f' i') : i ≠ i' := by
  rintro rfl; exact hne (hs f f' i)

theorem stable_not_spurious (hs : Stable Φ) (f f' : F) (i : I) : ¬ Spurious Φ f f' i i :=
  fun h => h.1 (hs f f' i)

/-- **Instability is a spurious invalidation**: some unchanged interface reports a change. -/
theorem unstable_spurious (hs : ¬ Stable Φ) : ∃ f f' i, Spurious Φ f f' i i := by
  simp only [Stable, not_forall] at hs
  obtain ⟨f, f', i, h⟩ := hs
  exact ⟨f, f', i, h, fun _ => rfl⟩

/-- **The canonical form**: hash every view after normalising it to the canonical form's. -/
def canonical (norm : V → V) : Forms F I V H Qy A := ⟨fun f i => norm (Φ.view f i), Φ.h, Φ.answer⟩

theorem canonical_stable (c : F) (norm : V → V) (hn : ∀ f i, norm (Φ.view f i) = Φ.view c i) :
    Stable (canonical Φ norm) := by
  intro f f' i
  simp only [π, canonical, hn]

/-- The canonical form inherits abstraction from the canonical view alone. -/
theorem canonical_noMasking (c : F) (norm : V → V) (hn : ∀ f i, norm (Φ.view f i) = Φ.view c i)
    (hc : ∀ i i', Φ.h (Φ.view c i) = Φ.h (Φ.view c i') → ∀ q, Φ.answer i q = Φ.answer i' q) :
    NoMasking (canonical Φ norm) := by
  intro f f' i i' e q
  simp only [π, canonical, hn] at e
  exact hc i i' e q

/-- **The form in the key.** Comparing only hashes of the same form, and skipping a comparison
across forms (reporting nothing), misses a real change made while the form changed. -/
def reportsSkip (f f' : F) (i i' : I) : Prop := f = f' ∧ π Φ f i ≠ π Φ f' i'

theorem skip_unsound (f f' : F) (hf : f ≠ f') (i i' : I) (q : Qy)
    (hdiff : Φ.answer i q ≠ Φ.answer i' q) :
    ¬ reportsSkip Φ f f' i i' ∧ ¬ ∀ q, Φ.answer i q = Φ.answer i' q :=
  ⟨fun h => hf h.1, fun h => hdiff (h q)⟩

/-- Reporting every cross-form comparison as a change is sound when same-form hashes do not mask,
and spurious for every unchanged interface read through another form. -/
def reportsConservative (f f' : F) (i i' : I) : Prop := f ≠ f' ∨ π Φ f i ≠ π Φ f' i'

theorem conservative_sound (hsame : ∀ f i i', π Φ f i = π Φ f i' → ∀ q, Φ.answer i q = Φ.answer i' q)
    (f f' : F) (i i' : I) (hno : ¬ reportsConservative Φ f f' i i') : ∀ q, Φ.answer i q = Φ.answer i' q := by
  simp only [reportsConservative, not_or, not_not] at hno
  obtain ⟨rfl, h⟩ := hno
  exact hsame f i i' h

theorem conservative_spurious (f f' : F) (hf : f ≠ f') (i : I) : reportsConservative Φ f f' i i :=
  .inl hf

end Zinc.HashForms

/-! ## The cluster's bugs -/

namespace Zinc.HashForms.Bugs

open Zinc.HashForms

/-- A unit's interface version, seen with an artefact of the form. -/
def artefactForms (art : Bool → String) : Forms Bool ℕ (ℕ × String) (ℕ × String) Unit (fun _ => ℕ) :=
  ⟨fun f i => (i, art f), id, fun i _ => i⟩

/-- The artefact each bug puts in the view, in the two forms Zinc compares. -/
def bugs : List (String × String × String) :=
  [("sbt/zinc#1782: type parameter id through a refinement owner", "A.T", "A.<refinement>.T"),
   ("sbt/zinc#88: override flag", "", "override"),
   ("scala/scala3#18080: context-bound evidence name", "evidence$1", "evidence$2"),
   ("scala/scala3#9133: full name moved by an owner change", "p.C.f", "p.C$f"),
   ("scala/scala3#9730: identity hash in a toString", "Foo@1b6d3586", "Foo@4554617c")]

/-- **Every bug of the cluster is a spurious invalidation**: the same interface hashes differently
in the two forms. -/
theorem artefact_bugs : ∀ b ∈ bugs, ∃ f f' i,
    Spurious (artefactForms fun f => if f then b.2.1 else b.2.2) f f' i i := by
  intro b hb
  refine ⟨true, false, 0, ?_, fun _ => rfl⟩
  simp only [π, artefactForms, id, ite_true, Bool.false_eq_true, ite_false, ne_eq, Prod.mk.injEq,
    true_and]
  revert b
  decide

/-- An interface: its members, and whether it carries an annotation (the query reads it). -/
def annForms : Forms Bool (ℕ × Bool) (ℕ × Bool) (ℕ × Bool) Unit (fun _ => Bool) :=
  ⟨fun keep i => if keep then i else (i.1, false), id, fun i _ => i.2⟩

/-- **sbt/zinc#237**: read at a phase that drops annotations, an annotation added hashes like the
interface without it: a masked change, so abstraction fails. -/
theorem masking_237 : ¬ NoMasking annForms := by
  intro h
  have := h false false (0, true) (0, false) rfl ()
  simp [annForms] at this

end Zinc.HashForms.Bugs
