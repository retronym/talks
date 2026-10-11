import Zinc.HashForms

/-!
# The extraHash lineage and the companion namespace

A companion pair is two units, the type half and the term half, under one name. Zinc keys them by
the name: one `AnalyzedClass`, one `extraHash`, one list of parents, one set of name hashes, each a
combination of the two halves. An inheritor reads the type half (its members, its private members,
its trait ancestors' private members); a user of `A.x` reads one half's `x`.

* `merged_spurious`: a key that combines the halves moves with the term half while every answer
  read from the type half stays (sbt/zinc#1793, #1795, #1796 are instances).
* `qualified_precise`, `qualified_sound`: per-namespace keys are not moved by the other half, and
  are sound when each half's hash determines its answers.
* `noFold_misses` (#542, #662): an inheritor whose key does not fold its ancestors' private members
  misses a private change in an ancestor.
* `coldWarm_spurious` (#1794): folding the parents' `extraHash` from the previous analysis is two
  forms of one hash, cold (no fold) and warm (folded): `HashForms.unstable_spurious`.
-/

namespace Zinc.ExtraHash

inductive Ns | type | term
  deriving DecidableEq, Repr

variable {V H A : Type}

/-- A companion pair's two halves, each with a view (what its hash covers). -/
abbrev Pair (V : Type) := Ns → V

/-- Zinc's key: one hash of both halves. -/
def merged (h : V × V → H) (p : Pair V) : H := h (p .type, p .term)

/-- The fix: one hash per half. -/
def qualified (h : V → H) (p : Pair V) (n : Ns) : H := h (p n)

/-- **A merged key is spurious**: a change to the term half alone moves it, while every answer of
the type half stays. -/
theorem merged_spurious (h : V × V → H) (answer : V → A) (p : Pair V) (t' : V)
    (hmove : h (p .type, p .term) ≠ h (p .type, t')) :
    merged h p ≠ merged h (fun n => if n = .term then t' else p n) ∧
      answer (p .type) = answer ((fun n => if n = .term then t' else p n) .type) := by
  simp [merged, hmove]

/-- **Per-namespace keys**: the type half's key does not move with the term half. -/
theorem qualified_precise (h : V → H) (p : Pair V) (t' : V) :
    qualified h p .type = qualified h (fun n => if n = .term then t' else p n) .type := by
  simp [qualified]

/-- And they are sound when each half's hash determines its answers. -/
theorem qualified_sound (h : V → H) (answer : V → A) (hab : ∀ v v', h v = h v' → answer v = answer v')
    (p p' : Pair V) (n : Ns) (heq : qualified h p n = qualified h p' n) : answer (p n) = answer (p' n) :=
  hab _ _ heq

/-- **No fold misses** (#542, #662): an inheritor `D` reads its ancestor `A`'s private members,
but its key on the intermediate `B` hashes only `B`'s own; a private change in `A` keeps the key
and changes the answer. -/
theorem noFold_misses (privB privA privA' : ℕ) (hA : privA ≠ privA') :
    let keyNoFold := fun (privB _ : ℕ) => privB
    let answerD := fun (privB privA : ℕ) => (privB, privA)
    keyNoFold privB privA = keyNoFold privB privA' ∧ answerD privB privA ≠ answerD privB privA' := by
  simp [hA]

/-- With the fold, the key moves (sbt/zinc#1289). -/
example (privB privA privA' : ℕ) (hA : privA ≠ privA') : (privB, privA) ≠ (privB, privA') := by simp [hA]

/-- **Cold and warm** (#1794): a trait `B`'s `extraHash` with its parents' folded from the previous
analysis: none on a cold build, `A`'s on the next. Two forms of one unchanged interface. -/
def coldWarm : HashForms.Forms Bool (ℕ × ℕ) (ℕ × Option ℕ) (ℕ × Option ℕ) Unit (fun _ => ℕ × ℕ) :=
  ⟨fun warm i => (i.1, if warm then some i.2 else none), id, fun i _ => i⟩

theorem coldWarm_spurious : ∃ f f' i, HashForms.Spurious coldWarm f f' i i :=
  HashForms.unstable_spurious coldWarm (by
    intro h
    have := h false true (0, 0)
    simp [HashForms.π, coldWarm] at this)

/-! ## The bugs as instances of `merged_spurious` -/

/-- **#1793**: `trait A` / `object A`; adding `def y` to `object A` moves the pair's `extraHash`,
and with it `B`'s and `D`'s; `D` reads only the trait's private members. -/
example : merged (fun x : List String × List String => x) (fun n => if n = .type then [] else ["x"]) ≠
    merged (fun x => x) (fun n => if n = .term then ["x", "y"] else (fun n => if n = Ns.type then [] else ["x"]) n) := by
  decide

/-- **#1795**: `trait B` / `object B extends A`: the pair's parents are both halves' parents, so a
private change in `A` reaches `trait B`'s inheritor `D`; per namespace, `trait B`'s parents are
empty. -/
example : qualified (fun ps : List String => ps) (fun n => if n = .type then [] else ["A"]) .type = [] := rfl

/-- **#1796** (open): `class A { def x: Int }`, `object A { def x: String }`; a user of `object A.x`
is invalidated by `class A.x`'s change under one name hash; per namespace it is not. -/
example : merged (fun x : String × String => x) (fun n => if n = .type then "Int" else "String") ≠
      merged (fun x => x) (fun n => if n = .type then "Long" else "String") ∧
    qualified (fun x : String => x) (fun n => if n = .type then "Int" else "String") .term =
      qualified (fun x => x) (fun n => if n = .type then "Long" else "String") .term := by
  decide

end Zinc.ExtraHash
