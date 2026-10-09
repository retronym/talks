import V2.Model

/-!
# A non-local hash compared only on the recompiled set is unsound

Rewritten from `zinc-incrementality/lean/Zinc/Stale.lean` for the general model. Two units. `P`
(a parent) exposes one value; `C` (a client) asks `P` for it and emits it. `C` records a single
key `(C, k)` whose hash reads both interfaces, Merkle-style (`hashDeps C = {P, C}`). The
obligations hold.

Edit `P`. With `Δ` over `affected {P} = {P, C}`, the hash of `(C, k)` is recomputed, found
changed, and `C` is invalidated (`stale_affected`). With `Δ` over `{P}` only, no recorded key is
owned by `P`, nothing is invalidated, and `C` keeps a stale output (`stale_unsound`).
-/

namespace V2.Stale

open V1

inductive U | P | C
  deriving DecidableEq, Repr

instance : Fintype U := ⟨{.P, .C}, by intro x; cases x <;> decide⟩

inductive Q | value
  deriving DecidableEq, Repr

def Ans : Q → Type
  | .value => ℕ

inductive K | k
  deriving DecidableEq, Repr

/-- A source is a number: `0` is a client (asks `P`), `n + 1` a parent exposing `n + 1`. -/
abbrev Src := ℕ
abbrev Iface := ℕ
abbrev Out := ℕ

def unit : Src → V1.Task (U × Q) (fun p => Ans p.2) Out
  | 0 => .ask (U.P, Q.value) fun (v : ℕ) => .pure v
  | n + 1 => .pure (n + 1)

def answer (I : U → Iface) : (q : U × Q) → Ans q.2
  | (u, .value) => I u

/-- Joint compilation: group-mates answered from their source interfaces (the number itself). -/
def group (G : Finset U) (src : U → Src) (I : U → Iface) : U → Out :=
  fun u => if u ∈ G then (unit (src u)).run (answer fun v => if v ∈ G then src v else I v) else 0

def compiler : NCompiler U Src Out Iface K (ℕ × ℕ) Q Ans where
  unit := unit
  group := group
  iface := id
  answer := answer
  π := fun I _ _ => (I U.P, I U.C)     -- `C`'s key hashes both interfaces
  hashDeps := fun _ _ => {U.P, U.C}
  keys := fun _ tr => if tr.isEmpty then ∅ else {(U.C, K.k)}
  covers := fun _ _ k => k = (U.C, K.k)

theorem trace_P (s : Src) (e : (q : U × Q) → Ans q.2) : ∀ q ∈ (unit s).trace e, q = (U.P, Q.value) := by
  intro q hq
  cases s <;> simp [unit, V1.Task.trace] at hq
  exact hq

theorem group_P (G : Finset U) (src : U → Src) (I : U → Iface) (hP : U.P ∈ G) :
    group G src I U.P = src U.P := by
  simp only [group, hP, ite_true]
  cases h : src U.P <;> simp [unit, V1.Task.run, answer, hP, h]

theorem obligations : compiler.Obligations where
  comp := by
    intro G src I d hd
    change group G src I d = (unit (src d)).run (answer (NCompiler.override I G (id ∘ group G src I)))
    simp only [group, hd, ite_true]
    apply V1.Task.run_congr
    intro q hq
    rw [trace_P _ _ q hq]
    simp only [answer, NCompiler.override, Function.comp, id]
    by_cases hPG : U.P ∈ G
    · simp only [hPG, ite_true]; exact (group_P G src I hPG).symm
    · simp only [hPG, ite_false]; rfl
  coverage := by
    intro I d s q hq
    refine ⟨(U.C, K.k), ?_, rfl⟩
    have : ¬ ((compiler.unit s).trace (compiler.answer I)).isEmpty := by
      intro h; rw [List.isEmpty_iff] at h; rw [h] at hq; simp at hq
    show (U.C, K.k) ∈ (if ((compiler.unit s).trace (compiler.answer I)).isEmpty then ∅ else {(U.C, K.k)})
    simp [this]
  abstraction := by
    intro I I' k h q hc
    change (I U.P, I U.C) = (I' U.P, I' U.C) at h
    simp only [Prod.mk.injEq] at h
    refine ⟨?_, hc⟩
    rcases q with ⟨u, ⟨⟩⟩
    cases u
    · exact h.1
    · exact h.2
  locality := by
    intro I I' c h _
    show (I U.P, I U.C) = (I' U.P, I' U.C)
    rw [h U.P (by simp [compiler]), h U.C (by simp [compiler])]

/-! ## The scenario -/

abbrev S : Finset U := {U.P, U.C}

def src₀ : U → Src | .P => 1 | .C => 0
def src₁ : U → Src | .P => 2 | .C => 0

/-- The previous clean build of `src₀`, with recorded keys. -/
def s₀ : Compiler.State U Out K := compiler.round src₀ S { out := fun _ => 0, U := fun _ => ∅ }

/-- The round after editing `P`. -/
def s₁ : Compiler.State U Out K := compiler.round src₁ {U.P} s₀

/-- `Δ` over the recompiled set only: nothing is invalidated… -/
example : compiler.invalidated S {U.P} s₀ s₁ = ∅ := by native_decide

/-- …and `C`'s output is stale: it still carries `P`'s old value. -/
theorem stale_unsound :
    s₁.out U.C = 1 ∧ (compiler.unit (src₁ U.C)).run (compiler.answer (compiler.ifaces s₁)) = 2 := by
  native_decide

/-- `Δ` over `affected {P}`: `C` is invalidated, as T2″ requires. -/
theorem stale_affected : compiler.invalidated S (compiler.affected {U.P} s₀) s₀ s₁ = {U.C} := by
  native_decide

end V2.Stale
