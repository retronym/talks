import Zinc.NonLocal

/-!
# T2-stale: a non-local hash compared only on the recompiled set is unsound

Two units. `P` (a parent) exposes one value; `C` (a client) asks `P` for it and emits it. `C`
records a single *closure* key `(C, k)`, Merkle-style: its hash is computed from the interfaces of
both units (`hashDeps C = {P, C}`). That is a perfectly good key: `Obligations` hold.

Edit `P`. If `Δ` is taken over `affected {P} = {P, C}`, the hash of `(C, k)` is recomputed, found
changed, and `C` is invalidated (`stale_affected`). If `Δ` is taken over `{P}` only, nobody
records a key owned by `P`, nothing is invalidated, and `C` keeps a stale output
(`stale_unsound`). This is the trap in the bridge's TODO about "using parent hashes instead":
memoised non-local hashes must be recomputed for the hash dependents of whatever was recompiled,
which is what Zinc's transitive inheritance walk does at invalidation time.

The same applies to an erasure witness (`Erasure.lean`). Computed from the current interfaces
(as there, a non-local hash over the ancestor chain and `V`), it must be diffed over `affected`.
Stored at the owner's compile instead, it is a local hash, and freshness comes from the owner
recompiling when the value class changes.
-/

namespace Zinc.Stale

inductive U | P | C
  deriving DecidableEq, Repr

inductive Q | value
  deriving DecidableEq, Repr

def Ans : Q → Type
  | .value => ℕ

inductive K | k
  deriving DecidableEq, Repr

/-- A source is a number: `0` is the client (asks `P`), `n + 1` is a parent exposing `n + 1`. -/
abbrev Src := ℕ
abbrev Iface := ℕ
abbrev Out := ℕ

abbrev Env := GCompiler.Env (CUnit := U) (Q := Q) (A := Ans)

def unit : Src → Task (U × Q) (fun p => Ans p.2) Out
  | 0 => Task.ask (U.P, Q.value) fun (v : ℕ) => Task.pure v
  | n + 1 => Task.pure (n + 1)

/-- Joint compilation: group-mates answered from their source interfaces (the number itself). -/
def group (G : Finset U) (src : U → Src) (e : Env) : U → Out :=
  fun u => if u ∈ G then (unit (src u)).run (fun p => if p.1 ∈ G then src p.1 else e p) else 0

def compiler : GCompiler U Src Out Iface K (ℕ × ℕ) Q Ans where
  unit := unit
  group := group
  iface := id
  answer := fun i _ => i
  π := fun I _ _ => (I U.P, I U.C)     -- `C`'s key hashes both interfaces, Merkle-style
  hashDeps := fun _ => {U.P, U.C}
  hashRevDeps := fun _ => {U.P, U.C}
  keys := fun tr => if tr.isEmpty then ∅ else {(U.C, K.k)}
  covers := fun _ _ k => k = (U.C, K.k)

open GCompiler Compiler

theorem group_P (G : Finset U) (src : U → Src) (e : Env) (hP : U.P ∈ G) :
    group G src e U.P = src U.P := by
  simp only [group, hP, ite_true]
  cases h : src U.P <;> simp [unit, Task.run, hP, h]

theorem comp_lemma : ∀ (G : Finset U) (src : U → Src) (e : Env),
    ∀ d ∈ G, compiler.group G src e d =
      (compiler.unit (src d)).run (compiler.override e G (compiler.iface ∘ compiler.group G src e)) := by
  intro G src e d hd
  show group G src e d = (unit (src d)).run (GCompiler.override compiler e G (id ∘ group G src e))
  simp only [group, hd, ite_true]
  apply Task.run_congr
  intro q hq
  simp only [GCompiler.override, compiler, Function.comp, id]
  by_cases hqG : q.1 ∈ G
  · simp only [hqG]
    -- the only query any task asks is `(P, value)`
    have hqP : q.1 = U.P := by
      cases h : src d <;> simp [unit, Task.trace, h] at hq
      simp_all
    rw [hqP] at hqG ⊢
    exact (group_P G src e hqG).symm
  · simp only [hqG]
    exact rfl

theorem obligations : compiler.Obligations where
  comp := comp_lemma
  coverage := by
    intro I s q hq
    refine ⟨(U.C, K.k), ?_, rfl⟩
    show (U.C, K.k) ∈ (if ((compiler.unit s).trace (compiler.envOf I)).isEmpty then ∅ else {(U.C, K.k)})
    have : ¬ ((compiler.unit s).trace (compiler.envOf I)).isEmpty := by
      intro h; rw [List.isEmpty_iff] at h; rw [h] at hq; simp at hq
    simp [this]
  abstraction := by
    intro I I' k h q hc
    change (I U.P, I U.C) = (I' U.P, I' U.C) at h
    simp only [Prod.mk.injEq] at h
    refine ⟨?_, hc⟩
    rcases q with ⟨u, _⟩
    cases u
    · exact h.1
    · exact h.2
  locality := by
    intro I I' c h _
    show (I U.P, I U.C) = (I' U.P, I' U.C)
    rw [h U.P (by simp [compiler]), h U.C (by simp [compiler])]
  rev := by intro c d _; cases c <;> simp [compiler]

/-! ## The scenario -/

abbrev S : Finset U := {U.P, U.C}

def src₀ : U → Src | .P => 1 | .C => 0
def src₁ : U → Src | .P => 2 | .C => 0

/-- Previous clean build of `src₀`, with recorded keys. -/
def s₀ : State U Out K := compiler.round src₀ S { out := fun _ => 0, U := fun _ => ∅ }

/-- Round 0 after editing `P`. -/
def s₁ : State U Out K := compiler.round src₁ {U.P} s₀

/-- `Δ` over the recompiled set only: nothing is invalidated… -/
example : compiler.invalidated S {U.P} s₀ s₁ = ∅ := by native_decide

/-- `stale_unsound`: …and `C`'s output is stale: it still carries `P`'s old value. -/
example : s₁.out U.C = 1 ∧ (compiler.unit (src₁ U.C)).run (compiler.env s₁) = 2 := by
  native_decide

/-- `stale_affected`: `Δ` over `affected {P}`: `C` is invalidated, as T2′ requires. -/
example : compiler.invalidated S (compiler.affected {U.P}) s₀ s₁ = {U.C} := by
  native_decide

/-- And after recompiling it, the build is right. -/
example : (compiler.round src₁ {U.C} s₁).out U.C = 2 := by native_decide

end Zinc.Stale
