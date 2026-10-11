import Zinc.Tree
import Zinc.Termination

/-!
# Desugaring and post-typer phases, with keys from the tree

A client `C` of a class `A`, with two kinds of expression:

* `x += 1` with `x : A` (`assignOp`). The typer looks up `+=` in `A`; if it is missing, it looks up
  `+` and rewrites to `x = x + 1`. The typed tree shows the selection it kept.
* `x match { case A(a, b) => }` (`pat`). The typer resolves the synthetic `unapply`, whose
  signature does not mention the fields. After extraction, the pattern matcher selects `_1` and
  `_2`, and checks that the product has no `_3` (an arity error otherwise).

Three extractors over the same typed tree:

| extractor | `assignOp` | `pat` |
|---|---|---|
| `today` | the selection kept (`+` or `+=`) | `unapply` |
| `selectors` | as `today` | `unapply`, `_1`, `_2` |
| `fixed` | `+=` and `+` (the failed lookup too) | `unapply`, `_1`, `_2`, and `_3` as a sentinel |

`fixed` meets the obligations (`obligations_fixed`), so T2 and T3a hold for it; `today` does not
(`not_obligations_today`). Three edits to `A`, each a checked example:

* `A` gains `+=`: `today` and `selectors` leave `C` on `x = x + 1` (`assign-op-member-added`);
* `_1`'s type changes: `today` leaves `C` with the old binder type (scala/scala3#26231);
* `A` gains `_3`: `today` and `selectors` miss the arity error; the sentinel catches it
  (scala/scala3#26262 records `_N+1` for this).
-/

namespace Zinc.TreeToy

open Compiler (State Policy)

inductive Cls | A | C
  deriving DecidableEq, Repr

instance : Fintype Cls := ⟨{.A, .C}, by intro x; cases x <;> decide⟩

inductive Name | plus | plusEq | unapply | p1 | p2 | p3
  deriving DecidableEq, Repr

inductive Ty | int | str
  deriving DecidableEq, Repr

structure Member where
  name : Name
  ty : Ty
  deriving DecidableEq, Repr

abbrev Decl := List Member

inductive Expr
  | assignOp (c : Cls)
  | pat (c : Cls)
  deriving DecidableEq, Repr

structure Src where
  decl : Decl := []
  body : List Expr := []
  deriving DecidableEq, Repr

/-- A node of the typed tree, as the extractor sees it. -/
inductive Node
  /-- Source wrote `+=`; the typer kept a selection of `n`. -/
  | assignOp (c : Cls) (n : Name)
  /-- An extractor pattern on `c` with two binders. -/
  | pat (c : Cls)
  deriving DecidableEq, Repr

inductive PatOut
  | ok (t₁ t₂ : Option Ty)
  | arityError
  deriving DecidableEq, Repr

structure Out where
  iface : Decl
  tree : List Node
  pats : List PatOut
  deriving DecidableEq, Repr

inductive Q | lookup (n : Name)
  deriving DecidableEq, Repr

abbrev Ans (_ : Q) : Type := Option Ty

def answer (i : Decl) : (q : Q) → Ans q
  | .lookup n => ((i.filter (·.name = n)).head?).map (·.ty)

inductive K | name (n : Name)
  deriving DecidableEq, Repr

inductive Hash | mems (l : List Member)
  deriving DecidableEq, Repr

def π (i : Decl) : K → Hash
  | .name n => .mems (i.filter (·.name = n))

inductive Covers : Q → K → Prop
  | lookup (n : Name) : Covers (.lookup n) (.name n)

/-! ## The per-unit task: typer, then the pattern matcher -/

abbrev T := Task (Cls × Q) (fun p => Ans p.2)
abbrev Env := Task.Env (Cls × Q) (fun p => Ans p.2)

def look {α : Type} (c : Cls) (n : Name) (k : Option Ty → T α) : T α :=
  Task.ask (c, .lookup n) k

def typer : List Expr → T (List Node)
  | [] => .pure []
  | .assignOp c :: es => look c .plusEq fun r =>
      match r with
      | some _ => (typer es).bind fun ns => .pure (.assignOp c .plusEq :: ns)
      | none => look c .plus fun _ => (typer es).bind fun ns => .pure (.assignOp c .plus :: ns)
  | .pat c :: es => look c .unapply fun _ => (typer es).bind fun ns => .pure (.pat c :: ns)

def patmat : List Expr → T (List PatOut)
  | [] => .pure []
  | .assignOp _ :: es => patmat es
  | .pat c :: es => look c .p1 fun t₁ => look c .p2 fun t₂ => look c .p3 fun t₃ =>
      (patmat es).bind fun rs =>
        .pure ((if t₃.isSome then PatOut.arityError else PatOut.ok t₁ t₂) :: rs)

def compileUnit (s : Src) : T Out :=
  (typer s.body).bind fun tree => (patmat s.body).bind fun pats => .pure ⟨s.decl, tree, pats⟩

/-! ## Extractors -/

inductive Extractor | today | selectors | fixed
  deriving DecidableEq, Repr

def nodeKeys : Extractor → Node → List (Cls × K)
  | .fixed, .assignOp c _ => [(c, .name .plusEq), (c, .name .plus)]
  | _, .assignOp c n => [(c, .name n)]
  | .today, .pat c => [(c, .name .unapply)]
  | .selectors, .pat c => [(c, .name .unapply), (c, .name .p1), (c, .name .p2)]
  | .fixed, .pat c => [(c, .name .unapply), (c, .name .p1), (c, .name .p2), (c, .name .p3)]

def keysOf (x : Extractor) (o : Out) : Finset (Cls × K) :=
  (o.tree.flatMap (nodeKeys x)).toFinset

/-! ## The compiler -/

theorem iface_run (s : Src) (e : Env) : ((compileUnit s).run e).iface = s.decl := by
  simp [compileUnit]

def group (G : Finset Cls) (src : Cls → Src) (e : Env) : Cls → Out :=
  fun u => (compileUnit (src u)).run fun p => if p.1 ∈ G then answer (src p.1).decl p.2 else e p

def compiler (x : Extractor) : TCompiler Cls Src Out Decl K Hash Q Ans where
  unit := compileUnit
  group := group
  iface := Out.iface
  answer := answer
  π := π
  keysOf := keysOf x
  covers := Covers

theorem comp (x : Extractor) : ∀ (G : Finset Cls) (src : Cls → Src) (e : Env), ∀ d ∈ G,
    (compiler x).group G src e d =
      ((compiler x).unit (src d)).run ((compiler x).override e G ((compiler x).iface ∘ (compiler x).group G src e)) := by
  intro G src e d _
  show group G src e d = (compileUnit (src d)).run _
  simp only [group]
  congr 1
  funext p
  simp only [TCompiler.override, compiler, Function.comp]
  split
  · rw [group, iface_run]
  · rfl

theorem abstraction : ∀ (i i' : Decl) (k : K), π i k = π i' k →
    ∀ q, Covers q k → answer i q = answer i' q := by
  intro i i' k h q hc
  cases hc
  simp only [π, Hash.mems.injEq] at h
  simp only [answer]
  rw [h]

/-! ## Coverage of the fixed extractor -/

/-- The queries an expression can lead to. -/
def exprQs : Expr → List (Cls × Q)
  | .assignOp c => [(c, .lookup .plusEq), (c, .lookup .plus)]
  | .pat c => [(c, .lookup .unapply), (c, .lookup .p1), (c, .lookup .p2), (c, .lookup .p3)]

theorem trace_typer (e : Env) : ∀ (es : List Expr), ∀ q ∈ (typer es).trace e,
    ∃ x ∈ es, q ∈ exprQs x := by
  intro es
  induction es with
  | nil => simp [typer]
  | cons x es ih =>
    intro q hq
    have tail : q ∈ (typer es).trace e → ∃ x' ∈ x :: es, q ∈ exprQs x' := fun h =>
      let ⟨y, hy, hq'⟩ := ih q h; ⟨y, List.mem_cons_of_mem _ hy, hq'⟩
    cases x with
    | assignOp c =>
      simp only [typer, look, Task.trace_ask] at hq
      rcases List.mem_cons.1 hq with h | h
      · exact ⟨_, List.mem_cons_self .., by simp [exprQs, h]⟩
      · split at h
        · simp only [Task.trace_bind, Task.trace_pure, List.append_nil] at h
          exact tail h
        · simp only [Task.trace_ask, Task.trace_bind, Task.trace_pure, List.append_nil] at h
          rcases List.mem_cons.1 h with h | h
          · exact ⟨_, List.mem_cons_self .., by simp [exprQs, h]⟩
          · exact tail h
    | pat c =>
      simp only [typer, look, Task.trace_ask] at hq
      simp only [Task.trace_bind, Task.trace_pure, List.append_nil] at hq
      rcases List.mem_cons.1 hq with h | h
      · exact ⟨_, List.mem_cons_self .., by simp [exprQs, h]⟩
      · exact tail h

theorem trace_patmat (e : Env) : ∀ (es : List Expr), ∀ q ∈ (patmat es).trace e,
    ∃ x ∈ es, q ∈ exprQs x := by
  intro es
  induction es with
  | nil => simp [patmat]
  | cons x es ih =>
    intro q hq
    have tail : q ∈ (patmat es).trace e → ∃ x' ∈ x :: es, q ∈ exprQs x' := fun h =>
      let ⟨y, hy, hq'⟩ := ih q h; ⟨y, List.mem_cons_of_mem _ hy, hq'⟩
    cases x with
    | assignOp c => exact tail (by simpa [patmat] using hq)
    | pat c =>
      simp only [patmat, look, Task.trace_ask] at hq
      simp only [Task.trace_bind, Task.trace_pure, List.append_nil] at hq
      rcases List.mem_cons.1 hq with h | h
      · exact ⟨_, List.mem_cons_self .., by simp [exprQs, h]⟩
      rcases List.mem_cons.1 h with h | h
      · exact ⟨_, List.mem_cons_self .., by simp [exprQs, h]⟩
      rcases List.mem_cons.1 h with h | h
      · exact ⟨_, List.mem_cons_self .., by simp [exprQs, h]⟩
      · exact tail h

/-- The run of the typer on `y :: es` keeps every node of the run on `es`. -/
theorem typer_cons_mem (e : Env) (y : Expr) (es : List Expr) (node : Node)
    (hn : node ∈ (typer es).run e) : node ∈ (typer (y :: es)).run e := by
  cases y with
  | assignOp c =>
    simp only [typer, look, Task.run_ask]
    split <;> simp [Task.run_bind, Task.run_pure, hn]
  | pat c =>
    simp only [typer, look, Task.run_ask]
    simp [Task.run_bind, Task.run_pure, hn]

/-- Every expression leaves a node in the tree whose fixed keys cover all its queries. -/
theorem node_of_expr (e : Env) : ∀ (es : List Expr), ∀ x ∈ es, ∀ q ∈ exprQs x,
    ∃ node ∈ (typer es).run e, ∃ k ∈ nodeKeys .fixed node, q.1 = k.1 ∧ Covers q.2 k.2 := by
  intro es
  induction es with
  | nil => simp
  | cons y es ih =>
    intro x hx q hq
    rcases List.mem_cons.1 hx with rfl | hx
    · cases x with
      | assignOp c =>
        simp only [exprQs, List.mem_cons, List.not_mem_nil, or_false] at hq
        have key : ∀ n, ∃ k ∈ nodeKeys .fixed (.assignOp c n), q.1 = k.1 ∧ Covers q.2 k.2 := by
          intro n
          rcases hq with rfl | rfl
          · exact ⟨(c, .name .plusEq), by simp [nodeKeys], rfl, .lookup _⟩
          · exact ⟨(c, .name .plus), by simp [nodeKeys], rfl, .lookup _⟩
        simp only [typer, look, Task.run_ask]
        split
        · simp only [Task.run_bind, Task.run_pure]
          exact ⟨_, List.mem_cons_self .., key _⟩
        · simp only [Task.run_ask, Task.run_bind, Task.run_pure]
          exact ⟨_, List.mem_cons_self .., key _⟩
      | pat c =>
        simp only [typer, look, Task.run_ask]
        simp only [Task.run_bind, Task.run_pure]
        refine ⟨.pat c, List.mem_cons_self .., ?_⟩
        simp only [exprQs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact ⟨(c, .name .unapply), by simp [nodeKeys], rfl, .lookup _⟩
        · exact ⟨(c, .name .p1), by simp [nodeKeys], rfl, .lookup _⟩
        · exact ⟨(c, .name .p2), by simp [nodeKeys], rfl, .lookup _⟩
        · exact ⟨(c, .name .p3), by simp [nodeKeys], rfl, .lookup _⟩
    · obtain ⟨node, hn, hk⟩ := ih x hx q hq
      exact ⟨node, typer_cons_mem e y es node hn, hk⟩

theorem coverage_fixed : ∀ (s : Src) (e : Env), ∀ q ∈ (compileUnit s).trace e,
    ∃ k ∈ keysOf .fixed ((compileUnit s).run e), q.1 = k.1 ∧ Covers q.2 k.2 := by
  intro s e q hq
  have hx : ∃ x ∈ s.body, q ∈ exprQs x := by
    simp only [compileUnit, Task.trace_bind, Task.trace_pure, List.append_nil, List.mem_append] at hq
    rcases hq with h | h
    · exact trace_typer e _ q h
    · exact trace_patmat e _ q h
  obtain ⟨x, hx, hqx⟩ := hx
  obtain ⟨node, hn, k, hk, h1, h2⟩ := node_of_expr e s.body x hx q hqx
  refine ⟨k, ?_, h1, h2⟩
  simp only [keysOf, compileUnit, Task.run_bind, Task.run_pure, List.mem_toFinset, List.mem_flatMap]
  exact ⟨node, hn, hk⟩

theorem obligations_fixed : (compiler .fixed).Obligations where
  comp := comp .fixed
  coverage := coverage_fixed
  abstraction := abstraction

/-- Zinc's extractor misses the pattern matcher's `_1`. -/
theorem not_obligations_today : ¬ (compiler .today).Obligations := by
  intro ob
  have h := ob.coverage { body := [.pat .A] } (fun _ => none) (Cls.A, .lookup .p1)
    (by simp [compiler, compileUnit, typer, patmat, look])
  obtain ⟨k, hk, _, hc⟩ := h
  simp [compiler, compileUnit, typer, patmat, look, keysOf, nodeKeys] at hk
  subst hk
  cases hc

/-! ## Scripted tests -/

open Cls Name

abbrev S : Finset Cls := {A, C}

def dummyOut : Out := ⟨[], [], []⟩

def initial (x : Extractor) (src : Cls → Src) : State Cls Out K :=
  (compiler x).round src S { out := fun _ => dummyOut, U := fun _ => ∅ }

def incremental (x : Extractor) (src₀ src₁ : Cls → Src) : Option (State Cls Out K) :=
  (compiler x).zinc S src₁ Policy.plain 5 0 {A} (initial x src₀)

def cleanOut (src : Cls → Src) (u : Cls) : Out :=
  group S src (fun _ => none) u

def agrees (x : Extractor) (src₀ src₁ : Cls → Src) : Bool :=
  [A, C].all fun c => (incremental x src₀ src₁).map (·.out c) == some (cleanOut src₁ c)

/-- `A` gains `+=` (`assign-op-member-added`). -/
def ao₀ : Cls → Src
  | A => { decl := [⟨plus, .int⟩] }
  | C => { body := [.assignOp A] }
def ao₁ : Cls → Src
  | A => { decl := [⟨plus, .int⟩, ⟨plusEq, .int⟩] }
  | c => ao₀ c

example : (incremental .today ao₀ ao₁).map (·.out C |>.tree) = some [.assignOp A plus] := by
  native_decide
example : (cleanOut ao₁ C).tree = [.assignOp A plusEq] := by native_decide
example : agrees .today ao₀ ao₁ = false := by native_decide
example : agrees .selectors ao₀ ao₁ = false := by native_decide
example : agrees .fixed ao₀ ao₁ = true := by native_decide

/-- `_1`'s type changes (scala/scala3#26231). -/
def pt₀ : Cls → Src
  | A => { decl := [⟨unapply, .int⟩, ⟨p1, .int⟩, ⟨p2, .int⟩] }
  | C => { body := [.pat A] }
def pt₁ : Cls → Src
  | A => { decl := [⟨unapply, .int⟩, ⟨p1, .str⟩, ⟨p2, .int⟩] }
  | c => pt₀ c

example : (incremental .today pt₀ pt₁).map (·.out C |>.pats) = some [.ok (some .int) (some .int)] := by
  native_decide
example : (cleanOut pt₁ C).pats = [.ok (some .str) (some .int)] := by native_decide
example : agrees .today pt₀ pt₁ = false := by native_decide
example : agrees .selectors pt₀ pt₁ = true := by native_decide
example : agrees .fixed pt₀ pt₁ = true := by native_decide

/-- `A` gains `_3`: the two-binder pattern no longer fits. -/
def ar₁ : Cls → Src
  | A => { decl := [⟨unapply, .int⟩, ⟨p1, .int⟩, ⟨p2, .int⟩, ⟨p3, .int⟩] }
  | c => pt₀ c

example : (cleanOut ar₁ C).pats = [.arityError] := by native_decide
example : agrees .today pt₀ ar₁ = false := by native_decide
example : agrees .selectors pt₀ ar₁ = false := by native_decide
example : agrees .fixed pt₀ ar₁ = true := by native_decide

end Zinc.TreeToy
