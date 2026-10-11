import Zinc.Termination

/-!
# Bodies that are API: inlining and constants, with and without pipelining

A client `C` calls members of `A`. Some calls compile to the callee's *value* instead of a call:

* Scala 3 `inline def`: the body is in TASTy, so it is available from an early output;
* Scala 2 `@inline` with the optimizer: the body is read from `A`'s bytecode, which an early output
  does not have;
* a Java `static final` constant: folded when `A` is read from its classfile, not when it is read
  from its source (`-Ypickle-java`, scala/bug#5333).

The compiler is parameterised by the *view* of `A` the client compiles against, `early` (a pickle
JAR) or `final` (classfiles), and by its hash:

* `today`: a member's hash covers its kind, and its body only for Scala 3 `inline` and constants.
  The Scala 2 `@inline` body is not covered, so `today` fails abstraction
  (`not_obligations_today`) and a body edit leaves `C` with the old inlined value (sbt/zinc#537,
  fixed by sbt/zinc#1310).
* `withBodies`: every body is covered. It meets the obligations in both views
  (`obligations_withBodies`), so each view is sound on its own.

The views disagree, so a pipelined build and a non-pipelined build of the same sources differ
(`pipelined_ne_final`): early agreement (`Pipelining.lean`) fails for Scala 2 `@inline` and for
Java constants, and holds for Scala 3 `inline`.
-/

namespace Zinc.Inline

open Compiler (State Policy)

inductive Cls | A | C
  deriving DecidableEq, Repr

inductive Name | f | g | k
  deriving DecidableEq, Repr

inductive Kind | plain | inline2 | inline3 | javaConst
  deriving DecidableEq, Repr

structure Member where
  name : Name
  kind : Kind
  /-- The value an inlined call or a folded constant becomes. -/
  body : ℕ
  deriving DecidableEq, Repr

abbrev Decl := List Member

structure Src where
  decl : Decl := []
  calls : List (Cls × Name) := []
  deriving DecidableEq, Repr

inductive Emit | call (c : Cls) (n : Name) | inlined (v : ℕ)
  deriving DecidableEq, Repr

structure Out where
  iface : Decl
  code : List Emit
  deriving DecidableEq, Repr

inductive View | early | final
  deriving DecidableEq, Repr

/-- Is a member's body visible in this view? -/
def visible : View → Kind → Bool
  | _, .plain => false
  | _, .inline3 => true
  | .early, .inline2 => false
  | .final, .inline2 => true
  | .early, .javaConst => false
  | .final, .javaConst => true

inductive Q | member (n : Name)
  deriving DecidableEq, Repr

/-- The member's kind, and its body where the view shows it. -/
abbrev Ans (_ : Q) : Type := Option (Kind × Option ℕ)

def answer (v : View) (i : Decl) : (q : Q) → Ans q
  | .member n => ((i.filter (·.name = n)).head?).map fun m =>
      (m.kind, if visible v m.kind then some m.body else none)

inductive K | name (n : Name)
  deriving DecidableEq, Repr

inductive Hashing | today | withBodies
  deriving DecidableEq, Repr

/-- What a member contributes to its name's hash. -/
def memberHash : Hashing → Member → Kind × Option ℕ
  | .today, m => (m.kind, match m.kind with
      | .inline3 | .javaConst => some m.body
      | _ => none)
  | .withBodies, m => (m.kind, some m.body)

def π (h : Hashing) (i : Decl) : K → List (Kind × Option ℕ)
  | .name n => (i.filter (·.name = n)).map (memberHash h)

inductive Covers : Q → K → Prop
  | member (n : Name) : Covers (.member n) (.name n)

def keys (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.map fun p => match p.2 with | .member n => (p.1, K.name n)).toFinset

/-! ## The per-unit task -/

abbrev T := Task (Cls × Q) (fun p => Ans p.2)
abbrev Env := Task.Env (Cls × Q) (fun p => Ans p.2)

def compileCalls : List (Cls × Name) → T (List Emit)
  | [] => .pure []
  | (c, n) :: cs => Task.ask (c, .member n) fun r =>
      (compileCalls cs).bind fun es => .pure ((match r with
        | some (_, some v) => Emit.inlined v
        | _ => Emit.call c n) :: es)

def compileUnit (s : Src) : T Out :=
  (compileCalls s.calls).bind fun es => .pure ⟨s.decl, es⟩

theorem iface_run (s : Src) (e : Env) : ((compileUnit s).run e).iface = s.decl := by
  simp [compileUnit]

def group (v : View) (G : Finset Cls) (src : Cls → Src) (e : Env) : Cls → Out :=
  fun u => (compileUnit (src u)).run fun p => if p.1 ∈ G then answer v (src p.1).decl p.2 else e p

def compiler (v : View) (h : Hashing) :
    Compiler Cls Src Out Decl K (List (Kind × Option ℕ)) Q Ans where
  unit := compileUnit
  group := group v
  iface := Out.iface
  answer := answer v
  π := π h
  keys := keys
  covers := Covers

theorem comp (v : View) (h : Hashing) : ∀ (G : Finset Cls) (src : Cls → Src) (e : Env), ∀ d ∈ G,
    (compiler v h).group G src e d =
      ((compiler v h).unit (src d)).run ((compiler v h).override e G ((compiler v h).iface ∘ (compiler v h).group G src e)) := by
  intro G src e d _
  show group v G src e d = (compileUnit (src d)).run _
  simp only [group]
  congr 1
  funext p
  simp only [Compiler.override, compiler, Function.comp]
  split
  · rw [group, iface_run]
  · rfl

theorem coverage : ∀ (tr : List (Cls × Q)), ∀ q ∈ tr, ∃ k ∈ keys tr, q.1 = k.1 ∧ Covers q.2 k.2 := by
  intro tr q hq
  rcases q with ⟨c, ⟨n⟩⟩
  refine ⟨(c, .name n), ?_, rfl, .member n⟩
  simp only [keys, List.mem_toFinset, List.mem_map]
  exact ⟨(c, .member n), hq, rfl⟩

theorem abstraction_withBodies (v : View) : ∀ (i i' : Decl) (k : K), π .withBodies i k = π .withBodies i' k →
    ∀ q, Covers q k → answer v i q = answer v i' q := by
  intro i i' k h q hc
  cases hc with
  | member n =>
    have key : ∀ j : Decl, answer v j (.member n) =
        ((π .withBodies j (.name n)).head?).map
          (fun p => (p.1, if visible v p.1 then p.2 else none)) := by
      intro j
      simp only [answer, π, List.head?_map, Option.map_map]
      rfl
    rw [key i, key i', h]

theorem obligations_withBodies (v : View) : (compiler v .withBodies).Obligations where
  comp := comp v .withBodies
  coverage := coverage
  abstraction := abstraction_withBodies v

/-- Today's hash leaves a Scala 2 `@inline` body out, and the final view inlines it. -/
theorem not_obligations_today : ¬ (compiler .final .today).Obligations := by
  intro ob
  have := ob.abstraction [⟨.f, .inline2, 1⟩] [⟨.f, .inline2, 2⟩] (.name .f) (by decide)
    (.member .f) (.member .f)
  simp [compiler, answer, visible] at this

/-! ## Scripted tests -/

open Cls Name

abbrev S : Finset Cls := {A, C}

def dummyOut : Out := ⟨[], []⟩

def initial (v : View) (h : Hashing) (src : Cls → Src) : State Cls Out K :=
  (compiler v h).round src S { out := fun _ => dummyOut, U := fun _ => ∅ }

def incremental (v : View) (h : Hashing) (src₀ src₁ : Cls → Src) : Option (State Cls Out K) :=
  (compiler v h).zinc S src₁ Policy.plain 5 0 {A} (initial v h src₀)

def clean (v : View) (src : Cls → Src) (u : Cls) : Out := group v S src (fun _ => none) u

def agrees (v : View) (h : Hashing) (src₀ src₁ : Cls → Src) : Bool :=
  [A, C].all fun c => (incremental v h src₀ src₁).map (·.out c) == some (clean v src₁ c)

/-- `A` has a Scala 2 `@inline def f = 1`, a Scala 3 `inline def g = 1` and a Java constant
`k = 1`; `C` calls all three. -/
def src₀ : Cls → Src
  | A => { decl := [⟨f, .inline2, 1⟩, ⟨g, .inline3, 1⟩, ⟨k, .javaConst, 1⟩] }
  | C => { calls := [(A, f), (A, g), (A, k)] }

/-- Every body becomes 2. -/
def src₁ : Cls → Src
  | A => { decl := [⟨f, .inline2, 2⟩, ⟨g, .inline3, 2⟩, ⟨k, .javaConst, 2⟩] }
  | c => src₀ c

example : (clean .final src₁ C).code = [.inlined 2, .inlined 2, .inlined 2] := by native_decide

/-- Only the Scala 2 `@inline` body changes. -/
def srcF : Cls → Src
  | A => { decl := [⟨f, .inline2, 2⟩, ⟨g, .inline3, 1⟩, ⟨k, .javaConst, 1⟩] }
  | c => src₀ c

/-- Today's hash: `C` keeps the old `@inline` body (sbt/zinc#537). -/
example : (incremental .final .today src₀ srcF).map (·.out C |>.code) =
    some [.inlined 1, .inlined 1, .inlined 1] := by native_decide
example : (clean .final srcF C).code = [.inlined 2, .inlined 1, .inlined 1] := by native_decide
example : agrees .final .today src₀ srcF = false := by native_decide
example : agrees .final .withBodies src₀ srcF = true := by native_decide
/-- When other bodies change too, `C` recompiles anyway and the gap is hidden. -/
example : agrees .final .today src₀ src₁ = true := by native_decide

/-- Pipelined: the early view shows only the Scala 3 `inline` body. -/
example : (clean .early src₁ C).code = [.call A f, .inlined 2, .call A k] := by native_decide

/-- `pipelined_ne_final`: **A pipelined and a non-pipelined build of the same sources differ.** -/
example : clean .early src₁ C ≠ clean .final src₁ C := by native_decide

/-- Each view is sound on its own. -/
example : agrees .early .withBodies src₀ src₁ = true := by native_decide

end Zinc.Inline
