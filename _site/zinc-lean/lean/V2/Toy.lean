import V2.Embed
import V1.Examples

/-!
# The small Scala, with code generation

V1's toy plus two things the backend reads (simplified from `Zinc/Toy.lean` and the codegen
queries of `Zinc/Flat.lean`):

* **erasure**: a selection emits the JVM descriptor of the member's type. A value class erases to
  its underlying type, so the descriptor asks the class for its `underlying` type, and again if
  that is a value class (the next query depends on the last answer);
* **a mixin forwarder**: a class that mixes in a trait gets one forwarder per member of the trait,
  so it asks the trait for its declarations (`decls`). Simplified: no check that a class ahead of
  the trait in the linearization declares the name.

Zinc's name-only keys record neither query. The repaired keys record both: `(A, self)`, the class
name's hash, which Zinc folds a value class's underlying type into, and `(M, decls)`.

The compiler is a local V1 `Compiler`; the examples run it through `lift`, the general loop.
-/

namespace V2.Toy

open V1

inductive Cls | A | B | C | M
  deriving DecidableEq, Repr

instance : Fintype Cls := ⟨{.A, .B, .C, .M}, by intro x; cases x <;> decide⟩

inductive Name | x | y | foo
  deriving DecidableEq, Repr

inductive Ty | int | double | ref (c : Cls)
  deriving DecidableEq, Repr

structure Member where
  name : Name
  ty : Ty
  implicit : Bool := false
  deriving DecidableEq, Repr

structure ClassDecl where
  members : List Member := []
  /-- `some t`: a value class with underlying type `t`. -/
  underlying : Option Ty := none
  /-- Traits this class mixes in. -/
  mixins : List Cls := []
  deriving DecidableEq, Repr

inductive Expr
  | select (c : Cls) (m : Name)
  | implicitly (ty : Ty) (imports : List Cls)
  deriving DecidableEq, Repr

structure Src where
  decl : ClassDecl
  body : List Expr := []
  deriving DecidableEq, Repr

inductive JvmTy | I | D | L (c : Cls)
  deriving DecidableEq, Repr

structure Out where
  iface : ClassDecl
  descriptors : List JvmTy
  implicits : List (Option (Cls × Name))
  forwarders : List (Cls × Name)
  deriving DecidableEq, Repr

/-! ## Queries -/

inductive Q
  | lookup (n : Name)
  | underlying
  | implicitCandidates (ty : Ty)
  /-- The names a trait declares, for the forwarders of a class that mixes it in. -/
  | decls
  deriving DecidableEq, Repr

def Ans : Q → Type
  | .lookup _ => Option Ty
  | .underlying => Option Ty
  | .implicitCandidates _ => List Name
  | .decls => List Name

def answer (i : ClassDecl) : (q : Q) → Ans q
  | .lookup n => ((i.members.filter (·.name = n)).head?).map (·.ty)
  | .underlying => i.underlying
  | .implicitCandidates ty => ((i.members.filter (·.implicit)).filter (·.ty = ty)).map (·.name)
  | .decls => i.members.map (·.name)

/-! ## Keys and hashes -/

inductive K
  | name (n : Name)
  /-- The class's own name: Zinc folds a value class's underlying type into this hash. -/
  | self
  | implicitScope
  /-- The declared names, as a whole. -/
  | decls
  deriving DecidableEq, Repr

inductive Hash
  | mems (l : List Member)
  | ty (t : Option Ty)
  | names (l : List Name)
  deriving DecidableEq, Repr

def π (i : ClassDecl) : K → Hash
  | .name n => .mems (i.members.filter (·.name = n))
  | .self => .ty i.underlying
  | .implicitScope => .mems (i.members.filter (·.implicit))
  | .decls => .names (i.members.map (·.name))

inductive Covers : Q → K → Prop
  | lookup (n : Name) : Covers (.lookup n) (.name n)
  | underlying : Covers .underlying .self
  | implicits (ty : Ty) : Covers (.implicitCandidates ty) .implicitScope
  | decls : Covers .decls .decls

/-- Name-only keys: only member lookups are recorded. -/
def keysNameOnly (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.filterMap fun p => match p.2 with
    | .lookup n => some (p.1, .name n)
    | _ => none).toFinset

def keyOf : Q → K
  | .lookup n => .name n
  | .underlying => .self
  | .implicitCandidates _ => .implicitScope
  | .decls => .decls

/-- Repaired keys: every query kind has a key. -/
def keysRepaired (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.map fun p => (p.1, keyOf p.2)).toFinset

/-! ## The per-unit task -/

abbrev T := V1.Task (Cls × Q) (fun p => Ans p.2)

def askQ (c : Cls) (q : Q) : T (Ans q) := V1.Task.ask (c, q) V1.Task.pure

/-- Erasure: a value class erases to the erasure of its underlying type. Fuelled. -/
def erase : ℕ → Ty → T JvmTy
  | _, .int => pure .I
  | _, .double => pure .D
  | 0, .ref c => pure (.L c)
  | n + 1, .ref c => do
    match ← askQ c .underlying with
    | none => pure (.L c)
    | some t => erase n t

def shadowed (n : Name) : List Cls → T Bool
  | [] => pure false
  | c :: cs => do
    match ← askQ c (.lookup n) with
    | some _ => pure true
    | none => shadowed n cs

def firstEligible (imports : List Cls) (c : Cls) : List Name → T (Option (Cls × Name))
  | [] => pure none
  | n :: ns => do
    if ← shadowed n (imports.filter (· ≠ c)) then firstEligible imports c ns
    else pure (some (c, n))

def search (ty : Ty) (imports : List Cls) : List Cls → T (Option (Cls × Name))
  | [] => pure none
  | c :: cs => do
    match ← firstEligible imports c (← askQ c (.implicitCandidates ty)) with
    | some r => pure (some r)
    | none => search ty imports cs

def compileBody : List Expr → T (List JvmTy × List (Option (Cls × Name)))
  | [] => pure ([], [])
  | .select c m :: es => do
    let d ← match ← askQ c (.lookup m) with
      | none => pure (.L c)
      | some ty => erase 3 ty
    let (ds, is) ← compileBody es
    pure (d :: ds, is)
  | .implicitly ty imports :: es => do
    let r ← search ty imports imports
    let (ds, is) ← compileBody es
    pure (ds, r :: is)

/-- One forwarder per member of each trait mixed in. -/
def forwarders : List Cls → T (List (Cls × Name))
  | [] => pure []
  | t :: ts => do
    let ns ← askQ t .decls
    let fs ← forwarders ts
    pure (ns.map (t, ·) ++ fs)

def compileUnit (s : Src) : T Out := do
  let (ds, is) ← compileBody s.body
  let fs ← forwarders s.decl.mixins
  pure { iface := s.decl, descriptors := ds, implicits := is, forwarders := fs }

theorem iface_run (s : Src) (e : V1.Task.Env (Cls × Q) (fun p => Ans p.2)) :
    ((compileUnit s).run e).iface = s.decl := by
  simp [compileUnit]

/-! ## The compiler -/

def group (G : Finset Cls) (src : Cls → Src) (e : V1.Task.Env (Cls × Q) (fun p => Ans p.2)) :
    Cls → Out :=
  fun u => (compileUnit (src u)).run fun p => if p.1 ∈ G then answer (src p.1).decl p.2 else e p

def compiler (keys : List (Cls × Q) → Finset (Cls × K)) :
    Compiler Cls Src Out ClassDecl K Hash Q Ans where
  unit := compileUnit
  group := group
  iface := Out.iface
  answer := answer
  π := π
  keys := keys
  covers := Covers

theorem comp (keys) : ∀ (G : Finset Cls) (src : Cls → Src) (e : V1.Task.Env (Cls × Q) (fun p => Ans p.2)),
    ∀ d ∈ G, (compiler keys).group G src e d =
      ((compiler keys).unit (src d)).run ((compiler keys).override e G ((compiler keys).iface ∘ (compiler keys).group G src e)) := by
  intro G src e d _
  show group G src e d = (compileUnit (src d)).run _
  simp only [group]
  congr 1
  funext p
  simp only [Compiler.override, compiler, Function.comp]
  split
  · rw [group, iface_run]
  · rfl

theorem abstraction : ∀ (i i' : ClassDecl) (k : K), π i k = π i' k →
    ∀ q, Covers q k → answer i q = answer i' q := by
  intro i i' k h q hc
  cases hc <;> simp only [π, Hash.mems.injEq, Hash.ty.injEq, Hash.names.injEq] at h <;>
    simp only [answer] <;> rw [h]

theorem coverage_repaired : ∀ (tr : List (Cls × Q)), ∀ q ∈ tr,
    ∃ k ∈ keysRepaired tr, q.1 = k.1 ∧ Covers q.2 k.2 := by
  intro tr q hq
  refine ⟨(q.1, keyOf q.2), ?_, rfl, ?_⟩
  · simp only [keysRepaired, List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, rfl⟩
  · cases q.2 <;> constructor

theorem obligations_repaired : (compiler keysRepaired).Obligations where
  comp := comp keysRepaired
  coverage := coverage_repaired
  abstraction := abstraction

/-- Through the embedding, the repaired compiler meets the general obligations too. -/
theorem general_obligations_repaired : (lift (compiler keysRepaired)).Obligations :=
  lift_obligations _ obligations_repaired

/-- Name-only keys record neither codegen query. -/
theorem not_obligations_nameOnly : ¬ (compiler keysNameOnly).Obligations := by
  intro ob
  obtain ⟨k, hk, _, _⟩ := ob.coverage [(Cls.A, Q.underlying)] (Cls.A, Q.underlying) (by simp)
  simp [compiler, keysNameOnly] at hk

end V2.Toy
