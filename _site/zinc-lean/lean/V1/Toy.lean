import V1.Termination

/-!
# A small Scala, typechecking only

Simplified from `zinc-incrementality/lean/Zinc/Toy.lean`: no value classes and no erasure, so a
selection's output is the member's Scala type. Erasure comes back in `V2`.

* classes with typed members, some implicit;
* a body of expressions: `select c m` (the type of `c.m`) and `implicitly ty imports` (a search
  over the imported classes, with shadowing);
* queries `lookup` and `implicitCandidates`;
* two extractors: name-only keys (only lookups are recorded) and repaired keys (every query kind
  has a key; implicit search gets one key per class, Zinc's unconditional implicit channel).

Interfaces are source-determined (explicit member types), so joint compilation is definable and
compositionality is a lemma.
-/

namespace V1.Toy

inductive Cls | A | B | C
  deriving DecidableEq, Repr

inductive Name | x | y | foo
  deriving DecidableEq, Repr

inductive Ty | int | str
  deriving DecidableEq, Repr

structure Member where
  name : Name
  ty : Ty
  implicit : Bool := false
  deriving DecidableEq, Repr

structure ClassDecl where
  members : List Member := []
  deriving DecidableEq, Repr

inductive Expr
  | select (c : Cls) (m : Name)
  | implicitly (ty : Ty) (imports : List Cls)
  deriving DecidableEq, Repr

structure Src where
  decl : ClassDecl
  body : List Expr := []
  deriving DecidableEq, Repr

structure Out where
  iface : ClassDecl
  /-- The type of each selection, `none` if the member is missing (a compile error). -/
  selects : List (Option Ty)
  /-- The implicit each search resolved to. -/
  implicits : List (Option (Cls × Name))
  deriving DecidableEq, Repr

/-! ## Queries -/

inductive Q
  | lookup (n : Name)
  | implicitCandidates (ty : Ty)
  deriving DecidableEq, Repr

def Ans : Q → Type
  | .lookup _ => Option Ty
  | .implicitCandidates _ => List Name

def answer (i : ClassDecl) : (q : Q) → Ans q
  | .lookup n => ((i.members.filter (·.name = n)).head?).map (·.ty)
  | .implicitCandidates ty => ((i.members.filter (·.implicit)).filter (·.ty = ty)).map (·.name)

/-! ## Keys and hashes -/

inductive K
  | name (n : Name)
  /-- The implicit members as a whole: Zinc's unconditional implicit invalidation. -/
  | implicitScope
  deriving DecidableEq, Repr

inductive Hash
  | mems (l : List Member)
  deriving DecidableEq, Repr

def π (i : ClassDecl) : K → Hash
  | .name n => .mems (i.members.filter (·.name = n))
  | .implicitScope => .mems (i.members.filter (·.implicit))

inductive Covers : Q → K → Prop
  | lookup (n : Name) : Covers (.lookup n) (.name n)
  | implicits (ty : Ty) : Covers (.implicitCandidates ty) .implicitScope

/-- Name-only keys: only member lookups are recorded. -/
def keysNameOnly (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.filterMap fun p => match p.2 with
    | .lookup n => some (p.1, .name n)
    | _ => none).toFinset

/-- Repaired keys: every query kind has a key. -/
def keyOf : Q → K
  | .lookup n => .name n
  | .implicitCandidates _ => .implicitScope

def keysRepaired (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.map fun p => (p.1, keyOf p.2)).toFinset

/-! ## The per-unit task -/

abbrev T := Task (Cls × Q) (fun p => Ans p.2)

def askQ (c : Cls) (q : Q) : T (Ans q) := Task.ask (c, q) Task.pure

/-- Is a candidate named `n` shadowed by a member of that name in another imported class? -/
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

def compileBody : List Expr → T (List (Option Ty) × List (Option (Cls × Name)))
  | [] => pure ([], [])
  | .select c m :: es => do
    let t ← askQ c (.lookup m)
    let (ts, is) ← compileBody es
    pure (t :: ts, is)
  | .implicitly ty imports :: es => do
    let r ← search ty imports imports
    let (ts, is) ← compileBody es
    pure (ts, r :: is)

def compileUnit (s : Src) : T Out := do
  let (ts, is) ← compileBody s.body
  pure { iface := s.decl, selects := ts, implicits := is }

theorem iface_run (s : Src) (e : Task.Env (Cls × Q) (fun p => Ans p.2)) :
    ((compileUnit s).run e).iface = s.decl := by
  simp [compileUnit]

/-! ## The compiler, parameterised by the extractor -/

/-- Joint compilation: every unit of the group sees its group-mates' source interfaces. -/
def group (G : Finset Cls) (src : Cls → Src) (e : Task.Env (Cls × Q) (fun p => Ans p.2)) :
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

/-- Compositionality holds by construction. -/
theorem comp (keys) : ∀ (G : Finset Cls) (src : Cls → Src) (e : Task.Env (Cls × Q) (fun p => Ans p.2)),
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
  cases hc <;> simp only [π, Hash.mems.injEq] at h <;> simp only [answer] <;> rw [h]

theorem coverage_repaired : ∀ (tr : List (Cls × Q)), ∀ q ∈ tr,
    ∃ k ∈ keysRepaired tr, q.1 = k.1 ∧ Covers q.2 k.2 := by
  intro tr q hq
  refine ⟨(q.1, keyOf q.2), ?_, rfl, ?_⟩
  · simp only [keysRepaired, List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, rfl⟩
  · cases q.2 <;> constructor

/-- The repaired extractor meets the obligations. -/
theorem obligations_repaired : (compiler keysRepaired).Obligations where
  comp := comp keysRepaired
  coverage := coverage_repaired
  abstraction := abstraction

/-- The name-only extractor does not: an implicit search has no key. -/
theorem not_obligations_nameOnly : ¬ (compiler keysNameOnly).Obligations := by
  intro ob
  obtain ⟨k, hk, _, _⟩ := ob.coverage [(Cls.A, Q.implicitCandidates .int)]
    (Cls.A, Q.implicitCandidates .int) (by simp)
  simp [compiler, keysNameOnly] at hk

/-- Interfaces are source-determined, so T3's explicit-interface hypothesis holds. -/
theorem explicit (keys) : ∀ (sr : Src) (e : Task.Env (Cls × Q) (fun p => Ans p.2)),
    (compiler keys).iface (((compiler keys).unit sr).run e) = sr.decl :=
  fun sr e => iface_run sr e

end V1.Toy
