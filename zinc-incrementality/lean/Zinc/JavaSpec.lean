import Zinc.Tree
import Mathlib.Data.Fintype.Prod

/-!
# Java name resolution as a specification

A `TCompiler` instance (`Tree.lean`: keys are read off the output) for a Java client resolving one
simple type name `n`. The output is the classfile and, for the fix, facts from javac's attributed
tree; Zinc's Java side reads its keys from both. Everything is over arbitrary finite sets of
packages `Pkg` and simple names `N`, and arbitrary programs: any number of classes, members and
imports.

**Units** are top-level classes, named by package and simple name (`Pkg × N`); a unit's source is
absent, a class with member types, or the client. **Queries** to a unit: does the class exist, and
does it have a member type `m`.

**The task** is JLS 6.4.1 / 7.5 resolution by levels. Every probe of a level is asked; the first
level with a hit decides: one hit resolves, two are an ambiguity error, none moves on.

1. member types of the superinterfaces (inherited member types);
2. single-type imports and single-static imports named `n`;
3. the client's own package;
4. on-demand imports (packages, static on-demand) and `java.lang`.

Before resolving, javac checks that every single-type import names an existing class.

Simplifications: one name and one use; superinterfaces' own supertypes are not searched; a
single-static import is assumed to name an existing static member (in the harness, `X` always has a
static method of that name), and on-demand packages are assumed to exist; two hits on one level are
always distinct classes.

**Keys.** Zinc records, for a Java class, the classes in its constant pool (`JavaAnalyze`): its
superinterfaces and the class the name resolved to (for a member type, the outer class, from
`InnerClasses`). A Java dependent is invalidated on any API change of such a class (no name
filter): the key `cls` with the whole interface as hash. A Java class records no used names, so
retronym/zinc#34's rule (invalidate the users of an added class's simple name) adds no key: `cheap`
and `today` are the same key set. The fix (retronym/zinc#43) adds the used name, read as #34 uses it,
as an existence key on every unit with that simple name; and an edge (`cls`) to the class of every
import (#43 records static imports; the single-type import edge is the refinement `J4` asks for).

**Results.** `today` fails coverage, with one witness per family (`J1` to `J4`), and so does
`names` (#34 reaching Java clients, without import edges) for `J2` to `J4`. `fix` meets the
obligations (`obligations_fix`) and inherits T3a (`fix_sound`).
-/

set_option linter.unusedSectionVars false

namespace Zinc.JavaSpec

open Compiler (State Policy)

variable {Pkg N : Type} [DecidableEq Pkg] [DecidableEq N]

abbrev CU (Pkg N : Type) := Pkg × N

inductive Q (N : Type) | present | member (m : N)
  deriving DecidableEq

abbrev Ans (_ : Q N) : Type := Bool

/-- A place the lookup looks: a top-level class, or a member type of a class. -/
inductive Probe (Pkg N : Type) | top (u : CU Pkg N) | mem (x : CU Pkg N) (m : N)
  deriving DecidableEq

def Probe.query : Probe Pkg N → CU Pkg N × Q N
  | .top u => (u, .present)
  | .mem x m => (x, .member m)

/-- The class a reference to the probe's hit records in the constant pool (an outer class for a
member type). -/
def Probe.owner : Probe Pkg N → CU Pkg N
  | .top u => u
  | .mem x _ => x

structure Client (Pkg N : Type) where
  pkg : Pkg
  name : N
  sup : List (CU Pkg N)
  /-- `import q.C;` -/
  single : List (CU Pkg N)
  /-- `import static X.m;` -/
  sstatic : List (CU Pkg N × N)
  /-- `import q.*;` -/
  od : List Pkg
  /-- `import static W.*;` -/
  swild : List (CU Pkg N)

inductive Src (Pkg N : Type)
  | absent
  | cls (members : List N)
  | client (c : Client Pkg N)

inductive Res (Pkg N : Type)
  | ok (p : Probe Pkg N)
  | ambiguous
  | notFound
  | badImport
  deriving DecidableEq

/-- `some members` if the class exists. -/
abbrev Iface (N : Type) := Option (List N)

structure Out (Pkg N : Type) where
  iface : Iface N
  res : Res Pkg N
  /-- The classfile's constant pool, as Zinc reads it. -/
  pool : List (CU Pkg N)
  /-- From javac's attributed tree (the fix): the simple names looked up, and imported classes. -/
  names : List N
  imports : List (CU Pkg N)

abbrev T (Pkg N : Type) := Task (CU Pkg N × Q N) (fun p => Ans p.2)
abbrev Env (Pkg N : Type) := Task.Env (CU Pkg N × Q N) (fun p => Ans p.2)

def ask1 (p : Probe Pkg N) : T Pkg N Bool := .ask p.query .pure

/-- Ask every probe, return the hits. -/
def askAll : List (Probe Pkg N) → T Pkg N (List (Probe Pkg N))
  | [] => .pure []
  | p :: ps => (ask1 p).bind fun b => (askAll ps).bind fun hs => .pure (if b then p :: hs else hs)

/-- The first level with a hit decides. -/
def resolve : List (List (Probe Pkg N)) → T Pkg N (Res Pkg N)
  | [] => .pure .notFound
  | l :: ls => (askAll l).bind fun hs =>
      match hs with
      | [] => resolve ls
      | [h] => .pure (.ok h)
      | _ :: _ :: _ => .pure .ambiguous

variable (javaLang : Pkg)

def levels (c : Client Pkg N) : List (List (Probe Pkg N)) :=
  [c.sup.map (.mem · c.name),
   (c.single.filter (·.2 = c.name)).map .top ++ (c.sstatic.filter (·.2 = c.name)).map (fun x => .mem x.1 c.name),
   [.top (c.pkg, c.name)],
   c.od.map (fun q => .top (q, c.name)) ++ c.swild.map (.mem · c.name) ++ [.top (javaLang, c.name)]]

def importChecks (c : Client Pkg N) : List (Probe Pkg N) := c.single.map .top

def poolOf (c : Client Pkg N) : Res Pkg N → List (CU Pkg N)
  | .ok p => c.sup ++ [p.owner]
  | _ => c.sup

def clientOut (c : Client Pkg N) (r : Res Pkg N) : Out Pkg N :=
  ⟨some [], r, poolOf c r, [c.name], c.single ++ c.sstatic.map (·.1) ++ c.swild⟩

def unit : Src Pkg N → T Pkg N (Out Pkg N)
  | .absent => .pure ⟨none, .notFound, [], [], []⟩
  | .cls ms => .pure ⟨some ms, .notFound, [], [], []⟩
  | .client c => (askAll (importChecks c)).bind fun hs =>
      if hs.length < c.single.length then .pure (clientOut c .badImport)
      else (resolve (levels javaLang c)).bind fun r => .pure (clientOut c r)

def ifaceOf : Src Pkg N → Iface N
  | .absent => none
  | .cls ms => some ms
  | .client _ => some []

/-! ## The trace stays among the probes -/

theorem trace_ask1 (e : Env Pkg N) (p : Probe Pkg N) : (ask1 p).trace e = [p.query] := rfl

theorem mem_trace_askAll (e : Env Pkg N) :
    ∀ (ps : List (Probe Pkg N)), ∀ q ∈ (askAll ps).trace e, ∃ p ∈ ps, q = p.query
  | [], q, h => by simp [askAll] at h
  | p :: ps, q, h => by
    simp only [askAll, Task.trace_bind, trace_ask1, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, Task.trace_pure, List.append_nil] at h
    rcases h with h | h
    · exact ⟨p, by simp, h⟩
    · obtain ⟨p', hp', hq⟩ := mem_trace_askAll e ps q h
      exact ⟨p', by simp [hp'], hq⟩

theorem mem_trace_resolve (e : Env Pkg N) :
    ∀ (ls : List (List (Probe Pkg N))), ∀ q ∈ (resolve ls).trace e, ∃ l ∈ ls, ∃ p ∈ l, q = p.query
  | [], q, h => by simp [resolve] at h
  | l :: ls, q, h => by
    simp only [resolve, Task.trace_bind, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨p, hp, hq⟩ := mem_trace_askAll e l q h
      exact ⟨l, by simp, p, hp, hq⟩
    · revert h
      split
      · intro h
        obtain ⟨l', hl', p, hp, hq⟩ := mem_trace_resolve e ls q h
        exact ⟨l', by simp [hl'], p, hp, hq⟩
      · simp
      · simp

/-- Every query a client's compilation asks is one of its import checks or level probes. -/
theorem mem_trace_client (e : Env Pkg N) (c : Client Pkg N) :
    ∀ q ∈ (unit javaLang (.client c)).trace e,
      (∃ p ∈ importChecks c, q = p.query) ∨ ∃ l ∈ levels javaLang c, ∃ p ∈ l, q = p.query := by
  intro q h
  simp only [unit, Task.trace_bind, List.mem_append] at h
  rcases h with h | h
  · exact .inl (mem_trace_askAll e _ q h)
  · revert h
    split
    · simp
    · intro h
      simp only [Task.trace_bind, List.mem_append, Task.trace_pure, List.not_mem_nil, or_false] at h
      exact .inr (mem_trace_resolve e _ q h)

theorem iface_unit (e : Env Pkg N) (s : Src Pkg N) : ((unit javaLang s).run e).iface = ifaceOf s := by
  cases s with
  | absent => rfl
  | cls ms => rfl
  | client c =>
    simp only [unit, Task.run_bind]
    split
    · rfl
    · simp only [Task.run_bind, Task.run_pure]; rfl

/-- The output of a client compile: the client's facts and its resolution. -/
theorem run_client (e : Env Pkg N) (c : Client Pkg N) :
    ∃ r, (unit javaLang (.client c)).run e = clientOut c r := by
  simp only [unit, Task.run_bind]
  split
  · exact ⟨_, rfl⟩
  · simp only [Task.run_bind, Task.run_pure]; exact ⟨_, rfl⟩

/-! ## JLS 6.4.1: the first level with a hit decides -/

/-- The answers of a level's probes. -/
def hits (e : Env Pkg N) (l : List (Probe Pkg N)) : List (Probe Pkg N) := l.filter fun p => e p.query

theorem run_askAll (e : Env Pkg N) : ∀ l : List (Probe Pkg N), (askAll l).run e = hits e l
  | [] => rfl
  | p :: ps => by
    simp only [askAll, Task.run_bind, Task.run_pure, hits, List.filter_cons, run_askAll e ps]
    rfl

theorem resolve_cons (e : Env Pkg N) (l : List (Probe Pkg N)) (ls : List (List (Probe Pkg N))) :
    (resolve (l :: ls)).run e =
      match hits e l with
      | [] => (resolve ls).run e
      | [h] => .ok h
      | _ :: _ :: _ => .ambiguous := by
  simp only [resolve, Task.run_bind, run_askAll]
  split <;> rfl

/-- A level with exactly one hit shadows every later level: an inherited member type over the
imports, a single import over the package, the package over the on-demand imports. -/
theorem shadows (e : Env Pkg N) (l : List (Probe Pkg N)) (ls : List (List (Probe Pkg N))) (h : Probe Pkg N)
    (hl : hits e l = [h]) : (resolve (l :: ls)).run e = .ok h := by
  rw [resolve_cons, hl]

/-- Two hits on one level are an error, whatever later levels hold: two on-demand imports that
supply the name (`import q.*` and `import static W.*`, or either and `java.lang`). -/
theorem ambiguous (e : Env Pkg N) (l : List (Probe Pkg N)) (ls : List (List (Probe Pkg N)))
    (h₁ h₂ : Probe Pkg N) (t : List (Probe Pkg N)) (hl : hits e l = h₁ :: h₂ :: t) :
    (resolve (l :: ls)).run e = .ambiguous := by
  rw [resolve_cons, hl]

/-- A level with no hit defers to the next. -/
theorem defers (e : Env Pkg N) (l : List (Probe Pkg N)) (ls : List (List (Probe Pkg N)))
    (hl : hits e l = []) : (resolve (l :: ls)).run e = (resolve ls).run e := by
  rw [resolve_cons, hl]

/-! ## Keys -/

inductive K | cls | present
  deriving DecidableEq

def coversB : Q N → K → Bool
  | _, .cls => true
  | .present, .present => true
  | .member _, .present => false

def covers (q : Q N) (k : K) : Prop := coversB q k = true

def π : Iface N → K → Iface N
  | i, .cls => i
  | i, .present => i.map fun _ => []

def answer (i : Iface N) : (q : Q N) → Ans q
  | .present => i.isSome
  | .member m => (i.getD []).contains m

/-- The bridge designs. `cheap` is `today`: #34 reads used names, and a Java class has none. -/
inductive Design | today | names | fix
  deriving DecidableEq

variable [Fintype Pkg] [Fintype N]

/-- Existence keys on every unit with a used simple name: #34's rule as keys. -/
def nameKeys (o : Out Pkg N) : Finset (CU Pkg N × K) :=
  (Finset.univ.filter fun u : CU Pkg N => u.2 ∈ o.names).image (·, K.present)

def keysOf : Design → Out Pkg N → Finset (CU Pkg N × K)
  | .today, o => (o.pool.map (·, K.cls)).toFinset
  | .names, o => (o.pool.map (·, K.cls)).toFinset ∪ nameKeys o
  | .fix, o => (o.pool.map (·, K.cls)).toFinset ∪ nameKeys o ∪ (o.imports.map (·, K.cls)).toFinset

def group (G : Finset (CU Pkg N)) (src : CU Pkg N → Src Pkg N) (e : Env Pkg N) : CU Pkg N → Out Pkg N :=
  fun u => (unit javaLang (src u)).run fun p => if p.1 ∈ G then answer (ifaceOf (src p.1)) p.2 else e p

def compiler (d : Design) : TCompiler (CU Pkg N) (Src Pkg N) (Out Pkg N) (Iface N) K (Iface N) (Q N) Ans where
  unit := unit javaLang
  group := group javaLang
  iface := Out.iface
  answer := answer
  π := π
  keysOf := keysOf d
  covers := covers

omit [Fintype Pkg] [Fintype N] in
theorem iface_group (G : Finset (CU Pkg N)) (src : CU Pkg N → Src Pkg N) (e : Env Pkg N) (u : CU Pkg N) :
    (group javaLang G src e u).iface = ifaceOf (src u) := iface_unit javaLang _ _

theorem obligations_comp (d : Design) :
    ∀ (G : Finset (CU Pkg N)) (src : CU Pkg N → Src Pkg N) (e : Env Pkg N), ∀ u ∈ G,
      (compiler javaLang d).group G src e u =
        ((compiler javaLang d).unit (src u)).run
          ((compiler javaLang d).override e G ((compiler javaLang d).iface ∘ (compiler javaLang d).group G src e)) := by
  intro G src e u _
  show (unit javaLang (src u)).run _ = (unit javaLang (src u)).run _
  congr 1
  funext p
  simp only [TCompiler.override, compiler, Function.comp, iface_group]

theorem obligations_abstraction (d : Design) :
    ∀ (i i' : Iface N) (k : K), (compiler javaLang d).π i k = (compiler javaLang d).π i' k →
      ∀ q, (compiler javaLang d).covers q k → (compiler javaLang d).answer i q = (compiler javaLang d).answer i' q := by
  intro i i' k h q hq
  simp only [compiler] at h hq ⊢
  cases k with
  | cls => simp only [π] at h; rw [h]
  | present =>
    cases q with
    | member m => simp [covers, coversB] at hq
    | present =>
      simp only [π] at h
      cases i <;> cases i' <;> simp_all [answer]

theorem mem_pool (c : Client Pkg N) (r : Res Pkg N) (u : CU Pkg N) (hu : u ∈ c.sup) :
    u ∈ (clientOut c r).pool := by
  cases r <;> simp [clientOut, poolOf, hu]

theorem key_pool (d : Design) (c : Client Pkg N) (r : Res Pkg N) (u : CU Pkg N) (hu : u ∈ c.sup) :
    (u, K.cls) ∈ keysOf d (clientOut c r) := by
  have := mem_pool c r u hu
  cases d <;> simp [keysOf, this]

theorem key_name (c : Client Pkg N) (r : Res Pkg N) (u : CU Pkg N) (hu : u.2 = c.name) :
    (u, K.present) ∈ keysOf .fix (clientOut c r) := by
  simp [keysOf, nameKeys, clientOut, hu]

theorem key_import (c : Client Pkg N) (r : Res Pkg N) (u : CU Pkg N)
    (hu : u ∈ c.single ∨ u ∈ c.sstatic.map (·.1) ∨ u ∈ c.swild) :
    (u, K.cls) ∈ keysOf .fix (clientOut c r) := by
  simp only [keysOf, Finset.mem_union, List.mem_toFinset, List.mem_map, Prod.mk.injEq, and_true,
    exists_eq_right]
  right
  simp only [clientOut, List.mem_append]
  rcases hu with h | h | h <;> simp_all

/-- **Coverage of the fix**: every probe of the client's lookup has a key. -/
theorem obligations_coverage :
    ∀ (s : Src Pkg N) (e : Env Pkg N), ∀ q ∈ (unit javaLang s).trace e,
      ∃ k ∈ keysOf .fix ((unit javaLang s).run e), q.1 = k.1 ∧ covers q.2 k.2 := by
  intro s e q hq
  cases s with
  | absent => simp [unit] at hq
  | cls ms => simp [unit] at hq
  | client c =>
    obtain ⟨r, hr⟩ := run_client javaLang e c
    rw [hr]
    have cls : ∀ u, (u, K.cls) ∈ keysOf .fix (clientOut c r) → q.1 = u → ∃ k ∈ keysOf .fix (clientOut c r), q.1 = k.1 ∧ covers q.2 k.2 :=
      fun u hk hq1 => ⟨(u, .cls), hk, hq1, rfl⟩
    rcases mem_trace_client javaLang e c q hq with ⟨p, hp, rfl⟩ | ⟨l, hl, p, hp, rfl⟩
    · simp only [importChecks, List.mem_map] at hp
      obtain ⟨u, hu, rfl⟩ := hp
      exact cls u (key_import c r u (.inl hu)) rfl
    · simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · simp only [List.mem_map] at hp
        obtain ⟨u, hu, rfl⟩ := hp
        exact cls u (key_pool .fix c r u hu) rfl
      · simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
        rcases hp with ⟨u, ⟨hu, _⟩, rfl⟩ | ⟨x, ⟨hx, _⟩, rfl⟩
        · exact cls u (key_import c r u (.inl hu)) rfl
        · exact cls x.1 (key_import c r x.1 (.inr (.inl (List.mem_map_of_mem hx)))) rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        exact ⟨((c.pkg, c.name), .present), key_name c r _ rfl, rfl, rfl⟩
      · simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with (⟨q', _, rfl⟩ | ⟨w, hw, rfl⟩) | rfl
        · exact ⟨((q', c.name), .present), key_name c r _ rfl, rfl, rfl⟩
        · exact cls w (key_import c r w (.inr (.inr hw))) rfl
        · exact ⟨((javaLang, c.name), .present), key_name c r _ rfl, rfl, rfl⟩

/-- **The fix meets the obligations.** -/
theorem obligations_fix : (compiler javaLang .fix (Pkg := Pkg) (N := N)).Obligations where
  comp := obligations_comp javaLang .fix
  coverage := obligations_coverage javaLang
  abstraction := obligations_abstraction javaLang .fix

/-- **T3a for the fix.** When Zinc's loop stops, every class is up to date: its output is its
compilation against the final state, and its keys cover that compilation's queries. Starting from
an up-to-date state and an edit of the sources `D`, the loop reaches the clean build's fixed point
whatever the program, the edit or the (sound) invalidation policy. -/
theorem fix_sound (S : Finset (CU Pkg N)) (src : CU Pkg N → Src Pkg N)
    (P : Policy (CU Pkg N) (Out Pkg N) K) (hP : P.Sound S) (fuel n : ℕ) (R : Finset (CU Pkg N))
    (s : State (CU Pkg N) (Out Pkg N) K) (D : Finset (CU Pkg N)) (hD : D ⊆ R)
    (hInv : (compiler javaLang .fix).Inv S src s D) (s' : State (CU Pkg N) (Out Pkg N) K)
    (h : (compiler javaLang .fix).zinc S src P fuel n R s = some s') :
    (compiler javaLang .fix).Inv S src s' ∅ :=
  (compiler javaLang .fix).zinc_sound (obligations_fix javaLang) S src P hP fuel n R s D hD hInv s' h

theorem key_name_names (c : Client Pkg N) (r : Res Pkg N) (u : CU Pkg N) (hu : u.2 = c.name) :
    (u, K.present) ∈ keysOf .names (clientOut c r) := by
  simp [keysOf, nameKeys, clientOut, hu]

/-- #34 reaching Java clients (`names`) covers every lookup of a client without imports beyond
on-demand package imports: J1 is fixed by used names alone. -/
theorem names_coverage_no_imports (e : Env Pkg N) (c : Client Pkg N)
    (h1 : c.single = []) (h2 : c.sstatic = []) (h3 : c.swild = []) :
    ∀ q ∈ (unit javaLang (.client c)).trace e,
      ∃ k ∈ keysOf .names ((unit javaLang (.client c)).run e), q.1 = k.1 ∧ covers q.2 k.2 := by
  intro q hq
  obtain ⟨r, hr⟩ := run_client javaLang e c
  rw [hr]
  rcases mem_trace_client javaLang e c q hq with ⟨p, hp, rfl⟩ | ⟨l, hl, p, hp, rfl⟩
  · simp [importChecks, h1] at hp
  · simp only [levels, h1, h2, h3, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · simp only [List.mem_map] at hp
      obtain ⟨u, hu, rfl⟩ := hp
      exact ⟨(u, .cls), key_pool .names c r u hu, rfl, rfl⟩
    · simp at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact ⟨((c.pkg, c.name), .present), key_name_names c r _ rfl, rfl, rfl⟩
    · have : (∃ q' ∈ c.od, p = .top (q', c.name)) ∨ p = .top (javaLang, c.name) := by
        simp only [List.map_nil, List.append_nil, List.mem_append, List.mem_map, List.mem_cons,
          List.not_mem_nil, or_false] at hp
        rcases hp with ⟨q', hq', rfl⟩ | rfl
        · exact .inl ⟨q', hq', rfl⟩
        · exact .inr rfl
      rcases this with ⟨q', _, rfl⟩ | rfl
      · exact ⟨((q', c.name), .present), key_name_names c r _ rfl, rfl, rfl⟩
      · exact ⟨((javaLang, c.name), .present), key_name_names c r _ rfl, rfl, rfl⟩

/-! ## Today's keys fail coverage: one witness per family -/

/-- A traced query with no covering key refutes the obligations. -/
theorem not_obligations_of (d : Design) (s : Src Pkg N) (e : Env Pkg N) (q : CU Pkg N × Q N)
    (hq : q ∈ (unit javaLang s).trace e)
    (hnot : ∀ k ∈ keysOf d ((unit javaLang s).run e), ¬ (q.1 = k.1 ∧ coversB q.2 k.2 = true)) :
    ¬ (compiler javaLang d (Pkg := Pkg) (N := N)).Obligations := by
  intro ob
  obtain ⟨k, hk, h⟩ := ob.coverage s e q hq
  exact hnot k hk h

end Zinc.JavaSpec

/-! The witnesses, in packages `a.b` (0), `a.q` (1) and `java.lang` (2), with the names `Foo` (0)
and `Bar` (1). -/

namespace Zinc.JavaSpec.Witness

open Zinc.JavaSpec

abbrev P := Fin 3
abbrev Nm := Fin 2

def client (pkg : P) : Client P Nm := ⟨pkg, 0, [], [], [], [], []⟩

/-- The oracle where exactly the listed queries answer yes. -/
def env (yes : List (CU P Nm × Q Nm)) : Env P Nm := fun q => decide (q ∈ yes)

/-- **J1, a class added to the client's package.** `Foo` resolves through `import a.q.*`; the miss
on `a.b.Foo` is asked and leaves no key: the constant pool names `a.q.Foo` only, and a Java class
records no used names (so #34's key is absent too). -/
theorem j1_today : ¬ (compiler (2 : P) .today (Pkg := P) (N := Nm)).Obligations :=
  not_obligations_of 2 .today (.client { client 0 with od := [1] }) (env [((1, 0), .present)])
    ((0, 0), .present) (by decide) (by decide)

/-- With #34 reaching Java clients (`names`) J1 is covered, but a member type behind a static
import is not: **J2**, `import static a.q.Bar.Foo` whose `Bar` had only a method `Foo`, the name
resolved in the package. -/
theorem j2_names : ¬ (compiler (2 : P) .names (Pkg := P) (N := Nm)).Obligations :=
  not_obligations_of 2 .names (.client { client 0 with sstatic := [((1, 1), 0)] })
    (env [((0, 0), .present)]) ((1, 1), .member 0) (by decide) (by decide)

/-- **J3, a second on-demand binding.** `import a.q.*` and `import static a.q.Bar.*`; the lookup asks
`Bar` for a member `Foo` (all on-demand imports are asked, to detect an ambiguity), with no key. -/
theorem j3_names : ¬ (compiler (2 : P) .names (Pkg := P) (N := Nm)).Obligations :=
  not_obligations_of 2 .names (.client { client 0 with od := [1], swild := [(1, 1)] })
    (env [((1, 0), .present)]) ((1, 1), .member 0) (by decide) (by decide)

/-- **J4, an unused single-type import.** `import a.q.Bar;` is checked to exist, whether or not
`Bar` is used; neither the constant pool nor the used names record it, so deleting `a.q.Bar` leaves
the client compiled where a clean build fails. -/
theorem j4_names : ¬ (compiler (2 : P) .names (Pkg := P) (N := Nm)).Obligations :=
  not_obligations_of 2 .names (.client { client 0 with single := [(1, 1)] })
    (env [((1, 1), .present), ((0, 0), .present)]) ((1, 1), .present) (by decide) (by decide)

/-- The keys of `names` include today's, so every witness against `names` refutes `today` too. -/
theorem j2_today : ¬ (compiler (2 : P) .today (Pkg := P) (N := Nm)).Obligations :=
  not_obligations_of 2 .today (.client { client 0 with sstatic := [((1, 1), 0)] })
    (env [((0, 0), .present)]) ((1, 1), .member 0) (by decide) (by decide)

end Zinc.JavaSpec.Witness
