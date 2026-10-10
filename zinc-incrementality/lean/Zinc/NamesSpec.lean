import Zinc.JavaSpec

/-!
# Scala name resolution and implicit search as a specification

A `TCompiler` instance (`Tree.lean`) for a Scala client resolving one simple name `n`
(`Names.lean`) or summoning one type (`Givens.lean`). The lookup is `JavaSpec`'s: probes grouped
in levels, every probe of a level asked, the first level with a hit decides. Packages `Pkg` and
names `N` are arbitrary types, and the oracle is arbitrary, so every result here holds for any
program, with any number of bindings in the searched scopes, not only the enumerated bases.

**Units** are top-level classes, named by package and simple name (`Pkg × N`). A package object
is the unit `(p, pk)`, for a distinguished name `pk` (`package`); a Scala 3 file's top-level
definitions are the unit `(p, F$package)`. **Queries** to a unit, as in `JavaSpec`: does the class
exist (`present`), does it have the member `m` (`member m`, declared or inherited).

**The lookup** (`levels`), innermost first:

1. the block's wildcard imports and the parents (inherited members);
2. the explicit imports `import X.n` (also checked to exist before resolving);
3. the file's wildcard imports: objects (`import W._`) and packages (`import q._`: the class
   `q.n` and the package object's member);
4. each enclosing package, innermost first: its package object's member and its class `p.n`.

The levels follow Scala 3's nesting. Scala 2 orders a package's package object before its classes
and lets imports beat package members of other files; those rules decide *which* hit wins, which
`Names.lean` models and checks against the compiler, not *what* the lookup reads, which is all
coverage depends on. Implicit search (`glevels`) asks every scope for an instance of `T` (a member
named `imp`): the block import, the parents, the file's wildcard imports with the client's own
package, each enclosing package (its package object and every `$package` file class, `files`), and
last `T`'s companion.

**Keys.** Today's bridge records a member-ref edge to the owner of the symbol the reference resolved
to and the used name; edges to import qualifiers that are objects (a package records nothing),
charged with the import's selector name to one class of the file (`first`); inheritance edges, on
which any API change invalidates. A changed implicit invalidates every member-ref dependent, used
names or not. As keys: `has n` on the resolved owner and on import qualifiers when the charged
class uses `n`, `api` on parents. The fixes are keys too:

* `searched`: a key per probe, hit or miss (Kotlin's `LookupTracker`);
* #34 (`cheap`): `present` on every top-level class named `n`, in every package (`global`, what #34
  does) or only in the searched packages (`narrowed`);
* F2: `has n` on package objects, with the same two reaches;
* F3: the wildcard import's qualifier keyed with every class's used names in the file;
* G: `has imp` on package objects and `$package` classes, with the same two reaches.

`narrowed` reaches the enclosing packages, and the wildcard-imported packages only when the bridge
records `import q._` (`imports`).

**Results** (no `native_decide`): today's keys fail coverage, one witness per family (F1, F2, F3,
G1, G2); the narrowed rules without recorded package imports fail it too (a wildcard-imported
package); every set of rules that reaches all searched scopes meets the obligations and inherits
T3a (`obligations_rules`, `rules_sound`), as does `searched`. #24's declarations-only `π` fails
abstraction (an inherited member); composed from the ancestors it is `full`. Precision: the
narrowed rules and `searched` record only keys a probe of the lookup justifies (`tight`); the
global ones record keys on every package.

Simplifications: one name and one use per client; a class's inherited members are part of its
source (the inheritance edge itself is `Hier.lean`'s); the result (which hit wins, ambiguities)
follows the levels and is refined in `Names.lean`.
-/

set_option linter.unusedSectionVars false

namespace Zinc.NamesSpec

open Zinc.JavaSpec (CU Q Ans Probe Res T Env askAll resolve run_askAll mem_trace_askAll
  mem_trace_resolve)
open Compiler (State Policy)

variable {Pkg N : Type} [DecidableEq Pkg] [DecidableEq N]

structure Client (Pkg N : Type) where
  /-- The enclosing packages, innermost first: `package a; package b` searches `a.b` and `a`,
  `package a.b` only `a.b`. -/
  pkgs : List Pkg
  name : N
  /-- `{ import V._; n }` -/
  blk : List (CU Pkg N)
  /-- `extends P` -/
  sup : List (CU Pkg N)
  /-- `import X.n` -/
  expl : List (CU Pkg N)
  /-- `import W._` -/
  wild : List (CU Pkg N)
  /-- `import q._` -/
  wpkg : List Pkg
  /-- Another class of the file is charged with the top-level imports. -/
  first : Bool
  /-- Implicit search: the companion of the summoned type. -/
  comp : List (CU Pkg N) := []

inductive Src (Pkg N : Type)
  | absent
  /-- A class with its declared members and all its members (declared and inherited). -/
  | cls (decls all : List N)
  | client (c : Client Pkg N)

/-- `some (declared, all)` if the class exists. -/
abbrev Iface (N : Type) := Option (List N × List N)

structure Out (Pkg N : Type) where
  iface : Iface N
  client : Option (Client Pkg N)
  res : Res Pkg N

def importChecks (c : Client Pkg N) : List (Probe Pkg N) := c.expl.map (.mem · c.name)

/-- The levels of the name lookup. -/
def levels (pk : N) (c : Client Pkg N) : List (List (Probe Pkg N)) :=
  [c.blk.map (.mem · c.name) ++ c.sup.map (.mem · c.name),
   c.expl.map (.mem · c.name),
   c.wild.map (.mem · c.name) ++ c.wpkg.map (fun q => .top (q, c.name)) ++
     c.wpkg.map (fun q => .mem (q, pk) c.name)] ++
  c.pkgs.map fun p => [.mem (p, pk) c.name, .top (p, c.name)]

/-- The scopes of a package for implicit search: its package object and its `$package` classes. -/
def pkgProbes (pk : N) (files : List N) (imp : N) (p : Pkg) : List (Probe Pkg N) :=
  .mem (p, pk) imp :: files.map fun x => .mem (p, x) imp

/-- The levels of implicit search (Scala 3): the client's own package shares a level with the
file's imports. -/
def glevels (pk : N) (files : List N) (c : Client Pkg N) : List (List (Probe Pkg N)) :=
  [c.blk.map (.mem · c.name), c.sup.map (.mem · c.name),
   c.wild.map (.mem · c.name) ++ (c.wpkg ++ c.pkgs.take 1).flatMap (pkgProbes pk files c.name)] ++
  (c.pkgs.drop 1).map (pkgProbes pk files c.name) ++ [c.comp.map (.mem · c.name)]

/-- Every probe a lookup can ask. -/
def probes (lv : Client Pkg N → List (List (Probe Pkg N))) (c : Client Pkg N) : List (Probe Pkg N) :=
  importChecks c ++ (lv c).flatten

def unit (lv : Client Pkg N → List (List (Probe Pkg N))) : Src Pkg N → T Pkg N (Out Pkg N)
  | .absent => .pure ⟨none, none, .notFound⟩
  | .cls d a => .pure ⟨some (d, a), none, .notFound⟩
  | .client c => (askAll (importChecks c)).bind fun hs =>
      if hs.length < c.expl.length then .pure ⟨some ([], []), some c, .badImport⟩
      else (resolve (lv c)).bind fun r => .pure ⟨some ([], []), some c, r⟩

def ifaceOf : Src Pkg N → Iface N
  | .absent => none
  | .cls d a => some (d, a)
  | .client _ => some ([], [])

theorem iface_unit (lv : Client Pkg N → List (List (Probe Pkg N))) (e : Env Pkg N) (s : Src Pkg N) :
    ((unit lv s).run e).iface = ifaceOf s := by
  cases s with
  | absent => rfl
  | cls d a => rfl
  | client c =>
    simp only [unit, Task.run_bind]
    split
    · rfl
    · simp only [Task.run_bind, Task.run_pure]; rfl

/-- The output of a client compile. -/
theorem run_client (lv : Client Pkg N → List (List (Probe Pkg N))) (e : Env Pkg N) (c : Client Pkg N) :
    ∃ r, (unit lv (.client c)).run e = ⟨some ([], []), some c, r⟩ := by
  simp only [unit, Task.run_bind]
  split
  · exact ⟨_, rfl⟩
  · simp only [Task.run_bind, Task.run_pure]; exact ⟨_, rfl⟩

theorem run_cls (lv : Client Pkg N → List (List (Probe Pkg N))) (e : Env Pkg N) (s : Src Pkg N)
    (h : ∀ c, s ≠ .client c) : ((unit lv s).run e).client = none := by
  cases s with
  | absent => rfl
  | cls d a => rfl
  | client c => exact absurd rfl (h c)

/-- Every query a client's compilation asks is one of its probes. -/
theorem mem_trace_client (lv : Client Pkg N → List (List (Probe Pkg N))) (e : Env Pkg N)
    (c : Client Pkg N) : ∀ q ∈ (unit lv (.client c)).trace e, ∃ p ∈ probes lv c, q = p.query := by
  intro q h
  simp only [unit, Task.trace_bind, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨p, hp, rfl⟩ := mem_trace_askAll e _ q h
    exact ⟨p, by simp [probes, hp], rfl⟩
  · revert h
    split
    · simp
    · intro h
      simp only [Task.trace_bind, List.mem_append, Task.trace_pure, List.not_mem_nil, or_false] at h
      obtain ⟨l, hl, p, hp, rfl⟩ := mem_trace_resolve e _ q h
      exact ⟨p, by simp only [probes, List.mem_append, List.mem_flatten]; exact .inr ⟨l, hl, hp⟩, rfl⟩

theorem trace_cls (lv : Client Pkg N → List (List (Probe Pkg N))) (e : Env Pkg N) (s : Src Pkg N)
    (h : ∀ c, s ≠ .client c) : (unit lv s).trace e = [] := by
  cases s with
  | absent => rfl
  | cls d a => rfl
  | client c => exact absurd rfl (h c)

/-! ## Keys -/

inductive K (N : Type) | api | present | has (m : N)
  deriving DecidableEq

def coversB : Q N → K N → Bool
  | _, .api => true
  | .present, .present => true
  | .member m, .has m' => decide (m = m')
  | _, _ => false

def covers (q : Q N) (k : K N) : Prop := coversB q k = true

def answer (i : Iface N) : (q : Q N) → Ans q
  | .present => i.isSome
  | .member m => ((i.map (·.2)).getD []).contains m

/-- What the API hash of a member sees: all members (develop; #24 with names composed from the
ancestors), or the declared ones only (#24 without composition). -/
inductive Api | full | decls
  deriving DecidableEq

def hasMember (a : Api) (i : Iface N) (m : N) : Bool :=
  match a with
  | .full => ((i.map (·.2)).getD []).contains m
  | .decls => ((i.map (·.1)).getD []).contains m

/-- `π`, with an interface as the hash: the whole interface for `api`, existence for `present`,
whether the member is there for `has m`. -/
def π (a : Api) : Iface N → K N → Iface N
  | i, .api => i
  | i, .present => i.map fun _ => ([], [])
  | i, .has m => if hasMember a i m then some ([], []) else none

/-- How far a rule reaches: nowhere, the packages the lookup searches, or every package. -/
inductive Reach | off | narrowed | global
  deriving DecidableEq

structure Design where
  searched : Bool := false
  cheap : Reach := .off
  f2 : Reach := .off
  f3 : Bool := false
  g : Reach := .off
  /-- The bridge records `import q._` of a package. -/
  imports : Bool := false

/-- The key of a probe. -/
def probeKey : Probe Pkg N → CU Pkg N × K N
  | .top u => (u, .present)
  | .mem x m => (x, .has m)

theorem probeKey_covers (p : Probe Pkg N) : p.query.1 = (probeKey p).1 ∧ covers p.query.2 (probeKey p).2 := by
  cases p <;> simp [Probe.query, probeKey, covers, coversB]

variable [Fintype Pkg]

def reach (d : Design) (r : Reach) (c : Client Pkg N) : Finset Pkg :=
  match r with
  | .off => ∅
  | .narrowed => (c.pkgs ++ if d.imports then c.wpkg else []).toFinset
  | .global => Finset.univ

/-- Today's keys for a name: the qualifiers of the block import (charged to the client) and of
the explicit import (with its selector's name), the parents, the wildcard import's qualifier when
the class charged with it uses the name (or with F3), and the resolved owner. -/
def nameKeys (d : Design) (c : Client Pkg N) (r : Res Pkg N) : List (CU Pkg N × K N) :=
  c.blk.map (·, .has c.name) ++ c.sup.map (·, .api) ++ c.expl.map (·, .has c.name) ++
  (if d.f3 || !c.first || !c.expl.isEmpty then c.wild.map (·, .has c.name) else []) ++
  (match r with | .ok p => [probeKey p] | _ => [])

/-- Today's keys for implicit search: an implicit change invalidates every member-ref dependent, so
every import qualifier counts, whichever class is charged; the companion, which the client names. -/
def givenKeys (c : Client Pkg N) (r : Res Pkg N) : List (CU Pkg N × K N) :=
  c.blk.map (·, .has c.name) ++ c.sup.map (·, .api) ++ c.expl.map (·, .has c.name) ++
  c.wild.map (·, .has c.name) ++
  c.comp.map (·, .has c.name) ++ (match r with | .ok p => [probeKey p] | _ => [])

variable (pk : N) (files : List N)

def keysOf (lv : Client Pkg N → List (List (Probe Pkg N))) (gv : Bool) (d : Design) (o : Out Pkg N) :
    Finset (CU Pkg N × K N) :=
  match o.client with
  | none => ∅
  | some c =>
    ((if gv then givenKeys c o.res else nameKeys d c o.res).toFinset ∪
      (reach d d.cheap c).image (fun p => ((p, c.name), K.present)) ∪
      (reach d d.f2 c).image (fun p => ((p, pk), K.has c.name)) ∪
      (reach d d.g c).biUnion (fun p => ((pkgProbes pk files c.name p).map probeKey).toFinset)) ∪
    (if d.searched then ((probes lv c).map probeKey).toFinset else ∅)

def group (lv : Client Pkg N → List (List (Probe Pkg N))) (G : Finset (CU Pkg N))
    (src : CU Pkg N → Src Pkg N) (e : Env Pkg N) : CU Pkg N → Out Pkg N :=
  fun u => (unit lv (src u)).run fun p => if p.1 ∈ G then answer (ifaceOf (src p.1)) p.2 else e p

def mk (lv : Client Pkg N → List (List (Probe Pkg N))) (gv : Bool) (a : Api) (d : Design) :
    TCompiler (CU Pkg N) (Src Pkg N) (Out Pkg N) (Iface N) (K N) (Iface N) (Q N) Ans where
  unit := unit lv
  group := group lv
  iface := Out.iface
  answer := answer
  π := π a
  keysOf := keysOf pk files lv gv d
  covers := covers

/-- Name resolution under a bridge design. -/
def names (a : Api) (d : Design) :
    TCompiler (CU Pkg N) (Src Pkg N) (Out Pkg N) (Iface N) (K N) (Iface N) (Q N) Ans :=
  mk pk files (levels pk) false a d

/-- Implicit search under a bridge design; the client's `name` is the instance's (`imp`). -/
def givens (a : Api) (d : Design) :
    TCompiler (CU Pkg N) (Src Pkg N) (Out Pkg N) (Iface N) (K N) (Iface N) (Q N) Ans :=
  mk pk files (glevels pk files) true a d

/-! ## Compositionality and abstraction -/

theorem obligations_comp (lv : Client Pkg N → List (List (Probe Pkg N))) (gv : Bool) (a : Api)
    (d : Design) : ∀ (G : Finset (CU Pkg N)) (src : CU Pkg N → Src Pkg N) (e : Env Pkg N), ∀ u ∈ G,
      (mk pk files lv gv a d).group G src e u =
        ((mk pk files lv gv a d).unit (src u)).run
          ((mk pk files lv gv a d).override e G ((mk pk files lv gv a d).iface ∘ (mk pk files lv gv a d).group G src e)) := by
  intro G src e u _
  show (unit lv (src u)).run _ = (unit lv (src u)).run _
  congr 1
  funext p
  simp only [TCompiler.override, mk, Function.comp, group, iface_unit]

theorem obligations_abstraction (lv : Client Pkg N → List (List (Probe Pkg N))) (gv : Bool)
    (d : Design) : ∀ (i i' : Iface N) (k : K N), (mk pk files lv gv .full d).π i k = (mk pk files lv gv .full d).π i' k →
      ∀ q, (mk pk files lv gv .full d).covers q k → (mk pk files lv gv .full d).answer i q = (mk pk files lv gv .full d).answer i' q := by
  intro i i' k h q hq
  simp only [mk] at h hq ⊢
  cases k with
  | api => simp only [π] at h; rw [h]
  | present =>
    cases q with
    | member m => simp [covers, coversB] at hq
    | present => simp only [π] at h; cases i <;> cases i' <;> simp_all [answer]
  | has m =>
    cases q with
    | present => simp [covers, coversB] at hq
    | member m' =>
      simp only [covers, coversB, decide_eq_true_eq] at hq
      subst hq
      simp only [π, hasMember] at h
      simp only [answer]
      by_cases h1 : ((i.map (·.2)).getD []).contains m' = true <;>
        by_cases h2 : ((i'.map (·.2)).getD []).contains m' = true <;> simp_all

/-- **#24 without composition fails abstraction**: two interfaces with the same declarations and
different inherited members hash alike on `has m`, and answer `member m` differently. With names
composed from the ancestors (`MerkleHashes.composed`) the hash sees all members: `Api.full`. -/
theorem decls_violates_abstraction (lv : Client Pkg N → List (List (Probe Pkg N))) (gv : Bool)
    (d : Design) (m : N) : ¬ (mk pk files lv gv .decls d).Obligations := by
  intro ob
  have := ob.abstraction (some ([], [m])) (some ([], [])) (.has m) (by simp [mk, π, hasMember])
    (.member m) (by simp [mk, covers, coversB])
  simp [mk, answer] at this

/-! ## Coverage -/

/-- A design covers a client's lookup when every probe has a key among its keys. -/
theorem coverage_of (lv : Client Pkg N → List (List (Probe Pkg N))) (gv : Bool) (d : Design)
    (h : ∀ c r, ∀ p ∈ probes lv c, ∃ k ∈ keysOf pk files lv gv d ⟨some ([], []), some c, r⟩,
      p.query.1 = k.1 ∧ covers p.query.2 k.2) :
    ∀ (s : Src Pkg N) (e : Env Pkg N), ∀ q ∈ (unit lv s).trace e,
      ∃ k ∈ keysOf pk files lv gv d ((unit lv s).run e), q.1 = k.1 ∧ covers q.2 k.2 := by
  intro s e q hq
  cases s with
  | absent => simp [unit] at hq
  | cls _ _ => simp [unit] at hq
  | client c =>
    obtain ⟨r, hr⟩ := run_client lv e c
    rw [hr]
    obtain ⟨p, hp, rfl⟩ := mem_trace_client lv e c q hq
    exact h c r p hp

theorem searched_key (lv : Client Pkg N → List (List (Probe Pkg N))) (gv : Bool) (d : Design)
    (hd : d.searched = true) (c : Client Pkg N) (r : Res Pkg N) (p : Probe Pkg N) (hp : p ∈ probes lv c) :
    probeKey p ∈ keysOf pk files lv gv d ⟨some ([], []), some c, r⟩ := by
  simp only [keysOf, hd, ite_true, Finset.mem_union, List.mem_toFinset, List.mem_map]
  exact .inr ⟨p, hp, rfl⟩

/-- **`searched` meets the obligations**, for names and for implicits: a key per probe. -/
theorem obligations_searched (lv : Client Pkg N → List (List (Probe Pkg N))) (gv : Bool)
    (d : Design) (hd : d.searched = true) : (mk pk files lv gv .full d).Obligations where
  comp := obligations_comp pk files lv gv .full d
  coverage := coverage_of pk files lv gv d fun c r p hp =>
    ⟨probeKey p, searched_key pk files lv gv d hd c r p hp, probeKey_covers p⟩
  abstraction := obligations_abstraction pk files lv gv d

/-- The rules reach a package `p` of a client's lookup for #34, F2 and G. -/
def Reaches (d : Design) (c : Client Pkg N) (p : Pkg) : Prop :=
  p ∈ reach d d.cheap c ∧ p ∈ reach d d.f2 c ∧ p ∈ reach d d.g c

theorem mem_nameKeys {d : Design} {c : Client Pkg N} {r : Res Pkg N} {k : CU Pkg N × K N}
    (h : k ∈ nameKeys d c r) :
    k ∈ keysOf pk files (levels pk) false d ⟨some ([], []), some c, r⟩ := by
  simp only [keysOf, Bool.false_eq_true, ite_false, Finset.mem_union, List.mem_toFinset]
  exact .inl (.inl (.inl (.inl h)))

theorem mem_givenKeys {lv : Client Pkg N → List (List (Probe Pkg N))} {d : Design} {c : Client Pkg N}
    {r : Res Pkg N} {k : CU Pkg N × K N} (h : k ∈ givenKeys c r) :
    k ∈ keysOf pk files lv true d ⟨some ([], []), some c, r⟩ := by
  simp only [keysOf, ite_true, Finset.mem_union, List.mem_toFinset]
  exact .inl (.inl (.inl (.inl h)))

/-- **The name rules cover the lookup** when F3 is on and #34 and F2 reach every searched package
(the enclosing ones and the wildcard-imported ones). -/
theorem names_coverage (d : Design) (h3 : d.f3 = true)
    (hr : ∀ c : Client Pkg N, ∀ p ∈ c.pkgs ++ c.wpkg, p ∈ reach d d.cheap c ∧ p ∈ reach d d.f2 c) :
    ∀ (s : Src Pkg N) (e : Env Pkg N), ∀ q ∈ (unit (levels pk) s).trace e,
      ∃ k ∈ keysOf pk files (levels pk) false d ((unit (levels pk) s).run e), q.1 = k.1 ∧ covers q.2 k.2 := by
  apply coverage_of
  intro c r p hp
  have hn : ∀ k ∈ nameKeys d c r, p.query.1 = k.1 → covers p.query.2 k.2 →
      ∃ k ∈ keysOf pk files (levels pk) false d ⟨some ([], []), some c, r⟩, p.query.1 = k.1 ∧ covers p.query.2 k.2 :=
    fun k hk h1 h2 => ⟨k, mem_nameKeys pk files hk, h1, h2⟩
  have hcheap : ∀ q ∈ c.pkgs ++ c.wpkg, p = .top (q, c.name) →
      ∃ k ∈ keysOf pk files (levels pk) false d ⟨some ([], []), some c, r⟩, p.query.1 = k.1 ∧ covers p.query.2 k.2 := by
    intro q hq hpq
    subst hpq
    refine ⟨((q, c.name), .present), ?_, rfl, rfl⟩
    simp only [keysOf, Finset.mem_union, Finset.mem_image]
    exact .inl (.inl (.inl (.inr ⟨q, (hr c q hq).1, rfl⟩)))
  have hf2 : ∀ q ∈ c.pkgs ++ c.wpkg, p = .mem (q, pk) c.name →
      ∃ k ∈ keysOf pk files (levels pk) false d ⟨some ([], []), some c, r⟩, p.query.1 = k.1 ∧ covers p.query.2 k.2 := by
    intro q hq hpq
    subst hpq
    refine ⟨((q, pk), .has c.name), ?_, rfl, by simp [covers, coversB, Probe.query]⟩
    simp only [keysOf, Finset.mem_union, Finset.mem_image]
    exact .inl (.inl (.inr ⟨q, (hr c q hq).2, rfl⟩))
  simp only [probes, importChecks, levels, List.mem_append, List.mem_flatten, List.mem_cons,
    List.mem_map, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨x, hx, rfl⟩ | ⟨l, hl, hp⟩
  · exact hn (x, .has c.name) (by simp [nameKeys, hx]) rfl (by simp [covers, coversB, Probe.query])
  · rcases hl with (rfl | rfl | rfl) | ⟨q, hq, rfl⟩
    · simp only [List.mem_append, List.mem_map] at hp
      rcases hp with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · exact hn (x, .has c.name) (by simp [nameKeys, hx]) rfl (by simp [covers, coversB, Probe.query])
      · exact hn (x, .api) (by simp [nameKeys, hx]) rfl rfl
    · simp only [List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      exact hn (x, .has c.name) (by simp [nameKeys, hx]) rfl (by simp [covers, coversB, Probe.query])
    · simp only [List.mem_append, List.mem_map] at hp
      rcases hp with (⟨x, hx, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩
      · exact hn (x, .has c.name) (by simp [nameKeys, h3, hx]) rfl (by simp [covers, coversB, Probe.query])
      · exact hcheap q (by simp [hq]) rfl
      · exact hf2 q (by simp [hq]) rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hf2 q (by simp [hq]) rfl
      · exact hcheap q (by simp [hq]) rfl

/-- **#34 with F2 and F3, global** (every package): the obligations hold. -/
theorem obligations_rules_global :
    (names pk files (Pkg := Pkg) .full { cheap := .global, f2 := .global, f3 := true }).Obligations where
  comp := obligations_comp pk files _ _ _ _
  coverage := names_coverage pk files _ rfl fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  abstraction := obligations_abstraction pk files _ _ _

/-- **#34 with F2 and F3, narrowed** to the packages the lookup searches: the obligations hold
when the bridge records wildcard imports of packages. -/
theorem obligations_rules_narrowed :
    (names pk files (Pkg := Pkg) .full
      { cheap := .narrowed, f2 := .narrowed, f3 := true, imports := true }).Obligations where
  comp := obligations_comp pk files _ _ _ _
  coverage := names_coverage pk files _ rfl fun c p hp => by
    simp only [reach, ite_true, List.mem_toFinset]
    exact ⟨hp, hp⟩
  abstraction := obligations_abstraction pk files _ _ _

/-- **The G rule covers implicit search** when it reaches every searched package. -/
theorem givens_coverage (d : Design)
    (hr : ∀ c : Client Pkg N, ∀ p ∈ c.pkgs ++ c.wpkg, p ∈ reach d d.g c) :
    ∀ (s : Src Pkg N) (e : Env Pkg N), ∀ q ∈ (unit (glevels pk files) s).trace e,
      ∃ k ∈ keysOf pk files (glevels pk files) true d ((unit (glevels pk files) s).run e),
        q.1 = k.1 ∧ covers q.2 k.2 := by
  apply coverage_of
  intro c r p hp
  have hg : ∀ k ∈ givenKeys c r, p.query.1 = k.1 → covers p.query.2 k.2 →
      ∃ k ∈ keysOf pk files (glevels pk files) true d ⟨some ([], []), some c, r⟩, p.query.1 = k.1 ∧ covers p.query.2 k.2 :=
    fun k hk h1 h2 => ⟨k, mem_givenKeys pk files hk, h1, h2⟩
  have hpkg : ∀ q ∈ c.pkgs ++ c.wpkg, p ∈ pkgProbes pk files c.name q →
      ∃ k ∈ keysOf pk files (glevels pk files) true d ⟨some ([], []), some c, r⟩, p.query.1 = k.1 ∧ covers p.query.2 k.2 := by
    intro q hq hpq
    refine ⟨probeKey p, ?_, probeKey_covers p⟩
    simp only [keysOf, ite_true, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, List.mem_map]
    exact .inl (.inr ⟨q, hr c q hq, p, hpq, rfl⟩)
  have hkey : ∀ x ∈ c.blk ++ c.expl ++ c.wild ++ c.comp, p = .mem x c.name →
      ∃ k ∈ keysOf pk files (glevels pk files) true d ⟨some ([], []), some c, r⟩, p.query.1 = k.1 ∧ covers p.query.2 k.2 := by
    intro x hx hpx
    subst hpx
    refine hg (x, .has c.name) ?_ rfl (by simp [covers, coversB, Probe.query])
    simp only [List.mem_append] at hx
    simp only [givenKeys, List.mem_append, List.mem_map, Prod.mk.injEq, and_true, exists_eq_right]
    rcases hx with ((hx | hx) | hx) | hx <;> simp_all
  simp only [probes, importChecks, glevels, List.mem_append, List.mem_flatten, List.mem_cons,
    List.mem_map, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨x, hx, rfl⟩ | ⟨l, hl, hp⟩
  · exact hkey x (by simp [hx]) rfl
  · rcases hl with ((rfl | rfl | rfl) | ⟨q, hq, rfl⟩) | rfl
    · simp only [List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      exact hkey x (by simp [hx]) rfl
    · simp only [List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      exact hg (x, .api) (by simp [givenKeys, hx]) rfl rfl
    · simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hp
      rcases hp with ⟨x, hx, rfl⟩ | ⟨q, hq, hpq⟩
      · exact hkey x (by simp [hx]) rfl
      · refine hpkg q ?_ hpq
        simp only [List.mem_append] at hq ⊢
        rcases hq with hq | hq
        · exact .inr hq
        · exact .inl (List.mem_of_mem_take hq)
    · exact hpkg q (List.mem_append_left _ (List.mem_of_mem_drop hq)) hp
    · simp only [List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      exact hkey x (by simp [hx]) rfl

/-- **The G rule, global** (every package object and `$package` class): the obligations hold. -/
theorem obligations_g_global :
    (givens pk files (Pkg := Pkg) .full { g := .global }).Obligations where
  comp := obligations_comp pk files _ _ _ _
  coverage := givens_coverage pk files _ fun _ _ _ => Finset.mem_univ _
  abstraction := obligations_abstraction pk files _ _ _

/-- **The G rule, narrowed** to the searched packages: the obligations hold when the bridge
records wildcard imports of packages. -/
theorem obligations_g_narrowed :
    (givens pk files (Pkg := Pkg) .full { g := .narrowed, imports := true }).Obligations where
  comp := obligations_comp pk files _ _ _ _
  coverage := givens_coverage pk files _ fun c p hp => by
    simp only [reach, ite_true, List.mem_toFinset]
    exact hp
  abstraction := obligations_abstraction pk files _ _ _

/-! ## T3a for the sound designs -/

/-- Any design meeting the obligations inherits T3a: when Zinc's loop stops, every class is up to
date, from any up-to-date state, any edit, any sound policy. Edits of several files, and sequences
of edits, are covered: the loop starts from any state satisfying the invariant. -/
theorem sound_of {C : TCompiler (CU Pkg N) (Src Pkg N) (Out Pkg N) (Iface N) (K N) (Iface N) (Q N) Ans}
    (ob : C.Obligations) (S : Finset (CU Pkg N)) (src : CU Pkg N → Src Pkg N)
    (P : Policy (CU Pkg N) (Out Pkg N) (K N)) (hP : P.Sound S) (fuel n : ℕ) (R : Finset (CU Pkg N))
    (s : State (CU Pkg N) (Out Pkg N) (K N)) (D : Finset (CU Pkg N)) (hD : D ⊆ R)
    (hInv : C.Inv S src s D) (s' : State (CU Pkg N) (Out Pkg N) (K N))
    (h : C.zinc S src P fuel n R s = some s') : C.Inv S src s' ∅ :=
  C.zinc_sound ob S src P hP fuel n R s D hD hInv s' h

/-- A traced query with no covering key refutes the obligations. -/
theorem not_obligations_of (lv : Client Pkg N → List (List (Probe Pkg N))) (gv : Bool) (a : Api)
    (d : Design) (s : Src Pkg N) (e : Env Pkg N) (q : CU Pkg N × Q N) (hq : q ∈ (unit lv s).trace e)
    (hnot : ∀ k ∈ keysOf pk files lv gv d ((unit lv s).run e), ¬ (q.1 = k.1 ∧ coversB q.2 k.2 = true)) :
    ¬ (mk pk files lv gv a d).Obligations := by
  intro ob
  obtain ⟨k, hk, h⟩ := ob.coverage s e q hq
  exact hnot k hk h

/-! ## Precision: keys a probe justifies -/

theorem resolve_ok_mem (e : Env Pkg N) :
    ∀ (ls : List (List (Probe Pkg N))) (p : Probe Pkg N), (resolve ls).run e = .ok p → ∃ l ∈ ls, p ∈ l
  | [], p, h => by simp [resolve] at h
  | l :: ls, p, h => by
    rw [JavaSpec.resolve_cons] at h
    split at h
    · obtain ⟨l', hl', hp⟩ := resolve_ok_mem e ls p h
      exact ⟨l', by simp [hl'], hp⟩
    · rename_i x hx
      cases h
      have : p ∈ JavaSpec.hits e l := by rw [hx]; simp
      exact ⟨l, by simp, List.mem_of_mem_filter this⟩
    · simp at h

/-- A design is **tight** for a lookup when every key it records is justified by a probe of the
lookup: it covers a query the lookup asks when nothing earlier binds. A tight design invalidates a
class only when an answer the lookup can read changed, or through an `api` key (inheritance). -/
def Tight (C : TCompiler (CU Pkg N) (Src Pkg N) (Out Pkg N) (Iface N) (K N) (Iface N) (Q N) Ans)
    (lv : Client Pkg N → List (List (Probe Pkg N))) : Prop :=
  ∀ (s : Src Pkg N) (e : Env Pkg N), ∀ k ∈ C.keysOf ((C.unit s).run e),
    ∃ c, s = .client c ∧ ∃ p ∈ probes lv c, p.query.1 = k.1 ∧ covers p.query.2 k.2

/-- A client compile's result is a probe when it resolves. -/
theorem run_client_res (lv : Client Pkg N → List (List (Probe Pkg N))) (e : Env Pkg N) (c : Client Pkg N) :
    ∃ r, (unit lv (.client c)).run e = ⟨some ([], []), some c, r⟩ ∧ ∀ p, r = .ok p → p ∈ probes lv c := by
  simp only [unit, Task.run_bind]
  split
  · exact ⟨_, rfl, fun p h => by cases h⟩
  · simp only [Task.run_bind, Task.run_pure]
    refine ⟨_, rfl, fun p h => ?_⟩
    obtain ⟨l, hl, hp⟩ := resolve_ok_mem e (lv c) p h
    simp only [probes, List.mem_append, List.mem_flatten]
    exact .inr ⟨l, hl, hp⟩

/-- The narrowed name rules (#34, F2, F3, with recorded package imports) are **tight**. -/
theorem narrowed_tight :
    Tight (names pk files (Pkg := Pkg) .full
      { cheap := .narrowed, f2 := .narrowed, f3 := true, imports := true }) (levels pk) := by
  intro s e k hk
  cases s with
  | absent => simp [names, mk, unit, keysOf] at hk
  | cls _ _ => simp [names, mk, unit, keysOf] at hk
  | client c =>
    refine ⟨c, rfl, ?_⟩
    obtain ⟨r, hr, hres⟩ := run_client_res (levels pk) e c
    simp only [names, mk] at hk
    rw [hr] at hk
    have lv : ∀ l ∈ levels pk c, ∀ p ∈ l, p ∈ probes (levels pk) c := fun l hl p hp => by
      simp only [probes, List.mem_append, List.mem_flatten]; exact .inr ⟨l, hl, hp⟩
    have pr : ∀ p ∈ probes (levels pk) c, p.query.1 = (probeKey p).1 → ∃ p' ∈ probes (levels pk) c,
        p'.query.1 = (probeKey p).1 ∧ covers p'.query.2 (probeKey p).2 :=
      fun p hp _ => ⟨p, hp, probeKey_covers p⟩
    have l1 : c.blk.map (.mem · c.name) ++ c.sup.map (.mem · c.name) ∈ levels pk c := by simp [levels]
    have l3 : c.wild.map (.mem · c.name) ++ c.wpkg.map (fun q => .top (q, c.name)) ++
        c.wpkg.map (fun q => .mem (q, pk) c.name) ∈ levels pk c := by simp [levels]
    have lp : ∀ q ∈ c.pkgs, [Probe.mem (q, pk) c.name, .top (q, c.name)] ∈ levels pk c := by
      intro q hq; simp only [levels, List.mem_append, List.mem_map]; exact .inr ⟨q, hq, rfl⟩
    simp only [keysOf, Bool.false_eq_true, ite_false,
      Finset.mem_union, List.mem_toFinset, Finset.mem_image, Finset.mem_biUnion, reach, ite_true,
      List.mem_append, Finset.notMem_empty, or_false, false_and, exists_false] at hk
    rcases hk with ((hk | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩)
    · simp only [nameKeys, Bool.true_or, ite_true, List.mem_append, List.mem_map] at hk
      rcases hk with ((((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) | hk)
      · exact ⟨.mem x c.name, lv _ l1 _ (by simp [hx]), rfl, by simp [covers, coversB, Probe.query]⟩
      · exact ⟨.mem x c.name, lv _ l1 _ (by simp [hx]), rfl, rfl⟩
      · exact ⟨.mem x c.name, by simp [probes, importChecks, hx], rfl, by simp [covers, coversB, Probe.query]⟩
      · exact ⟨.mem x c.name, lv _ l3 _ (by simp [hx]), rfl, by simp [covers, coversB, Probe.query]⟩
      · cases r with
        | ok p =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          subst hk
          exact ⟨p, hres p rfl, probeKey_covers p⟩
        | _ => simp at hk
    · rcases hq with hq | hq
      · exact ⟨.top (q, c.name), lv _ (lp q hq) _ (by simp), rfl, rfl⟩
      · exact ⟨.top (q, c.name), lv _ l3 _ (by simp [hq]), rfl, rfl⟩
    · rcases hq with hq | hq
      · exact ⟨.mem (q, pk) c.name, lv _ (lp q hq) _ (by simp), rfl, by simp [covers, coversB, Probe.query]⟩
      · exact ⟨.mem (q, pk) c.name, lv _ l3 _ (by simp [hq]), rfl, by simp [covers, coversB, Probe.query]⟩

end Zinc.NamesSpec

/-! The witnesses, in packages `a.b` (0), `a` (1) and `a.q` (2), with the names `Foo` (0, also the
summoned instance), `package` (1) and a third (2: the object `a.W`, `T`'s companion `a.T`, a file
class `Inner$package`). -/

namespace Zinc.NamesSpec.Witness

open Zinc.NamesSpec Zinc.JavaSpec

abbrev P := Fin 3
abbrev Nm := Fin 3

/-- A client named `Foo` in packages `ps`, nothing imported. -/
def client (ps : List P) : Client P Nm := ⟨ps, 0, [], [], [], [], [], false, []⟩

/-- The oracle where exactly the listed queries answer yes. -/
def env (yes : List (CU P Nm × Q Nm)) : Env P Nm := fun q => decide (q ∈ yes)

def today : Design := {}

/-- **F1, a class added in an inner package.** `package a; package b`, `Foo` resolves to `a.Foo`;
the miss on `a.b.Foo` leaves no key. -/
theorem f1_today : ¬ (names (1 : Nm) [2] (Pkg := P) .full today).Obligations :=
  not_obligations_of 1 [2] _ _ _ _ (.client (client [0, 1])) (env [((1, 0), .present)]) ((0, 0), .present)
    (by decide) (by decide)

/-- **F2, a member added to a package object**, under #34 and F3: the miss on `package object b`'s
`Foo` has no key (#34's keys are on classes named `Foo`). -/
theorem f2_cheap : ¬ (names (1 : Nm) [2] (Pkg := P) .full { cheap := .global, f3 := true }).Obligations :=
  not_obligations_of 1 [2] _ _ _ _ (.client (client [0, 1])) (env [((1, 0), .present)]) ((0, 1), .member 0)
    (by decide) (by decide)

/-- **F3, a member added to a wildcard-imported object, the import charged to another class** that
does not use the name, under #34 and F2. -/
theorem f3_cheap : ¬ (names (1 : Nm) [2] (Pkg := P) .full { cheap := .global, f2 := .global }).Obligations :=
  not_obligations_of 1 [2] _ _ _ _ (.client { client [1] with wild := [(1, 2)], first := true })
    (env [((1, 0), .present)]) ((1, 2), .member 0) (by decide) (by decide)

/-- **The narrowed rules without recorded package imports**: `import a.q._`, and a class `a.q.Foo`
added; the probe of `a.q` is outside the enclosing packages. -/
theorem narrowed_without_imports :
    ¬ (names (1 : Nm) [2] (Pkg := P) .full { cheap := .narrowed, f2 := .narrowed, f3 := true }).Obligations :=
  not_obligations_of 1 [2] _ _ _ _ (.client { client [1] with wpkg := [2] }) (env [((1, 0), .present)])
    ((2, 0), .present) (by decide) (by decide)

/-- A givens client: `summon[a.T]` in `ps`, the companion `a.T` holding an instance. -/
def gclient (ps : List P) : Client P Nm := { client ps with comp := [(1, 2)] }

def genv : Env P Nm := env [((1, 2), .member 0)]

/-- **G1, an instance added to a package object**, under #34: the search asked `package object b`
and recorded nothing. -/
theorem g1_cheap : ¬ (givens (1 : Nm) [2] (Pkg := P) .full { cheap := .global }).Obligations :=
  not_obligations_of 1 [2] _ _ _ _ (.client (gclient [0, 1])) genv ((0, 1), .member 0) (by decide) (by decide)

/-- **G2, a top-level given in a new file** (`Inner$package`), under #34. -/
theorem g2_cheap : ¬ (givens (1 : Nm) [2] (Pkg := P) .full { cheap := .global }).Obligations :=
  not_obligations_of 1 [2] _ _ _ _ (.client (gclient [0, 1])) genv ((0, 2), .member 0) (by decide) (by decide)

/-- **The narrowed G rule without recorded package imports**: `import a.q.given`, and an instance
added to `a.q`'s package object. -/
theorem g_narrowed_without_imports :
    ¬ (givens (1 : Nm) [2] (Pkg := P) .full { g := .narrowed }).Obligations :=
  not_obligations_of 1 [2] _ _ _ _ (.client { gclient [1] with wpkg := [2] }) genv ((2, 1), .member 0)
    (by decide) (by decide)

/-- **The global rules are not tight**: a client in package `a` that imports nothing records a key
on `a.q.Foo`, which its lookup never asks about: adding `a.q.Foo` recompiles it. -/
theorem global_not_tight :
    ¬ Tight (names (1 : Nm) [2] (Pkg := P) .full { cheap := .global, f2 := .global, f3 := true }) (levels 1) := by
  intro h
  obtain ⟨c, hc, p, hp, h1, -⟩ :=
    h (.client (client [1])) (env [((1, 0), .present)]) ((2, 0), .present) (by decide)
  injection hc with hc
  subst hc
  have : ∀ p ∈ probes (levels (1 : Nm)) (client [1]), p.query.1 ≠ ((2 : P), (0 : Nm)) := by decide
  exact this p hp h1

end Zinc.NamesSpec.Witness
