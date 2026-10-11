import Zinc.SplitProof
import Zinc.General

/-!
# Implicit search on the shared names instance

`SplitProof.Spec` looks a name up scope by scope and stops at the first hit. Implicit search reads
more: an instance found at one nesting level is ambiguous with another at the same level, so the
search asks every scope of the hit's level before it stops (Scala 3's rule; Scala 2 reads the whole
lexical scope, one level). The scope it resolved to is then not the trace's last query, so the keys
read it from the output: this is an `XCompiler` (`General.lean`), whose extractor reads output and
trace.

Scopes are `Spec`'s, with what the search adds (`GScope`): the nesting level; whether the scope is
a package-level container of implicits (a package object, a Scala 3 `$package` class), which a
client reaches through no edge; whether its package is reached through a wildcard import of the
package; whether its instance is inherited, which #24's declarations-only hash does not see.

Today's bridge: every import qualifier, parent and the summoned type's companion is keyed whatever
the class charged with it uses (a changed implicit invalidates every member-ref dependent, used
names or not), so those scopes are `Scope.pinned`; and the scope the search resolved to. The G rule
keys the package-level containers, all of them (`global`), or those of the searched packages, the
wildcard-imported ones only when the bridge records the import (`narrowed`).

`narrowed` reaches the scopes the client's search reads, which is retronym/zinc#47's `sees`. In Scala
2 the implicit scope also holds the package objects of the summoned type's prefix; they are scopes the
search reads, so the narrowed rule reaches them, which in Zinc is the rule's Scala 2 referrer edges.

Results: today's keys fail coverage on G1 (a package object's instance) and G2 (a top-level given in
a new file); the G rule meets the obligations, global or narrowed given recorded imports, and so do
`searched`'s; the narrowed rule without recorded imports fails coverage; a declarations-only hash
fails abstraction on an inherited instance. T3a follows from `XCompiler.zinc_sound`.
-/

namespace Zinc.SplitProof.Spec

variable {n : ℕ}

/-- What implicit search knows about a scope beyond `Scope`. -/
structure GScope where
  level : ℕ
  pkgLevel : Bool
  imported : Bool
  inherited : Bool
  deriving DecidableEq

/-- The output of a compile: the interface, and the scopes the search found an instance in. -/
structure GOut (n : ℕ) where
  iface : Bool
  hits : List (Fin n)
  deriving DecidableEq

abbrev GT (n : ℕ) := Task (U n × Q) (fun _ => Bool) (GOut n)

variable (gx : Fin n → GScope)

/-- Implicit search from scope `k`: ask the scopes in order; once an instance is found, ask the
rest of its level, then stop. -/
def gsearch (k : ℕ) (hits : List (Fin n)) : GT n :=
  if h : k < n then
    if hits.any (fun i => (gx i).level != (gx ⟨k, h⟩).level) then .pure ⟨false, hits⟩
    else .ask (some ⟨k, h⟩, .binds) fun x => gsearch (k + 1) (if x then hits ++ [⟨k, h⟩] else hits)
  else .pure ⟨false, hits⟩
termination_by n - k

def gunit : Src → GT n
  | .bind x => .pure ⟨x, []⟩
  | .client => gsearch gx 0 []

def ggroup (G : Finset (U n)) (src : U n → Src) (I : U n → Bool) : U n → GOut n :=
  fun u => (gunit gx (src u)).run (answer fun v => if v ∈ G then ifaceSrc (src v) else I v)

theorem iface_gsearch (e : Task.Env (U n × Q) (fun _ => Bool)) :
    ∀ k hits, ((gsearch gx k hits).run e).iface = false := by
  intro k hits
  induction k, hits using gsearch.induct gx with
  | case1 k hits h hany => rw [gsearch, dite_cond_eq_true (eq_true h), ite_cond_eq_true _ _ (eq_true hany)]; rfl
  | case2 k hits h hany ih =>
    rw [gsearch, dite_cond_eq_true (eq_true h), ite_cond_eq_false _ _ (eq_false hany), Task.run_ask]
    exact ih _
  | case3 k hits h => rw [gsearch, dite_cond_eq_false (eq_false h)]; rfl

theorem iface_grun (s : Src) (e : Task.Env (U n × Q) (fun _ => Bool)) :
    ((gunit gx s).run e).iface = ifaceSrc s := by
  cases s with
  | bind x => rfl
  | client => exact iface_gsearch gx e 0 []

/-- Every query of the search asks a scope. -/
theorem trace_gsearch (e : Task.Env (U n × Q) (fun _ => Bool)) :
    ∀ k hits, ∀ q ∈ (gsearch gx k hits).trace e, ∃ i : Fin n, q = (some i, Q.binds) := by
  intro k hits
  induction k, hits using gsearch.induct gx with
  | case1 k hits h hany => intro q hq; rw [gsearch, dite_cond_eq_true (eq_true h), ite_cond_eq_true _ _ (eq_true hany)] at hq; simp at hq
  | case2 k hits h hany ih =>
    intro q hq
    rw [gsearch, dite_cond_eq_true (eq_true h), ite_cond_eq_false _ _ (eq_false hany), Task.trace_ask] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨⟨k, h⟩, rfl⟩
    · exact ih _ q hq
  | case3 k hits h => intro q hq; rw [gsearch, dite_cond_eq_false (eq_false h)] at hq; simp at hq

theorem trace_gunit (s : Src) (e : Task.Env (U n × Q) (fun _ => Bool)) :
    ∀ q ∈ (gunit gx s).trace e, ∃ i : Fin n, q = (some i, Q.binds) := by
  cases s with
  | bind x => intro q hq; simp [gunit] at hq
  | client => exact trace_gsearch gx e 0 []

/-! ## Keys -/

variable (sc : Fin n → Scope)

/-- `today`; the G rule, `global` or not, with recorded package imports or not; `searched`. -/
inductive GDesign | today | rule (global imports : Bool) | searched
  deriving DecidableEq

/-- The package-level containers the G rule reaches. -/
def gruled : GDesign → Fin n → Bool
  | .rule g imp, i => (gx i).pkgLevel && (g || !(gx i).imported || imp)
  | _, _ => false

/-- What a presence key's hash sees of a scope: its binding (develop; #24 with names composed from
ancestors), or only a declared one (#24 without composition). -/
def gπ (decls : Bool) (d : GDesign) (I : U n → Bool) : U n → KR → List Bool
  | none, .presence => [I none]
  | some i, .presence => [I (some i) && !(decls && (gx i).inherited)]
  | none, .rule => (List.finRange n).map fun i => gruled gx d i && I (some i)
  | some _, .rule => []

def gcovers (d : GDesign) (_ : U n → Bool) (q : U n × Q) : U n × KR → Prop
  | (u, .presence) => q.1 = u
  | (none, .rule) => ∃ i, q.1 = some i ∧ gruled gx d i = true
  | (some _, .rule) => False

/-- The scope the search resolved to, when exactly one. -/
def resolvedKeys (o : GOut n) : Finset (U n × KR) :=
  match o.hits with
  | [i] => {(some i, KR.presence)}
  | _ => ∅

def gkeys : GDesign → U n → GOut n → List (U n × Q) → Finset (U n × KR)
  | .searched, _, _, tr => (tr.map fun q => (q.1, KR.presence)).toFinset
  | .today, _, o, _ =>
    resolvedKeys o ∪ (((List.finRange n).filter fun i => (sc i).pinned).map (fun i => (some i, KR.presence))).toFinset
  | .rule _ _, _, o, _ =>
    resolvedKeys o ∪ (((List.finRange n).filter fun i => (sc i).pinned).map (fun i => (some i, KR.presence))).toFinset ∪
      {(none, KR.rule)}

def gcompiler (decls : Bool) (d : GDesign) :
    XCompiler (U n) Src (GOut n) Bool KR (List Bool) Q (fun _ => Bool) where
  unit := gunit gx
  group := ggroup gx
  iface := GOut.iface
  answer := answer
  π := gπ gx decls d
  hashDeps := hashDeps
  keys := gkeys sc d
  covers := gcovers gx d

theorem gcomp (decls : Bool) (d : GDesign) : ∀ (G : Finset (U n)) (src : U n → Src) (I : U n → Bool),
    ∀ u ∈ G, (gcompiler gx sc decls d).group G src I u =
      ((gcompiler gx sc decls d).unit (src u)).run ((gcompiler gx sc decls d).answer
        (XCompiler.override I G ((gcompiler gx sc decls d).iface ∘ (gcompiler gx sc decls d).group G src I))) := by
  intro G src I u _
  have : XCompiler.override I G (GOut.iface ∘ ggroup gx G src I) =
      fun v => if v ∈ G then ifaceSrc (src v) else I v := by
    funext v
    simp only [XCompiler.override, Function.comp]
    split
    · simp only [ggroup, iface_grun]
    · rfl
  show ggroup gx G src I u = (gunit gx (src u)).run (answer (XCompiler.override I G (GOut.iface ∘ ggroup gx G src I)))
  rw [this]
  rfl

theorem glocality (decls : Bool) (d : GDesign) : ∀ (I I' : U n → Bool) (c : U n),
    (∀ u ∈ (gcompiler gx sc decls d).hashDeps I c, I u = I' u) →
      ∀ k, (gcompiler gx sc decls d).π I c k = (gcompiler gx sc decls d).π I' c k := by
  intro I I' c h k
  cases c with
  | none =>
    have hall : ∀ u, I u = I' u := fun u => h u (by simp [gcompiler, hashDeps])
    cases k <;> simp [gcompiler, gπ, hall]
  | some i =>
    have hi : I (some i) = I' (some i) := h (some i) (by simp [gcompiler, hashDeps])
    cases k <;> simp [gcompiler, gπ, hi]

/-- Abstraction holds on develop's hash (and #24's composed one). -/
theorem gabstraction (d : GDesign) : ∀ (I I' : U n → Bool) (k : U n × KR),
    (gcompiler gx sc false d).π I k.1 k.2 = (gcompiler gx sc false d).π I' k.1 k.2 →
      ∀ q, (gcompiler gx sc false d).covers I q k →
        (gcompiler gx sc false d).answer I q = (gcompiler gx sc false d).answer I' q ∧
          (gcompiler gx sc false d).covers I' q k := by
  rintro I I' ⟨u, k⟩ h q hc
  refine ⟨?_, hc⟩
  show I q.1 = I' q.1
  cases k with
  | presence =>
    simp only [gcompiler, gcovers] at hc
    rw [hc]
    cases u with
    | none => simpa [gcompiler, gπ] using h
    | some i => simpa [gcompiler, gπ] using h
  | rule =>
    cases u with
    | some _ => simp [gcompiler, gcovers] at hc
    | none =>
      obtain ⟨i, hq, hr⟩ := hc
      rw [hq]
      simp only [gcompiler, gπ] at h
      have := (List.map_inj_left.1 h) i (List.mem_finRange i)
      simpa [hr] using this

/-- **The G rule covers implicit search** when every scope is pinned (an import qualifier, a parent,
the companion) or a package-level container the rule reaches. -/
theorem gcoverage (g imp : Bool) (decls : Bool)
    (hk : ∀ i, (sc i).pinned = true ∨ gruled gx (.rule g imp) i = true) :
    ∀ (I : U n → Bool) (u : U n) (s : Src),
    ∀ q ∈ ((gcompiler gx sc decls (.rule g imp)).unit s).trace ((gcompiler gx sc decls (.rule g imp)).answer I),
      ∃ k ∈ (gcompiler gx sc decls (.rule g imp)).keys u
          (((gcompiler gx sc decls (.rule g imp)).unit s).run ((gcompiler gx sc decls (.rule g imp)).answer I))
          (((gcompiler gx sc decls (.rule g imp)).unit s).trace ((gcompiler gx sc decls (.rule g imp)).answer I)),
        (gcompiler gx sc decls (.rule g imp)).covers I q k := by
  intro I u s q hq
  obtain ⟨i, rfl⟩ := trace_gunit gx s _ q hq
  rcases hk i with hp | hr
  · exact ⟨(some i, .presence), by simp [gcompiler, gkeys, hp], rfl⟩
  · exact ⟨(none, .rule), by simp [gcompiler, gkeys], i, rfl, hr⟩

theorem gsearched_coverage (decls : Bool) : ∀ (I : U n → Bool) (u : U n) (s : Src),
    ∀ q ∈ ((gcompiler gx sc decls .searched).unit s).trace ((gcompiler gx sc decls .searched).answer I),
      ∃ k ∈ (gcompiler gx sc decls .searched).keys u
          (((gcompiler gx sc decls .searched).unit s).run ((gcompiler gx sc decls .searched).answer I))
          (((gcompiler gx sc decls .searched).unit s).trace ((gcompiler gx sc decls .searched).answer I)),
        (gcompiler gx sc decls .searched).covers I q k := by
  intro I u s q hq
  refine ⟨(q.1, .presence), ?_, rfl⟩
  show (q.1, KR.presence) ∈ (List.map _ _).toFinset
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨q, hq, rfl⟩

/-- Implicit search's slot language: every scope is pinned or a package-level container. -/
def GivensScopes : Prop := ∀ i, (sc i).pinned = true ∨ (gx i).pkgLevel = true

/-- **The G rule, global**: the obligations hold for every implicit search, so T3a. -/
theorem g_global_obligations (h : GivensScopes gx sc) :
    (gcompiler gx sc false (.rule true false)).Obligations where
  comp := gcomp gx sc false _
  coverage := gcoverage gx sc true false false fun i => by
    rcases h i with h | h
    · exact .inl h
    · exact .inr (by simp [gruled, h])
  abstraction := gabstraction gx sc _
  locality := glocality gx sc false _

/-- **The G rule, narrowed**: the obligations hold given recorded package imports. -/
theorem g_narrowed_obligations (h : GivensScopes gx sc) :
    (gcompiler gx sc false (.rule false true)).Obligations where
  comp := gcomp gx sc false _
  coverage := gcoverage gx sc false true false fun i => by
    rcases h i with h | h
    · exact .inl h
    · exact .inr (by simp [gruled, h])
  abstraction := gabstraction gx sc _
  locality := glocality gx sc false _

theorem g_searched_obligations : (gcompiler gx sc false .searched).Obligations where
  comp := gcomp gx sc false _
  coverage := gsearched_coverage gx sc false
  abstraction := gabstraction gx sc _
  locality := glocality gx sc false _

/-! ## Witnesses: two scopes, the companion (1, level 1, pinned) holds an instance -/

/-- Scope 0 a package-level container (level 0) with the flags given; scope 1 the companion. -/
def gtwo (imported inherited : Bool) : (Fin 2 → Scope) × (Fin 2 → GScope) :=
  (fun i => if i = 0 then ⟨false, false, false, false⟩ else ⟨true, false, false, false⟩,
   fun i => if i = 0 then ⟨0, true, imported, inherited⟩ else ⟨1, false, false, false⟩)

def compOnly : U 2 → Bool := fun u => u == some 1

theorem gtrace_compOnly (gx' : Fin 2 → GScope) :
    (gunit gx' .client).trace (answer compOnly) = [(some 0, .binds), (some 1, .binds)] := by
  simp [gunit, gsearch, answer, compOnly]

/-- A traced miss on scope 0 that no key covers refutes the obligations. -/
theorem g_not_obligations_of (sc' : Fin 2 → Scope) (gx' : Fin 2 → GScope) (decls : Bool) (d : GDesign)
    (h : ∀ k ∈ gkeys sc' d none ((gunit gx' .client).run (answer compOnly)) [(some 0, .binds), (some 1, .binds)],
      ¬ gcovers gx' d compOnly (some 0, .binds) k) :
    ¬ (gcompiler gx' sc' decls d).Obligations := by
  intro ob
  obtain ⟨k, hk, hc⟩ := ob.coverage compOnly none .client (some 0, .binds)
    (by show _ ∈ (gunit gx' .client).trace (answer compOnly); rw [gtrace_compOnly gx']; simp)
  change k ∈ gkeys sc' d none ((gunit gx' .client).run (answer compOnly))
    ((gunit gx' .client).trace (answer compOnly)) at hk
  rw [gtrace_compOnly gx'] at hk
  exact h k hk hc

/-- **G1/G2**: an instance added to a package object (or a top-level given in a new file, scope 0)
over the companion's. Today's keys hold the companion and the resolved scope only. -/
theorem g12_today : ¬ (gcompiler (gtwo false false).2 (gtwo false false).1 false .today).Obligations :=
  g_not_obligations_of _ _ _ _ (by
    intro k hk
    simp [gkeys, resolvedKeys, gunit, gsearch, answer, compOnly, gtwo, List.finRange] at hk
    subst hk
    simp [gcovers])

/-- **The narrowed G rule without recorded package imports**: the container is in a wildcard-imported
package. -/
theorem g_narrowed_without_imports :
    ¬ (gcompiler (gtwo true false).2 (gtwo true false).1 false (.rule false false)).Obligations :=
  g_not_obligations_of _ _ _ _ (by
    intro k hk
    simp [gkeys, resolvedKeys, gunit, gsearch, answer, compOnly, gtwo, List.finRange] at hk
    rcases hk with rfl | rfl <;> simp [gcovers, gruled, gtwo])

/-- **#24 without composition fails abstraction**: an inherited instance in the package object
(`package object b extends a.PT`) moves no declaration. -/
theorem g_decls_not_abstraction :
    ¬ (gcompiler (gtwo false true).2 (gtwo false true).1 true .today).Obligations := by
  intro ob
  have := (ob.abstraction (fun _ => false) (fun u => u == some 0) (some 0, .presence)
    (by simp [gcompiler, gπ, gtwo]) (some 0, .binds) rfl).1
  simp [gcompiler, answer] at this


/-! ## Given prioritisation (Phase 26, `PLAN-imports.md`)

At the decisive level the search has read every scope; the rule picks among the level's hits:
Scala 3.7 and later the most general instance (`general`), Scala 3 before 3.7 and Scala 2 the most
specific (`specific`); with no such instance the search is ambiguous (probes g1–g5). `le i j`: the
instance in scope `i` has a type at least as specific as `j`'s. The rule reads no more than the
trace, so it changes no obligation; it changes which edits change the choice. A type edit is a
container's instance leaving one scope (its old type) and entering another (its new type). -/

inductive Prio | general | specific
  deriving DecidableEq

variable (le : Fin n → Fin n → Bool)

/-- The instance the rule picks among the hits. -/
def best (p : Prio) (hs : List (Fin n)) : Option (Fin n) :=
  hs.find? fun i => hs.all fun j => match p with
    | .general => le j i
    | .specific => le i j

/-- Today's keys read the scope the search picked. -/
def pickedKeys (p : Prio) (o : GOut n) : Finset (U n × KR) :=
  match best le p o.hits with
  | some i => {(some i, KR.presence)}
  | none => ∅

def gkeysP (p : Prio) : GDesign → U n → GOut n → List (U n × Q) → Finset (U n × KR)
  | .searched, _, _, tr => (tr.map fun q => (q.1, KR.presence)).toFinset
  | .today, _, o, _ =>
    pickedKeys le p o ∪ (((List.finRange n).filter fun i => (sc i).pinned).map (fun i => (some i, KR.presence))).toFinset
  | .rule _ _, _, o, _ =>
    pickedKeys le p o ∪ (((List.finRange n).filter fun i => (sc i).pinned).map (fun i => (some i, KR.presence))).toFinset ∪
      {(none, KR.rule)}

def gcompilerP (p : Prio) (d : GDesign) :
    XCompiler (U n) Src (GOut n) Bool KR (List Bool) Q (fun _ => Bool) :=
  { gcompiler gx sc false d with keys := gkeysP sc le p d }

/-- **The G rule meets the obligations under either rule**, global or narrowed with recorded
imports: the rule picks among what the trace read. -/
theorem gP_rule_obligations (p : Prio) (g imp : Bool)
    (hk : ∀ i, (sc i).pinned = true ∨ gruled gx (.rule g imp) i = true) :
    (gcompilerP gx sc le p (.rule g imp)).Obligations where
  comp := gcomp gx sc false (.rule g imp)
  coverage := by
    intro I u s q hq
    obtain ⟨i, rfl⟩ := trace_gunit gx s _ q hq
    rcases hk i with hp | hr
    · exact ⟨(some i, .presence), by simp [gcompilerP, gkeysP, hp], rfl⟩
    · exact ⟨(none, .rule), by simp [gcompilerP, gkeysP], i, rfl, hr⟩
  abstraction := gabstraction gx sc (.rule g imp)
  locality := glocality gx sc false (.rule g imp)

theorem gP_global_obligations (p : Prio) (h : GivensScopes gx sc) :
    (gcompilerP gx sc le p (.rule true false)).Obligations :=
  gP_rule_obligations gx sc le p true false fun i => by
    rcases h i with h | h
    · exact .inl h
    · exact .inr (by simp [gruled, h])

theorem gP_searched_obligations (p : Prio) : (gcompilerP gx sc le p .searched).Obligations where
  comp := gcomp gx sc false .searched
  coverage := gsearched_coverage gx sc false
  abstraction := gabstraction gx sc .searched
  locality := glocality gx sc false .searched

/-! ### Witnesses: one level, scope 0 an imported `X { given B }` (pinned), scope 1 `package
object b`'s instance of `A`, scope 2 its instance of `C` (`C <: B <: A`) -/

def g3Scopes : Fin 3 → Scope := fun i => if i = 0 then ⟨true, false, false, false⟩ else ⟨false, false, false, false⟩
def g3Levels : Fin 3 → GScope := fun i => if i = 0 then ⟨0, false, false, false⟩ else ⟨0, true, false, false⟩
/-- `C <: B <: A`: scope 2 at least as specific as 0, 0 as 1. -/
def g3Le : Fin 3 → Fin 3 → Bool := fun i j => i == j || (i == 2) || (i == 0 && j == 1)

def onlyB : U 3 → Bool := fun u => u == some 0
def bAndA : U 3 → Bool := fun u => u == some 0 || u == some 1
def bAndC : U 3 → Bool := fun u => u == some 0 || u == some 2

theorem run_onlyB : (gunit g3Levels .client).run (answer onlyB) = ⟨false, [0]⟩ := by
  simp [gunit, gsearch, answer, onlyB, g3Levels]
theorem run_bAndA : (gunit g3Levels .client).run (answer bAndA) = ⟨false, [0, 1]⟩ := by
  simp [gunit, gsearch, answer, bAndA, g3Levels]
theorem run_bAndC : (gunit g3Levels .client).run (answer bAndC) = ⟨false, [0, 2]⟩ := by
  simp [gunit, gsearch, answer, bAndC, g3Levels]

/-- **The rules differ** (probe g1): with `B` and `A` at one level, Scala 3.7+ picks `A`, the old
rule `B`. -/
theorem prio_differs : best g3Le .general [0, 1] = some 1 ∧ best g3Le .specific [0, 1] = some 0 := by
  decide

/-- **A more general instance added to a package object**: under 3.7+ the choice moves from `B`
to `A`, and no key today's bridge recorded moves (the package object is reached through no edge);
under the old rule the choice stays. -/
theorem general_added_stale :
    best g3Le .general ((gunit g3Levels .client).run (answer onlyB)).hits = some 0 ∧
    best g3Le .general ((gunit g3Levels .client).run (answer bAndA)).hits = some 1 ∧
    best g3Le .specific ((gunit g3Levels .client).run (answer bAndA)).hits = some 0 ∧
    ∀ k ∈ gkeysP g3Scopes g3Le .general .today none ((gunit g3Levels .client).run (answer onlyB)) [],
      gπ g3Levels false .today onlyB k.1 k.2 = gπ g3Levels false .today bAndA k.1 k.2 := by
  rw [run_onlyB, run_bAndA]; decide

/-- **A package object's instance retyped from `C` to `A`**: with the imported `B`, 3.7+ picks `B`
before (`C` is more specific, `B` more general) and `A` after; today's keys do not move. -/
theorem type_widened_stale :
    best g3Le .general ((gunit g3Levels .client).run (answer bAndC)).hits = some 0 ∧
    best g3Le .general ((gunit g3Levels .client).run (answer bAndA)).hits = some 1 ∧
    ∀ k ∈ gkeysP g3Scopes g3Le .general .today none ((gunit g3Levels .client).run (answer bAndC)) [],
      gπ g3Levels false .today bAndC k.1 k.2 = gπ g3Levels false .today bAndA k.1 k.2 := by
  rw [run_bAndC, run_bAndA]; decide


/-- Every environment of the three scopes. -/
def g3Envs : List (U 3 → Bool) :=
  [false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].map fun c =>
    fun u => match u with
      | some 0 => a | some 1 => b | some 2 => c | none => false

/-- Check, on the bounded space: under the global G rule's keys, when no key the client recorded
moves, the choice does not either, under both rules (the obligations' consequence, enumerated). -/
example : g3Envs.all (fun e => g3Envs.all fun e' => [Prio.general, .specific].all fun p =>
    let o := (gunit g3Levels .client).run (answer e)
    let o' := (gunit g3Levels .client).run (answer e')
    !(decide (∀ k ∈ gkeysP g3Scopes g3Le p (.rule true false) none o [],
        gπ g3Levels false (.rule true false) e k.1 k.2 = gπ g3Levels false (.rule true false) e' k.1 k.2)) ||
      best g3Le p o.hits == best g3Le p o'.hits) = true := by
  native_decide

end Zinc.SplitProof.Spec
