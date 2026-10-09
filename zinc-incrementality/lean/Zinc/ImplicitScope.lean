import Zinc.NonLocalAns
import Zinc.Termination

/-!
# Implicit scope through an ancestor's companion, across projects (sbt/zinc#1845)

The implicit scope of `Show[C]` includes the companions of `C`'s base classes, so a client that
resolves it depends on `object B` when `C extends B`, without naming `B`:

```scala
// lib
class A; object A { implicit def sa[T <: A]: Show[T] }
class B extends A                   // edit: object B { implicit def sb[T <: B]: Show[T] }
class C extends B
// app
object X { implicitly[Show[C]] }    // clean: sb, incremental (develop): sa
```

Within one project `MemberRefInvalidator` invalidates the memberRef clients of every inheritor of
a class whose implicit names changed (the *fallback*). A downstream project only diffs the classes
it recorded, `C`, `Show` and `A`, and `C`'s `AnalyzedClass` does not change.

The fix (`AnalysisCallback.InheritedImplicitScopes`) has each class publish one more `Implicit`
name hash, `<inherited implicit scope>`: the set of its direct parents' implicit name-hash sets.
A parent's set includes its own entry, so the value covers every ancestor; it is also folded into
the class's `apiHash`. Parents in the project are read from this cycle (or the previous analysis
if not recompiled), external parents from the inheritance dependency.

## The model

Classes have one parent (a trait parent behaves the same), companion implicits, class-side
implicits, an optional parent of the companion (`object C extends L`), and a non-implicit
companion member. An implicit `(bound, list, v)` is `implicit def _[T <: bound]: Show[T]`
(`Show[List[T]]` if `list`). A search for `Show[t]` walks `t`'s base classes, collects the
applicable implicits of their companions (declared or inherited by the companion), and picks the
unique applicable one from the most derived base; for an object `t` the bases exclude `t`.

Name hashes are Zinc's, per `AnalyzedClass` (class and companion): the `Implicit` entries of the
class side and of the companion, each *including inherited members* (`Visit` walks
`structure.inherited`), tagged by side and owner as the definition's location is. Hashes are
modelled injectively: a hash is the structure it hashes.

Keys, as Zinc records them: a client searching `Show[t]` records `(t, cls)` (its parents) and
`(t, imp)` (memberRef on `t`, unconditional on implicit names), and `(o, imp)` for the owner of
the selected implicit; a class reading its parents' or its companion's parents' published API
records `(p, inh)`, whose hash is `apiHash`.

Two forms of the fix (`Ext.sto`):

* **recomputed**: `(t, imp)` is a non-local hash over `t`'s ancestors, recomputed over `affected`
  (T2″). Interfaces are source-determined. This is the specification;
* **stored**: what Zinc does. The published interface carries the linearization, the name hashes
  (with inherited members) and the summary, computed at the class's compile from its parents'
  published ones. Every hash is local. Freshness comes from the inheritance key, which covers the
  summary because it is folded into `apiHash` (`Ext.fold`).

Projects are policies on one loop, as in `Erasure.lean`: transitive inheritance invalidation and
the implicit fallback act only within the owner's project (`proj`); across projects only recorded
keys count (`plain`).

## Results

1. Scenarios (the Zinc branch's scripted tests) as checked examples.
2. `is_obligations`: the recomputed fix meets `NCompiler.Obligations` if it is published for
   objects too, so `is_sound` (T3a″) holds with the plain policy: no in-project rule is needed.
3. `stored_eq_recomputed`: where every class's published interface is its own compile against the
   current ones (`Consistent`; `consistent_of_upToDate`: every class up to date), the stored
   hashes are the recomputed ones. Without the `apiHash` fold an edit leaves a descendant in another
   project stale (checked example).
4. Counterexamples: `object O extends B` (only `NameKind.Type` sources reach `typeParents`), and,
   only if inherited members were missing from name hashes, `object C extends L`.
5. `lake exe exhaustive implicit`: stored = recomputed run for run, and the fix across projects
   recompiles what the fallback recompiles in one project (counts at the end of the file).
-/

namespace Zinc.ImplicitScope

inductive Cls | A | B | C | D | L | O | X | W | Y | Z
  deriving DecidableEq, Repr

def allCls : List Cls := [.A, .B, .C, .D, .L, .O, .X, .W, .Y, .Z]

instance : Fintype Cls := ⟨allCls.toFinset, by intro x; cases x <;> decide⟩

/-- `implicit def _[T <: bound]: Show[T]`, or `Show[List[T]]` if `list`; `v` tells them apart. -/
structure Imp where
  bound : Cls
  list : Bool := false
  v : ℕ
  deriving DecidableEq, Repr

structure Decl where
  /-- An object with no companion class. -/
  obj : Bool := false
  parent : Option Cls := none
  /-- Class-side implicits (an object's own). -/
  cimps : List Imp := []
  /-- Companion implicits. -/
  comp : List Imp := []
  /-- The companion's parent: `object C extends L`. -/
  cpar : Option Cls := none
  /-- A non-implicit companion member. -/
  other : ℕ := 0
  deriving DecidableEq, Repr

/-- `Implicit`-scope name hashes, by side (the definition's location). -/
structure Names where
  cls : List Imp := []
  comp : List Imp := []
  deriving DecidableEq, Repr

/-- The published API. Under the recomputed fix only `decl` is set. -/
structure Pub where
  decl : Decl := {}
  /-- Linearization: each base with its object flag and parent. -/
  cl : List (Cls × Bool × Option Cls) := []
  names : Names := {}
  /-- The inherited implicit scope: each base with its names (the injective summary). -/
  sum : List (Cls × Names) := []
  deriving DecidableEq, Repr

structure Src where
  me : Cls
  decl : Decl := {}
  /-- `implicitly[Show[t]]`, or `Show[List[t]]`. -/
  goals : List (Cls × Bool) := []
  deriving DecidableEq, Repr

structure Out where
  pub : Pub
  /-- The implicit each goal resolved to, with the companion it came from. -/
  picks : List (Option (Cls × Imp))
  deriving DecidableEq, Repr

/-! ## Queries -/

inductive Ctx
  /-- A search for `Show[t]`. -/
  | srch (t : Cls)
  /-- A reference to the selected implicit. -/
  | sel
  /-- A class reading its parent's (or its companion's parent's) published API. -/
  | inh
  deriving DecidableEq, Repr

inductive Q
  | parents (x : Ctx)
  /-- The companion's implicits, declared and inherited. -/
  | cscope (x : Ctx)
  | api (x : Ctx)
  deriving DecidableEq, Repr

inductive AnsV
  | par (o : Bool) (p : Option Cls)
  | imps (l : List Imp)
  | pub (p : Pub)
  deriving DecidableEq, Repr

@[irreducible] def depth : ℕ := 4

theorem depth_eq : depth = 3 + 1 := by unfold depth; rfl

/-- The class side, inherited members included. -/
def clsP (I : Cls → Pub) : ℕ → Cls → List Imp
  | 0, _ => []
  | f + 1, c => (I c).decl.cimps ++ match (I c).decl.parent with
    | some p => clsP I f p
    | none => []

/-- What the companion's parent contributes to the companion. -/
def cparP (I : Cls → Pub) (c : Cls) : List Imp :=
  match (I c).decl.cpar with
  | some l => clsP I depth l
  | none => []

/-- The companion's implicits, declared and inherited: what a search finds there. -/
def cscopeP (I : Cls → Pub) (c : Cls) : List Imp := (I c).decl.comp ++ cparP I c

/-- Answers read declarations, except `api`. -/
def answer (I : Cls → Pub) : Cls × Q → AnsV
  | (c, .parents _) => .par (I c).decl.obj (I c).decl.parent
  | (c, .cscope _) => .imps (cscopeP I c)
  | (c, .api _) => .pub (I c)

abbrev T := Task (Cls × Q) (fun _ => AnsV)

def askQ (c : Cls) (q : Q) : T AnsV := Task.ask (c, q) Task.pure

@[simp] theorem run_askQ (c : Cls) (q : Q) (e : Task.Env (Cls × Q) (fun _ => AnsV)) :
    (askQ c q).run e = e (c, q) := rfl
@[simp] theorem trace_askQ (c : Cls) (q : Q) (e : Task.Env (Cls × Q) (fun _ => AnsV)) :
    (askQ c q).trace e = [(c, q)] := rfl

/-! ## The compiler -/

/-- The base classes of `c`, with their object flags. -/
def chainT (t : Cls) : ℕ → Cls → T (List (Cls × Bool))
  | 0, _ => pure []
  | f + 1, c => do
    match ← askQ c (.parents (.srch t)) with
    | .par o (some p) => do
      let l ← chainT t f p
      pure ((c, o) :: l)
    | .par o none => pure [(c, o)]
    | _ => pure []

def cscT (t : Cls) : List Cls → T (List (Cls × List Imp))
  | [] => pure []
  | e :: es => do
    let r ← askQ e (.cscope (.srch t))
    let l ← cscT t es
    pure ((e, match r with | .imps l => l | _ => []) :: l)

/-- The unique applicable implicit of the most derived base that has any. -/
def select (ch : List Cls) (list : Bool) : List (Cls × List Imp) → Option (Cls × Imp)
  | [] => none
  | (e, l) :: rest => match l.filter (fun i => i.list == list && ch.contains i.bound) with
    | [] => select ch list rest
    | [i] => some (e, i)
    | _ => none

/-- An object's own members are not in the implicit scope of its singleton type. -/
def bases : List (Cls × Bool) → List Cls
  | (_, true) :: rest => rest.map (·.1)
  | l => l.map (·.1)

def searchT (g : Cls × Bool) : T (Option (Cls × Imp)) := do
  let ch ← chainT g.1 depth g.1
  let cs ← cscT g.1 (bases ch)
  match select (ch.map (·.1)) g.2 cs with
  | some (o, i) => do
    let _ ← askQ o (.cscope .sel)
    pure (some (o, i))
  | none => pure none

def goalsT : List (Cls × Bool) → T (List (Option (Cls × Imp)))
  | [] => pure []
  | g :: gs => do
    let r ← searchT g
    let l ← goalsT gs
    pure (r :: l)

/-- Extractor and design options. -/
structure Ext where
  /-- Publish the inherited implicit scope. -/
  fix : Bool := true
  /-- …for objects too (Zinc: only `NameKind.Type` sources reach `typeParents`). -/
  objects : Bool := false
  /-- Name hashes include inherited members (Zinc: yes, `Visit` walks `structure.inherited`). -/
  inhNames : Bool := true
  /-- Stored (Zinc) rather than recomputed. -/
  sto : Bool := false
  /-- The stored summary is folded into `apiHash`. -/
  fold : Bool := true
  deriving DecidableEq, Repr

def fixes (x : Ext) (d : Decl) : Bool := x.fix && (!d.obj || x.objects)

def pubOf : AnsV → Option Pub
  | .pub p => some p
  | _ => none

def askPub (o : Option Cls) : T (Option Pub) :=
  match o with
  | some p => do
    let a ← askQ p (.api .inh)
    pure (pubOf a)
  | none => pure none

/-- The stored fields, from the parents' published ones. -/
def store (x : Ext) (me : Cls) (d : Decl) (pp lp : Option Pub) : Pub :=
  let names : Names :=
    { cls := d.cimps ++ ((pp.map (·.names.cls)).getD [])
      comp := d.comp ++ (if x.inhNames then (lp.map (·.names.cls)).getD [] else []) }
  { decl := d
    cl := (me, d.obj, d.parent) :: ((pp.map (·.cl)).getD [])
    names := names
    sum := (me, names) :: ((pp.map (·.sum)).getD []) }

def pubT (x : Ext) (me : Cls) (d : Decl) : T Pub :=
  if x.sto then do
    let pp ← askPub d.parent
    let lp ← askPub d.cpar
    pure (store x me d pp lp)
  else pure { decl := d }

def unitF (x : Ext) (s : Src) : T Out := do
  let p ← pubT x s.me s.decl
  let ps ← goalsT s.goals
  pure ⟨p, ps⟩

/-! ## Pure views and hashes -/

def chainP (I : Cls → Pub) : ℕ → Cls → List Cls
  | 0, _ => []
  | f + 1, c => c :: match (I c).decl.parent with
    | some p => chainP I f p
    | none => []

def namesP (x : Ext) (I : Cls → Pub) (c : Cls) : Names :=
  { cls := clsP I depth c
    comp := (I c).decl.comp ++ (if x.inhNames then cparP I c else []) }

def clP (I : Cls → Pub) (c : Cls) : List (Cls × Bool × Option Cls) :=
  (chainP I depth c).map fun e => (e, (I e).decl.obj, (I e).decl.parent)

def sumP (x : Ext) (I : Cls → Pub) (c : Cls) : List (Cls × Names) :=
  (chainP I depth c).map fun e => (e, namesP x I e)

inductive K
  /-- The class's parents (its own name's hash). -/
  | cls
  /-- Its `Implicit` name hashes: memberRef clients, unconditionally. -/
  | imp
  /-- The inheritance edge: `apiHash`. -/
  | inh
  deriving DecidableEq, Repr

inductive H
  | cl (l : List (Cls × Bool × Option Cls))
  | imp (l : List (Cls × Names))
  | api (p : Pub)
  deriving DecidableEq, Repr

def π (x : Ext) (I : Cls → Pub) (c : Cls) : K → H
  | .cls => .cl (if x.sto then (I c).cl else clP I c)
  | .imp =>
    if x.sto then .imp (if fixes x (I c).decl then (I c).sum else [(c, (I c).names)])
    else .imp (if fixes x (I c).decl then sumP x I c else [(c, namesP x I c)])
  | .inh => .api (if x.sto && !x.fold then { I c with sum := [] } else I c)

def keyOf : Cls × Q → Cls × K
  | (_, .parents (.srch t)) => (t, .cls)
  | (_, .cscope (.srch t)) => (t, .imp)
  | (o, .cscope _) => (o, .imp)
  | (c, _) => (c, .inh)

/-- Which queries a key stands for. -/
def scope (I : Cls → Pub) : Cls × Q → Prop
  | (e, .parents (.srch t)) => e ∈ chainP I depth t
  | (e, .cscope (.srch t)) => e ∈ chainP I depth t
  | (_, .cscope .sel) => True
  | (_, .api .inh) => True
  | _ => False

def keys (_ : Cls) (tr : List (Cls × Q)) : Finset (Cls × K) := (tr.map keyOf).toFinset

/-- Joint compilation. Recomputed: interfaces are the sources' declarations. Stored: group-mates'
published interfaces are computed bottom-up, `depth + 1` passes (enough for an acyclic hierarchy
of height at most `depth`). -/
def group (x : Ext) (G : Finset Cls) (src : Cls → Src) (I : Cls → Pub) : Cls → Out :=
  if x.sto then
    let step (prev : Cls → Pub) : List (Cls × Out) := allCls.map fun u =>
      (u, (unitF x (src u)).run (answer fun v => if v ∈ G then prev v else I v))
    let look (t : List (Cls × Out)) (v : Cls) : Pub :=
      match t.lookup v with | some o => o.pub | none => I v
    let rec iter : ℕ → List (Cls × Out) → List (Cls × Out)
      | 0, t => t
      | n + 1, t => iter n (step (look t))
    let t := iter depth (step I)
    fun u => match t.lookup u with | some o => o | none => ⟨I u, []⟩
  else fun u => (unitF x (src u)).run (answer fun v => if v ∈ G then { decl := (src v).decl } else I v)

def Is (x : Ext) : NCompiler Cls Src Out Pub K H Q (fun _ => AnsV) where
  unit := unitF x
  group := group x
  iface := Out.pub
  answer := answer
  π := π x
  hashDeps := fun _ _ => Finset.univ
  keys := keys
  covers := fun I q k => k = keyOf q ∧ scope I q

/-! ## The recomputed fix meets the bridge spec -/

section obligations

open Zinc.Task

abbrev Env := Task.Env (Cls × Q) (fun _ => AnsV)

theorem run_chainT (I : Cls → Pub) (t : Cls) :
    ∀ f c, (chainT t f c).run (answer I) = (chainP I f c).map fun e => (e, (I e).decl.obj) := by
  intro f
  induction f with
  | zero => intro c; rfl
  | succ f ih =>
    intro c
    simp only [chainT, chainP, bind_eq, Task.run_bind, run_askQ, answer]
    cases (I c).decl.parent with
    | none => rfl
    | some p => simp [ih]

theorem trace_chainT (I : Cls → Pub) (t : Cls) :
    ∀ f c, (chainT t f c).trace (answer I) = (chainP I f c).map fun e => (e, Q.parents (.srch t)) := by
  intro f
  induction f with
  | zero => intro c; rfl
  | succ f ih =>
    intro c
    simp only [chainT, chainP, bind_eq, Task.trace_bind, trace_askQ, run_askQ, answer]
    cases (I c).decl.parent with
    | none => rfl
    | some p => simp [ih]

theorem trace_cscT (I : Cls → Pub) (t : Cls) :
    ∀ es, (cscT t es).trace (answer I) = es.map fun e => (e, Q.cscope (.srch t)) := by
  intro es
  induction es with
  | nil => rfl
  | cons e es ih => simp [cscT, ih]

theorem mem_bases {e : Cls} : ∀ {l : List (Cls × Bool)}, e ∈ bases l → e ∈ l.map (·.1)
  | [], h => h
  | (_, true) :: _, h => List.mem_cons_of_mem _ h
  | (_, false) :: _, h => h

theorem scope_searchT (I : Cls → Pub) (g : Cls × Bool) :
    ∀ q ∈ (searchT g).trace (answer I), scope I q := by
  intro q hq
  unfold searchT at hq
  rw [bind_eq, trace_bind, trace_chainT, run_chainT, List.mem_append] at hq
  rcases hq with hq | hq
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hq
    exact he
  rw [bind_eq, trace_bind, trace_cscT, List.mem_append] at hq
  rcases hq with hq | hq
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hq
    have := mem_bases he
    rw [List.map_map] at this
    show e ∈ chainP I depth g.1
    simpa using this
  split at hq
  · rw [bind_eq, trace_bind, trace_askQ, List.mem_append, List.mem_singleton] at hq
    rcases hq with rfl | hq
    · trivial
    · simp at hq
  · simp at hq

theorem scope_goalsT (I : Cls → Pub) :
    ∀ gs, ∀ q ∈ (goalsT gs).trace (answer I), scope I q := by
  intro gs
  induction gs with
  | nil => intro q hq; simp [goalsT] at hq
  | cons g gs ih =>
    intro q hq
    simp only [goalsT, bind_eq, trace_bind, pure_eq, trace_pure, List.append_nil, List.mem_append] at hq
    rcases hq with hq | hq
    · exact scope_searchT I g q hq
    · exact ih q hq

theorem scope_askPub (I : Cls → Pub) :
    ∀ o, ∀ q ∈ (askPub o).trace (answer I), scope I q := by
  intro o q hq
  cases o with
  | none => simp [askPub] at hq
  | some p =>
    simp only [askPub, bind_eq, trace_bind, trace_askQ, pure_eq, trace_pure, List.append_nil,
      List.mem_singleton] at hq
    subst hq
    trivial

theorem scope_unitF (x : Ext) (I : Cls → Pub) (s : Src) :
    ∀ q ∈ (unitF x s).trace (answer I), scope I q := by
  intro q hq
  simp only [unitF, bind_eq, trace_bind, pure_eq, trace_pure, List.append_nil, List.mem_append] at hq
  rcases hq with hq | hq
  · cases hs : x.sto
    · simp [pubT, hs] at hq
    · simp only [pubT, hs, ite_true, bind_eq, trace_bind, pure_eq, trace_pure, List.append_nil,
        List.mem_append] at hq
      rcases hq with hq | hq
      · exact scope_askPub I _ q hq
      · exact scope_askPub I _ q hq
  · exact scope_goalsT I _ q hq

theorem mem_of_map_pair {α β : Type} {l l' : List α} {f g : α → β}
    (h : l.map (fun e => (e, f e)) = l'.map (fun e => (e, g e))) {e : α} (he : e ∈ l) :
    e ∈ l' ∧ f e = g e := by
  have : (e, f e) ∈ l'.map (fun e => (e, g e)) := h ▸ List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨e', he', hee⟩ := List.mem_map.1 this
  simp only [Prod.mk.injEq] at hee
  obtain ⟨rfl, hfg⟩ := hee
  exact ⟨he', hfg.symm⟩

theorem run_askPub (I : Cls → Pub) (o : Option Cls) : (askPub o).run (answer I) = o.map I := by
  cases o <;> rfl

theorem pub_unitF (x : Ext) (s : Src) (e : Env) :
    ((unitF x s).run e).pub = (pubT x s.me s.decl).run e := by
  simp [unitF]

theorem iface_unitF (x : Ext) (hx : x.sto = false) (s : Src) (e : Env) :
    ((unitF x s).run e).pub = { decl := s.decl } := by
  rw [pub_unitF]; simp [pubT, hx]

theorem Is_comp (x : Ext) (hx : x.sto = false) :
    ∀ (G : Finset Cls) (src : Cls → Src) (I : Cls → Pub), ∀ d ∈ G,
      (Is x).group G src I d = ((Is x).unit (src d)).run
        ((Is x).answer (NCompiler.override I G ((Is x).iface ∘ (Is x).group G src I))) := by
  intro G src I d _
  show group x G src I d =
    (unitF x (src d)).run (answer (NCompiler.override I G (Out.pub ∘ group x G src I)))
  simp only [group, hx, Bool.false_eq_true, ite_false]
  congr 2
  funext v
  simp only [NCompiler.override, Function.comp, iface_unitF x hx]

theorem mem_chainP_self (I : Cls → Pub) (c : Cls) : c ∈ chainP I depth c := by
  rw [depth_eq, chainP]; exact List.mem_cons_self

/-- The recomputed fix with faithful name hashes, published for every class (objects too). -/
def recAll : Ext := { objects := true }

/-- **Soundness of the fix.** The recomputed fix, published for objects too and with inherited
members in the name hashes, meets `NCompiler.Obligations`. The search's reads of every base's
companion are covered by the one key `(t, imp)` a memberRef client of `t` records. -/
theorem is_obligations : (Is recAll).Obligations where
  comp := Is_comp recAll rfl
  coverage := by
    intro I d s q hq
    exact ⟨keyOf q, List.mem_toFinset.2 (List.mem_map.2 ⟨q, hq, rfl⟩), rfl,
      scope_unitF recAll I s q hq⟩
  abstraction := by
    intro I I' k hk q hc
    obtain ⟨rfl, hs⟩ := hc
    obtain ⟨e, q⟩ := q
    change π recAll I _ _ = π recAll I' _ _ at hk
    suffices answer I (e, q) = answer I' (e, q) ∧ scope I' (e, q) from ⟨this.1, rfl, this.2⟩
    have hsum : ∀ t, π recAll I t .imp = π recAll I' t .imp → ∀ e ∈ chainP I depth t,
        e ∈ chainP I' depth t ∧ cscopeP I e = cscopeP I' e := by
      intro t h e he
      simp only [π, recAll, fixes, Bool.or_true, Bool.and_self, ite_true, Bool.false_eq_true,
        ite_false, H.imp.injEq, sumP] at h
      have := mem_of_map_pair h he
      refine ⟨this.1, ?_⟩
      have h2 := congrArg Names.comp this.2
      simpa only [namesP, ite_true, cscopeP] using h2
    cases q with
    | parents y =>
      cases y with
      | srch t =>
        simp only [keyOf, π, recAll, Bool.false_eq_true, ite_false, H.cl.injEq, clP] at hk
        have := mem_of_map_pair (f := fun e => ((I e).decl.obj, (I e).decl.parent))
          (g := fun e => ((I' e).decl.obj, (I' e).decl.parent)) hk hs
        simp only [Prod.mk.injEq] at this
        exact ⟨by simp only [answer, this.2.1, this.2.2], this.1⟩
      | sel => exact absurd hs (by simp [scope])
      | inh => exact absurd hs (by simp [scope])
    | cscope y =>
      cases y with
      | srch t =>
        obtain ⟨h1, h2⟩ := hsum t hk e hs
        exact ⟨by simp only [answer, h2], h1⟩
      | sel =>
        obtain ⟨_, h2⟩ := hsum e hk e (mem_chainP_self I e)
        exact ⟨by simp only [answer, h2], trivial⟩
      | inh => exact absurd hs (by simp [scope])
    | api y =>
      cases y with
      | inh =>
        simp only [keyOf, π, recAll, Bool.false_eq_true, Bool.false_and, ite_false,
          H.api.injEq] at hk
        exact ⟨by simp only [answer, hk], trivial⟩
      | srch t => exact absurd hs (by simp [scope])
      | sel => exact absurd hs (by simp [scope])
  locality := by
    intro I I' c h k
    have : I = I' := funext fun d => h d (Finset.mem_univ d)
    rw [this]

/-- …so a terminating run with the plain policy (no in-project rule at all) leaves no class
dirty (T3a″): every downstream client of every descendant is reached. -/
theorem is_sound (S : Finset Cls) (src : Cls → Src) (P : Compiler.Policy Cls Out K)
    (hP : P.Sound S) (fuel n : ℕ) (R : Finset Cls) (s : Compiler.State Cls Out K) (D : Finset Cls)
    (hD : D ⊆ R) (hInv : (Is recAll).Inv S src s D) (s' : Compiler.State Cls Out K)
    (h : (Is recAll).zinc S src P fuel n R s = some s') : (Is recAll).Inv S src s' ∅ :=
  (Is recAll).zinc_sound is_obligations S src P hP fuel n R s D hD hInv s' h

end obligations

/-! ## Cold vs warm: the stored summary is the recomputed one

Zinc takes the summary of a parent that was not recompiled from the previous analysis, and of an
external parent from the inheritance dependency. Both are values stored when the parent was
compiled. Where every published interface is its own compile against the current ones
(`Consistent`: a clean build, or a state in which every class is up to date), the stored
linearization, names and summary are the recomputed ones, so the stored `π` is the recomputed `π`.
What keeps a state consistent across an edit is the inheritance key on the parent, which covers
the summary only because it is folded into `apiHash` (the `up₀`/`up₁` example). -/

section stale

/-- Every published interface is what its class's compile computes from the current ones. -/
def Consistent (x : Ext) (I : Cls → Pub) : Prop :=
  ∀ c, I c = store x c (I c).decl ((I c).decl.parent.map I) ((I c).decl.cpar.map I)

variable (x : Ext) (I : Cls → Pub) (hc : Consistent x I)

include hc in
theorem hc_cl (c : Cls) :
    (I c).cl = (c, (I c).decl.obj, (I c).decl.parent) :: ((((I c).decl.parent.map I).map (·.cl)).getD []) := by
  have h := congrArg Pub.cl (hc c)
  simpa only [store] using h

include hc in
theorem hc_names (c : Cls) : (I c).names =
    { cls := (I c).decl.cimps ++ ((((I c).decl.parent.map I).map (·.names.cls)).getD [])
      comp := (I c).decl.comp ++
        (if x.inhNames then (((I c).decl.cpar.map I).map (·.names.cls)).getD [] else []) } := by
  have h := congrArg Pub.names (hc c)
  simpa only [store] using h

include hc in
theorem hc_sum (c : Cls) :
    (I c).sum = (c, (I c).names) :: ((((I c).decl.parent.map I).map (·.sum)).getD []) := by
  have h := congrArg Pub.sum (hc c)
  have hn := hc_names x I hc c
  simp only [store] at h
  rw [h, hn]

variable (r : Cls → ℕ) (hp : ∀ c p, (I c).decl.parent = some p → r p < r c)
include hc hp

theorem cls_eq : ∀ f c, r c < f → (I c).names.cls = clsP I f c := by
  intro f
  induction f with
  | zero => intro c h; omega
  | succ f ih =>
    intro c h
    rw [hc_names x I hc c, clsP]
    cases hpar : (I c).decl.parent with
    | none => simp
    | some p =>
      simp only [Option.map_some, Option.getD_some]
      rw [ih p (by have := hp c p hpar; omega)]

theorem cl_eq : ∀ f c, r c < f →
    (I c).cl = (chainP I f c).map fun e => (e, (I e).decl.obj, (I e).decl.parent) := by
  intro f
  induction f with
  | zero => intro c h; omega
  | succ f ih =>
    intro c h
    rw [hc_cl x I hc c, chainP, List.map_cons]
    cases hpar : (I c).decl.parent with
    | none => simp
    | some p =>
      simp only [Option.map_some, Option.getD_some]
      rw [ih p (by have := hp c p hpar; omega)]

theorem names_eq (hr : ∀ c, r c < depth) : ∀ c, (I c).names = namesP x I c := by
  intro c
  rw [hc_names x I hc c, namesP, ← cls_eq x I hc r hp depth c (hr c), hc_names x I hc c, cparP]
  congr 2
  cases hl : (I c).decl.cpar with
  | none => simp
  | some l =>
    simp only [Option.map_some, Option.getD_some]
    rw [cls_eq x I hc r hp depth l (hr l)]

theorem sum_eq (hr : ∀ c, r c < depth) : ∀ f c, r c < f →
    (I c).sum = (chainP I f c).map fun e => (e, namesP x I e) := by
  intro f
  induction f with
  | zero => intro c h; omega
  | succ f ih =>
    intro c h
    rw [hc_sum x I hc c, chainP, List.map_cons, names_eq x I hc r hp hr c]
    cases hpar : (I c).decl.parent with
    | none => simp
    | some p =>
      simp only [Option.map_some, Option.getD_some]
      rw [ih p (by have := hp c p hpar; omega)]

/-- **Cold vs warm.** In a consistent state over an acyclic hierarchy of height below `depth`, the
stored hashes are the recomputed ones. -/
theorem stored_eq_recomputed (hr : ∀ c, r c < depth) (c : Cls) (k : K) (hk : k ≠ .inh) :
    π { x with sto := true } I c k = π { x with sto := false } I c k := by
  cases k with
  | cls =>
    simp only [π, ite_true, Bool.false_eq_true, ite_false, H.cl.injEq, clP]
    exact cl_eq x I hc r hp depth c (hr c)
  | imp =>
    simp only [π, ite_true, Bool.false_eq_true, ite_false, fixes, sumP]
    rw [sum_eq x I hc r hp hr depth c (hr c), names_eq x I hc r hp hr c]
    rfl
  | inh => exact absurd rfl hk

end stale

/-- A state in which every class is up to date is consistent. -/
theorem consistent_of_upToDate (x : Ext) (hx : x.sto = true) (src : Cls → Src)
    (hme : ∀ c, (src c).me = c) (s : Compiler.State Cls Out K)
    (h : ∀ c, (Is x).UpToDate src s c) : Consistent x ((Is x).ifaces s) := by
  have hpub : ∀ c, (Is x).ifaces s c =
      store x c (src c).decl ((src c).decl.parent.map ((Is x).ifaces s))
        ((src c).decl.cpar.map ((Is x).ifaces s)) := by
    intro c
    show (s.out c).pub = _
    rw [(h c).1]
    show ((unitF x (src c)).run (answer ((Is x).ifaces s))).pub = _
    rw [pub_unitF, hme c]
    simp only [pubT, hx, ite_true, Task.bind_eq, Task.run_bind, Task.pure_eq, Task.run_pure,
      run_askPub]
  intro c
  have hd : ((Is x).ifaces s c).decl = (src c).decl := by rw [hpub c]; rfl
  rw [hd]
  exact hpub c

/-! ## Runs -/

section runs
open Compiler (State Policy)

abbrev St := State Cls Out K

/-- A list-backed copy of a state, so that native evaluation computes each value once (a
definition returning a function would be eta-expanded, and recompute). -/
def memo (s : St) : St :=
  let o := allCls.map fun c => (c, s.out c)
  let u := allCls.map fun c => (c, s.U c)
  { out := fun c => match o.lookup c with | some x => x | none => s.out c
    U := fun c => match u.lookup c with | some x => x | none => s.U c }

/-- `d` inherits from `e`, through its parents or its companion's. -/
def inhRel (I : Cls → Pub) (d e : Cls) : Bool :=
  (chainP I depth d).contains e || (chainP I depth d).any fun y => (I y).decl.cpar == some e

/-- Project layouts: `lay c` is `c`'s project, upstream first. -/
abbrev Layout := Cls → ℕ

def isClient : Cls → Bool
  | .X | .W | .Y | .Z => true
  | _ => false

def oneP : Layout := fun _ => 0
/-- `lib` (all classes), `app` (clients). -/
def twoP : Layout := fun c => if isClient c then 1 else 0
/-- `lib` (`A B D L`), `mid` (`C O`), `app`. -/
def threeP : Layout
  | .C | .O => 1
  | c => if isClient c then 2 else 0

/-- Zinc's in-project rules for a layout: transitive inheritance invalidation when a class's API
changed, and the implicit fallback (memberRef clients of every inheritor of a class whose implicit
names changed), both within the class's own project. -/
def projExtra (x : Ext) (lay : Layout) (R : Finset Cls) (s s' : St) : Finset Cls :=
  let C := Is x
  let I := C.ifaces s
  let I' := C.ifaces s'
  let chg := fun e k => decide (π x I e k ≠ π x I' e k)
  Finset.univ.filter fun d => allCls.any fun e => lay d == lay e && (
    (decide (e ∈ R) && chg e .inh && d != e && inhRel I' d e) ||
    (chg e .imp && allCls.any fun c => [K.cls, K.imp].any fun k =>
      decide ((c, k) ∈ s'.U d) && lay c == lay e && inhRel I' c e))

inductive Pol | plain | proj (lay : Layout)

def Pol.apply (x : Ext) : Pol → Policy Cls Out K
  | .plain => Compiler.Policy.plain
  | .proj lay => fun _ R s s' I => I ∪ projExtra x lay R s s'

structure Run where
  state : St
  rounds : ℕ
  compiled : Finset Cls

def runE (x : Ext) (src : Cls → Src) (P : Pol) :
    ℕ → ℕ → Finset Cls → Finset Cls → St → Option Run
  | 0, _, _, _, _ => none
  | fuel + 1, n, acc, R, s =>
    let C := Is x
    let s' := memo (C.round src R s)
    let I := P.apply x n R s s' (C.invalidated Finset.univ (C.affected R s) s s')
    if I ⊆ R then some ⟨s', n + 1, acc ∪ R⟩
    else runE x src P fuel (n + 1) (acc ∪ R) I s'

def dummy : St := { out := fun _ => ⟨{}, []⟩, U := fun _ => ∅ }

def init (x : Ext) (src : Cls → Src) : St := memo ((Is x).round src Finset.univ dummy)

def clean (x : Ext) (src : Cls → Src) : Cls → Out := group x Finset.univ src fun _ => {}

structure Report where
  recompiled : List Cls
  rounds : ℕ
  /-- Classes whose final output differs from a clean build. -/
  wrong : List Cls
  /-- Recompiled classes (other than the edited ones) whose output did not change. -/
  wasted : List Cls
  deriving Repr, DecidableEq

def report (x : Ext) (P : Pol) (src₀ src₁ : Cls → Src) (R₀ : Finset Cls) : Option Report :=
  let s₀ := init x src₀
  (runE x src₁ P 8 0 ∅ R₀ s₀).map fun res =>
    let cl := clean x src₁
    let rec_ := allCls.filter fun c => c ∈ res.compiled ∧ c ∉ R₀
    { recompiled := rec_
      rounds := res.rounds
      wrong := allCls.filter fun c => res.state.out c != cl c
      wasted := rec_.filter fun c => res.state.out c == s₀.out c }

/-- What a client resolved in a clean build. -/
def picks (src : Cls → Src) (c : Cls) : List (Option (Cls × Imp)) := (clean {} src c).picks

end runs

/-! ## Scenarios -/

open Cls

/-- The designs compared: Zinc on develop, the fix as Zinc stores it, the fix recomputed. -/
def develop : Ext := { fix := false, sto := true }
def stored : Ext := { sto := true }
def recomputed : Ext := {}

def sa : Imp := ⟨A, false, 1⟩
def sb : Imp := ⟨B, false, 2⟩

/-- `implicit-scope-grandparent-companion`: `A` has `sa`, `B extends A`, `C extends B`,
`D extends A`; `X` resolves `Show[C]`, `Z` resolves `Show[D]`. -/
def gp₀ : Cls → Src
  | A => { me := A, decl := { comp := [sa] } }
  | B => { me := B, decl := { parent := some A } }
  | C => { me := C, decl := { parent := some B } }
  | D => { me := D, decl := { parent := some A } }
  | X => { me := X, goals := [(C, false)] }
  | Z => { me := Z, goals := [(D, false)] }
  | c => { me := c }

/-- `object B { implicit def sb[T <: B]: Show[T] }`. -/
def gp₁ : Cls → Src
  | B => { me := B, decl := { parent := some A, comp := [sb] } }
  | c => gp₀ c

/-- …plus a non-implicit member. -/
def gp₂ : Cls → Src
  | B => { me := B, decl := { parent := some A, comp := [sb], other := 1 } }
  | c => gp₀ c

example : picks gp₀ X = [some (A, sa)] ∧ picks gp₁ X = [some (B, sb)] ∧
    picks gp₁ Z = [some (A, sa)] := by native_decide

/-- **The bug.** On develop, across projects, `X` is not recompiled and keeps `sa`. -/
example : report develop (.proj twoP) gp₀ gp₁ {B} = some ⟨[C], 2, [X], []⟩ := by native_decide
/-- In one project the fallback reaches `X` (a memberRef client of `C`, an inheritor of `B`). -/
example : report develop (.proj oneP) gp₀ gp₁ {B} = some ⟨[C, X], 2, [], []⟩ := by native_decide
/-- **The fix**, across projects: `C`'s summary moves, so `X` is recompiled; `Z` is not. -/
example : report stored (.proj twoP) gp₀ gp₁ {B} = some ⟨[C, X], 3, [], []⟩ := by native_decide
/-- Recomputed, with no in-project rule at all. -/
example : report recomputed .plain gp₀ gp₁ {B} = some ⟨[X], 2, [], []⟩ := by native_decide

/-- A non-implicit companion member reaches neither `X` nor `Z` (`C` recompiles by inheritance,
its published API is unchanged). -/
example : report stored (.proj twoP) gp₁ gp₂ {B} = some ⟨[C], 2, [], [C]⟩ := by native_decide
/-- Removing `sb`: `X` falls back to `sa`. On develop this already works: `B`, the owner of the
selected implicit, is a memberRef dependency of `X`. -/
example : report stored (.proj twoP) gp₁ gp₀ {B} = some ⟨[C, X], 2, [], []⟩ := by native_decide
example : report develop (.proj twoP) gp₁ gp₀ {B} = some ⟨[C, X], 2, [], []⟩ := by native_decide

/-! ### `implicit-scope-type-argument-companion`: `Show[List[C]]` -/

def ta₀ : Cls → Src
  | A => { me := A, decl := { comp := [{ sa with list := true }] } }
  | X => { me := X }
  | W => { me := W, goals := [(C, true)] }
  | c => gp₀ c

def ta₁ : Cls → Src
  | B => { me := B, decl := { parent := some A, comp := [{ sb with list := true }] } }
  | c => ta₀ c

example : picks ta₀ W = [some (A, { sa with list := true })] ∧
    picks ta₁ W = [some (B, { sb with list := true })] := by native_decide
example : report develop (.proj twoP) ta₀ ta₁ {B} = some ⟨[C], 2, [W], []⟩ := by native_decide
example : report stored (.proj twoP) ta₀ ta₁ {B} = some ⟨[C, W], 3, [], []⟩ := by native_decide

/-! ### `implicit-scope-ancestor-in-upstream-project`: `lib (A, B) → mid (C) → app (X)`

`implicit-scope-trait-parent-companion` is the grandparent case again in this model: a trait
parent is a parent. -/

example : report develop (.proj threeP) gp₀ gp₁ {B} = some ⟨[C], 2, [X], []⟩ := by native_decide
example : report stored (.proj threeP) gp₀ gp₁ {B} = some ⟨[C, X], 3, [], []⟩ := by native_decide

/-! ### Cold vs warm: the summary must be in `apiHash`

`A` gains an implicit; `C` is two levels down, in `mid`. In `lib`, `B` recompiles (it inherits
from `A`) and its summary moves, but its own API does not. Without the fold `mid` sees no change in
`B`, never recompiles `C`, and `C` keeps a stale summary: `X` keeps resolving nothing. (`Z`, a client of
`D` in `lib`'s hierarchy, recompiles either way.) This is the
`Stale.lean` trap: a non-local value read from a parent must be refreshed in every descendant, and
across projects only `apiHash` can trigger that. -/

def up₀ : Cls → Src
  | A => { me := A }
  | c => gp₀ c

def up₁ : Cls → Src
  | A => { me := A, decl := { comp := [sa] } }
  | c => gp₀ c

example : picks up₀ X = [none] ∧ picks up₁ X = [some (A, sa)] := by native_decide
example : report { stored with fold := false } (.proj threeP) up₀ up₁ {A} =
    some ⟨[B, D, Z], 3, [C, X], []⟩ := by native_decide
example : report stored (.proj threeP) up₀ up₁ {A} = some ⟨[B, C, D, X, Z], 4, [], []⟩ := by
  native_decide
/-- In one project transitive inheritance invalidation refreshes `C` without the fold. -/
example : report { stored with fold := false } (.proj oneP) up₀ up₁ {A} =
    some ⟨[B, C, D, X, Z], 2, [], []⟩ := by native_decide

/-! ### Not covered: an object's singleton type

`object O extends B`; `Y` resolves `Show[O.type]`, whose implicit scope includes `B`'s and `A`'s
companions. The fix publishes nothing for `O`: only `NameKind.Type` sources reach `typeParents`.
Within one project the fallback reaches `Y` (`O` inherits from `B`). -/

def ob₀ : Cls → Src
  | O => { me := O, decl := { obj := true, parent := some B } }
  | X => { me := X }
  | Y => { me := Y, goals := [(O, false)] }
  | c => gp₀ c

def ob₁ : Cls → Src
  | B => { me := B, decl := { parent := some A, comp := [sb] } }
  | c => ob₀ c

example : picks ob₀ Y = [some (A, sa)] ∧ picks ob₁ Y = [some (B, sb)] := by native_decide
example : report stored (.proj twoP) ob₀ ob₁ {B} = some ⟨[C, O], 2, [Y], []⟩ := by
  native_decide
example : report stored (.proj oneP) ob₀ ob₁ {B} = some ⟨[C, O, Y], 2, [], []⟩ := by
  native_decide
/-- Publishing it for objects too covers it. -/
example : report { stored with objects := true } (.proj twoP) ob₀ ob₁ {B} =
    some ⟨[C, O, Y], 3, [], []⟩ := by native_decide

/-! ### Covered without the fix: implicits a companion inherits

`object C extends L`, `L` gains `implicit def lp[T <: C]: Show[T]`. `lp` is an inherited member of
object `C`, so it is in `C`'s `Implicit` name hashes, and object `C` recompiles when `L` changes
(it inherits from it). Even develop is clean. It is a gap only if inherited members are missing
from the name hashes (`inhNames := false`), e.g. ancestors a bridge skips. -/

def lp : Imp := ⟨C, false, 3⟩

def co₀ : Cls → Src
  | C => { me := C, decl := { parent := some B, cpar := some L } }
  | c => gp₀ c

def co₁ : Cls → Src
  | L => { me := L, decl := { cimps := [lp] } }
  | c => co₀ c

example : picks co₀ X = [some (A, sa)] ∧ picks co₁ X = [some (C, lp)] := by native_decide
example : report develop (.proj twoP) co₀ co₁ {L} = some ⟨[C, X], 3, [], []⟩ := by native_decide
example : report stored (.proj twoP) co₀ co₁ {L} = some ⟨[C, X], 3, [], []⟩ := by native_decide
example : report { stored with inhNames := false } (.proj twoP) co₀ co₁ {L} =
    some ⟨[C], 2, [X], [C]⟩ := by native_decide

/-! ### Over-approximation: a class-side implicit on an ancestor

The summary hashes a parent's `Implicit` names whichever side they are on, so a class-side
implicit of `B` (not in the implicit scope of `Show[C]`) moves `C`'s summary. It costs nothing
extra here: it is an inherited member of `C`, so `C`'s own names move too, and develop recompiles
`X` as well. (A private one would be an extra cost of the fix; the model has no privacy.) -/

def cs₁ : Cls → Src
  | B => { me := B, decl := { parent := some A, cimps := [⟨B, false, 5⟩] } }
  | c => gp₀ c

example : report develop (.proj twoP) gp₀ cs₁ {B} = some ⟨[C, X], 3, [], [X]⟩ := by native_decide
example : report stored (.proj twoP) gp₀ cs₁ {B} = some ⟨[C, X], 3, [], [X]⟩ := by native_decide

end Zinc.ImplicitScope
