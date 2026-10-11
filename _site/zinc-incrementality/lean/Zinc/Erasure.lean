import Zinc.NonLocalAns
import Zinc.Termination

/-!
# Erasure through inheritance: renderings, witnesses and dependency edges

How should `ExtractAPI` render an inherited member, and what must reach a class whose bytecode
depends on the *erasure* of a member it inherits? The Scala 2 bridge renders inherited members
*as seen from* the inheriting class (`memberInfo`); Scala 3 renders them *as declared* in their
owner (`sym.info`) and keeps the type arguments only in `parents` (talk §7).

The language: classes with two type parameters and a parent with type arguments, a value class
`V` referenced by name, and an intersection type `W with Z` (`W` a trait). A class's bytecode
depends on erasure in three places:

* **its own members**: their descriptors;
* **bridges**: a member it declares that overrides an ancestor's member gets a bridge for each
  overridden member whose erased descriptor differs from its own;
* **forwarders**: a class with `fwd` set (mixin forwarders, or a mirror class) emits one for
  each inherited member, with that member's erasure.

A client selecting `c.n` emits the descriptor of the member found.

Erasure has three inputs here, and they fail in different places:

* **type parameters**: `M[T].m: T` erases to `Object` whatever `T` is instantiated to in a
  subclass. Erasure is a function of the declaration;
* **value classes**: `vc` erases to the erasure of `V`'s underlying type, another class's
  contents. `V`'s name hash covers the underlying type (sbt/zinc#444);
* **intersections**: `W with Z` erases to `Z` if `Z` is a class or extends `W`, and to `W`
  otherwise. The class-name hash of `Z` covers its parents, but not (in Zinc, per sbt/zinc#1844)
  whether it is a trait or a class.

An erasure-only change reaches a descendant in two hops: the declaring class must recompile,
and the descendant must notice that the declaration's erasure moved. Interfaces store each
class's own erased signatures, computed when it compiles (`Iface.ers`), so a witness built from
them is only as fresh as the declarer.

Keys, as Zinc records them:

* a descendant `d` with direct parent `p` records one inheritance key `(p, inh)` for everything its
  own compilation reads from its ancestors (across subprojects there is nothing else);
* a client selecting `c.n` records `(c, name n)`, the class-name key `(c, cls)` (its hash
  covers `c`'s parents: use-site expansion), and the owner's `(o, name n)` (Zinc's `memberRef`
  on the owner of the member found);
* a macro observing `c.n` records `(c, name n)`, and `(c, cls)` only if its reads are recorded
  faithfully (`Ext.safe`);
* erasing a type that mentions `V` or `Z` records the name of that class (`(V, und)`,
  `(Z, cls)`): the declarer names it, and so does a client (sbt/zinc#95's argument).

Options (`Rend`, `Ext`):

* rendering `asf` (Scala 2) or `decl` (Scala 3) of the name and inheritance keys;
* `wit`: an erasure witness in the name and inheritance hashes. `vcStored` is sbt/zinc#1844 as
  implemented (value-class references only); `stored` is each member's erased signature hashed at
  its definition (sbt/zinc#1844's alternative 1, retronym/zinc#26's option (a)); `fresh` is the
  same, recomputed from the current interfaces like a Merkle hash, so it does not wait for the
  declarer; `diverge` records an erasure only where it differs from the erasure of the
  as-seen-from type (generic erasure only, for Scala 2);
* `dep`: a descendant that erases an inherited signature records the names of the classes the
  erasure reads (sbt/zinc#1844's alternative 3), instead of folding the read into `(p, inh)`;
* `kind`: the class-name hash covers whether the class is a trait.

Results (checked below; counts from `lake exe exhaustive erasure`, see the end of the file):

1. `asf` undercompiles the missing bridge of `erasure-bridge-upstream-grandparent`; `decl` does
   not. With Zinc's transitive inheritance invalidation (one subproject) `asf` is clean too.
2. `asf` hashes are functions of `decl` hashes (`asf_of_decl`): `decl` is a sound
   over-approximation, and the converse fails on the precision case (`M[T,U].m: T → m: U`).
3. The class-name key: `decl` per-name hashes do not move on a type-argument change, `(c, cls)`
   does, and that suffices for clients that record it. A macro that observes a member as seen from
   `c` without recording `(c, cls)` escapes.
4. Value classes need the second hop only: a witness or a dependency edge closes them.
   Intersections need the first hop too: when `Z` turns from trait into class, neither the
   declarer nor any descendant nor any client is recompiled unless the class-name hash of `Z`
   covers its kind. Without it, no witness and no edge helps, except a witness recomputed from
   the current interfaces, which fixes descendants and clients but still leaves the declarer's
   own descriptor stale.
5. `Er_obligations`: as declared with faithful macro keys and a kind-covering class-name hash
   meets `NCompiler.Obligations` with either a recomputed witness or a dependency edge, so both
   are sound by T3a″. A stored witness cannot be proved in this framework: its soundness rests on
   the declarer being up to date, an invariant of runs, not of hashes.

`Flat.lean` reaches the value-class result independently, inside the Merkle PoC's model: its
`erasure` keys (codegen's reads of `V`, kind `.erasure`) are the dependency edge here.
-/

namespace Zinc.Erasure

inductive Cls | V | W | Z | M | A | B | X | Y
  deriving DecidableEq, Repr

def allCls : List Cls := [.V, .W, .Z, .M, .A, .B, .X, .Y]

instance : Fintype Cls := ⟨allCls.toFinset, by intro x; cases x <;> decide⟩

inductive Name | m | g
  deriving DecidableEq, Repr

def names : List Name := [.m, .g]

/-- Types: two type parameters, three base types, the value class `V` by name, and the
intersection `W with Z`. -/
inductive Ty | int | long | str | p0 | p1 | vc | wz
  deriving DecidableEq, Repr

/-- `asSeenFrom`: instantiate the enclosing class's parameters. -/
def Ty.subst (args : List Ty) : Ty → Ty
  | .p0 => args.getD 0 .p0
  | .p1 => args.getD 1 .p1
  | t => t

def ids : List Ty := [.p0, .p1]

/-- JVM descriptors. -/
inductive JTy | I | J | Str | Obj | cW | cZ
  deriving DecidableEq, Repr

def eraseBase : Ty → JTy
  | .int => .I
  | .long => .J
  | .str => .Str
  | _ => .Obj

/-- The erasure of `V`: its underlying type's. -/
def eraseV (und : Option Ty) : JTy := (und.map eraseBase).getD .Obj

/-- Does erasing the type read another class? -/
def special : Ty → Bool
  | .vc => true
  | .wz => true
  | _ => false

structure Decl where
  parent : Option (Cls × List Ty) := none
  decls : List (Name × Ty) := []
  /-- A value class's underlying type. -/
  und : Option Ty := none
  /-- Emits a forwarder for every inherited member (mixin forwarders, or a mirror class). -/
  fwd : Bool := false
  isTrait : Bool := false
  deriving DecidableEq, Repr

/-- The declaration, and the erased signatures of its own members, computed when the class was
compiled. -/
structure Iface where
  decl : Decl := {}
  ers : List (Name × JTy) := []
  deriving DecidableEq, Repr

structure Src where
  decl : Decl
  /-- Member selections `c.n`. -/
  sel : List (Cls × Name) := []
  /-- Macro observations of `c.n`'s type as seen from `c`. -/
  obs : List (Cls × Name) := []
  deriving DecidableEq, Repr

structure Out where
  iface : Iface
  /-- Override conformance errors. -/
  errs : List Name
  /-- Bridge descriptors per own member. -/
  bridges : List (Name × List JTy)
  /-- Forwarder descriptors per inherited member. -/
  fwds : List (Name × JTy)
  /-- Each selection: its type as seen from the receiver, and the descriptor it links to. -/
  descs : List (Option Ty × Option JTy)
  /-- What each macro observation saw. -/
  seen : List (Option Ty)
  deriving DecidableEq, Repr

/-! ## Pure views of an interface map -/

def depth : ℕ := 4

def linP (I : Cls → Iface) : ℕ → Cls → List Ty → List (Cls × List Ty)
  | 0, _, _ => []
  | f + 1, c, a =>
    match (I c).decl.parent with
    | some (q, qa) => (c, a) :: linP I f q (qa.map (Ty.subst a))
    | none => [(c, a)]

def chainP (I : Cls → Iface) (c : Cls) : List Cls := (linP I depth c ids).map (·.1)

/-- Erasure, from the current declarations. -/
def eraseT (I : Cls → Iface) : Ty → JTy
  | .vc => eraseV (I .V).decl.und
  | .wz => if !(I .Z).decl.isTrait || (chainP I .Z).contains .W then .cZ else .cW
  | t => eraseBase t

def entriesP (I : Cls → Iface) (n : Name) (L : List (Cls × List Ty)) : List (List Ty × Option Ty) :=
  L.map fun e => (e.2, (I e.1).decl.decls.lookup n)

/-- The first declaration, as seen from the start of the linearization. -/
def render (es : List (List Ty × Option Ty)) : Option Ty :=
  (es.filterMap fun e => e.2.map (Ty.subst e.1)).head?

/-- The type of `c.n` as seen from `c`. -/
def asfP (I : Cls → Iface) (c : Cls) (n : Name) : Option Ty :=
  render (entriesP I n (linP I depth c ids))

/-- The class whose declaration of `n` `c` inherits (or `c` itself). Zinc's rendering of a member
also tells a declared member from an inherited one, and covers `override`, so it moves when the
winner does even if the type as seen from `c` does not. -/
def winnerP (I : Cls → Iface) (c : Cls) (n : Name) : Option Cls :=
  (((chainP I c).map fun e => (e, (I e).decl.decls.lookup n)).find? (·.2.isSome)).map (·.1)

/-! ## Queries

A query names the class it reads and *why*: the context says which tree the compiler was
typing. The extractor maps each query to a key by its context, which is how the bridge knows
whether a read belongs to a client's selection or to a descendant's own checks. -/

inductive Ctx
  /-- A descendant reading its ancestors through its direct parent `p`. -/
  | inh (p : Cls)
  /-- A client selecting through `c`. -/
  | sel (c : Cls)
  /-- A client reading the owner of the member it selected (Zinc's `memberRef` on the owner). -/
  | ownr
  /-- A macro observing `c.n`. -/
  | obs (c : Cls) (n : Name)
  /-- Erasing an own member. -/
  | own
  deriving DecidableEq, Repr

inductive Q
  | parent (x : Ctx)
  | decl (x : Ctx) (n : Name)
  /-- The erasure of the type `t` of member `n` (addressed to the class it reads). -/
  | er (x : Ctx) (n : Name) (t : Ty)
  deriving DecidableEq, Repr

inductive AnsV
  | par (p : Option (Cls × List Ty))
  | ty (t : Option Ty)
  | j (x : JTy)
  deriving DecidableEq, Repr

def answer (I : Cls → Iface) : Cls × Q → AnsV
  | (c, .parent _) => .par (I c).decl.parent
  | (c, .decl _ n) => .ty ((I c).decl.decls.lookup n)
  | (_, .er _ _ t) => .j (eraseT I t)

/-- The class an erasure query is addressed to. -/
def homeC : Ty → Cls
  | .wz => .Z
  | _ => .V

abbrev T := Task (Cls × Q) (fun _ => AnsV)

def askQ (c : Cls) (q : Q) : T AnsV := Task.ask (c, q) Task.pure

@[simp] theorem run_askQ (c : Cls) (q : Q) (e : Task.Env (Cls × Q) (fun _ => AnsV)) :
    (askQ c q).run e = e (c, q) := rfl
@[simp] theorem trace_askQ (c : Cls) (q : Q) (e : Task.Env (Cls × Q) (fun _ => AnsV)) :
    (askQ c q).trace e = [(c, q)] := rfl

/-! ## The compiler -/

/-- `c` and its ancestors, each with its type arguments as seen from the start (`a` for `c`). -/
def linT (x : Ctx) : ℕ → Cls → List Ty → T (List (Cls × List Ty))
  | 0, _, _ => pure []
  | f + 1, c, a => do
    match ← askQ c (.parent x) with
    | .par (some (q, qa)) => do
      let l ← linT x f q (qa.map (Ty.subst a))
      pure ((c, a) :: l)
    | _ => pure [(c, a)]

/-- The declarations of `n` along a linearization. -/
def entriesT (x : Ctx) (n : Name) : List (Cls × List Ty) → T (List (List Ty × Option Ty))
  | [] => pure []
  | (c, a) :: rest => do
    let r ← askQ c (.decl x n)
    let l ← entriesT x n rest
    pure ((a, match r with | .ty t => t | _ => none) :: l)

/-- Erase declared types; a type that mentions another class asks it. -/
def erasT (x : Ctx) : List (Name × Ty) → T (List (Name × JTy))
  | [] => pure []
  | (n, t) :: rest => do
    let j ← if special t then do
        match ← askQ (homeC t) (.er x n t) with
        | .j y => pure y
        | _ => pure .Obj
      else pure (eraseBase t)
    let l ← erasT x rest
    pure ((n, j) :: l)

structure PerName where
  err : Bool
  bridges : List JTy
  fwd : Option JTy

/-- A descendant's own checks and codegen for one name, against its parent `p`'s chain `L`. -/
def nameT (d : Decl) (p : Cls) (L : List (Cls × List Ty)) (ownJ : List (Name × JTy)) (n : Name) :
    T PerName := do
  let es ← entriesT (.inh p) n L
  let js ← erasT (.inh p) ((es.filterMap (·.2)).map (n, ·))
  let inh := render es
  match d.decls.lookup n with
  | some t =>
    let jo := (ownJ.lookup n).getD .Obj
    pure ⟨inh.isSome && inh != some t, ((js.map (·.2)).filter (· != jo)).dedup, none⟩
  | none => pure ⟨false, [], if d.fwd then (js.map (·.2)).head? else none⟩

def namesT (d : Decl) (p : Cls) (L : List (Cls × List Ty)) (ownJ : List (Name × JTy)) :
    List Name → T (List (Name × PerName))
  | [] => pure []
  | n :: rest => do
    let r ← nameT d p L ownJ n
    let l ← namesT d p L ownJ rest
    pure ((n, r) :: l)

def descT (d : Decl) (ownJ : List (Name × JTy)) : T (List (Name × PerName)) :=
  match d.parent with
  | none => pure []
  | some (p, a) => do
    let L ← linT (.inh p) depth p a
    namesT d p L ownJ names

/-- The class of the first declaration along a linearization. -/
def winner : List (Cls × List Ty) → List (List Ty × Option Ty) → Option Cls
  | (c, _) :: L, e :: es => if e.2.isSome then some c else winner L es
  | _, _ => none

/-- A client's descriptor for `c.n`: the owner's declaration, erased. -/
def descOf (c : Cls) (n : Name) : Option Cls → T (Option JTy)
  | none => pure none
  | some o => do
    match ← askQ o (.decl .ownr n) with
    | .ty (some t) => do
      let js ← erasT (.sel c) [(n, t)]
      pure (js.head?.map (·.2))
    | _ => pure none

def selsT : List (Cls × Name) → T (List (Option Ty × Option JTy))
  | [] => pure []
  | (c, n) :: rest => do
    let L ← linT (.sel c) depth c ids
    let es ← entriesT (.sel c) n L
    let j ← descOf c n (winner L es)
    let l ← selsT rest
    pure ((render es, j) :: l)

def obsT : List (Cls × Name) → T (List (Option Ty))
  | [] => pure []
  | (c, n) :: rest => do
    let L ← linT (.obs c n) depth c ids
    let es ← entriesT (.obs c n) n L
    let l ← obsT rest
    pure (render es :: l)

def unitF (s : Src) : T Out := do
  let ownJ ← erasT .own s.decl.decls
  let r ← descT s.decl ownJ
  let descs ← selsT s.sel
  let seen ← obsT s.obs
  pure ⟨⟨s.decl, ownJ⟩, r.filterMap (fun e => if e.2.err then some e.1 else none),
    r.filterMap (fun e => if e.2.bridges.isEmpty then none else some (e.1, e.2.bridges)),
    r.filterMap (fun e => e.2.fwd.map (e.1, ·)), descs, seen⟩

/-! ## Keys and hashes -/

inductive K
  | name (n : Name)
  /-- The class-name key: its hash covers the class's parents (and, with `kind`, its kind). -/
  | cls
  /-- The inheritance edge: the class's whole API. -/
  | inh
  /-- The name `V`: its hash covers the underlying type. -/
  | und
  deriving DecidableEq, Repr

inductive Rend | asf | decl
  deriving DecidableEq, Repr

inductive Wit | none | vcStored | stored | fresh | diverge
  deriving DecidableEq, Repr

/-- Extractor and hash options. -/
structure Ext where
  /-- A macro's reads are recorded as a client's (its reads of parents under the class-name key). -/
  safe : Bool := false
  wit : Wit := .none
  /-- A descendant records the names of the classes its erasure of an inherited signature reads. -/
  dep : Bool := false
  /-- The class-name hash covers whether the class is a trait. -/
  kind : Bool := false
  deriving DecidableEq, Repr

inductive H
  | ty (t : Option Ty) (o : Option Cls)
  | ents (l : List (Cls × Option Ty))
  | chain (l : List (Cls × Option (Cls × List Ty))) (ks : List Bool)
  | asfInh (lin : List (Cls × List Ty)) (ts : List (Option Ty)) (os : List (Option Cls))
  | inh (l : List (Cls × Option (Cls × List Ty) × List (Name × Ty)))
  | j (x : JTy)
  /-- A name hash with a witness: the erasure of each declaration on the chain. -/
  | nm (b : H) (w : List (Cls × Option JTy))
  /-- An inheritance hash with a witness: erased signatures per class on the chain. -/
  | inhW (b : H) (w : List (Cls × List (Name × JTy)))
  deriving DecidableEq, Repr

/-- Parents and declarations along the chain: the as-declared API. -/
def declsP (I : Cls → Iface) (c : Cls) : List (Cls × Option (Cls × List Ty) × List (Name × Ty)) :=
  (chainP I c).map fun e => (e, (I e).decl.parent, (I e).decl.decls)

/-- The witness in a name hash. -/
def witN (x : Ext) (I : Cls → Iface) (c : Cls) (n : Name) : List (Cls × Option JTy) :=
  match x.wit with
  | .fresh => (chainP I c).map fun e => (e, ((I e).decl.decls.lookup n).map (eraseT I))
  | .stored => (chainP I c).map fun e => (e, (I e).ers.lookup n)
  | .vcStored => (chainP I c).map fun e =>
      (e, if (I e).decl.decls.lookup n = some .vc then (I e).ers.lookup n else none)
  | _ => []

/-- The witness in an inheritance hash. -/
def witI (x : Ext) (I : Cls → Iface) (c : Cls) : List (Cls × List (Name × JTy)) :=
  match x.wit with
  | .fresh => (chainP I c).map fun e => (e, (I e).decl.decls.map fun d => (d.1, eraseT I d.2))
  | .stored => (chainP I c).map fun e => (e, (I e).ers)
  | .vcStored => (chainP I c).map fun e =>
      (e, ((I e).decl.decls.filter (·.2 == .vc)).map fun d => (d.1, ((I e).ers.lookup d.1).getD .Obj))
  | .diverge => (linP I depth c ids).map fun e =>
      (e.1, (I e.1).decl.decls.filterMap fun d =>
        if eraseT I d.2 ≠ eraseT I (Ty.subst e.2 d.2) then some (d.1, eraseT I d.2) else none)
  | .none => []

def π (r : Rend) (x : Ext) (I : Cls → Iface) (c : Cls) : K → H
  | .name n =>
    .nm (match r with
      | .asf => .ty (asfP I c n) (winnerP I c n)
      | .decl => .ents ((chainP I c).map fun e => (e, (I e).decl.decls.lookup n))) (witN x I c n)
  | .cls => .chain ((chainP I c).map fun e => (e, (I e).decl.parent))
      (if x.kind then (chainP I c).map fun e => (I e).decl.isTrait else [])
  | .inh =>
    .inhW (match r with
      | .asf => .asfInh (linP I depth c ids) (names.map (asfP I c)) (names.map (winnerP I c))
      | .decl => .inh (declsP I c)) (witI x I c)
  | .und => .j (eraseV (I c).decl.und)

/-- The key of a type's erasure: the name of the class it reads. -/
def homeK (t : Ty) : Cls × K := (homeC t, if t = .wz then .cls else .und)

/-- The key a query is recorded under. -/
def keyOf (x : Ext) : Cls × Q → Cls × K
  | (_, .parent (.inh p)) => (p, .inh)
  | (_, .decl (.inh p) _) => (p, .inh)
  | (_, .er (.inh p) _ t) => if x.dep then homeK t else (p, .inh)
  | (_, .parent (.sel c)) => (c, .cls)
  | (_, .decl (.sel c) n) => (c, .name n)
  | (_, .er (.sel c) n t) => if x.wit = .fresh ∨ x.wit = .stored then (c, .name n) else homeK t
  | (o, .decl .ownr n) => (o, .name n)
  | (_, .parent (.obs c n)) => if x.safe then (c, .cls) else (c, .name n)
  | (_, .decl (.obs c _) n) => (c, .name n)
  | (_, .er _ _ t) => homeK t
  | (c, _) => (c, .cls)

/-- Which queries a key stands for. -/
def scope (x : Ext) (I : Cls → Iface) : Cls × Q → Prop
  | (e, .parent (.inh p)) => e ∈ chainP I p
  | (e, .decl (.inh p) _) => e ∈ chainP I p
  | (e, .er (.inh p) n t) => e = homeC t ∧ special t = true ∧
      (x.dep = true ∨ ∃ d ∈ chainP I p, (n, t) ∈ (I d).decl.decls)
  | (e, .parent (.sel c)) => e ∈ chainP I c
  | (e, .decl (.sel c) _) => e ∈ chainP I c
  | (e, .er (.sel c) n t) => e = homeC t ∧ special t = true ∧
      (¬(x.wit = .fresh ∨ x.wit = .stored) ∨ ∃ d ∈ chainP I c, (I d).decl.decls.lookup n = some t)
  | (_, .decl .ownr _) => True
  | (e, .parent (.obs c _)) => e ∈ chainP I c
  | (e, .decl (.obs c _) _) => e ∈ chainP I c
  | (e, .er .own _ t) => e = homeC t ∧ special t = true
  | _ => False

def keys (x : Ext) (_ : Cls) (tr : List (Cls × Q)) : Finset (Cls × K) :=
  (tr.map (keyOf x)).toFinset

/-- Own members' erased signatures against a set of declarations. -/
def ownErs (I : Cls → Iface) (d : Decl) : List (Name × JTy) := d.decls.map fun p => (p.1, eraseT I p.2)

/-- Joint compilation: a group member's interface stores the erasures computed against the
group's declarations. -/
def declI (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface) (v : Cls) : Iface :=
  if v ∈ G then { decl := (src v).decl } else I v

def matI (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface) (v : Cls) : Iface :=
  if v ∈ G then ⟨(src v).decl, ownErs (declI G src I) (src v).decl⟩ else I v

def group (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface) (u : Cls) : Out :=
  (unitF (src u)).run (answer (matI G src I))

def Er (r : Rend) (x : Ext) : NCompiler Cls Src Out Iface K H Q (fun _ => AnsV) where
  unit := unitF
  group := group
  iface := Out.iface
  answer := answer
  π := π r x
  hashDeps := fun I c => insert .V ((chainP I c).toFinset ∪ (chainP I .Z).toFinset)
  keys := keys x
  covers := fun I q k => k = keyOf x q ∧ scope x I q

/-! ## As declared determines as seen from

Without a witness, `π .asf` is determined by `π .decl`, key by key (the name key with the
class-name key, and the inheritance key on its own). So as declared can only invalidate *more*.
The converse fails on the precision case below. -/

theorem mem_of_map_pair {α β : Type} {l l' : List α} {f g : α → β}
    (h : l.map (fun e => (e, f e)) = l'.map (fun e => (e, g e))) {e : α} (he : e ∈ l) :
    e ∈ l' ∧ f e = g e := by
  have : (e, f e) ∈ l'.map (fun e => (e, g e)) := h ▸ List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨e', he', hee⟩ := List.mem_map.1 this
  simp only [Prod.mk.injEq] at hee
  obtain ⟨rfl, hfg⟩ := hee
  exact ⟨he', hfg.symm⟩

theorem map_pair_fst {α β : Type} {l l' : List α} {f g : α → β}
    (h : l.map (fun e => (e, f e)) = l'.map (fun e => (e, g e))) : l = l' := by
  have := congrArg (List.map Prod.fst) h
  simpa [List.map_map, Function.comp_def] using this

theorem linP_congr (I I' : Cls → Iface) :
    ∀ f c a, (∀ e ∈ (linP I f c a).map (·.1), (I e).decl.parent = (I' e).decl.parent) →
      linP I f c a = linP I' f c a := by
  intro f
  induction f with
  | zero => intro c a _; rfl
  | succ f ih =>
    intro c a h
    have hc : (I c).decl.parent = (I' c).decl.parent := h c (by
      simp only [linP]; split <;> simp)
    simp only [linP, ← hc]
    split
    · rename_i q qa hq
      congr 1
      apply ih
      intro e he
      apply h
      simp only [linP, hq, List.map_cons, List.mem_cons]
      exact Or.inr he
    · rfl

theorem chain_fst (I : Cls → Iface) :
    ∀ f c a a', (linP I f c a).map (·.1) = (linP I f c a').map (·.1) := by
  intro f
  induction f with
  | zero => intro c a a'; rfl
  | succ f ih =>
    intro c a a'
    simp only [linP]
    split
    · simp only [List.map_cons]; rw [ih]
    · rfl

theorem mem_chainP_self (I : Cls → Iface) (c : Cls) : c ∈ chainP I c := by
  simp only [chainP, depth, linP]; split <;> simp

theorem entriesP_congr (I I' : Cls → Iface) (n : Name) (L : List (Cls × List Ty))
    (h : ∀ e ∈ L.map (·.1), (I e).decl.decls.lookup n = (I' e).decl.decls.lookup n) :
    entriesP I n L = entriesP I' n L := by
  unfold entriesP
  apply List.map_congr_left
  intro e he
  rw [h e.1 (List.mem_map.2 ⟨e, he, rfl⟩)]

/-- **Item 2.** The name key as seen from is determined by the as-declared name key and the
class-name key. -/
theorem asf_of_decl (x : Ext) (hw : x.wit = .none) (I I' : Cls → Iface) (c : Cls) (n : Name)
    (hc : π .decl x I c .cls = π .decl x I' c .cls)
    (hn : π .decl x I c (.name n) = π .decl x I' c (.name n)) :
    π .asf x I c (.name n) = π .asf x I' c (.name n) := by
  simp only [π, H.chain.injEq, H.nm.injEq, H.ents.injEq, witN, hw] at hc hn
  have hlin : linP I depth c ids = linP I' depth c ids :=
    linP_congr I I' _ _ _ fun e he => (mem_of_map_pair hc.1 he).2
  simp only [π, asfP, H.nm.injEq, H.ty.injEq, witN, hw, and_true]
  refine ⟨?_, by simp only [winnerP, hn.1]⟩
  rw [← hlin]
  congr 1
  apply entriesP_congr
  intro e he
  exact (mem_of_map_pair hn.1 he).2

/-- …and the inheritance key as seen from by the as-declared one. -/
theorem asfInh_of_declInh (x : Ext) (hw : x.wit = .none) (I I' : Cls → Iface) (c : Cls)
    (h : π .decl x I c .inh = π .decl x I' c .inh) : π .asf x I c .inh = π .asf x I' c .inh := by
  simp only [π, H.inhW.injEq, H.inh.injEq, witI, hw, and_true, declsP] at h
  have hp : ∀ e ∈ chainP I c,
      (I e).decl.parent = (I' e).decl.parent ∧ (I e).decl.decls = (I' e).decl.decls := by
    intro e he
    have := (mem_of_map_pair (f := fun e => ((I e).decl.parent, (I e).decl.decls))
      (g := fun e => ((I' e).decl.parent, (I' e).decl.decls)) h he).2
    simpa using this
  have hlin : linP I depth c ids = linP I' depth c ids :=
    linP_congr I I' _ _ _ fun e he => (hp e he).1
  have hchain : chainP I c = chainP I' c := by unfold chainP; rw [hlin]
  simp only [π, H.inhW.injEq, H.asfInh.injEq, witI, hw, and_true]
  refine ⟨hlin, ?_, ?_⟩
  · apply List.map_congr_left
    intro n _
    unfold asfP
    rw [← hlin, entriesP_congr I I' n _ fun e he => by rw [(hp e he).2]]
  · apply List.map_congr_left
    intro n _
    unfold winnerP
    rw [← hchain, List.map_congr_left fun e he => by rw [(hp e he).2]]

/-! ## Soundness

As declared, with faithful macro keys and a kind-covering class-name hash, meets
`NCompiler.Obligations` with a recomputed witness or with the dependency edge. -/

section obligations

abbrev Env := Task.Env (Cls × Q) (fun _ => AnsV)

theorem run_linT (I : Cls → Iface) (x : Ctx) :
    ∀ f c a, (linT x f c a).run (answer I) = linP I f c a := by
  intro f
  induction f with
  | zero => intro c a; rfl
  | succ f ih =>
    intro c a
    simp only [linT, linP, Task.bind_eq, Task.run_bind, run_askQ, answer]
    rcases h : (I c).decl.parent with _ | ⟨q, qa⟩
    · simp
    · simp [ih]

theorem trace_linT (I : Cls → Iface) (x : Ctx) :
    ∀ f c a q, q ∈ (linT x f c a).trace (answer I) →
      q.2 = .parent x ∧ q.1 ∈ (linP I f c a).map (·.1) := by
  intro f
  induction f with
  | zero => intro c a q hq; simp [linT] at hq
  | succ f ih =>
    intro c a q hq
    simp only [linT, Task.bind_eq, Task.trace_bind, trace_askQ, run_askQ, answer,
      List.singleton_append, List.mem_cons] at hq
    rcases hq with rfl | hq
    · refine ⟨rfl, ?_⟩
      simp only [linP]; split <;> simp
    · rcases h : (I c).decl.parent with _ | ⟨p, pa⟩
      · simp [h] at hq
      · simp only [h, Task.trace_bind, Task.pure_eq, Task.trace_pure,
          List.append_nil] at hq
        obtain ⟨h1, h2⟩ := ih _ _ q hq
        refine ⟨h1, ?_⟩
        simp only [linP, h, List.map_cons, List.mem_cons]
        exact Or.inr h2

theorem run_entriesT (I : Cls → Iface) (x : Ctx) (n : Name) :
    ∀ L, (entriesT x n L).run (answer I) = entriesP I n L := by
  intro L
  induction L with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨c, a⟩ := e
    simp [entriesT, entriesP, answer, ih]

theorem trace_entriesT (I : Cls → Iface) (x : Ctx) (n : Name) :
    ∀ L q, q ∈ (entriesT x n L).trace (answer I) → q.2 = .decl x n ∧ q.1 ∈ L.map (·.1) := by
  intro L
  induction L with
  | nil => intro q hq; simp [entriesT] at hq
  | cons e rest ih =>
    intro q hq
    obtain ⟨c, a⟩ := e
    simp only [entriesT, Task.bind_eq, Task.trace_bind, trace_askQ, run_askQ, Task.pure_eq,
      Task.trace_pure, List.append_nil, List.singleton_append, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp
    · obtain ⟨h1, h2⟩ := ih q hq
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem eraseT_base (I : Cls → Iface) (t : Ty) (h : special t = false) : eraseT I t = eraseBase t := by
  cases t <;> simp_all [special, eraseT]

theorem run_erasT (I : Cls → Iface) (x : Ctx) :
    ∀ ns, (erasT x ns).run (answer I) = ns.map fun p => (p.1, eraseT I p.2) := by
  intro ns
  induction ns with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨n, t⟩ := p
    cases ht : special t
    · simp [erasT, ht, Task.bind, ih, eraseT_base I t ht]
    · simp [erasT, ht, Task.bind, answer, askQ, ih]

theorem trace_erasT (I : Cls → Iface) (x : Ctx) :
    ∀ ns q, q ∈ (erasT x ns).trace (answer I) →
      ∃ n t, q = (homeC t, .er x n t) ∧ special t = true ∧ (n, t) ∈ ns := by
  intro ns
  induction ns with
  | nil => intro q hq; simp [erasT] at hq
  | cons p rest ih =>
    intro q hq
    obtain ⟨n, t⟩ := p
    cases ht : special t
    · simp [erasT, ht, Task.bind] at hq
      obtain ⟨n', t', h1, h2, h3⟩ := ih q hq
      exact ⟨n', t', h1, h2, List.mem_cons_of_mem _ h3⟩
    · simp [erasT, ht, answer, askQ, Task.bind] at hq
      rcases hq with rfl | hq
      · exact ⟨n, t, rfl, ht, List.mem_cons_self⟩
      · obtain ⟨n', t', h1, h2, h3⟩ := ih q hq
        exact ⟨n', t', h1, h2, List.mem_cons_of_mem _ h3⟩

theorem lookup_mem {n : Name} {t : Ty} : ∀ {l : List (Name × Ty)}, l.lookup n = some t → (n, t) ∈ l
  | [], h => by simp at h
  | (k, v) :: rest, h => by
    by_cases hk : n = k
    · subst hk
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      subst h
      simp
    · have : (n == k) = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- What a descendant reads, through its parent `p`. -/
def inhScope (I : Cls → Iface) (p : Cls) (q : Cls × Q) : Prop :=
  ((q.2 = .parent (.inh p) ∨ ∃ n, q.2 = .decl (.inh p) n) ∧ q.1 ∈ chainP I p) ∨
    ∃ n t, q = (homeC t, .er (.inh p) n t) ∧ special t = true ∧
      ∃ d ∈ chainP I p, (n, t) ∈ (I d).decl.decls

theorem trace_nameT (I : Cls → Iface) (d : Decl) (p : Cls) (a : List Ty)
    (ownJ : List (Name × JTy)) (n : Name) (q : Cls × Q)
    (hq : q ∈ (nameT d p (linP I depth p a) ownJ n).trace (answer I)) : inhScope I p q := by
  have hch : (linP I depth p a).map (·.1) = chainP I p := chain_fst I depth p a ids
  simp only [nameT, Task.bind_eq, Task.trace_bind, List.mem_append] at hq
  rcases hq with hq | hq | hq
  · obtain ⟨h1, h2⟩ := trace_entriesT I _ n _ q hq
    exact Or.inl ⟨Or.inr ⟨n, h1⟩, hch ▸ h2⟩
  · rw [run_entriesT] at hq
    obtain ⟨n', t, rfl, hs, hm⟩ := trace_erasT I _ _ q hq
    simp only [List.mem_map, List.mem_filterMap, entriesP, Prod.mk.injEq] at hm
    obtain ⟨t', ⟨_, ⟨e, he, rfl⟩, hlk⟩, rfl, rfl⟩ := hm
    refine Or.inr ⟨n, t', rfl, hs, e.1, ?_, lookup_mem hlk⟩
    rw [← hch]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  · split at hq <;> simp at hq

theorem trace_namesT (I : Cls → Iface) (d : Decl) (p : Cls) (a : List Ty)
    (ownJ : List (Name × JTy)) :
    ∀ ns q, q ∈ (namesT d p (linP I depth p a) ownJ ns).trace (answer I) → inhScope I p q := by
  intro ns
  induction ns with
  | nil => intro q hq; simp [namesT] at hq
  | cons n rest ih =>
    intro q hq
    simp only [namesT, Task.bind_eq, Task.trace_bind, Task.pure_eq, Task.trace_pure,
      List.append_nil, List.mem_append] at hq
    rcases hq with hq | hq
    · exact trace_nameT I d p a ownJ n q hq
    · exact ih q hq

theorem trace_descT (I : Cls → Iface) (d : Decl) (ownJ : List (Name × JTy)) (q : Cls × Q)
    (hq : q ∈ (descT d ownJ).trace (answer I)) : ∃ p, inhScope I p q := by
  unfold descT at hq
  split at hq
  · simp at hq
  · rename_i p a _
    refine ⟨p, ?_⟩
    have hch : (linP I depth p a).map (·.1) = chainP I p := chain_fst I depth p a ids
    simp only [Task.bind_eq, Task.trace_bind, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨h1, h2⟩ := trace_linT I _ _ _ _ q hq
      exact Or.inl ⟨Or.inl h1, hch ▸ h2⟩
    · rw [run_linT] at hq
      exact trace_namesT I d p a ownJ names q hq

theorem winner_mem : ∀ (L : List (Cls × List Ty)) (es : List (List Ty × Option Ty)) (o : Cls),
    winner L es = some o → o ∈ L.map (·.1)
  | [], _, _, h => by simp [winner] at h
  | (_ :: _), [], _, h => by simp [winner] at h
  | (c, _) :: L, e :: es, o, h => by
    simp only [winner] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (winner_mem L es o h)

/-- What a client reads, selecting `c.n`. -/
def selScope (I : Cls → Iface) (c : Cls) (n : Name) (q : Cls × Q) : Prop :=
  ((q.2 = .parent (.sel c) ∨ q.2 = .decl (.sel c) n) ∧ q.1 ∈ chainP I c) ∨
    q.2 = .decl .ownr n ∨
    ∃ t, q = (homeC t, .er (.sel c) n t) ∧ special t = true ∧
      ∃ d ∈ chainP I c, (I d).decl.decls.lookup n = some t

theorem trace_descOf (I : Cls → Iface) (c : Cls) (n : Name) (oo : Option Cls)
    (ho : ∀ o, oo = some o → o ∈ chainP I c) (q : Cls × Q)
    (hq : q ∈ (descOf c n oo).trace (answer I)) : selScope I c n q := by
  cases oo with
  | none => simp [descOf] at hq
  | some o =>
    simp only [descOf, Task.bind_eq, Task.trace_bind, trace_askQ, run_askQ, answer,
      List.singleton_append, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Or.inr (Or.inl rfl)
    · rcases hlk : (I o).decl.decls.lookup n with _ | t
      · simp [hlk] at hq
      · simp only [hlk, Task.bind_eq, Task.trace_bind, Task.pure_eq, Task.trace_pure,
          List.append_nil] at hq
        obtain ⟨n', t', rfl, hs, hm⟩ := trace_erasT I _ _ q hq
        simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact Or.inr (Or.inr ⟨t', rfl, hs, o, ho o rfl, hlk⟩)

theorem trace_selsT (I : Cls → Iface) :
    ∀ body q, q ∈ (selsT body).trace (answer I) → ∃ c n, selScope I c n q := by
  intro body
  induction body with
  | nil => intro q hq; simp [selsT] at hq
  | cons e rest ih =>
    intro q hq
    obtain ⟨c, n⟩ := e
    simp only [selsT, Task.bind_eq, Task.trace_bind, Task.pure_eq, Task.trace_pure,
      List.append_nil, List.mem_append] at hq
    rcases hq with hq | hq | hq | hq
    · obtain ⟨h1, h2⟩ := trace_linT I _ _ _ _ q hq
      exact ⟨c, n, Or.inl ⟨Or.inl h1, h2⟩⟩
    · rw [run_linT] at hq
      obtain ⟨h1, h2⟩ := trace_entriesT I _ n _ q hq
      exact ⟨c, n, Or.inl ⟨Or.inr h1, h2⟩⟩
    · rw [run_linT, run_entriesT] at hq
      exact ⟨c, n, trace_descOf I c n _ (fun o h => winner_mem _ _ o h) q hq⟩
    · exact ih q hq

theorem trace_obsT (I : Cls → Iface) :
    ∀ body q, q ∈ (obsT body).trace (answer I) → ∃ c n,
      (q.2 = .parent (.obs c n) ∨ q.2 = .decl (.obs c n) n) ∧ q.1 ∈ chainP I c := by
  intro body
  induction body with
  | nil => intro q hq; simp [obsT] at hq
  | cons e rest ih =>
    intro q hq
    obtain ⟨c, n⟩ := e
    simp only [obsT, Task.bind_eq, Task.trace_bind, Task.pure_eq, Task.trace_pure,
      List.append_nil, List.mem_append] at hq
    rcases hq with hq | hq | hq
    · obtain ⟨h1, h2⟩ := trace_linT I _ _ _ _ q hq
      exact ⟨c, n, Or.inl h1, h2⟩
    · rw [run_linT] at hq
      obtain ⟨h1, h2⟩ := trace_entriesT I _ n _ q hq
      exact ⟨c, n, Or.inr h1, h2⟩
    · exact ih q hq

theorem scope_unitF (x : Ext) (I : Cls → Iface) (s : Src) :
    ∀ q ∈ (unitF s).trace (answer I), scope x I q := by
  intro q hq
  simp only [unitF, Task.bind_eq, Task.trace_bind, Task.pure_eq, Task.trace_pure,
    List.append_nil, List.mem_append] at hq
  obtain ⟨e, q⟩ := q
  rcases hq with hq | hq | hq | hq
  · obtain ⟨n, t, h, hs, _⟩ := trace_erasT I _ _ _ hq
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hs⟩
  · obtain ⟨p, ⟨hq, he⟩ | ⟨n, t, h, hs, d, hd, hm⟩⟩ := trace_descT I _ _ _ hq
    · rcases hq with h | ⟨n, h⟩ <;> (cases h; exact he)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hs, Or.inr ⟨d, hd, hm⟩⟩
  · obtain ⟨c, n, ⟨hq, he⟩ | h | ⟨t, h, hs, d, hd, hm⟩⟩ := trace_selsT I _ _ hq
    · rcases hq with h | h <;> (cases h; exact he)
    · cases h; trivial
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hs, Or.inr ⟨d, hd, hm⟩⟩
  · obtain ⟨c, n, h, he⟩ := trace_obsT I _ _ hq
    rcases h with h | h <;> (cases h; exact he)

theorem eraseT_congr (I I' : Cls → Iface) (hV : (I .V).decl = (I' .V).decl)
    (hZ : ∀ e ∈ chainP I .Z, (I e).decl = (I' e).decl) (t : Ty) : eraseT I t = eraseT I' t := by
  have hch : chainP I .Z = chainP I' .Z := by
    unfold chainP; rw [linP_congr I I' _ _ _ fun e he => by rw [hZ e he]]
  cases t <;> simp only [eraseT, hV, hch, hZ .Z (mem_chainP_self I .Z)]

theorem iface_unitF (s : Src) (J : Cls → Iface) :
    ((unitF s).run (answer J)).iface = ⟨s.decl, ownErs J s.decl⟩ := by
  simp [unitF, run_erasT, ownErs]

theorem matI_eq (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface) :
    NCompiler.override I G (Out.iface ∘ group G src I) = matI G src I := by
  funext v
  simp only [NCompiler.override, Function.comp, group, iface_unitF]
  by_cases hv : v ∈ G
  · simp only [hv, ite_true, matI]
    congr 1
    unfold ownErs
    apply List.map_congr_left
    intro p _
    congr 1
    apply eraseT_congr
    · by_cases h : Cls.V ∈ G <;> simp [matI, declI, h]
    · intro e _
      by_cases h : e ∈ G <;> simp [matI, declI, h]
  · simp [hv, matI]

theorem Er_comp (r : Rend) (x : Ext) :
    ∀ (G : Finset Cls) (src : Cls → Src) (I : Cls → Iface), ∀ d ∈ G,
      (Er r x).group G src I d = ((Er r x).unit (src d)).run
        ((Er r x).answer (NCompiler.override I G ((Er r x).iface ∘ (Er r x).group G src I))) := by
  intro G src I d _
  show group G src I d = (unitF (src d)).run (answer (NCompiler.override I G (Out.iface ∘ group G src I)))
  rw [matI_eq]
  rfl

theorem Er_locality (r : Rend) (x : Ext) (I I' : Cls → Iface) (c : Cls)
    (h : ∀ d ∈ (Er r x).hashDeps I c, I d = I' d) (k : K) :
    (Er r x).π I c k = (Er r x).π I' c k := by
  have hch : ∀ e ∈ chainP I c, I e = I' e := fun e he =>
    h e (Finset.mem_insert_of_mem (Finset.mem_union_left _ (List.mem_toFinset.2 he)))
  have hZ : ∀ e ∈ chainP I .Z, I e = I' e := fun e he =>
    h e (Finset.mem_insert_of_mem (Finset.mem_union_right _ (List.mem_toFinset.2 he)))
  have hV : I .V = I' .V := h .V (Finset.mem_insert_self _ _)
  have her : ∀ t, eraseT I t = eraseT I' t :=
    eraseT_congr I I' (by rw [hV]) (fun e he => by rw [hZ e he])
  have her' : eraseT I = eraseT I' := funext her
  have hlin : linP I depth c ids = linP I' depth c ids :=
    linP_congr I I' _ _ _ fun e he => by rw [hch e he]
  have hchain : chainP I c = chainP I' c := by unfold chainP; rw [hlin]
  have hmap : ∀ {β : Type} (f : (Cls → Iface) → Cls → β),
      (∀ e ∈ chainP I c, f I e = f I' e) → (chainP I c).map (f I) = (chainP I' c).map (f I') := by
    intro β f hf
    rw [← hchain]
    exact List.map_congr_left hf
  have hasf : ∀ n, asfP I c n = asfP I' c n := by
    intro n
    unfold asfP
    rw [← hlin, entriesP_congr I I' n _ fun e he => by rw [hch e he]]
  have hwin : ∀ n, winnerP I c n = winnerP I' c n := by
    intro n
    unfold winnerP
    rw [hmap (fun I e => (e, (I e).decl.decls.lookup n)) fun e he => by rw [hch e he]]
  have hdecls : declsP I c = declsP I' c :=
    hmap (fun I e => (e, (I e).decl.parent, (I e).decl.decls)) fun e he => by rw [hch e he]
  have hwN : ∀ n, witN x I c n = witN x I' c n := by
    intro n
    unfold witN
    split
    · exact hmap (fun I e => (e, ((I e).decl.decls.lookup n).map (eraseT I))) fun e he => by
        rw [hch e he, her']
    · exact hmap (fun I e => (e, (I e).ers.lookup n)) fun e he => by rw [hch e he]
    · exact hmap (fun I e => (e, if (I e).decl.decls.lookup n = some .vc then (I e).ers.lookup n
        else none)) fun e he => by rw [hch e he]
    · rfl
  have hwI : witI x I c = witI x I' c := by
    unfold witI
    split
    · exact hmap (fun I e => (e, (I e).decl.decls.map fun d => (d.1, eraseT I d.2))) fun e he => by
        rw [hch e he]; simp only [her]
    · exact hmap (fun I e => (e, (I e).ers)) fun e he => by rw [hch e he]
    · exact hmap (fun I e => (e, ((I e).decl.decls.filter (·.2 == .vc)).map fun d =>
        (d.1, ((I e).ers.lookup d.1).getD .Obj))) fun e he => by rw [hch e he]
    · rw [← hlin]
      apply List.map_congr_left
      intro e he
      have he' : e.1 ∈ chainP I c := List.mem_map.2 ⟨e, he, rfl⟩
      rw [hch e.1 he']
      simp only [her]
    · rfl
  show π r x I c k = π r x I' c k
  cases k with
  | name n =>
    cases r
    · simp only [π, hasf, hwN, hwin]
    · simp only [π, hwN]
      rw [hmap (fun I e => (e, (I e).decl.decls.lookup n)) fun e he => by rw [hch e he]]
  | cls =>
    simp only [π]
    rw [hmap (fun I e => (e, (I e).decl.parent)) fun e he => by rw [hch e he],
      hmap (fun I e => (I e).decl.isTrait) fun e he => by rw [hch e he]]
  | inh =>
    cases r
    · simp only [π, hlin, List.map_congr_left fun n _ => hasf n,
        List.map_congr_left fun n _ => hwin n, hwI]
    · simp only [π, hdecls, hwI]
  | und =>
    simp only [π, hch c (mem_chainP_self I c)]

/-- The erasure of a type that reads another class is determined by that class's name key, if
the class-name hash covers the kind. -/
theorem home_abs (x : Ext) (hkind : x.kind = true) (I I' : Cls → Iface) (t : Ty)
    (hs : special t = true)
    (h : π .decl x I (homeK t).1 (homeK t).2 = π .decl x I' (homeK t).1 (homeK t).2) :
    eraseT I t = eraseT I' t := by
  cases t with
  | vc =>
    simp only [homeK, homeC, reduceCtorEq, ite_false, π, H.j.injEq] at h
    exact h
  | wz =>
    simp only [homeK, homeC, ite_true, π, H.chain.injEq, hkind] at h
    obtain ⟨hl, hk⟩ := h
    have hc := map_pair_fst hl
    rw [← hc] at hk
    have hz := (List.map_inj_left.1 hk) .Z (mem_chainP_self I .Z)
    simp only [eraseT, hc, hz]
  | _ => simp [special] at hs

/-- **Item 5.** As declared, with faithful macro keys and the kind in the class-name hash, meets
the bridge spec with a recomputed witness or with the dependency edge. As seen from does not:
its inheritance key does not determine the owner's declaration (`bridge₀`/`bridge₁` below). -/
theorem Er_obligations (x : Ext) (hsafe : x.safe = true) (hkind : x.kind = true)
    (hv : (x.wit = .fresh ∧ x.dep = false) ∨ (x.wit = .none ∧ x.dep = true)) :
    (Er .decl x).Obligations where
  comp := Er_comp .decl x
  coverage := by
    intro I d s q hq
    exact ⟨keyOf x q, List.mem_toFinset.2 (List.mem_map.2 ⟨q, hq, rfl⟩), rfl,
      scope_unitF x I s q hq⟩
  abstraction := by
    intro I I' k hk q hc
    obtain ⟨rfl, hs⟩ := hc
    obtain ⟨e, q⟩ := q
    change π .decl x I _ _ = π .decl x I' _ _ at hk
    suffices answer I (e, q) = answer I' (e, q) ∧ scope x I' (e, q) from ⟨this.1, rfl, this.2⟩
    have hinh : ∀ p, π .decl x I p .inh = π .decl x I' p .inh →
        declsP I p = declsP I' p ∧ witI x I p = witI x I' p := by
      intro p h
      simpa only [π, H.inhW.injEq, H.inh.injEq] using h
    have hdecl : ∀ p, π .decl x I p .inh = π .decl x I' p .inh → ∀ e ∈ chainP I p,
        e ∈ chainP I' p ∧ (I e).decl.parent = (I' e).decl.parent ∧
          (I e).decl.decls = (I' e).decl.decls := by
      intro p h e he
      have := mem_of_map_pair (f := fun e => ((I e).decl.parent, (I e).decl.decls))
        (g := fun e => ((I' e).decl.parent, (I' e).decl.decls))
        (by simpa only [declsP] using (hinh p h).1) he
      simpa only [Prod.mk.injEq] using this
    have hname : ∀ c n, π .decl x I c (.name n) = π .decl x I' c (.name n) →
        (chainP I c).map (fun e => (e, (I e).decl.decls.lookup n)) =
          (chainP I' c).map (fun e => (e, (I' e).decl.decls.lookup n)) ∧
        witN x I c n = witN x I' c n := by
      intro c n h
      simpa only [π, H.nm.injEq, H.ents.injEq] using h
    have hcls : ∀ c, π .decl x I c .cls = π .decl x I' c .cls →
        (chainP I c).map (fun e => (e, (I e).decl.parent)) =
          (chainP I' c).map (fun e => (e, (I' e).decl.parent)) := by
      intro c h
      simp only [π, H.chain.injEq] at h
      exact h.1
    cases q with
    | parent y =>
      cases y with
      | inh p =>
        obtain ⟨h1, h2, _⟩ := hdecl p hk e hs
        exact ⟨by simp only [answer, h2], h1⟩
      | sel c =>
        have := mem_of_map_pair (hcls c hk) hs
        exact ⟨by simp only [answer, this.2], this.1⟩
      | obs c n =>
        simp only [keyOf, hsafe, ite_true] at hk
        have := mem_of_map_pair (hcls c hk) hs
        exact ⟨by simp only [answer, this.2], this.1⟩
      | ownr => exact absurd hs (by simp [scope])
      | own => exact absurd hs (by simp [scope])
    | decl y n =>
      cases y with
      | inh p =>
        obtain ⟨h1, _, h3⟩ := hdecl p hk e hs
        exact ⟨by simp only [answer, h3], h1⟩
      | sel c =>
        have := mem_of_map_pair (hname c n hk).1 hs
        exact ⟨by simp only [answer, this.2], this.1⟩
      | obs c n' =>
        have := mem_of_map_pair (hname c n hk).1 hs
        exact ⟨by simp only [answer, this.2], this.1⟩
      | ownr =>
        have := mem_of_map_pair (hname e n hk).1 (mem_chainP_self I e)
        exact ⟨by simp only [answer, this.2], trivial⟩
      | own => exact absurd hs (by simp [scope])
    | er y n t =>
      cases y with
      | inh p =>
        obtain ⟨rfl, hsp, hex⟩ := hs
        by_cases hd : x.dep = true
        · simp only [keyOf, hd, ite_true] at hk
          exact ⟨by simp only [answer, home_abs x hkind I I' t hsp hk], rfl, hsp, Or.inl hd⟩
        · have hw : x.wit = .fresh := by
            rcases hv with ⟨hw, _⟩ | ⟨_, hd'⟩
            · exact hw
            · exact absurd hd' hd
          simp only [keyOf, hd, Bool.false_eq_true, ite_false] at hk
          obtain ⟨d, hdm, hmem⟩ := hex.resolve_left hd
          obtain ⟨hd1, _, hd3⟩ := hdecl p hk d hdm
          have hw' := mem_of_map_pair
            (f := fun e => (I e).decl.decls.map fun d => (d.1, eraseT I d.2))
            (g := fun e => (I' e).decl.decls.map fun d => (d.1, eraseT I' d.2))
            (by simpa only [witI, hw] using (hinh p hk).2) hdm
          rw [← hd3] at hw'
          have := (List.map_inj_left.1 hw'.2) (n, t) hmem
          simp only [Prod.mk.injEq, true_and] at this
          exact ⟨by simp only [answer, this], rfl, hsp, Or.inr ⟨d, hd1, hd3 ▸ hmem⟩⟩
      | sel c =>
        obtain ⟨rfl, hsp, hex⟩ := hs
        rcases hv with ⟨hw, _⟩ | ⟨hw, _⟩
        · simp only [keyOf, hw, true_or, ite_true] at hk
          obtain ⟨d, hdm, hlk⟩ := hex.resolve_left (by simp [hw])
          obtain ⟨he, hw'⟩ := hname c n hk
          have h1 := mem_of_map_pair he hdm
          have h2 := mem_of_map_pair (f := fun e => ((I e).decl.decls.lookup n).map (eraseT I))
            (g := fun e => ((I' e).decl.decls.lookup n).map (eraseT I'))
            (by simpa only [witN, hw] using hw') hdm
          rw [← h1.2, hlk] at h2
          simp only [Option.map_some, Option.some.injEq] at h2
          exact ⟨by simp only [answer, h2.2], rfl, hsp, Or.inr ⟨d, h1.1, h1.2 ▸ hlk⟩⟩
        · simp only [keyOf, hw, reduceCtorEq, or_self, ite_false] at hk
          exact ⟨by simp only [answer, home_abs x hkind I I' t hsp hk], rfl, hsp,
            Or.inl (by simp [hw])⟩
      | own =>
        obtain ⟨rfl, hsp⟩ := hs
        simp only [keyOf] at hk
        exact ⟨by simp only [answer, home_abs x hkind I I' t hsp hk], rfl, hsp⟩
      | ownr => exact absurd hs (by simp [scope])
      | obs c n' => exact absurd hs (by simp [scope])
  locality := Er_locality .decl x

/-- A recomputed witness with the kind in the class-name hash. -/
theorem fresh_obligations : (Er .decl { safe := true, wit := .fresh, kind := true }).Obligations :=
  Er_obligations _ rfl rfl (Or.inl ⟨rfl, rfl⟩)

/-- The dependency edge with the kind in the class-name hash: no witness. -/
theorem dep_obligations : (Er .decl { safe := true, dep := true, kind := true }).Obligations :=
  Er_obligations _ rfl rfl (Or.inr ⟨rfl, rfl⟩)

/-- …so a terminating run leaves no class dirty (T3a″). -/
theorem dep_sound (S : Finset Cls) (src : Cls → Src) (P : Compiler.Policy Cls Out K)
    (hP : P.Sound S) (fuel n : ℕ) (R : Finset Cls) (s : Compiler.State Cls Out K) (D : Finset Cls)
    (hD : D ⊆ R) (hInv : (Er .decl { safe := true, dep := true, kind := true }).Inv S src s D)
    (s' : Compiler.State Cls Out K)
    (h : (Er .decl { safe := true, dep := true, kind := true }).zinc S src P fuel n R s = some s') :
    (Er .decl { safe := true, dep := true, kind := true }).Inv S src s' ∅ :=
  (Er .decl _).zinc_sound dep_obligations S src P hP fuel n R s D hD hInv s' h

end obligations

/-! ## Runs -/

section runs
open Compiler (State Policy)

abbrev St := State Cls Out K

def memo (s : St) : St :=
  let o := allCls.map fun c => (c, s.out c)
  let u := allCls.map fun c => (c, s.U c)
  { out := fun c => match o.lookup c with | some x => x | none => s.out c
    U := fun c => match u.lookup c with | some x => x | none => s.U c }

structure Run where
  state : St
  rounds : ℕ
  compiled : Finset Cls

/-- Zinc's transitive inheritance invalidation within one subproject: every class whose chain
meets the recompiled set. -/
def inhPolicy : Policy Cls Out K := fun _ R _ s' I =>
  I ∪ Finset.univ.filter fun d => ∃ e ∈ chainP (fun c => (s'.out c).iface) d, e ∈ R

def plain : Policy Cls Out K := Compiler.Policy.plain

def runE (r : Rend) (x : Ext) (src : Cls → Src) (P : Policy Cls Out K) :
    ℕ → ℕ → Finset Cls → Finset Cls → St → Option Run
  | 0, _, _, _, _ => none
  | fuel + 1, n, acc, R, s =>
    let C := Er r x
    let s' := memo (C.round src R s)
    let I := P n R s s' (C.invalidated Finset.univ (C.affected R s) s s')
    if I ⊆ R then some ⟨s', n + 1, acc ∪ R⟩
    else runE r x src P fuel (n + 1) (acc ∪ R) I s'

def dummy : St := { out := fun _ => ⟨{}, [], [], [], [], []⟩, U := fun _ => ∅ }

def init (r : Rend) (x : Ext) (src : Cls → Src) : St :=
  memo ((Er r x).round src Finset.univ dummy)

def clean (src : Cls → Src) : Cls → Out := group Finset.univ src fun _ => {}

structure Report where
  recompiled : List Cls
  rounds : ℕ
  /-- Classes whose final output differs from a clean build. -/
  wrong : List Cls
  /-- Recompiled classes (other than the edited ones) whose output did not change. -/
  wasted : List Cls
  deriving Repr, DecidableEq

def report (r : Rend) (x : Ext) (P : Policy Cls Out K) (src₀ src₁ : Cls → Src)
    (R₀ : Finset Cls) : Option Report :=
  let s₀ := init r x src₀
  (runE r x src₁ P 8 0 ∅ R₀ s₀).map fun res =>
    let cl := clean src₁
    let rec_ := allCls.filter fun c => c ∈ res.compiled ∧ c ∉ R₀
    { recompiled := rec_
      rounds := res.rounds
      wrong := allCls.filter fun c => res.state.out c != cl c
      wasted := rec_.filter fun c => res.state.out c == s₀.out c }

end runs

/-! ## Scenarios -/

open Cls Name Ty

/-- `erasure-bridge-upstream-grandparent`: `trait M[T] { def m: Int }`, `A extends M[Int]`,
`B extends A { override def m: Int }`, client `X` of `B.m`. -/
def bridge₀ : Cls → Src
  | M => { decl := { decls := [(m, int)] } }
  | A => { decl := { parent := some (M, [int, int]) } }
  | B => { decl := { parent := some (A, [int, int]), decls := [(m, int)] } }
  | X => { decl := {}, sel := [(B, m)] }
  | _ => { decl := {} }

/-- `M.m: Int → T`: `M.m` now erases to `Object`, so `B` needs a bridge `m()Object`. As seen from
`A`, `m` is `Int` before and after. -/
def bridge₁ : Cls → Src
  | M => { decl := { decls := [(m, p0)] } }
  | c => bridge₀ c

/-- **As seen from is the wrong input for erasure.** `A` recompiles (its inheritance key on `M`
moved), but its own rendering of `m` is `Int` before and after, so across subprojects (only the
inheritance key on `A`) `B` keeps its old bridges. -/
example : report .asf {} plain bridge₀ bridge₁ {M} = some ⟨[A], 2, [B], [A]⟩ := by native_decide
/-- As declared (Scala 3), and with the witness, `B` recompiles. `X` too: the name `m` of `B` lists
`M.m` as declared. -/
example : report .decl {} plain bridge₀ bridge₁ {M} = some ⟨[A, B, X], 2, [], [A, X]⟩ := by
  native_decide
example : report .decl { wit := .stored } plain bridge₀ bridge₁ {M} = some ⟨[A, B, X], 2, [], [A, X]⟩ := by
  native_decide
/-- In one subproject, transitive inheritance invalidation hides the bug. -/
example : report .asf {} inhPolicy bridge₀ bridge₁ {M} = some ⟨[A, B], 2, [], [A]⟩ := by
  native_decide

/-- The precision case: `M[T, U].m: T → m: U`, `A extends M[Int, Int]`, `B` overrides `m`.
Neither the type as seen from `A` nor the erasure changes. -/
def prec₀ : Cls → Src
  | M => { decl := { decls := [(m, p0)] } }
  | A => { decl := { parent := some (M, [int, int]) } }
  | B => { decl := { parent := some (A, [int, int]), decls := [(m, int)] } }
  | X => { decl := {}, sel := [(B, m)] }
  | _ => { decl := {} }

def prec₁ : Cls → Src
  | M => { decl := { decls := [(m, p1)] } }
  | c => prec₀ c

/-- `asf` recompiles only `A`; `decl` also recompiles `B`, and `X` through the name `m` of `B`, for
nothing. The same mechanism as the bridge fix. (In Zinc, `X` recompiles under both bridges through
its `memberRef` on the owner `M`, which the model does not record.) -/
example : report .asf {} plain prec₀ prec₁ {M} = some ⟨[A], 2, [], [A]⟩ := by native_decide
example : report .decl {} plain prec₀ prec₁ {M} = some ⟨[A, B, X], 2, [], [A, B, X]⟩ := by
  native_decide

/-- The converse fails: on the precision case the as-seen-from hashes of `A` agree, the
as-declared ones do not. -/
example : π .asf {} (fun c => { decl := (prec₀ c).decl }) .A .inh =
      π .asf {} (fun c => { decl := (prec₁ c).decl }) .A .inh ∧
    π .decl {} (fun c => { decl := (prec₀ c).decl }) .A .inh ≠
      π .decl {} (fun c => { decl := (prec₁ c).decl }) .A .inh := by
  native_decide

/-- The class-name key: `trait M[T] { def m: T }`, `A extends M[T]` (passing its parameter on),
`B extends A[Int] → A[Long]`; client `X` selects `B.m`, macro `Y` observes `B.m`. -/
def hdr₀ : Cls → Src
  | M => { decl := { decls := [(m, p0)] } }
  | A => { decl := { parent := some (M, [p0, p1]) } }
  | B => { decl := { parent := some (A, [int, int]) } }
  | X => { decl := {}, sel := [(B, m)] }
  | Y => { decl := {}, obs := [(B, m)] }
  | _ => { decl := {} }

def hdr₁ : Cls → Src
  | B => { decl := { parent := some (A, [long, int]) } }
  | c => hdr₀ c

/-- Scala 2 moves the name `m` of `B`; both clients recompile. -/
example : report .asf {} plain hdr₀ hdr₁ {B} = some ⟨[X, Y], 2, [], []⟩ := by native_decide
/-- Scala 3's name `m` of `B` does not move; `X` recompiles through the class-name key, the macro
`Y` (recording names only) does not and keeps the stale type. -/
example : report .decl {} plain hdr₀ hdr₁ {B} = some ⟨[X], 2, [Y], []⟩ := by native_decide
/-- Recorded faithfully, the macro's reads of `B`'s parents are covered by the class-name key. -/
example : report .decl { safe := true } plain hdr₀ hdr₁ {B} = some ⟨[X, Y], 2, [], []⟩ := by native_decide

/-- `value-class-mixin-forwarder`: `class V(val x: String) extends AnyVal`, `trait M { def g: V }`,
`A extends M` with a mixin forwarder for `g`. -/
def vc₀ : Cls → Src
  | V => { decl := { und := some str } }
  | M => { decl := { decls := [(g, vc)] } }
  | A => { decl := { parent := some (M, [int, int]), fwd := true } }
  | _ => { decl := {} }

/-- `V(String) → V(Long)`. -/
def vc₁ : Cls → Src
  | V => { decl := { und := some long } }
  | c => vc₀ c

/-- Neither rendering moves: `M.g: V` names `V`. `M` recompiles (it erases its own `g`), `A`'s
forwarder keeps `g()Ljava/lang/String;`. -/
example : report .asf {} plain vc₀ vc₁ {V} = some ⟨[M], 2, [A], []⟩ := by native_decide
example : report .decl {} plain vc₀ vc₁ {V} = some ⟨[M], 2, [A], []⟩ := by native_decide
/-- The stored witness moves `A`'s inheritance key once `M` has recompiled: a round later. -/
example : report .decl { wit := .stored } plain vc₀ vc₁ {V} = some ⟨[M, A], 3, [], []⟩ := by
  native_decide
example : report .asf { wit := .vcStored } plain vc₀ vc₁ {V} = some ⟨[M, A], 3, [], []⟩ := by
  native_decide
/-- So does a dependency on `V` recorded by `A` when it erases `M.g`, with no change to any hash,
under either rendering. -/
example : report .decl { dep := true } plain vc₀ vc₁ {V} = some ⟨[M, A], 2, [], []⟩ := by
  native_decide
example : report .asf { dep := true } plain vc₀ vc₁ {V} = some ⟨[M, A], 2, [], []⟩ := by
  native_decide

/-- `erasure-intersection-trait-to-class` (sbt/zinc#1844, pending): `trait W`, `trait Z`,
`trait M { def g: W with Z }`, `A extends M` with forwarders (the test's mirror class), client `X`
of `A.g`. -/
def int₀ : Cls → Src
  | W => { decl := { isTrait := true } }
  | Z => { decl := { isTrait := true } }
  | M => { decl := { decls := [(g, wz)], isTrait := true } }
  | A => { decl := { parent := some (M, [int, int]), fwd := true } }
  | X => { decl := {}, sel := [(A, g)] }
  | _ => { decl := {} }

/-- `trait Z` becomes `abstract class Z`: `W with Z` now erases to `Z`. -/
def int₁ : Cls → Src
  | Z => { decl := {} }
  | c => int₀ c

/-- `erasure-intersection-parent-added`: `trait Z extends W`. -/
def int₂ : Cls → Src
  | Z => { decl := { parent := some (W, [int, int]), isTrait := true } }
  | c => int₀ c

/-- Trait to class: nothing recompiles under any witness or edge, because the name `Z` does not
cover its kind; the declarer `M`, the forwarder in `A` and the client `X` are all stale. -/
example : report .decl { wit := .stored } plain int₀ int₁ {Z} = some ⟨[], 1, [M, A, X], []⟩ := by
  native_decide
example : report .decl { dep := true } plain int₀ int₁ {Z} = some ⟨[], 1, [M, A, X], []⟩ := by
  native_decide
/-- A recomputed witness fixes the descendant and the client (whose name key carries it); the
declarer's own descriptor stays stale. -/
example : report .decl { wit := .fresh } plain int₀ int₁ {Z} = some ⟨[A, X], 2, [M], []⟩ := by
  native_decide
/-- With the kind in the class-name hash, the first hop holds, and the stored witness or the edge
completes the second. Without either, `A` stays stale. -/
example : report .decl { kind := true } plain int₀ int₁ {Z} = some ⟨[M, X], 2, [A], []⟩ := by
  native_decide
example : report .decl { wit := .stored, kind := true } plain int₀ int₁ {Z} =
    some ⟨[M, A, X], 3, [], []⟩ := by native_decide
example : report .decl { dep := true, kind := true } plain int₀ int₁ {Z} =
    some ⟨[M, A, X], 2, [], []⟩ := by native_decide

/-- Parent added: the name `Z` covers parents, so the first hop holds already. sbt/zinc#1844's
annotation of value-class references does not help; a stored witness or the edge does. -/
example : report .asf { wit := .vcStored } plain int₀ int₂ {Z} = some ⟨[M, X], 2, [A], []⟩ := by
  native_decide
example : report .decl { wit := .stored } plain int₀ int₂ {Z} = some ⟨[M, A, X], 3, [], []⟩ := by
  native_decide
example : report .decl { dep := true } plain int₀ int₂ {Z} = some ⟨[M, A, X], 2, [], []⟩ := by
  native_decide

/-! ## Bounded exhaustive comparison

`trait M[T, U]` declares `m` (none, `Int`, `Long`, `T`, `U`, `V`) and `g` (none, `V`,
`W with Z`); `A extends M[..]` (`[Int, Int]`, `[Int, Long]`, `[T, U]`) optionally declares `m`
(`Int`, `T`) and has forwarders or not; `B extends A[Int, Int]` or `A[Long, Int]` optionally
declares `m` (`Int`, `Long`, `V`) and has forwarders or not; `V` wraps `Int` or `Long`; `Z` is a
trait or an abstract class, and extends `W` or not. Client `X` selects `B.m` and `B.g`, macro `Y`
observes `B.m`. An edit changes one of these choices. `lake exe exhaustive erasure` runs every
(base, edit) pair under each variant.

Results: 41,472 bases × 20 edits; 189,888 pairs have a base and an edit that both compile (the
model rejects every non-conforming override, so most pairs are illegal). Macro reads are recorded
faithfully throughout. Unclean runs, by the class edited (`M`: generic erasure, `V`: value class,
`Z`: intersection, trait to class (2,176) or parent added (1,632)):

| variant | unclean | `M` | `V` | `Z` | recompiles |
|---|---|---|---|---|---|
| Scala 2 today, across subprojects | 12,064 | 4,608 | 3,648 | 3,808 | 337,856 |
| Scala 2 today, one subproject | 2,176 | | | 2,176 | 381,376 |
| Scala 2 + value-class annotation (sbt/zinc#1844) | 8,416 | 4,608 | | 3,808 | 351,360 |
| Scala 2 + divergence witness | 7,456 | | 3,648 | 3,808 | 345,536 |
| Scala 2 + erased signature at definition | 2,176 | | | 2,176 | 407,488 |
| … + kind in class-name hash | **0** | | | | 418,368 |
| Scala 3 today | 7,456 | | 3,648 | 3,808 | 398,912 |
| Scala 3 + erased signature at definition | 2,176 | | | 2,176 | 412,288 |
| … + kind in class-name hash | **0** | | | | 423,168 |
| Scala 3 + dependency edge | 2,176 | | | 2,176 | 417,088 |
| … + kind in class-name hash | **0** | | | | 434,496 |
| Scala 3 + recomputed witness | 2,176 (declarer only) | | | 2,176 | 418,816 |
| … + kind in class-name hash | **0** | | | | 423,168 |

* Each input fails at its own hop. Generic erasure fails only at the second hop under as seen
  from: the divergence witness closes exactly the 4,608 `M` runs, and Scala 2 with it fails
  exactly where Scala 3 does today. Value classes fail at the second hop under both renderings:
  sbt/zinc#1844's annotation, the stored witness and the dependency edge all close them.
  Intersections fail at the first hop when `Z` turns from trait into class (2,176): nothing
  closes those without the kind in the class-name hash. A recomputed witness reaches the
  descendants and clients but not the declarer's own descriptor.
* The parent-added intersection runs (1,632) need only the second hop: `Z`'s name hash covers
  its parents.
* One subproject: transitive inheritance invalidation closes everything but the first hop.
* Cost: closing everything costs 24% more recompiles than Scala 2 today and 6% more than
  Scala 3 today (stored witness + kind). The dependency edge costs 3% more than the stored
  witness: it recompiles descendants whose erasure reads `V` or `Z` even when the erasure did
  not move.
* `winnerP`: the as-seen-from hashes include the class whose declaration wins, standing for
  Zinc's rendering of declared vs inherited members and `override`. Without it the model
  reports a spurious client undercompilation when a subclass adds an override of the same type
  as seen from it. -/

inductive OM | none | int | long | p0 | p1 | vc
  deriving DecidableEq, Repr

def OM.ty : OM → Option Ty
  | .none => Option.none | .int => some .int | .long => some .long | .p0 => some .p0 | .p1 => some .p1
  | .vc => some .vc

structure Cfg where
  mM : OM
  gM : Fin 3
  aArgs : Fin 3
  mA : Fin 3
  fA : Bool
  bArg : Bool
  mB : Fin 4
  fB : Bool
  vLong : Bool
  zClass : Bool
  zExtW : Bool
  deriving DecidableEq, Repr

def tyOpt (o : Option Ty) (n : Name) : List (Name × Ty) := (o.map fun t => [(n, t)]).getD []

def Cfg.src (k : Cfg) : Cls → Src
  | V => { decl := { und := some (if k.vLong then long else int) } }
  | W => { decl := { isTrait := true } }
  | Z => { decl := { isTrait := !k.zClass, parent := if k.zExtW then some (W, [int, int]) else none } }
  | M => { decl := { decls := tyOpt k.mM.ty m ++
                       tyOpt ([Option.none, some Ty.vc, some Ty.wz].getD k.gM.val Option.none) g,
                     isTrait := true } }
  | A => { decl := { parent := some (M, [[int, int], [int, long], [p0, p1]].getD k.aArgs.val []),
                     decls := tyOpt ([Option.none, some Ty.int, some Ty.p0].getD k.mA.val Option.none) m,
                     fwd := k.fA } }
  | B => { decl := { parent := some (A, if k.bArg then [long, int] else [int, int]),
                     decls := tyOpt ([Option.none, some Ty.int, some Ty.long, some Ty.vc].getD k.mB.val Option.none) m,
                     fwd := k.fB } }
  | X => { decl := {}, sel := [(B, m), (B, g)] }
  | Y => { decl := {}, obs := [(B, m)] }

def oms : List OM := [.none, .int, .long, .p0, .p1, .vc]

def cfgs : List Cfg := do
  let mM ← oms; let gM ← [0, 1, 2]
  let aArgs ← [0, 1, 2]; let mA ← [0, 1, 2]; let fA ← [false, true]
  let bArg ← [false, true]; let mB ← [0, 1, 2, 3]; let fB ← [false, true]
  let vLong ← [false, true]; let zClass ← [false, true]; let zExtW ← [false, true]
  pure ⟨mM, gM, aArgs, mA, fA, bArg, mB, fB, vLong, zClass, zExtW⟩

/-- Single-choice edits, with the class edited. -/
def edits (k : Cfg) : List (Cfg × Cls) :=
  (oms.filter (· != k.mM)).map (fun o => ({ k with mM := o }, M)) ++
  (([0, 1, 2] : List (Fin 3)).filter (· != k.gM)).map (fun o => ({ k with gM := o }, M)) ++
  (([0, 1, 2] : List (Fin 3)).filter (· != k.aArgs)).map (fun o => ({ k with aArgs := o }, A)) ++
  (([0, 1, 2] : List (Fin 3)).filter (· != k.mA)).map (fun o => ({ k with mA := o }, A)) ++
  [({ k with fA := !k.fA }, A), ({ k with bArg := !k.bArg }, B)] ++
  (([0, 1, 2, 3] : List (Fin 4)).filter (· != k.mB)).map (fun o => ({ k with mB := o }, B)) ++
  [({ k with fB := !k.fB }, B), ({ k with vLong := !k.vLong }, V),
   ({ k with zClass := !k.zClass }, Z), ({ k with zExtW := !k.zExtW }, Z)]

def Cfg.size (k : Cfg) : ℕ :=
  (if k.mM != .none then 1 else 0) + (if k.gM != 0 then 1 else 0) + (if k.aArgs != 0 then 1 else 0) +
    (if k.mA != 0 then 1 else 0) + (if k.fA then 1 else 0) + (if k.bArg then 1 else 0) +
    (if k.mB != 0 then 1 else 0) + (if k.fB then 1 else 0) + (if k.vLong then 1 else 0) +
    (if k.zClass then 1 else 0) + (if k.zExtW then 1 else 0)

/-- A variant: rendering, options, and the policy (`true`: Zinc's transitive inheritance
invalidation, as within one subproject). Macro reads are recorded faithfully throughout. -/
structure Variant where
  name : String
  rend : Rend
  ext : Ext
  inh : Bool

def variants : List Variant :=
  [⟨"Scala 2 today, across subprojects", .asf, { safe := true }, false⟩,
   ⟨"Scala 2 today, one subproject", .asf, { safe := true }, true⟩,
   ⟨"Scala 2 + value-class annotation (sbt/zinc#1844 as implemented)", .asf,
     { safe := true, wit := .vcStored }, false⟩,
   ⟨"Scala 2 + divergence witness", .asf, { safe := true, wit := .diverge }, false⟩,
   ⟨"Scala 2 + erased signature at definition", .asf, { safe := true, wit := .stored }, false⟩,
   ⟨"Scala 2 + erased signature, kind in class-name hash", .asf,
     { safe := true, wit := .stored, kind := true }, false⟩,
   ⟨"Scala 3 today", .decl, { safe := true }, false⟩,
   ⟨"Scala 3 + erased signature at definition", .decl, { safe := true, wit := .stored }, false⟩,
   ⟨"Scala 3 + erased signature, kind in class-name hash", .decl,
     { safe := true, wit := .stored, kind := true }, false⟩,
   ⟨"Scala 3 + dependency edge", .decl, { safe := true, dep := true }, false⟩,
   ⟨"Scala 3 + dependency edge, kind in class-name hash", .decl,
     { safe := true, dep := true, kind := true }, false⟩,
   ⟨"Scala 3 + recomputed witness", .decl, { safe := true, wit := .fresh }, false⟩,
   ⟨"Scala 3 + recomputed witness, kind in class-name hash", .decl,
     { safe := true, wit := .fresh, kind := true }, false⟩]

/-- A clean build reports no errors. Incremental runs are compared only between legal programs. -/
def Cfg.legal (k : Cfg) : Bool := allCls.all fun c => (clean k.src c).errs.isEmpty

def runVariant (v : Variant) (k k' : Cfg) (e : Cls) : Option Report :=
  report v.rend v.ext (if v.inh then inhPolicy else plain) k.src k'.src {e}

end Zinc.Erasure
