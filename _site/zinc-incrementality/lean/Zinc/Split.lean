import ZincNames.Names
import ZincNames.Givens
import Zinc.SplitProof

/-!
# Name resolution across subprojects: the binding upstream, the client downstream

`Names.lean` and `Givens.lean` put the client and every binding in one subproject. Here every
binding is in an upstream subproject and the client's file downstream (the harness's `split`
layout). Resolution does not care; Zinc does. The downstream never sees the edit as a changed
source: `detectInitialChanges` compares, for each upstream class the downstream recorded an edge to
(`apis.allExternals`), the stored `AnalyzedClass` with the upstream analysis's (a class that is gone
is `emptyAnalyzedClass`), and `invalidateClassesExternally` invalidates the inheritance dependents
and the member-ref dependents that use a changed name (all of them when an implicit changed).

The upstream class's name hashes include its own simple name (`NameHashing` visits the class
itself), so a deleted or renamed class reaches the users of its name, as a deleted source does
inside a subproject; an added upstream class is in no one's `allExternals`, as an added source has
no dependents. `ext_eq_internal` checks that the external rule, stated on its own terms, is the
internal one on the whole space.

Two things do change. retronym/zinc#34 invalidates the users of a class that a cycle of the
*current* subproject added: an upstream class is added by the upstream's run, where the client is
not, so F1 comes back (`split_cheap_is_today`). And Scala 3's trait initialiser (F6, G3) vanishes:
the client reads `P` from the upstream's TASTy in the clean build too.

The `check_` theorems are checks, not proofs: `native_decide` over the enumerated bases (at most
two bindings), an executable spec run exhaustively. The general statements, over every program of
the slot language and with no enumeration, are in `SplitProof.lean`; `check_abstract` checks that
this model is an instance of that language on the bases.
-/

namespace Zinc.Split

open Zinc.Names (Ver Slot Prog Res resolve changed invalidates addsClass besideResolution separateInit aliased)

inductive Layout | single | split
  deriving DecidableEq, Repr

/-- retronym/zinc#34 and its extension across subprojects. -/
inductive Mode
  /-- Zinc today. -/
  | today
  /-- #34: the users of the simple name of a top-level class a cycle of the client's subproject added. -/
  | cheap
  /-- #34 across subprojects: also the classes the upstream added since the client's last compilation. -/
  | upstream
  /-- The proposal of `SplitProof.lean`: also any name newly bound in a slot, in any subproject (an
  added top-level class, a member added to a package object or an imported object). -/
  | names
  deriving DecidableEq, Repr

/-- A class of the client's file: the client, or the other class charged with the imports (Scala 2's
`First`, Scala 3's `Last`). -/
inductive Cls | client | other
  deriving DecidableEq, Repr

/-- An edge the client's file records, from one of its classes to the class of a slot. -/
structure Edge where
  frm : Cls
  dst : Slot
  inh : Bool
  deriving DecidableEq, Repr

/-- The class charged with the top-level imports. -/
def charged (p : Prog) : Cls := if p.cl.first then .other else .client

/-- The edges of the client's file, given what the client resolved to (`ExtractDependencies`):
the inheritance edge to `P`, the block import's edge to `V` from the client, the explicit and
wildcard imports' edges charged to one class, and the edge from the client to the class that owns
the symbol it resolved to. A package (`a.q`, `a.b`, `a`) records nothing. Two more, from the
client: Scala 2's bridge gives the package object's declared `object Foo` and the class `a.b.Foo`
one name (`Names.aliased`), so resolving either is an edge to both; Scala 3 records the inherited
package-object member it passed over for `a.b.Foo`. -/
def edges (v : Ver) (p : Prog) (r : Res) : List Edge :=
  (if p.cl.inh then [⟨.client, .inh, true⟩] else []) ++
  (if p.cl.blk then [⟨.client, .blk, false⟩] else []) ++
  (if p.cl.expl then [⟨charged p, .expl, false⟩] else []) ++
  (if p.cl.wild then [⟨charged p, .wild, false⟩] else []) ++
  (match r with
    | .ok s => if s == .lib then [] else [⟨.client, s, false⟩]
    | _ => []) ++
  (if aliased v p && r == .ok .pobj then [⟨.client, .inner, false⟩] else []) ++
  (if aliased v p && r == .ok .inner then [⟨.client, .pobj, false⟩] else []) ++
  (if v == .s3 && p.cl.pinh && r == .ok .inner && p.st .pobj == .foo then [⟨.client, .pobj, false⟩] else [])

/-- Does a class of the client's file use the name? The client does; the other class does when the
explicit import's selector is charged to it. -/
def uses (p : Prog) : Cls → Bool
  | .client => true
  | .other => p.cl.expl

/-- Is the class of slot `s` among the downstream's externals, and so compared at all? A top-level
class is a dependency only if it existed: its file held the name. -/
def known (p : Prog) (s : Slot) : Bool := !s.topLevel || p.st s == .foo

/-- Zinc's external rule: a changed upstream class (its name hashes differ in `Foo`, the member or
the class itself) invalidates the class of an edge to it that inherits from it or uses `Foo`. -/
def extInvalidates (v : Ver) (p : Prog) (r : Res) (s : Slot) : Bool :=
  (known p s || (edges v p r).any fun e => e.dst == s && s == .inner && aliased v p) &&
    (edges v p r).any fun e => e.dst == s && (e.inh || uses p e.frm)

def recompiles (m : Mode) (l : Layout) (v : Ver) (p p' : Prog) : Bool :=
  let r := resolve v p
  let base := match l with
    | .single => (changed p p').any (invalidates {} v p r)
    | .split => (changed p p').any (extInvalidates v p r)
  base || match m with
    | .today => false
    | .cheap => l == .single && addsClass {} v p p'
    | .upstream => addsClass {} v p p'
    | .names => (changed p p').any fun s => !p.binds s && p'.binds s

/-- The verdict; the trait initialiser counts only when the client and `P` share a subproject. -/
def verdict (m : Mode) (l : Layout) (v : Ver) (p p' : Prog) : Zinc.Names.Verdict :=
  let r := resolve v p
  let r' := resolve v p'
  let rc := recompiles m l v p p'
  let bytes := l == .single && separateInit v p' rc && r' matches .ok _
  ⟨r, r', rc, (rc || r == r') && !besideResolution v p p' && !bytes⟩

def toNames : Mode → Zinc.Names.Mode
  | .today => .today | .cheap => .cheap | .upstream => .cheap | .names => .names

/-- `check_single_is_names`: In one subproject, this is `Names.verdict`. -/
example : (Zinc.Names.bases.all fun p => (Zinc.Names.edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => [Mode.today, .cheap, .upstream].all fun m =>
      verdict m .single v p p' == Zinc.Names.verdict (toNames m) v p p') = true := by
  native_decide

/-- `check_ext_eq_internal`: The external rule is the internal one on every slot an edit changes. -/
example : (Zinc.Names.bases.all fun p => (Zinc.Names.edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => (changed p p').all fun s =>
      extInvalidates v p (resolve v p) s == invalidates {} v p (resolve v p) s) = true := by
  native_decide

/-- `check_split_cheap_is_today`: #34 changes nothing across subprojects. -/
example : (Zinc.Names.bases.all fun p => (Zinc.Names.edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => recompiles .cheap .split v p p' == recompiles .today .split v p p') = true := by
  native_decide

/-- `check_upstream_added_clean`: Extended across subprojects, it makes every edit that adds a class clean, but for the
divergences beside resolution. -/
example : (Zinc.Names.bases.all fun p => (Zinc.Names.edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => !addsClass {} v p p' ||
      (verdict .upstream .split v p p').clean || besideResolution v p p') = true := by
  native_decide

/-- `check_inner_added_split_cheap`: **F1 across subprojects**: `a.b.Foo` added upstream over `a.Foo`, under #34. -/
example :
    verdict .cheap .split .s2 Zinc.Names.innerBase (Zinc.Names.innerBase.set .inner .foo) =
      ⟨.ok .outer, .ok .inner, false, false⟩ := by native_decide

/-- `check_inner_added_split_upstream`. -/
example :
    verdict .upstream .split .s2 Zinc.Names.innerBase (Zinc.Names.innerBase.set .inner .foo) =
      ⟨.ok .outer, .ok .inner, true, true⟩ := by native_decide

/-- `check_names_clean`: The proposal makes every edit clean, but for the divergences beside resolution. -/
example : (Zinc.Names.bases.all fun p => (Zinc.Names.edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => (verdict .names .split v p p').clean || besideResolution v p p') = true := by
  native_decide

/-! ## This model as an instance of `SplitProof`'s slot language -/

/-- The slots in search order: Scala 2 looks in the package object before the package's classes,
and an inherited member of the package object before the file's imports (`Names.resolve`). -/
def order (v : Ver) (c : Zinc.Names.Client) : List Slot :=
  let vis := Zinc.Names.visible c
  if v == .s2 then
    let o := (vis.filter (· != .inner)).flatMap fun s => if s == .pobj then [.pobj, .inner] else [s]
    if c.pinh then
      let o := o.filter (· != .pobj)
      (o.filter (fun s => s == .blk || s == .inh)) ++ [.pobj] ++ o.filter (fun s => s != .blk && s != .inh)
    else o
  else vis

/-- A slot is pinned when the client's file has an edge to its class from a class that uses the
name, whatever the client resolved to. -/
def pinned (p : Prog) : Slot → Bool
  | .inh | .blk | .expl => true
  | .wild => !p.cl.first || p.cl.expl
  | _ => false

def absClient (v : Ver) (p : Prog) : Zinc.SplitProof.Client where
  n := (order v p.cl).length
  sc := fun j => let s := (order v p.cl).getD j .lib
    ⟨pinned p s, false, s.topLevel, true⟩
  amb := fun _ => False
  mono := fun _ _ _ h => h
  pinned_of_required := fun _ h => absurd h (by simp)

def absBits (v : Ver) (q : Prog) (o : List Slot) (j : ℕ) : Bool :=
  match o[j]? with
  | some s => q.binds s
  | none => false

/-- `check_abstract`: On the bases, resolution is the first binding slot in `order`, today's rule and #34 are
`SplitProof`'s, and the proposal fires whenever `SplitProof.Client.proposed` does (it also fires on
a binding added outside the client's scopes, which `SplitProof` does not model: over-invalidation). -/
example : (Zinc.Names.bases.all fun p => (Zinc.Names.edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v =>
      -- outside the slot language: the edges that depend on the resolution of another slot
      -- (Scala 2's class-name alias, Scala 3's passed-over inherited member)
      aliased v p || (v == .s3 && p.cl.pinh) ||
      let o := order v p.cl
      let c := absClient v p
      let b := absBits v p o
      let b' := absBits v p' o
      (match resolve v p with
        | .ok s => Zinc.SplitProof.first b o.length == some (o.idxOf s)
        | _ => true) &&
      (match resolve v p' with
        | .ok s => Zinc.SplitProof.first b' o.length == some (o.idxOf s)
        | _ => true) &&
      (!(resolve v p matches .ok _) ||
        (recompiles .today .split v p p' == decide (c.today b b') &&
         recompiles .cheap .split v p p' == decide (c.cheap b b') &&
         (!decide (c.proposed b b') || recompiles .names .split v p p')))) = true := by
  native_decide

/-! ## Givens

A changed implicit invalidates every member-ref dependent of its class, inside a subproject and
across: the edges are those of `Names` without the used-name filter, and `Givens.invalidates`
states them. #34 never fires here (`Givens.cheap_is_today`); what the layout changes is the trait
initialiser. -/

def givensRecompiles (m : Mode) (v : Ver) (p p' : Zinc.Givens.Prog) : Bool :=
  Zinc.Givens.recompiles (toNames m) v p p'

def givensVerdict (m : Mode) (l : Layout) (v : Ver) (p p' : Zinc.Givens.Prog) : Zinc.Givens.Verdict :=
  let r := Zinc.Givens.resolve v p
  let r' := Zinc.Givens.resolve v p'
  let rc := givensRecompiles m v p p'
  ⟨r, r', rc, (rc || r == r') && !(l == .single && Zinc.Givens.separateInit v p p' rc)⟩

/-- `check_givens_single_is_givens`. -/
example : ([Ver.s2, .s3].all fun v => (Zinc.Givens.bases v).all fun p =>
    (Zinc.Givens.edits v p).all fun (_, p') => [Mode.today, .cheap].all fun m =>
      givensVerdict m .single v p p' == Zinc.Givens.verdict (toNames m) v p p') = true := by
  native_decide

/-! ## Rendering: each file's subproject -/

/-- The files a names program can have: the client's downstream, every other upstream. -/
def namesTiers : List (String × Nat) :=
  [("Client.scala", 2)] ++
  ["V.scala", "P.scala", "X.scala", "W.scala", "U.scala", "Q.scala", "Inner.scala", "PObj.scala",
   "U2.scala", "Outer.scala", "Other.scala"].map (·, 1)

def givensTiers : List (String × Nat) :=
  [("Client.scala", 2)] ++
  ["V.scala", "P.scala", "W.scala", "Inner.scala", "PObj.scala", "Outer.scala", "T.scala"].map (·, 1)

end Zinc.Split
