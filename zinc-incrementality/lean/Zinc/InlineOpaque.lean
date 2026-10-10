import Mathlib.Data.List.Basic

/-!
# Scala 3 `inline` and opaque types: bytecode that reads what the API renders by name

Two Scala 3 features put into a class's bytecode something its dependencies' APIs show only by
name:

* an `inline` call puts the callee's body into the client: its literals, the constants and type
  aliases it reads (folded), the descriptors of what it calls;
* an opaque type erases to its right-hand side everywhere, though only the defining scope sees it.

The model is a small Zinc loop over keys (`run`). A class records the keys it uses (owner and name,
Zinc's member ref with used name) and its parents (inheritance); each key of a class's API covers
the facts ("atoms") whose change moves its hash when the class compiles; each class's bytecode
reads atoms. A run recompiles the edited file's classes, invalidates by used name and by
inheritance (on any API change), and is clean iff every class reading a changed atom was
recompiled. What each class records and hashes follows dotc 3.9.0 (read from `ExtractAPI`,
`ExtractDependencies` and `Inlining`, then probed with the conformance harness):

* an inline method's hash is `treeHash` of its body: shape, names and literals, no types (a
  `TypeTree` hashes as its node kind); a reference to another inline symbol mixes in that symbol's
  API definition, so inline-to-inline chains are transitive;
* the `Inlining` phase records the references of each expansion as the client's used names, after
  the inliner folded constants read through a module path (`D.K`, `L.K`) and type-level reads
  (`constValue[D.N]`, an inline match on `erasedValue[D.N]`) into literals: those leave no name;
* a `transparent inline` call is expanded in typer, and the dependency phase after typer records
  only the call of an `Inlined` tree: nothing of the expansion;
* an opaque type's right-hand side is in its owner's self type, which Zinc hashes under the
  owner's own name (`O`, or `O$package` at the top level): every user of the owner is
  invalidated, and nobody else.

Everything below is *checked*, not proved: the `check_` theorems are `native_decide` over the
bounded spaces (`Inl.bases`, `Opq.bases`) of this executable spec, the same verdicts the conformance
dump hands the harness. The general statements, over every program of a slot language and through
the Phase 1 framework, are in `InlineOpaqueSound.lean`.

Results (checked below, and against the harness on Zinc `develop`, `lake exe conformance inline` and
`opaque`):

1. **Inline constants and aliases** (`check_dConst_today`): an inline body that reads `D.K`
   (`final val`), `L.K` (its own owner, through the path), `constValue[D.N]` or matches on
   `erasedValue[D.N]` leaves the client with the old value when `K` or `N` changes. The owner `L`
   recompiles (it uses `K`), its API does not move (the reference hashes as a name), and the
   client recorded no name. An unqualified `K` survives inlining and is recorded; an `inline val`
   is an inline symbol, so the body hash covers it.
2. **Transparent references** (`check_today_stale`): a transparent `inl` called directly (or from a
   plain `M.w`) leaves its caller stale when the type of a member its body calls changes (a helper,
   a private member's accessor, `D.v`) or an unqualified constant changes: the caller recorded
   only `inl`, whose hash covers names. Through an inline `M.w` it is clean: the expansion is in
   `w`'s body, and the client's `Inlining` phase records it.
3. **Opaque forwarders** (`check_fwd_today`): `class K extends Tr`, `Tr.h(t: O.T)`: an edit to `T`'s
   right-hand side recompiles `Tr` (it uses `O`), whose API does not move (`h` renders `O.T` by
   name), and leaves `K`'s mixin forwarder with the old erasure; the same for a bridge `K` inherits
   from a trait (`Tr2 extends Base[O.T]`). This is the value-class forwarder of `Erasure.lean`
   (P6.5) with the opaque type in place of the value class.
4. Everything else is clean: inline helpers, private members (through their public accessors),
   `inline val`, inline-to-inline chains, values; opaque clients that name the type, call a member,
   use an extension, inline a member, go through an alias, or override with it.
5. Fixes, clean on the whole space: for inline, `treeHash` mixing the constant or type a reference
   or `TypeTree` denotes (`hashConsts`), or the `Inlining` phase recording the body's references
   before folding (`bodyDeps`); for opaque, a descendant that erases an inherited signature
   recording the types it reads (`dep`, P6.8). Moving the right-hand side from the owner's hash into
   `T`'s and the hashes of the members whose signatures mention `T` (`refine`) saves recompiling
   the owner's other users and is otherwise the same.

Counts (`lake exe conformance inline|opaque [mode]`; the harness ran every edit in both layouts and
agrees with the model on every verdict and every recompiled set, but for a classfile artefact of
dotc, below):

| Space | Edits | Unclean today | Fixed by | Recompiles today → fixed |
|---|---|---|---|---|
| inline | 168 | 64: path constant 24, alias at the type level 24, transparent 16 | `hashConsts`, `bodyDeps` | 320 → 416, 384 |
| opaque | 108 | 24: forwarder 12, inherited bridge 12 | `dep` | 228 → 252 (`refine`: 216) |

The artefact: when an object is compiled apart from an object it references (as Zinc does, in a
later cycle), dotc may pickle a prefix differently (the package's `ThisType` vs its `TermRef`, in
the shared types of an extension call or a transparent expansion), so the TASTy UUID in the mirror
class's attribute differs from a joint build's. The module class is identical; 12 harness cases
differ only so.
-/

namespace Zinc.InlineOpaque

/-! ## The loop -/

/-- A name in a class's API: Zinc's `(class, name)` of a member ref with a used name. -/
structure Key where
  cls : String
  name : String
  deriving DecidableEq, Repr

/-- A class as Zinc sees it. -/
structure Cls where
  name : String
  file : String
  uses : List Key := []
  parents : List String := []
  /-- The names of the class's API, with the atoms each name's hash covers when it compiles. -/
  keys : List (String × List String) := []
  /-- The atoms the class's bytecode depends on. -/
  reads : List String := []
  deriving Repr

abbrev Prog := List Cls

def uniq (l : List String) : List String := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The keys of `c` whose hash moves when `c` compiles after atoms `ch` changed. -/
def Cls.moved (c : Cls) (ch : List String) : List Key :=
  c.keys.filterMap fun (n, as) => if as.any ch.contains then some ⟨c.name, n⟩ else none

/-- The ancestors of `c` in `p`. -/
def ancestors (p : Prog) (c : Cls) : List String :=
  let rec go (fuel : ℕ) (cs : List String) : List String :=
    match fuel with
    | 0 => cs
    | n + 1 =>
      let more := (p.filter (cs.contains ·.name)).flatMap (·.parents)
      let cs' := uniq (cs ++ more)
      if cs'.length == cs.length then cs else go n cs'
  (go p.length c.parents)

/-- One cycle: the classes compiled for the first time (`cur`) report their moved keys; Zinc
invalidates the users of those names and the descendants of classes whose API moved. A hash is
recomputed from the current sources, so it moves at a class's first recompilation only. -/
def next (p : Prog) (ch : List String) (done cur : List String) : List String :=
  let moved := (p.filter (cur.contains ·.name)).flatMap (·.moved ch)
  let apiChanged := uniq (moved.map (·.cls))
  let inv := p.filter fun d =>
    d.uses.any moved.contains || (ancestors p d).any apiChanged.contains
  (inv.map (·.name)).filter (!done.contains ·)

/-- Zinc's run after an edit of `files` that changed atoms `ch`: the classes recompiled. -/
def run (p : Prog) (ch : List String) (files : List String) : List String :=
  let rec go (fuel : ℕ) (done cur : List String) : List String :=
    match fuel with
    | 0 => done
    | n + 1 =>
      if cur.isEmpty then done
      else
        let done' := uniq (done ++ cur)
        go n done' (uniq (next p ch done' cur))
  go (p.length + 1) [] ((p.filter (files.contains ·.file)).map (·.name))

structure Verdict where
  recompiled : List String
  /-- Classes whose bytecode reads a changed atom and were not recompiled. -/
  stale : List String
  /-- Classes recompiled outside the edited files that read no changed atom. -/
  wasted : List String
  deriving DecidableEq, Repr

def Verdict.clean (v : Verdict) : Bool := v.stale.isEmpty

def verdict (p : Prog) (ch : List String) (files : List String) : Verdict :=
  let r := run p ch files
  ⟨r, (p.filter fun c => c.reads.any ch.contains && !r.contains c.name).map (·.name),
    (p.filter fun c => r.contains c.name && !files.contains c.file && !c.reads.any ch.contains).map
      (·.name)⟩

/-! ## Inline -/

namespace Inl

/-- Where `inl` lives: `object L`, or the top level of `L.scala` (class `L$package`). -/
inductive Owner | obj | top
  deriving DecidableEq, Repr

/-- How the client reaches `inl`: a call, a call of an inline `M.w` that calls it, or of a plain
`M.w` (then `M` inlines it, and the client reads nothing of it). -/
inductive Via | direct | inl | plain
  deriving DecidableEq, Repr

/-- What `inl`'s body reads: a literal; in its owner a public `h`, a private `p`, a constant `K`
through `this` or through the owner's path; in `object D` a constant, an `inline val`, a `val`, an
`inline def j`, or an alias `N` read by `constValue` or by an inline match on `erasedValue`. -/
inductive Ref | lit | helper | priv | thisK | pathK | dConst | dInlineVal | dVal | dInline
  | constValue | matchN
  deriving DecidableEq, Repr

def Ref.all : List Ref :=
  [.lit, .helper, .priv, .thisK, .pathK, .dConst, .dInlineVal, .dVal, .dInline, .constValue, .matchN]

def Ref.str : Ref → String
  | .lit => "lit" | .helper => "helper" | .priv => "priv" | .thisK => "thisK" | .pathK => "pathK"
  | .dConst => "dConst" | .dInlineVal => "dInlineVal" | .dVal => "dVal" | .dInline => "dInline"
  | .constValue => "constValue" | .matchN => "matchN"

/-- Is the referenced member in `object D`? -/
def Ref.inD : Ref → Bool
  | .dConst | .dInlineVal | .dVal | .dInline | .constValue | .matchN => true
  | _ => false

/-- Does the referenced member have a type an edit can change (`Int` to `String`)? -/
def Ref.typed : Ref → Bool
  | .helper | .priv | .dVal => true
  | _ => false

/-- The referenced member's name in its owner's API. -/
def Ref.member : Ref → String
  | .helper => "h" | .priv => "inline$p" | .thisK | .pathK | .dConst | .dInlineVal => "K"
  | .dVal => "v" | .dInline => "j" | .constValue | .matchN => "N" | .lit => ""

inductive Mode | today | hashConsts | bodyDeps
  deriving DecidableEq, Repr

structure Prog where
  owner : Owner
  trans : Bool
  via : Via
  ref : Ref
  /-- The value: the body literal, or the referenced member's. -/
  val : ℕ := 1
  /-- The referenced member's type is `String` (else `Int`). -/
  str : Bool := false
  deriving DecidableEq, Repr

def lName (p : Prog) : String := if p.owner == .obj then "L" else "L$package"

/-- The atoms an edit changed. -/
def changed (p p' : Prog) : List String :=
  (if p.val != p'.val then ["val"] else []) ++ (if p.str != p'.str then ["ty"] else [])

/-- What the expansion in the client reads. -/
def expReads (r : Ref) : List String :=
  match r with
  | .helper | .priv | .dVal => ["ty"]
  | _ => ["val"]

/-- The atoms `inl`'s hash covers: its literal, and an inline symbol's definition; with
`hashConsts`, also the constant or type each reference denotes. -/
def inlCovers (m : Mode) (r : Ref) : List String :=
  match r with
  | .lit | .dInlineVal | .dInline => ["val"]
  | .helper | .priv | .dVal => if m == .hashConsts then ["ty"] else []
  | _ => if m == .hashConsts then ["val"] else []

/-- The names recorded for an expansion (other than the call itself). The `Inlining` phase records
the references of the expansions it makes, after the inliner folded a constant read through a path
(`L.K`, `D.K`, `conf.K`) and type-level reads into literals; an unqualified `K` survives. A
transparent call is expanded in typer, whose dependency phase records only the call: the client of
a transparent `inl` (or the plain `M.w` calling it) records nothing of its body, while an inline
`M.w` carries the expansion in its own body, which the client's `Inlining` phase records. With
`bodyDeps`, every expansion records the references of the body before folding. -/
def expUses (m : Mode) (p : Prog) : List Key :=
  let l := lName p
  let all : List Key := match p.ref with
    | .lit => []
    | .helper | .priv | .thisK | .pathK => [⟨l, p.ref.member⟩]
    | r => [⟨"D", r.member⟩]
  if m == .bodyDeps then all
  else if p.trans && p.via != .inl then []
  else match p.ref with
    | .lit | .pathK | .dConst | .dInlineVal | .dInline | .constValue | .matchN => []
    | _ => all

/-- The program as Zinc sees it. -/
def classes (m : Mode) (p : Prog) : List Cls :=
  let l := lName p
  let own : List (String × List String) := match p.ref with
    | .helper | .priv => [(p.ref.member, ["ty"])]
    | .thisK | .pathK => [("K", ["val"])]
    | _ => []
  let lReads := match p.ref with
    | .helper | .priv => ["val", "ty"]
    | .thisK | .pathK => ["val"]
    | _ => []
  let lUses : List Key := if p.ref.inD then [⟨"D", p.ref.member⟩] else []
  let lCls : Cls :=
    { name := l, file := "L.scala", uses := lUses, keys := ("inl", inlCovers m p.ref) :: own, reads := lReads }
  let dCls : List Cls := if !p.ref.inD then [] else
    [{ name := "D", file := "D.scala", keys := [(p.ref.member, if p.ref == .dVal then ["ty"] else ["val"])], reads := match p.ref with | .dConst => ["val"] | .dVal => ["val", "ty"] | _ => [] }]
  let call : Key := ⟨l, "inl"⟩
  let e := expUses m p
  let mCls : List Cls := match p.via with
    | .direct => []
    | .inl => [{ name := "M", file := "M.scala", uses := [call], keys := [("w", inlCovers m p.ref)] }]
    | .plain => [{ name := "M", file := "M.scala", uses := call :: e, keys := [("w", [])], reads := expReads p.ref }]
  let client : Cls := match p.via with
    | .direct => { name := "Client", file := "Client.scala", uses := call :: e, reads := expReads p.ref }
    | .inl => { name := "Client", file := "Client.scala", uses := ⟨"M", "w"⟩ :: call :: e, reads := expReads p.ref }
    | .plain => { name := "Client", file := "Client.scala", uses := [⟨"M", "w"⟩] }
  [lCls] ++ dCls ++ mCls ++ [client]

/-- The file an edit of the referenced member (or the literal) touches. -/
def editedFile (r : Ref) : String := if r.inD then "D.scala" else "L.scala"

def check (m : Mode) (p p' : Prog) : Verdict :=
  verdict (classes m p) (changed p p') [editedFile p.ref]

def bases : List Prog := Id.run do
  let mut out := []
  for owner in [Owner.obj, .top] do
    for trans in [false, true] do
      for via in [Via.direct, .inl, .plain] do
        for ref in Ref.all do
          out := out ++ [{ owner := owner, trans := trans, via := via, ref := ref }]
  return out

inductive Edit | val | ty
  deriving DecidableEq, Repr

def Edit.str : Edit → String | .val => "value" | .ty => "type"

def edits (p : Prog) : List (Edit × Prog) :=
  [(.val, { p with val := 2 })] ++ (if p.ref.typed then [(.ty, { p with str := true })] else [])

/-! ### Families -/

def b0 : Prog := { owner := .obj, trans := false, via := .direct, ref := .dConst }

/-- **Inline constant**: `inline def inl: Any = D.K`, `D.K` edited from `1` to `2`: `D` and `L`
recompile, the client keeps `1`. -/
theorem check_dConst_today :
    check .today b0 { b0 with val := 2 } = ⟨["D", "L"], ["Client"], ["L"]⟩ := by native_decide

/-- Through `this`, the reference survives inlining and the client records `K`. -/
theorem check_thisK_today :
    (check .today { b0 with ref := .thisK } { b0 with ref := .thisK, val := 2 }).clean = true := by
  native_decide

/-- The owner's own constant through its path is folded like another object's. -/
theorem check_pathK_today :
    (check .today { b0 with ref := .pathK } { b0 with ref := .pathK, val := 2 }).stale = ["Client"] := by
  native_decide

/-- A helper's body is not the client's business: nothing but `L` recompiles. -/
theorem check_helper_body_precise :
    check .today { b0 with ref := .helper } { b0 with ref := .helper, val := 2 } = ⟨["L"], [], []⟩ := by
  native_decide

/-- The stale cases today: constants through a path and type-level reads of an alias; and for a
transparent `inl` expanded in typer, every reference whose hash moves without moving `inl`'s. -/
theorem check_today_stale : (bases.all fun p => (edits p).all fun (e, p') =>
    (check .today p p').clean ||
      [Ref.pathK, .dConst, .constValue, .matchN].contains p.ref ||
      p.trans && p.via != .inl && (p.ref == .thisK || e == .ty)) = true := by
  native_decide

theorem check_hashConsts_clean : (bases.all fun p => (edits p).all fun (_, p') =>
    (check .hashConsts p p').clean) = true := by native_decide

theorem check_bodyDeps_clean : (bases.all fun p => (edits p).all fun (_, p') =>
    (check .bodyDeps p p').clean) = true := by native_decide

/-- No mode recompiles a client that reads nothing the edit changed (`L` and `M` may recompile for
nothing: they use the names their bodies read). -/
theorem check_precise : ([Mode.today, .hashConsts, .bodyDeps].all fun m => bases.all fun p =>
    (edits p).all fun (_, p') => !(check m p p').wasted.contains "Client") = true := by native_decide

/-! ### Rendering -/

def tyStr (p : Prog) : String := if p.str then "String" else "Int"

def valStr (p : Prog) : String :=
  if p.str then (if p.val == 1 then "\"a\"" else "\"b\"") else toString p.val

def body (p : Prog) : String :=
  match p.ref with
  | .lit => toString p.val
  | .helper => "h"
  | .priv => "p"
  | .thisK => "K"
  | .pathK => if p.owner == .obj then "L.K" else "conf.K"
  | .dConst | .dInlineVal => "D.K"
  | .dVal => "D.v"
  | .dInline => "D.j"
  | .constValue => "scala.compiletime.constValue[D.N]"
  | .matchN =>
    "inline scala.compiletime.erasedValue[D.N] match {\n    case _: 1 => \"one\"\n    case _ => \"other\"\n  }"

def ownMember (p : Prog) : Option String :=
  match p.ref with
  | .helper => some ("def h: " ++ tyStr p ++ " = " ++ valStr p)
  | .priv => some ("private val p: " ++ tyStr p ++ " = " ++ valStr p)
  | .thisK | .pathK => some ("final val K = " ++ valStr p)
  | _ => none

def lSrc (p : Prog) : String :=
  let inl := (if p.trans then "transparent inline" else "inline") ++ " def inl: Any = " ++ body p
  let ms := (ownMember p).toList ++ [inl]
  match p.owner with
  | .obj => "package conf\n\nobject L {\n" ++ String.join (ms.map ("  " ++ · ++ "\n")) ++ "}\n"
  | .top => "package conf\n\n" ++ String.join (ms.map (· ++ "\n"))

def dSrc (p : Prog) : Option String :=
  let m := match p.ref with
    | .dConst => some ("final val K = " ++ valStr p)
    | .dInlineVal => some ("inline val K = " ++ valStr p)
    | .dVal => some ("val v: " ++ tyStr p ++ " = " ++ valStr p)
    | .dInline => some ("inline def j: Int = " ++ valStr p)
    | .constValue | .matchN => some ("type N = " ++ valStr p)
    | _ => none
  m.map fun m => "package conf\n\nobject D {\n  " ++ m ++ "\n}\n"

def callStr (p : Prog) : String := if p.owner == .obj then "L.inl" else "inl"

def mSrc (p : Prog) : Option String :=
  match p.via with
  | .direct => none
  | .inl => some ("package conf\n\nobject M {\n  inline def w: Any = " ++ callStr p ++ "\n}\n")
  | .plain => some ("package conf\n\nobject M {\n  def w: Any = " ++ callStr p ++ "\n}\n")

def clientSrc (p : Prog) : String :=
  "package conf\n\nobject Client {\n  def x: Any = " ++ (if p.via == .direct then callStr p else "M.w") ++
    "\n}\n"

def files (p : Prog) : List (String × String) :=
  [("L.scala", lSrc p)] ++ ((dSrc p).map ("D.scala", ·)).toList ++ ((mSrc p).map ("M.scala", ·)).toList ++
    [("Client.scala", clientSrc p)]

def fileEdits (p p' : Prog) : List (String × Option String) :=
  ((files p').filter fun f => !(files p).contains f).map fun (n, s) => (n, some s)

def tiers (p : Prog) : List (String × ℕ) := (files p).map fun (n, _) => (n, if n == "Client.scala" then 2 else 1)

def factors (p : Prog) : List (String × String) :=
  [("owner", if p.owner == .obj then "obj" else "top"), ("trans", toString p.trans),
   ("via", match p.via with | .direct => "direct" | .inl => "inl" | .plain => "plain"),
   ("ref", p.ref.str)]

end Inl

/-! ## Opaque types -/

namespace Opq

/-- Where `T` lives: `object O`, or the top level of `O.scala` (class `O$package`). -/
inductive Site | obj | top
  deriving DecidableEq, Repr

/-- The user: a client with a signature mentioning `T`, a call of `mk` returning it, an extension
method on it, an inline `imk` of the owner, an alias `A.S = O.T`, or only another member of the
owner; or a descendant `K`: overriding `Base[O.T].g`, inheriting `Tr.h(t: O.T)` (mixin forwarder),
or inheriting `g` from `Tr2 extends Base[O.T]` (forwarder and bridge). -/
inductive Use | sig | call | ext | inl | alias | other | over | fwd | inhBridge
  deriving DecidableEq, Repr

def Use.all : List Use := [.sig, .call, .ext, .inl, .alias, .other, .over, .fwd, .inhBridge]

def Use.str : Use → String
  | .sig => "sig" | .call => "call" | .ext => "ext" | .inl => "inl" | .alias => "alias"
  | .other => "other" | .over => "over" | .fwd => "fwd" | .inhBridge => "inhBridge"

inductive Rhs | int | long | any
  deriving DecidableEq, Repr

def Rhs.str : Rhs → String | .int => "Int" | .long => "Long" | .any => "Any"

inductive Mode | today | dep | refine
  deriving DecidableEq, Repr

structure Prog where
  site : Site
  use : Use
  rhs : Rhs
  deriving DecidableEq, Repr

def oName (p : Prog) : String := if p.site == .obj then "O" else "O$package"

/-- The owner's keys: its own name covers the right-hand side (the self type), or, with
`refine`, `T` and the members whose signatures mention `T`. -/
def oKeys (m : Mode) (p : Prog) : List (String × List String) :=
  if m == .refine then [("T", ["rhs"]), ("mk", ["rhs"]), ("value", ["rhs"]), ("imk", ["rhs"]), (oName p, [])]
  else [(oName p, ["rhs"]), ("T", []), ("mk", []), ("value", []), ("imk", [])]

/-- What a class that mentions `T` (or calls a member mentioning it) records of the owner. -/
def tUses (p : Prog) (member : String) : List Key :=
  [⟨oName p, oName p⟩, ⟨oName p, "T"⟩] ++ (if member == "" then [] else [⟨oName p, member⟩])

def classes (m : Mode) (p : Prog) : List Cls :=
  let o : Cls := { name := oName p, file := "O.scala", keys := oKeys m p, reads := ["rhs"] }
  let client (uses : List Key) (reads : List String) : Cls :=
    { name := "Client", file := "Client.scala", uses := uses, reads := reads }
  let inheritsT := if m == .dep then tUses p "" else []
  match p.use with
  | .sig => [o, client (tUses p "") ["rhs"]]
  | .call => [o, client (tUses p "mk") ["rhs"]]
  | .ext => [o, client (tUses p "mk" ++ [⟨oName p, "value"⟩]) ["rhs"]]
  | .inl => [o, client (tUses p "imk") ["rhs"]]
  | .alias => [o, { name := "A", file := "A.scala", uses := tUses p "", keys := [("S", [])] },
      client ([⟨"A", "A"⟩, ⟨"A", "S"⟩] ++ tUses p "") ["rhs"]]
  | .other => [o, client [⟨oName p, oName p⟩, ⟨oName p, "other"⟩] []]
  | .over => [o, { name := "Base", file := "Base.scala", keys := [("g", [])] },
      { name := "K", file := "K.scala", uses := tUses p "", parents := ["Base"], reads := ["rhs"] }]
  | .fwd => [o, { name := "Tr", file := "Tr.scala", uses := tUses p "", keys := [("h", [])], reads := ["rhs"] },
      { name := "K", file := "K.scala", uses := inheritsT, parents := ["Tr"], reads := ["rhs"] }]
  | .inhBridge => [o, { name := "Base", file := "Base.scala", keys := [("g", [])] },
      { name := "Tr2", file := "Tr2.scala", uses := tUses p "", parents := ["Base"], keys := [("g", [])], reads := ["rhs"] },
      { name := "K", file := "K.scala", uses := inheritsT, parents := ["Tr2"], reads := ["rhs"] }]

def check (m : Mode) (p p' : Prog) : Verdict :=
  verdict (classes m p) (if p.rhs != p'.rhs then ["rhs"] else []) ["O.scala"]

def bases : List Prog := Id.run do
  let mut out := []
  for site in [Site.obj, .top] do
    for use in Use.all do
      for rhs in [Rhs.int, .long, .any] do
        out := out ++ [{ site := site, use := use, rhs := rhs }]
  return out

def edits (p : Prog) : List (Rhs × Prog) :=
  ([Rhs.int, .long, .any].filter (· != p.rhs)).map fun r => (r, { p with rhs := r })

/-! ### Families -/

def b0 : Prog := { site := .obj, use := .fwd, rhs := .int }

/-- **Opaque forwarder**: `class K extends Tr`, `Tr.h(t: O.T)`; `T = Int` to `T = Any`: `O` and
`Tr` recompile, `K` keeps the forwarder `h(I)I`. -/
theorem check_fwd_today : check .today b0 { b0 with rhs := .any } = ⟨["O", "Tr"], ["K"], []⟩ := by
  native_decide

theorem check_today_stale : (bases.all fun p => (edits p).all fun (_, p') =>
    (check .today p p').clean || [Use.fwd, .inhBridge].contains p.use) = true := by native_decide

theorem check_dep_clean : (bases.all fun p => (edits p).all fun (_, p') => (check .dep p p').clean) = true := by
  native_decide

theorem check_refine_clean_with_dep_gap : (bases.all fun p => (edits p).all fun (_, p') =>
    (check .refine p p').clean || [Use.fwd, .inhBridge].contains p.use) = true := by native_decide

/-- Today an edit of the right-hand side recompiles a client that uses only another member of the
owner; `refine` does not. -/
theorem check_other_wasted :
    (check .today { b0 with use := .other } { b0 with use := .other, rhs := .any }).wasted = ["Client"] ∧
    (check .refine { b0 with use := .other } { b0 with use := .other, rhs := .any }).wasted = [] := by
  native_decide

/-! ### Rendering -/

def oSrc (p : Prog) : String :=
  let ms := ["opaque type T = " ++ p.rhs.str, "def mk(x: Int): T = x",
    "extension (t: T) def value: Int = 0", "inline def imk(x: Int): T = x", "def other: Int = 1"]
  match p.site with
  | .obj => "package conf\n\nobject O {\n" ++ String.join (ms.map ("  " ++ · ++ "\n")) ++ "}\n"
  | .top => "package conf\n\n" ++ String.join (ms.map (· ++ "\n"))

def q (p : Prog) (s : String) : String := if p.site == .obj then "O." ++ s else s

def obj (n body : String) : String := "package conf\n\nobject " ++ n ++ " {\n" ++ body ++ "}\n"

def files (p : Prog) : List (String × String) :=
  let t := q p "T"
  let base := ("Base.scala", "package conf\n\ntrait Base[A] {\n  def g(a: A): Int\n}\n")
  [("O.scala", oSrc p)] ++ match p.use with
  | .sig => [("Client.scala", obj "Client" ("  def f(t: " ++ t ++ "): " ++ t ++ " = t\n"))]
  | .call => [("Client.scala", obj "Client" ("  def a: Any = " ++ q p "mk(1)" ++ "\n"))]
  | .ext => [("Client.scala", obj "Client" ("  def a: Any = " ++ q p "mk(1)" ++ ".value\n"))]
  | .inl => [("Client.scala", obj "Client" ("  def a: Any = " ++ q p "imk(1)" ++ "\n"))]
  | .alias => [("A.scala", obj "A" ("  type S = " ++ t ++ "\n")),
      ("Client.scala", obj "Client" "  def f(s: A.S): A.S = s\n")]
  | .other => [("Client.scala", obj "Client" ("  def a: Int = " ++ q p "other" ++ "\n"))]
  | .over => [base, ("K.scala", "package conf\n\nclass K extends Base[" ++ t ++ "] {\n  def g(a: " ++ t ++
      "): Int = 0\n}\n")]
  | .fwd => [("Tr.scala", "package conf\n\ntrait Tr {\n  def h(t: " ++ t ++ "): Int = 0\n}\n"),
      ("K.scala", "package conf\n\nclass K extends Tr\n")]
  | .inhBridge => [base, ("Tr2.scala", "package conf\n\ntrait Tr2 extends Base[" ++ t ++ "] {\n  def g(a: " ++
      t ++ "): Int = 0\n}\n"), ("K.scala", "package conf\n\nclass K extends Tr2\n")]

def tiers (p : Prog) : List (String × ℕ) :=
  (files p).map fun (n, _) => (n, if n == "Client.scala" || n == "K.scala" then 2 else 1)

def factors (p : Prog) : List (String × String) :=
  [("site", if p.site == .obj then "obj" else "top"), ("use", p.use.str), ("rhs", p.rhs.str)]

end Opq

end Zinc.InlineOpaque
