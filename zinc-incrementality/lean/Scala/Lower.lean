import Zinc.Task
import Jvm.Link
import Scala.Syntax

/-!
# Lowering a Scala subset to classfiles, as a `Task`

Lowering a unit reads other definitions' interfaces (`Q.decl`), which is what scalac reads from
pickles or TASTy: an ancestor's members for linearization, mixin forwarders and bridges, a value
class's underlying type for erasure. So a unit's lowering has a trace, and T1 (`lower_congr`)
says an environment that agrees on it gives the same classfiles.

The output is a `Jvm.Classfile` (`ClassOut.toJvm`) plus what `Jvm` does not model yet: fields,
access, `ACC_BRIDGE`, and the invoke instructions of synthesized bodies (forwarders, bridges,
`$init$` calls). Those are compared with scalac's classfiles by the calibration probe
(`probes/scala`).

The rules are scalac 2.13's; where 2.12 or Scala 3 differs, the code branches on `Dialect` and says so.
-/

namespace Scala

inductive Q | decl (n : String) (isObj : Bool)
  deriving DecidableEq, Repr

/-- A definition's interface, and whether this compiler run reads it from source (it is one of the
run's units) or from a pickle (TASTy, or Scala 2's pickle) on the classpath. -/
structure View where
  decl : Decl
  inRun : Bool := true
  deriving DecidableEq, Repr

def Ans : Q → Type
  | .decl .. => Option View

/-- The environment of a compiler run over the units `run` of `p`; the others are on the
classpath. -/
def Program.envIn (p : Program) (run : List String) : (q : Q) → Ans q
  | .decl n o => (p.find? (·.name = n)).bind fun s =>
    ((if o then s.obj else s.cls).map fun d => { decl := d, inRun := run.contains n })

/-- The environment of one run over the whole program. -/
def Program.env (p : Program) : (q : Q) → Ans q := p.envIn (p.map (·.name))

abbrev M := ExceptT String (Zinc.Task Q Ans)

def askDecl (n : String) (o : Bool) : M (Option View) :=
  ExceptT.lift (Zinc.Task.ask (Q.decl n o) Zinc.Task.pure : Zinc.Task Q Ans (Option View))

def needView (n : String) : M View := do
  match ← askDecl n false with
  | some v => pure v
  | none => throw s!"not found: {n}"

def need (n : String) : M Decl := (·.decl) <$> needView n

/-! ## Linearization and member lookup -/

/-- A base class with its type argument as the class being lowered sees it: `C.this baseType A`.
The class itself comes first, applied to its own parameter. -/
abbrev Anc := Decl × Option Ty

/-- The base-type facts of a top-level class `self` with base classes `l`, for `AsSeenFrom`. Only
`self.this` has base types; the prefix of a top-level class is its package, where the walk stops. -/
def classWorld (self : String) (l : List Anc) : AsSeenFrom.World String Ty where
  bpre _ _ := .this []
  hasBase p c := p == .this [self] && l.any fun (a, _) => [a.name] == c
  bargs p c := if p == .this [self] then
      ((l.find? fun (a, _) => [a.name] == c).bind (·.2)).toList
    else []

/-- `info.asSeenFrom(self.this, owner)`. -/
def seenFrom (self : String) (l : List Anc) (owner : String) (t : Ty) : Ty :=
  AsSeenFrom.asf (classWorld self l) (.this [self]) [owner] t

/-- Scala's linearization, the class first: `L(C) = C, L(Pn) +⃗ … +⃗ L(P1)`. A parent `P[a]`'s base
types are viewed from `C` by `asSeenFrom(C.this, P)`, which replaces `P`'s parameter by `a`
(scalac's `baseType`). -/
def lin : ℕ → Decl → M (List Anc)
  | 0, _ => throw "linearization too deep"
  | k + 1, d => do
    let mut acc : List Anc := []
    for (p, pa) in d.parents do
      let pd ← need p
      let lp ← lin k pd
      let w := classWorld d.name [(pd, pa)]
      let lp := lp.map fun (a, t) => (a, t.map (AsSeenFrom.asf w (.this [d.name]) [p]))
      acc := lp.filter (fun e => !acc.any (·.1.name == e.1.name)) ++ acc
    pure ((d, if d.tparam then some (Ty.X d.name) else none) :: acc)

def fuel : ℕ := 8

/-- A member as seen from the class: its owner, the owner's type argument, the member. -/
abbrev Hit := Anc × Mem

/-- The members named `n` along the linearization `l` of a class (the class first). A private
member is not inherited: only the class's own private members are seen. -/
def hits (l : List Anc) (n : String) : List Hit :=
  let self := (l.head?.map (·.1.name)).getD ""
  l.filterMap fun (d, a) => ((d.members.find? (·.name == n)).filter fun m => !m.priv || d.name == self).map
    fun m => ((d, a), m)

/-- The inherited members named `n`. -/
def hitsAbove (l : List Anc) (n : String) : List Hit :=
  let self := (l.head?.map (·.1.name)).getD ""
  (hits l n).filter (·.1.1.name != self)

/-- `C.this.memberType(m)`'s parameter types, for a member `m` of base class `owner` of `C`. -/
def paramsSeen (self : String) (l : List Anc) (h : Hit) : List Ty :=
  h.2.allParams.map (seenFrom self l h.1.1.name)

/-- Does `h` override (or implement) `h'` in `C`? Same name, and the same parameter types as seen
from `C` (`matches` after `memberType`); otherwise they are overloads. -/
def overridesIn (self : String) (l : List Anc) (h h' : Hit) : Bool :=
  h.2.name == h'.2.name && paramsSeen self l h == paramsSeen self l h'

def memberNames (l : List Anc) : List String :=
  (l.flatMap fun (d, _) => d.members.map (·.name)).dedup

def Hit.same (h h' : Hit) : Bool := h.1.1.name == h'.1.1.name && h.2 == h'.2

/-- The members of `C` by signature: each name's hits, grouped by `overridesIn` (members that
override one another as seen from `C`), in linearization order. Overloads are separate groups. -/
def sigGroups (self : String) (l : List Anc) : List (List Hit) :=
  (memberNames l).flatMap fun n =>
    (hits l n).foldl (init := []) fun gs h =>
      match gs.findIdx? fun g => (g.head?.map fun r => overridesIn self l r h).getD false with
      | some i => gs.modify i (· ++ [h])
      | none => gs ++ [[h]]

/-- The member a group resolves to: the first concrete one, else the first. -/
def winner (g : List Hit) : Option Hit := (g.find? (!·.2.abs)).or g.head?

/-- Member lookup by signature: what `h`'s group resolves to in `C`. -/
def lookupSig (self : String) (l : List Anc) (h : Hit) : Option Hit :=
  ((sigGroups self l).find? fun g => g.any (Hit.same h)).bind winner

/-- Traits mixed in by `d` itself: those before the superclass's linearization. -/
def mixins (d : Decl) (l : List Anc) : M (List Anc) := do
  match d.super with
  | none => pure (l.tail.filter (·.1.kind == .trt))
  | some (s, _) =>
    let ls ← lin fuel (← need s)
    pure (l.tail.filter fun e => e.1.kind == .trt && !ls.any (·.1.name == e.1.name))

/-! ## Erasure -/

def jname (n : String) : String := s!"L{n};"

/-- Erasure of a type in a descriptor. A value class erases to its underlying type, which needs
its declaration. -/
def erase : Ty → M String
  | .int => pure "I"
  | .bool => pure "Z"
  | .unit => pure "V"
  | .str => pure "Ljava/lang/String;"
  | .obj | .tp .. => pure "Ljava/lang/Object;"
  | .this c => pure (jname (c.headD ""))
  | .ref n => do
    let d ← need n
    match d.kind, d.under with
    | .vcls, some (_, .int) => pure "I"
    | .vcls, some (_, .str) => pure "Ljava/lang/String;"
    | .vcls, some _ => pure "Ljava/lang/Object;"
    | _, _ => pure (jname n)

/-- Erasure as a parameter: `Unit` is boxed. -/
def eraseP (t : Ty) : M String := do
  let e ← erase t
  pure (if e == "V" then "Lscala/runtime/BoxedUnit;" else e)

def descOf (pre : List String) (ps : List Ty) (r : Ty) : M String := do
  let ps ← ps.mapM eraseP
  pure s!"({String.join (pre ++ ps)}){← erase r}"

/-- The descriptor of a member as declared in its owner. -/
def Mem.desc (m : Mem) : M String := descOf [] m.allParams m.res

/-! ## Output -/

structure Insn where
  op : String
  owner : String
  name : String
  desc : String
  deriving DecidableEq, Repr

structure MOut where
  name : String
  desc : String
  static : Bool := false
  abs : Bool := false
  final : Bool := false
  priv : Bool := false
  bridge : Bool := false
  /-- A trait field's setter, `T$_setter_$v_$eq`. -/
  setter : Bool := false
  /-- The invokes of a synthesized body; `none` for a user body, which is not compared. For a
  constructor, only its `$init$` calls. -/
  calls : Option (List Insn) := none
  deriving DecidableEq, Repr

structure FOut where
  name : String
  desc : String
  static : Bool := false
  final : Bool := false
  priv : Bool := true
  deriving DecidableEq, Repr

structure ClassOut where
  name : String
  itf : Bool := false
  abs : Bool := false
  final : Bool := false
  super : Option String := none
  ifaces : List String := []
  methods : List MOut := []
  fields : List FOut := []
  /-- Only part of the classfile is modelled (a class implementing a trait's `lazy val`); the
  probe compares only what is listed. -/
  partly : Bool := false
  deriving DecidableEq, Repr

def ClassOut.toJvm (c : ClassOut) : Jvm.Classfile String String String where
  header := { isInterface := c.itf, isAbstract := c.abs, isFinal := c.final, super := c.super,
              ifaces := c.ifaces }
  methods := c.methods.map fun m =>
    (m.name, m.desc, { isStatic := m.static, isAbstract := m.abs, isFinal := m.final })

def toWorld (cs : List ClassOut) : Jvm.World String String String :=
  fun n => (cs.find? (·.name == n)).map ClassOut.toJvm

/-! ## Lowering -/

def setterName (t : String) (v : String) : String := s!"{t}$_setter_${v}_$eq"

/-- Does a trait have an initialiser `$init$`, and do its subclasses' constructors call it? Scala
2: unless the trait is an interface (no concrete member). Scala 3: if it has a statement or a field
to initialise; here, a concrete `val`. Also, *when the trait is compiled in the same run*, if it has
a `lazy val` or an extension method (even an abstract one). Read from TASTy, such a trait has
`NoInits`, so a subclass compiled apart from it does not call the `$init$` the trait has (F6 in
`PLAN.md`; the extension case is new). -/
def hasInit (dl : Dialect) (inRun : Bool) (t : Decl) : Bool :=
  match dl with
  | .s212 | .s213 => t.members.any (!·.abs)
  | .s3 => t.members.any fun m =>
    (m.isVal && !m.abs && !m.lzy) || (inRun && (m.lzy || m.ext.isSome))

/-- The classfile's interfaces: the direct trait parents, minus those another direct parent
already extends. -/
def ifacesOf (d : Decl) : M (List String) := do
  let ps ← d.parents.mapM fun (p, _) => do pure (p, ← lin fuel (← need p))
  pure (d.traits.map (·.1) |>.filter fun t =>
    !ps.any fun (p, l) => p != t && l.any (·.1.name == t))


/-- Add `m` unless a method of the same name and descriptor is already there. -/
def addM (ms : List MOut) (m : MOut) : List MOut :=
  if ms.any fun x => x.name == m.name && x.desc == m.desc then ms else ms ++ [m]

def ctorName : String := "<init>"

/-- A value class: its name, field and erased underlying type. -/
def vclsOf (t : Ty) : M (Option (String × String × String)) := do
  match t with
  | .ref n =>
    let d ← need n
    match d.kind, d.under with
    | .vcls, some (x, u) => pure (some (n, x, ← erase u))
    | _, _ => pure none
  | _ => pure none

/-- Bridges in class `d`: for each method `d` defines (its own and its mixin forwarders), an
ancestor's member it overrides (`overridesIn`, by `memberType`) whose erasure differs, unless the
superclass already pairs the two. -/
def bridges (self : String) (l : List Anc) (sup : List Anc) (ms : List MOut) :
    M (List MOut) := do
  let mut out := ms
  for g in sigGroups self l do
    let some ((o, _), m) := winner g | continue
    if m.abs then continue
    let n := m.name
    let e ← m.desc
    for ((a, _), m') in g do
      if a.name == o.name then continue
      let e' ← m'.desc
      if e' == e then continue
      if sup.any (·.1.name == o.name) && sup.any (·.1.name == a.name) then continue
      -- a value class in the target's signature is unboxed (argument) or boxed (result)
      let unbox ← m.allParams.filterMapM vclsOf
      let box ← (vclsOf m.res)
      let call : Insn := ⟨"invokevirtual", self, n, e⟩
      let calls : List Insn := unbox.map (fun (v, x, u) => ⟨"invokevirtual", v, x, s!"(){u}"⟩) ++ [call] ++
        box.toList.map fun (v, _, u) => ⟨"invokespecial", v, ctorName, s!"({u})V"⟩
      out := addM out { name := n, desc := e', bridge := true, calls := some calls }
  pure out

/-- Members of a class, object or value class body: its own members and, for each trait it mixes
in, forwarders to the trait's concrete methods and implementations of the trait's fields. Fields of an
object are static from 2.13 on; a trait's field implemented in a class is final in 2.12 only. -/
def classBody (dl : Dialect) (d : Decl) (isObj : Bool) (l : List Anc) :
    M (List MOut × List FOut × List Anc) := do
  let mut ms : List MOut := []
  let mut fs : List FOut := []
  for m in d.members do
    if m.static then continue
    let e ← m.desc
    if m.isVal && !m.abs then
      fs := fs ++ [{ name := m.name, desc := ← erase m.res, static := isObj && dl != .s212, final := true }]
    ms := addM ms { name := m.name, desc := e, abs := m.abs, final := m.final }
  let mx ← mixins d l
  for (t, _) in mx do
    for m in t.members do
      if m.lzy then continue
      let some ((o, _), w) := lookupSig d.name l ((t, none), m) | continue
      if o.name != t.name || w.abs then continue
      let e ← m.desc
      if m.isVal then
        fs := fs ++ [{ name := m.name, desc := ← erase m.res, static := isObj && dl != .s212, final := dl == .s212 }]
        ms := addM ms { name := m.name, desc := e }
        ms := addM ms { name := setterName t.name m.name, desc := s!"({← erase m.res})V", setter := true }
      else
        let sd ← descOf [jname t.name] m.allParams m.res
        let call : Insn := ⟨"invokestatic", t.name, m.name ++ "$", sd⟩
        ms := addM ms { name := m.name, desc := e, final := m.final, calls := some [call] }
  pure (ms, fs, mx)

/-- The `$init$` calls of a constructor: the mixed-in traits, base first. -/
def initCalls (dl : Dialect) (mx : List Anc) : M (List Insn) := do
  let ts ← mx.reverse.filterM fun (t, _) => do pure (hasInit dl (← needView t.name).inRun t)
  pure <| ts.map fun (t, _) => ⟨"invokestatic", t.name, "$init$", s!"({jname t.name})V"⟩

/-- Does `d` implement a trait's `lazy val`? Its classfile is then only partly modelled. -/
def implementsLazy (mx : List Anc) : Bool := mx.any fun (t, _) => t.members.any (·.lzy)

def lowerTrait (dl : Dialect) (d : Decl) : M ClassOut := do
  let mut ms : List MOut := []
  for m in d.members do
    let e ← m.desc
    if m.isVal && !m.lzy then
      ms := ms ++ [{ name := m.name, desc := e, abs := true }]
      if !m.abs then
        ms := ms ++ [{ name := setterName d.name m.name, desc := s!"({← erase m.res})V", abs := true }]
    else if m.abs then
      ms := ms ++ [{ name := m.name, desc := e, abs := true }]
    else
      ms := ms ++ [{ name := m.name, desc := e },
                   { name := m.name ++ "$", desc := ← descOf [jname d.name] m.allParams m.res, static := true,
                     calls := some [⟨"invokespecial", d.name, m.name, e⟩] }]
  if hasInit dl true d then
    ms := ms ++ [{ name := "$init$", desc := s!"({jname d.name})V", static := true }]
  pure { name := d.name, itf := true, abs := true, ifaces := ← ifacesOf d, methods := ms }

def superLin (d : Decl) : M (List Anc) := do
  match d.super with
  | none => pure []
  | some (s, _) => lin fuel (← need s)

def lowerClass (dl : Dialect) (d : Decl) : M ClassOut := do
  let l ← lin fuel d
  let (ms, fs, mx) ← classBody dl d false l
  let ctor : MOut := { name := ctorName, desc := "()V", calls := some (← initCalls dl mx) }
  let ms ← bridges d.name l (← superLin d) (ms ++ [ctor])
  let part := implementsLazy mx
  pure { name := d.name, abs := d.abs, final := d.final, super := d.super.map (·.1),
         ifaces := ← ifacesOf d, methods := if part then [ctor] else ms, fields := if part then [] else fs,
         partly := part }

def moduleName (n : String) : String := n ++ "$"

/-- A value class: the underlying field and its getter, each method forwarding to its extension
method in the companion, and `hashCode`/`equals` likewise. -/
def lowerVcls (d : Decl) : M ClassOut := do
  let some (x, u) := d.under | throw "value class without parameter"
  let eu ← erase u
  let mod := moduleName d.name
  let get : Insn := ⟨"getstatic", mod, "MODULE$", jname mod⟩
  let getx : Insn := ⟨"invokevirtual", d.name, x, s!"(){eu}"⟩
  let mut ms : List MOut := [{ name := x, desc := s!"(){eu}" }]
  let exts : List (String × List Ty × Ty) :=
    (d.members.filter fun m => !m.isVal).map fun m => (m.name, m.params, m.res)
  for (n, ps, r) in exts ++ [("hashCode", [], .int), ("equals", [.obj], .bool)] do
    let r' ← erase r
    let e := s!"({String.join (← ps.mapM eraseP)}){r'}"
    let ee := s!"({eu}{String.join (← ps.mapM eraseP)}){r'}"
    ms := ms ++ [{ name := n, desc := e, calls := some [get, getx, ⟨"invokevirtual", mod, n ++ "$extension", ee⟩] }]
  ms := ms ++ [{ name := ctorName, desc := s!"({eu})V", calls := some [] }]
  pure { name := d.name, final := true, ifaces := ← ifacesOf d, methods := ms,
         fields := [{ name := x, desc := eu, final := true }] }

/-- The extension methods a value class's companion gets. -/
def extensions (d : Decl) : M (List MOut) := do
  let some (_, u) := d.under | pure []
  let eu ← erase u
  let exts : List (String × List Ty × Ty) :=
    (d.members.filter fun m => !m.isVal).map fun m => (m.name, m.params, m.res)
  let all : List (String × List Ty × Ty) := exts ++ [("hashCode", [], .int), ("equals", [.obj], .bool)]
  all.mapM fun (n, ps, r) => do
    let r' ← erase r
    pure ({ name := n ++ "$extension", desc := s!"({eu}{String.join (← ps.mapM eraseP)}){r'}", final := true } : MOut)

def lowerObject (dl : Dialect) (d : Decl) (vc : Option Decl) : M ClassOut := do
  let self := moduleName d.name
  let l ← lin fuel d
  let (ms, fs, mx) ← classBody dl d true l
  let ms ← bridges self l (← superLin d) ms
  let ms := ms ++ (← match vc with | some v => extensions v | none => pure [])
  -- 2.12 initialises an object in its constructor, later versions in its static initialiser
  let inits ← initCalls dl mx
  let extra : List MOut :=
    [{ name := ctorName, desc := "()V", priv := true, calls := some (if dl == .s212 then inits else []) },
     { name := "<clinit>", desc := "()V", static := true, calls := some (if dl == .s212 then [] else inits) }] ++
    (if dl == .s3 then [{ name := "writeReplace", desc := "()Ljava/lang/Object;", priv := true }] else [])
  -- Scala 3 objects are serializable.
  let ser := if dl == .s3 then ["java/io/Serializable"] else []
  let part := implementsLazy mx
  pure { name := self, final := true, super := d.super.map (·.1), ifaces := (← ifacesOf d) ++ ser,
         -- (Scala 3's static initialiser of an object with a lazy val is private)
         methods := if part then (extra.take 2).map (fun m =>
             if m.name == "<clinit>" && dl == .s3 then { m with priv := true } else m)
           else ms ++ extra,
         fields := (if part then [] else [{ name := "MODULE$", desc := jname self, static := true, final := dl != .s212, priv := false }] ++ fs),
         partly := part }

/-- Static forwarders in the companion class (or a mirror class) for the object's public methods,
its own and inherited, except those whose name the companion class also has. Scala 2 skips
trait setters and bridges; Scala 3 forwards setters, and some bridges. -/
def forwarders (dl : Dialect) (od : Decl) (o : ClassOut) (clsNames : List String) : M (List MOut) := do
  let l ← lin fuel od
  let mut cands := o.methods.filter fun m =>
    !m.static && !m.priv && !m.abs && !m.bridge && m.name != ctorName &&
    !(dl != .s3 && m.setter)
  -- Scala 3 forwards a bridge too, when the member of that erased signature found first along
  -- the linearization is concrete: dotc looks members up by signature, and skips deferred ones.
  if dl == .s3 then
    for b in o.methods.filter (·.bridge) do
      let sameSig ← (hitsAbove l b.name).filterM fun (_, m) => do pure ((← m.desc) == b.desc)
      let concrete := match sameSig with
        | (_, m) :: _ => !m.abs
        | [] => false
      if concrete then cands := cands ++ [b]
  for g in sigGroups od.name l do
    let some ((w, _), m) := winner g | continue
    let n := m.name
    let e ← m.desc
    if m.abs || m.static || cands.any (fun c => c.name == n && c.desc == e) then continue
    cands := cands ++ [{ name := n, desc := e }]
    if dl == .s3 && m.isVal && !m.lzy then
      cands := cands ++ [{ name := setterName w.name n, desc := s!"({← erase m.res})V" }]
  pure <| (cands.filter fun m => !clsNames.contains m.name).map fun m =>
    { name := m.name, desc := m.desc, static := true,
      calls := some [⟨"getstatic", o.name, "MODULE$", jname o.name⟩, ⟨"invokevirtual", o.name, m.name, m.desc⟩] }

/-- Scala 3 `@static` members of an object move to its companion class: a method, or a field
initialised in the class's static initialiser (which is private). -/
def statics (od : Decl) : M (List MOut × List FOut) := do
  let ss := od.members.filter (·.static)
  let ms ← (ss.filter (!·.isVal)).mapM fun m => do pure ({ name := m.name, desc := ← m.desc, static := true } : MOut)
  let fs ← (ss.filter (·.isVal)).mapM fun m => do
    pure ({ name := m.name, desc := ← erase m.res, static := true, final := true, priv := false } : FOut)
  let clinit : List MOut := if fs.isEmpty then [] else [{ name := "<clinit>", desc := "()V", static := true, priv := true }]
  pure (ms ++ clinit, fs)

def lowerSrc (dl : Dialect) (s : Src) : M (List ClassOut) := do
  let c ← match s.cls with
    | none => pure none
    | some d => match d.kind with
      | .trt => some <$> lowerTrait dl d
      | .vcls => some <$> lowerVcls d
      | _ => some <$> lowerClass dl d
  let vc := s.cls.filter (·.kind == .vcls)
  match s.obj with
  | some od =>
    let o ← lowerObject dl od vc
    match c with
    | some c =>
      let clsNames := (← match s.cls with
        | some d => do pure (memberNames (← lin fuel d))
        | none => pure []) ++ c.methods.map (·.name)
      let fw ← forwarders dl od o clsNames
      let (sm, sf) ← statics od
      pure [{ c with methods := c.methods ++ sm ++ fw.filter (fun f =>
                !c.methods.any fun m => m.name == f.name && m.desc == f.desc),
                     fields := c.fields ++ sf }, o]
    | none =>
      let (sm, sf) ← statics od
      pure [{ name := s.name, final := true, methods := sm ++ (← forwarders dl od o []), fields := sf }, o]
  | none =>
    match vc, c with
    | some v, some c => do
      -- a value class always has a companion
      let od : Decl := { name := v.name, kind := .obj }
      let o ← lowerObject dl od vc
      pure [{ c with methods := c.methods ++ (← forwarders dl od o (c.methods.map (·.name))) }, o]
    | _, _ => pure c.toList

/-- Lower a unit against an environment of interfaces. -/
def lower (dl : Dialect) (s : Src) (env : (q : Q) → Ans q) : Except String (List ClassOut) :=
  (lowerSrc dl s).run.run env

def trace (dl : Dialect) (s : Src) (env : (q : Q) → Ans q) : List Q :=
  (lowerSrc dl s).run.trace env

/-- **T1 for lowering.** An environment that agrees on a unit's trace lowers it to the same
classfiles. -/
theorem lower_congr (dl : Dialect) (s : Src) (e e' : (q : Q) → Ans q)
    (h : ∀ q ∈ trace dl s e, e q = e' q) : lower dl s e = lower dl s e' :=
  (Zinc.Task.run_eq_of_trace _ e e' h).1

def lowerProgram (dl : Dialect) (p : Program) : Except String (List ClassOut) := do
  let cs ← p.mapM fun s => lower dl s p.env
  pure cs.flatten

/-- Separate compilation: the units `lib` in one run, then the rest in a second run that reads
`lib` from the classpath. -/
def lowerSeparately (dl : Dialect) (p : Program) (lib : List String) : Except String (List ClassOut) := do
  let cs ← p.mapM fun s =>
    if lib.contains s.name then lower dl s (p.envIn lib) else lower dl s (p.envIn (p.map (·.name) |>.filter (!lib.contains ·)))
  pure cs.flatten

end Scala
