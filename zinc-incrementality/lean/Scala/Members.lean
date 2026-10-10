import Scala.Lower

/-!
# Membership and overriding: Scala's refchecks, as a `Task`

For a class `C` the verdict is either the errors scalac (or dotc) reports for `C`, or, per
signature, the member a selection on `C` runs. It is computed over `C`'s interfaces only (`lin`,
`sigGroups`, `memberType` from `Lower` and `AsSeenFrom`), so it is a `Task` like lowering.

The checks are `RefChecks.checkAllOverrides`, per *overriding pair* `(member, other)`: `member` is
`C`'s member of a signature group (its first, along the linearization; they match as seen from
`C`), `other` a later one. A pair is checked in the class where it first meets, so it is skipped
when some parent of `C` already has both owners as base classes. An abstract member overriding a
concrete one is no pair. Only the first failing check of a member's first failing pair is reported, in `checkOverride`'s
order: access, `final`, a missing `override` (an inherited `override` that overrides nothing in its
own class counts as missing), accidental override (no third member overridden by both), `def`
over `val`, lazy against strict, result type. A private member is not inherited, so it is
in no pair with an inherited member (`Lower.hits`). Per class: `override` that overrides nothing,
and an abstract member left in a concrete class.

The member a selection runs is the group's first concrete member along the linearization
(`Lower.winner`): a concrete member is never overridden by an abstract one.

`membersSpace` is the calibration space; `probes/scala/members.py` compares its verdicts with
scalac 2.12, 2.13 and dotc 3, including the programs they reject.
-/

namespace Scala.Members

inductive Kind
  | needsOverride
  | conflicting
  | accidental
  | overridesNothing
  | finalOverride
  | needsAbstract
  | stable
  | lazyMismatch
  | weakerAccess
  | illegalModifiers
  | resultType
  deriving DecidableEq, Repr

def Kind.name : Kind → String
  | .needsOverride => "needsOverride" | .conflicting => "conflicting"
  | .overridesNothing => "overridesNothing" | .finalOverride => "finalOverride"
  | .accidental => "accidental" | .needsAbstract => "needsAbstract" | .stable => "stable"
  | .lazyMismatch => "lazyMismatch" | .weakerAccess => "weakerAccess"
  | .illegalModifiers => "illegalModifiers" | .resultType => "resultType"

/-- An error is reported for a class (or object, or trait). -/
structure Err where
  cls : String
  kind : Kind
  deriving DecidableEq, Repr

/-- The compiler stops before refchecks when an earlier phase reported an error. -/
def Kind.phase : Kind → Nat
  | .illegalModifiers => 0
  | _ => 1

def isBase (l : List Anc) (a : String) : Bool := l.any (·.1.name == a)

/-- Does a member carry `override`? Explicitly, or as printed: iff it overrides something in its
own class's linearization. -/
def hasOverride (owner : Decl) (m : Mem) : M Bool := do
  match m.ov with
  | some b => pure b
  | none =>
    let lo ← lin fuel owner
    match lo.head? with
    | some a => pure ((hitsAbove lo m.name).any (overridesIn owner.name lo (a, m)))
    | none => pure false

/-- `t <: u` for the types the spaces use: equal, or a reference type below `Object`. -/
def conforms (t u : Ty) : Bool :=
  t == u || (u == .obj && match t with | .int | .bool | .unit => false | _ => true)

/-- The member of a signature group that a selection on the class runs: the first concrete,
non-private one, unless an abstract member of a subclass of its owner comes earlier (the subclass
re-abstracts it). Only a class re-abstracts; an abstract member of a trait does not. `none` when the group has no such member: the class's member is abstract. -/
def effWinner (self : String) (g : List Hit) : M (Option Hit) := do
  let mut seen : List Hit := []
  for h in g do
    if h.2.priv && h.1.1.name != self then continue
    if !h.2.abs && !h.2.priv then
      let mut reabs := false
      for x in seen do
        if x.2.abs && x.1.1.kind != .trt && isBase (← lin fuel x.1.1) h.1.1.name then reabs := true
      if !reabs then return some h
    seen := seen ++ [h]
  pure none

/-- The refchecks errors of definition `d` (a class, trait or object). -/
def checkDecl (dl : Dialect) (d : Decl) : M (List Err) := do
  let l ← lin fuel d
  let pls ← d.parents.mapM fun (p, _) => do lin fuel (← need p)
  let mut ks : List Kind := []
  -- Scala 3 rejects `override private` before refchecks
  if dl == .s3 && d.members.any (fun m => m.priv && m.ov == some true) then
    ks := ks ++ [.illegalModifiers]
  for g in sigGroups d.name l do
    -- `override` that overrides nothing
    for h in g do
      if h.1.1.name == d.name && h.2.ov == some true && g.length == 1 then
        ks := ks ++ [.overridesNothing]
    -- The lower members of pairs: every member no earlier non-private concrete member
    -- overrides. Scala 2 stops at a private member of `C`; Scala 3 also checks the inherited
    -- member it fails to hide.
    let lows := g.zipIdx.filter fun (_, i) => !(g.take i).any fun x => !x.2.priv && !x.2.abs
    let lows := if dl != .s3 && (g.head?.any (·.2.priv)) then lows.take 1 else lows
    for (mh, i) in lows do
      let mo := mh.1.1
      let m := mh.2
      let lmo ← lin fuel mo
      -- `override` counts only if it overrides something in the owner (else "overrides nothing")
      let ov ← hasOverride mo m
      let overridesInOwner := (hitsAbove lmo m.name).any (overridesIn mo.name lmo ((mo, []), m))
      -- `checkOverride`: the first failing check of the first failing pair
      let mut found : Option Kind := none
      for oh in g.drop (i + 1) do
        if found.isSome then break
        let oo := oh.1.1
        let o := oh.2
        if mo.name == oo.name then continue
        -- a pair a parent has was checked there (2.13 checks it again)
        if dl != .s213 && pls.any fun pl => isBase pl mo.name && isBase pl oo.name then continue
        let loo ← lin fuel oo
        -- an abstract member forms no pair with a concrete one; Scala 3 checks it when it
        -- re-abstracts a member of a base class
        if m.abs && !o.abs && (dl != .s3 || !isBase lmo oo.name) then continue
        let third := g.any fun x => x.1.1.name != mo.name && x.1.1.name != oo.name &&
          isBase lmo x.1.1.name && isBase loo x.1.1.name
        let both := !o.abs && !m.abs
        found :=
          if m.priv && !(dl == .s3 && m.ov == some true) then some .weakerAccess
          else if o.final then some .finalOverride
          else if both && !(ov && (mo.name == d.name || overridesInOwner)) then
            some (if mo.name == d.name then .needsOverride else .conflicting)
          -- an inherited `override` of a member `other`'s owner does not have, with no third
          -- member overridden by both
          else if both && !isBase lmo oo.name && !third then some .accidental
          else if o.isVal && !m.isVal then some .stable
          else if o.isVal && m.isVal && !o.abs && o.lzy != m.lzy then some .lazyMismatch
          else if !conforms (seenFrom d.name l mo.name m.res) (seenFrom d.name l oo.name o.res) then
            some .resultType
          else none
      if let some k := found then ks := ks ++ [k]
  -- an abstract member left in a concrete class
  if d.kind != .trt && !d.abs then
    for g in sigGroups d.name l do
      if g.any (fun h => h.2.abs && !h.2.priv) && (← effWinner d.name g).isNone then
        ks := ks ++ [.needsAbstract]
  pure (ks.eraseDups.map fun k => { cls := d.name, kind := k })

/-- The errors the compiler reports for a program: those of the earliest phase that has any. -/
def errors (dl : Dialect) (p : Program) : Except String (List Err) := do
  let es ← p.flatMap (fun s => s.cls.toList ++ s.obj.toList) |>.mapM fun d =>
    (checkDecl dl d).run.run p.env
  let es := es.flatten
  match (es.map (·.kind.phase)).min? with
  | some ph => pure (es.filter (·.kind.phase == ph))
  | none => pure []

/-- For each concrete class, the owner of the `m` a selection runs (none if `m` is private). -/
def runs (p : Program) : List (String × String) :=
  p.filterMap fun s => do
    let d ← s.cls
    if d.kind == .trt || d.abs then none
    let r : M (Option Hit) := do
      let l ← lin fuel d
      match (sigGroups d.name l).find? fun g => g.any (·.2.name == "m") with
      | some g => effWinner d.name g
      | none => pure none
    match r.run.run p.env with
    | .ok (some w) => pure (d.name, w.1.1.name)
    | _ => none

/-! ## The calibration space -/

/-- How an owner declares `m: String`. -/
inductive V
  | none | abs | conc | ovr | fin | val | lval | ovrVal | ovrLval | priv | ovrPriv
  deriving DecidableEq, Repr

def V.mem (owner : String) : V → Option Mem
  | V.none => Option.none
  | v =>
    let base : Mem := { name := "m", res := .str, nullary := true, rhs := some s!"\"{owner}\"", ov := some false }
    some <| match v with
      | .abs => { base with abs := true }
      | .ovr => { base with ov := some true }
      | .fin => { base with final := true }
      | .val => { base with isVal := true }
      | .lval => { base with isVal := true, lzy := true }
      | .ovrVal => { base with isVal := true, ov := some true }
      | .ovrLval => { base with isVal := true, lzy := true, ov := some true }
      | .priv => { base with priv := true }
      | .ovrPriv => { base with priv := true, ov := some true }
      | _ => base

/-- `trait T`, `trait U` (extending `T` or not), `abstract class B` (extending `T` or not), and
`class C extends B with T with U`, each declaring `m` one way. -/
def program (t u : V) (uExt : Bool) (b : V) (bExt : Bool) (c : V) : Program :=
  let tD : Decl := { name := "T", kind := .trt, members := (t.mem "T").toList }
  let uD : Decl := { name := "U", kind := .trt, members := (u.mem "U").toList,
                     traits := if uExt then [("T", [])] else [] }
  let bD : Decl := { name := "B", abs := true, members := (b.mem "B").toList,
                     traits := if bExt then [("T", [])] else [] }
  let cD : Decl := { name := "C", abs := c == .abs, members := (c.mem "C").toList,
                     super := some ("B", []),
                     traits := [("T", [])] ++ (if u == .none then [] else [("U", [])]) }
  [{ name := "T", cls := some tD }] ++ (if u == .none then [] else [{ name := "U", cls := some uD }]) ++
    [{ name := "B", cls := some bD }, { name := "C", cls := some cD }]

def V.tag : V → String
  | .none => "-" | .abs => "abs" | .conc => "conc" | .ovr => "ovr" | .fin => "final" | .val => "val"
  | .lval => "lazy" | .ovrVal => "ovrVal" | .ovrLval => "ovrLazy" | .priv => "priv" | .ovrPriv => "ovrPriv"

/-- Each program with a one-line description: how `T`, `U`, `B`, `C` declare `m`. -/
def membersSpace : List (String × Program) :=
  [V.none, .abs, .conc, .fin, .val, .lval].flatMap fun t =>
  ([(V.none, false)] ++ ([V.abs, .conc, .ovr].flatMap fun u => [(u, true), (u, false)])).flatMap fun (u, uExt) =>
  [V.none, .abs, .conc, .ovr, .fin, .val, .priv].flatMap fun b =>
  [true, false].flatMap fun bExt =>
  [V.none, .abs, .conc, .ovr, .ovrVal, .ovrLval, .ovrPriv, .priv].map fun c =>
    (s!"T={t.tag} U={u.tag}{if uExt then "<:T" else ""} B={b.tag}{if bExt then "<:T" else ""} C={c.tag}",
     program t u uExt b bExt c)

/-! ## Witnesses -/

/-- `trait T { def m = "T" }; abstract class B { def m = "B" }; class C extends B with T`. -/
def conflict : Program := program .conc .none false .conc false .none

example : errors .s213 conflict = .ok [{ cls := "C", kind := .conflicting }] := by decide +kernel

/-- With `B extends T` and `B` overriding, the pair is checked in `B`, not again in `C`, and the
selection runs `B`'s `m`. -/
def viaB : Program := program .conc .none false .ovr true .none

example : errors .s213 viaB = .ok [] ∧ runs viaB = [("C", "B")] := by decide +kernel

/-- `override private` is a refchecks error in Scala 2 and an earlier error in Scala 3, which
hides the other programs' refchecks errors. -/
def ovrPriv : Program := program .none .none false .conc false .ovrPriv

example : errors .s213 ovrPriv = .ok [{ cls := "C", kind := .weakerAccess }] := by decide +kernel
example : errors .s3 ovrPriv = .ok [{ cls := "C", kind := .illegalModifiers }] := by decide +kernel

/-- `B extends T` overrides `T`'s concrete `m` without `override`. 2.12 and 3 report it once, in
`B`; 2.13 checks the pair again in `C` and reports conflicting members there too. -/
def recheck : Program := program .conc .none false .conc true .none

example : errors .s212 recheck = .ok [{ cls := "B", kind := .needsOverride }] := by decide +kernel
example : errors .s213 recheck =
    .ok [{ cls := "B", kind := .needsOverride }, { cls := "C", kind := .conflicting }] := by decide +kernel

/-- An abstract `m` in class `B extends T` re-abstracts `T`'s concrete `m`; in trait `U extends T`
it does not. -/
def reabsClass : Program := program .conc .none false .abs true .none
def reabsTrait : Program := program .conc .abs true .none false .none

example : errors .s213 reabsClass = .ok [{ cls := "C", kind := .needsAbstract }] := by decide +kernel
example : errors .s213 reabsTrait = .ok [] ∧ runs reabsTrait = [("C", "T")] := by decide +kernel

end Scala.Members
