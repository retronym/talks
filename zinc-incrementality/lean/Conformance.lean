import Zinc.FlatRules
import ZincNames.Names
import ZincNames.Givens
import Zinc.InlineOpaque
import Zinc.Companions
import Zinc.Split

/-! Dumps the program space of `Zinc/FlatRules.lean` as JSON lines, one line per base program
with all of its single-class edits, for the Zinc conformance harness (`Conformance` in Zinc's
`zincScripted` tests). The harness renders each program as Scala, builds the base, applies each
edit, and compares the incremental build's classfiles with a clean build of the edited program.

The programs are data in a generic shape (classes with a kind, parents with type arguments,
declared members, selections), so a later program space only has to supply its `Cls → Src`.
Each edit carries the model's verdict under the widened default rules: the classes the policy
recompiles besides the edited one, and whether the run equals the clean build.

`conformance names|givens 2|3 [mode]`: the name-resolution spaces of `ZincNames/Names.lean` and
`ZincNames/Givens.lean`, as source files, with the model's resolution before and after each edit,
its verdict for that Scala version under the mode (`Mode.parse`: `today` by default, `cheap` for
retronym/zinc#34, `all` for #34 with the F2, F3 and G rules, `+narrowed+imports` for the rules
narrowed to the searched packages with recorded package imports, `+decls` for #24's API without
composition), and the classes it recompiles beyond the edited files and their heirs
(`modelRecompiled`, among the client, `User`, `Near`, `Mid` and `Far`). Each edit also carries
`keys`: for the client, the keys the mode needs it to have recorded before the edit
(`Names.clientKeys`, `Givens.clientKeys`), in retronym/zinc#54's grammar, which the harness checks
against the Analysis and reports as `uncovered` when one is missing.

`conformance cost`: per space, version and mode, the edits, the wrong ones, and the recompilations
beyond the necessary, as a markdown table.

`conformance inline|opaque [mode]`: the Scala 3 spaces of `Zinc/InlineOpaque.lean`, as source files
with tiers (the client and descendants downstream), with the classes the model recompiles under
`today` or the named fix.
With `split`, the verdicts of `Zinc/Split.lean` with every binding upstream and the client
downstream (each file's `tiers`, for the harness's `split` layout); `upstream` is #34 extended
across subprojects, `proposed` the rule of `Zinc/SplitProof.lean`.

`conformance companions [today|merkle|pre56]`: companion pairs in a hierarchy (`Zinc/Companions.lean`),
as source files, Scala 2.

`conformance [all]`: bases whose model build has no errors, resolves every selection and
inherits one instance of each ancestor, or every base with `all`. -/

open Zinc.Flat
open Zinc.Hier (Cls Name Ty)
open Zinc.Hier.Cls Zinc.Hier.Name

def clsName : Cls → String
  | A => "A" | B => "B" | M => "M" | C => "C" | X => "X" | Y => "Y" | Z => "Z" | V => "V"

def nameStr : Name → String
  | m => "m" | g => "g"

def tyStr : Ty → String
  | .int => "Int" | .string => "String" | .param => "T" | .v => "V"

/-- The Scala kind of a class. -/
def kindStr (d : Decl) : String :=
  (if d.final then "final " else "") ++
    match d.kind with
    | .trt => "trait"
    | .obj => "object"
    | .cls => if d.abstract then "abstract class" else "class"

def modStr : Mod → String
  | .dfn => "def" | .val => "val" | .var => "var" | .lzy => "lazy val"

def jstr (s : String) : String := "\"" ++ s ++ "\""

def jarr (l : List String) : String := "[" ++ ",".intercalate l ++ "]"

def clsJson (c : Cls) (s : Src) : String :=
  let tparams := if s.decl.kind == .obj then "[]" else "[\"T\"]"
  "{\"name\":" ++ jstr (clsName c) ++ ",\"kind\":" ++ jstr (kindStr s.decl) ++
    ",\"tparams\":" ++ tparams ++
    ",\"parents\":" ++ jarr (s.decl.parents.map fun (p, t) => jarr [jstr (clsName p), jstr (tyStr t)]) ++
    ",\"decls\":" ++ jarr (s.decl.decls.map fun (n, mm) =>
      jarr [jstr (nameStr n), jstr (tyStr mm.ty), toString mm.deferred, jstr (modStr mm.mod),
        toString mm.priv]) ++
    ",\"under\":" ++ (match s.decl.under with | some t => jstr (tyStr t) | none => "null") ++
    ",\"observes\":" ++ jarr (s.observes.map (jstr ∘ clsName)) ++
    ",\"body\":" ++ jarr (s.body.map fun (c', n) => jarr [jstr (clsName c'), jstr (nameStr n)]) ++ "}"

/-- The classes of a program; `V` only where it is declared (the value-class space). -/
def progJson (src : Cls → Src) (withV : Bool := false) : String :=
  jarr ((all.filter fun c => c != V || withV).map fun c => clsJson c (src c))

def errStr : Err → String
  | .override n => "override " ++ nameStr n
  | .conflict n => "conflict " ++ nameStr n
  | .abstract n => "abstract " ++ nameStr n
  | .final p => "final " ++ clsName p

/-- The model's errors of a clean build, by class. -/
def modelErrs (src : Cls → Src) : List String :=
  let o := clean src
  all.flatMap fun c => (o c).errs.map fun e => clsName c ++ ": " ++ errStr e

/-- Does every selection resolve in the model's clean build? Scala rejects one that does not. -/
def resolves (src : Cls → Src) : Bool :=
  let o := clean src
  all.all fun c => (o c).descs.all (·.2.1.isSome)

/-- Does no class inherit two instances of one ancestor, `M[Int]` and `M[String]`? Scala rejects
that ("illegal inheritance"); the model's linearization merge keeps the first. -/
def coherent (src : Cls → Src) : Bool :=
  let o := clean src
  all.all fun c =>
    let es := (src c).decl.parents.flatMap fun (p, a) =>
      (p, a) :: (o p).iface.lin.map fun e => (e.1, Ty.subst a e.2)
    es.all fun e => es.all fun e' => e.1 != e'.1 || e.2 == e'.2

def optStr : Opt → String
  | .none => "-" | .int => "int" | .str => "str" | .par => "par" | .dfr => "dfr"
  | .val => "val" | .var => "var" | .lzy => "lazy" | .pval => "pval"

/-- `Cfg` compactly: `oA oB oM oC aPar bArg bUses bFinal xObj aTrait zObs`. -/
def cfgStr (k : Cfg) : String :=
  " ".intercalate ([k.oA, k.oB, k.oM, k.oC].map optStr ++
    [(k.aPar.map tyStr).getD "-", tyStr k.bArg, if k.bUses then "uses" else "-",
     if k.bFinal then "final" else "-", if k.xObj then "xobj" else "-",
     if k.aTrait then "atrait" else "-", if k.zObs then "zobs" else "-"])

/-- `Cfg` as named factors, for the harness's covering-array ordering. -/
def factorsJson (k : Cfg) : String :=
  let fs := [("oA", optStr k.oA), ("oB", optStr k.oB), ("oM", optStr k.oM), ("oC", optStr k.oC),
    ("aPar", (k.aPar.map tyStr).getD "-"), ("bArg", tyStr k.bArg), ("bUses", toString k.bUses),
    ("bFinal", toString k.bFinal), ("xObj", toString k.xObj), ("aTrait", toString k.aTrait), ("zObs", toString k.zObs)]
  "{" ++ ",".intercalate (fs.map fun (n, v) => jstr n ++ ":" ++ jstr v) ++ "}"

def editJsonSrc (src₀ src₁ : Cls → Src) (cfg factors : String) (e : Cls) (withV : Bool := false) :
    String :=
  let r := reportR clientOnly true allRules src₀ src₁ {e}
  let (recd, ok) := match r with
    | some r => (r.recompiled.map (jstr ∘ clsName), r.clean)
    | none => ([], false)
  "{\"cls\":" ++ jstr (clsName e) ++ ",\"cfg\":" ++ jstr cfg ++ ",\"factors\":" ++ factors ++
    ",\"prog\":" ++ progJson src₁ withV ++
    ",\"modelErrs\":" ++ jarr ((modelErrs src₁).map jstr) ++
    ",\"modelRecompiled\":" ++ jarr recd ++ ",\"modelClean\":" ++ toString ok ++ "}"

def editJson (k : Cfg) (k' : Cfg) (e : Cls) : String :=
  editJsonSrc k.src k'.src (cfgStr k') (factorsJson k') e

def optVStr : OptV → String
  | .none => "-" | .int => "int" | .vt => "V" | .vtd => "Vdfr" | .par => "par"

def cfgVFields (k : CfgV) : List (String × String) :=
  [("vU", (k.vU.map tyStr).getD "ref"), ("oA", optVStr k.oA), ("oB", optVStr k.oB),
   ("oM", optVStr k.oM), ("oC", optVStr k.oC), ("aPar", (k.aPar.map tyStr).getD "-"),
   ("bArg", tyStr k.bArg), ("xObj", toString k.xObj)]

def cfgVStr (k : CfgV) : String := " ".intercalate ((cfgVFields k).map (·.2))

def factorsV (k : CfgV) : String :=
  "{" ++ ",".intercalate ((cfgVFields k).map fun (n, v) => jstr n ++ ":" ++ jstr v) ++ "}"

def valid (src : Cls → Src) : Bool := (modelErrs src).isEmpty && resolves src && coherent src

def mainV (everything : Bool) : IO Unit := do
  let out ← IO.getStdout
  let mut i := 0
  for k in cfgsV do
    if everything || valid k.src then
      out.putStrLn ("{\"space\":\"flatV\",\"id\":\"v" ++ toString i ++ "\",\"cfg\":" ++
        jstr (cfgVStr k) ++ ",\"factors\":" ++ factorsV k ++ ",\"prog\":" ++ progJson k.src true ++
        ",\"edits\":" ++ jarr ((editsV k).map fun (k', e) =>
          editJsonSrc k.src k'.src (cfgVStr k') (factorsV k') e true) ++ "}")
    i := i + 1

section names
open Zinc.Names

def jfiles (fs : List (String × Option String)) : String :=
  "{" ++ ",".intercalate (fs.map fun (f, s) =>
    jstr f ++ ":" ++ match s with
      | some s => "\"" ++ (s.replace "\n" "\\n").replace "\"" "\\\"" ++ "\""
      | none => "null") ++ "}"

def stStr : Zinc.Names.St → String | .none => "-" | .foo => "Foo" | .bar => "Bar"

def namesFactors (p : Prog) : List (String × String) :=
  let c := p.cl
  [("pkg", c.pkg.str), ("blk", toString c.blk), ("inh", toString c.inh), ("expl", toString c.expl),
   ("wild", toString c.wild), ("wpkg", toString c.wpkg), ("first", toString c.first),
   ("opt", toString c.opt), ("exp", toString c.exp), ("pinh", toString c.pinh),
   ("winh", toString c.winh)] ++
  [Slot.blk, .inh, .expl, .wild, .wpkg, .inner, .pobj, .outer].map fun s => ("s." ++ s.str, stStr (p.st s))

def jfactors (fs : List (String × String)) : String :=
  "{" ++ ",".intercalate (fs.map fun (n, v) => jstr n ++ ":" ++ jstr v) ++ "}"

def namesCfg (p : Prog) : String := " ".intercalate ((namesFactors p).map (·.2))

def jtiers (ts : List (String × Nat)) : String :=
  "{" ++ ",".intercalate (ts.map fun (f, t) => jstr f ++ ":" ++ jstr (toString t)) ++ "}"

def mainNames (m : Mode) (v : Ver) (split : Option Zinc.Split.Mode := none) : IO Unit := do
  let out ← IO.getStdout
  let mut i := 0
  for p in bases.filter (fun p => v == .s3 || !p.cl.exp) do
    let es := (edits p).map fun (e, p') =>
      let r := match split with
        | some sm => Zinc.Split.verdict sm .split v p p'
        | none => verdict m v p p'
      "{\"cls\":" ++ jstr e.str ++ ",\"cfg\":" ++ jstr (e.str ++ ": " ++ r.before.str ++ " -> " ++ r.after.str) ++
        ",\"factors\":" ++ jfactors (namesFactors p') ++ ",\"files\":" ++ jfiles (fileEdits p p') ++
        ",\"modelRecompiled\":" ++ jarr (((if r.recompiled then ["Client"] else []) ++
          (if userRecompiled m v p p' then ["User"] else [])).map jstr) ++
        ",\"modelNecessary\":" ++ toString (necessary v p p') ++
        ",\"modelClean\":" ++ toString r.clean ++ ",\"modelFamily\":" ++ jstr (family m v p p') ++
        ",\"modelErrs\":" ++ jarr (match r.after with | .ok _ => [] | x => [jstr x.str]) ++
        ",\"keys\":{\"Client\":" ++ jarr ((clientKeys m v p p').map jstr) ++ "}}"
    out.putStrLn ("{\"space\":\"names\",\"id\":\"n" ++ toString i ++ "\",\"cfg\":" ++ jstr (namesCfg p) ++
      ",\"factors\":" ++ jfactors (namesFactors p) ++
      ",\"probe\":" ++ jstr (clientClass p) ++ ",\"files\":" ++ jfiles ((files v p).map fun (f, s) => (f, some s)) ++
      (if split.isSome then ",\"tiers\":" ++ jtiers Zinc.Split.namesTiers else "") ++ ",\"edits\":" ++ jarr es ++ "}")
    i := i + 1

end names

section givens
open Zinc.Givens

def givensFactors (v : Zinc.Names.Ver) (p : Prog) : List (String × String) :=
  let c := p.cl
  [("pkg", c.pkg.str), ("blk", toString c.blk), ("inh", toString c.inh), ("wild", toString c.wild),
   ("first", toString c.first), ("pinh", toString c.pinh), ("wpkg", toString c.wpkg)] ++
  Slot.all.map fun s => ("s." ++ s.str, if (present v c).contains s then toString (p.has s) else "-")

def mainGivens (m : Zinc.Names.Mode) (v : Zinc.Names.Ver) (split : Option Zinc.Split.Mode := none) :
    IO Unit := do
  let out ← IO.getStdout
  let mut i := 0
  for p in bases v do
    let es := (edits v p).map fun (e, p') =>
      let r := match split with
        | some sm => Zinc.Split.givensVerdict sm .split v p p'
        | none => verdict m v p p'
      let (near, mid, far) := bystanders m v p p'
      "{\"cls\":" ++ jstr e.str ++ ",\"cfg\":" ++ jstr (e.str ++ ": " ++ r.before.str ++ " -> " ++ r.after.str) ++
        ",\"factors\":" ++ jfactors (givensFactors v p') ++ ",\"files\":" ++ jfiles (fileEdits v p p') ++
        ",\"modelRecompiled\":" ++ jarr (((if r.recompiled then ["Client"] else []) ++
          (if near then ["Near"] else []) ++ (if mid then ["Mid"] else []) ++
          (if far then ["Far"] else [])).map jstr) ++
        ",\"modelNecessary\":" ++ toString (necessary v p p') ++
        ",\"modelClean\":" ++ toString r.clean ++ ",\"modelFamily\":" ++ jstr (family m v p p') ++
        ",\"modelErrs\":" ++ jarr (match r.after with | .ok _ => [] | x => [jstr x.str]) ++
        ",\"keys\":{\"Client\":" ++ jarr ((clientKeys m v p p').map jstr) ++ "}}"
    out.putStrLn ("{\"space\":\"givens\",\"id\":\"g" ++ toString i ++ "\",\"cfg\":" ++
      jstr (" ".intercalate ((givensFactors v p).map (·.2))) ++
      ",\"factors\":" ++ jfactors (givensFactors v p) ++
      ",\"probe\":" ++ jstr (if p.cl.pkg == .top then "a/Client$" else "a/b/Client$") ++
      ",\"files\":" ++ jfiles ((files v p).map fun (f, s) => (f, some s)) ++
      (if split.isSome then ",\"tiers\":" ++ jtiers Zinc.Split.givensTiers else "") ++ ",\"edits\":" ++ jarr es ++ "}")
    i := i + 1

end givens

/-- Per space, version and mode: the edits, the wrong ones (unsound), the client recompiled though
its resolution did not change, and the bystanders recompiled (each stands for every class of its
kind in a build). -/
def mainCost : IO Unit := do
  let out ← IO.getStdout
  let vs : List (String × Zinc.Names.Ver) := [("2.13", .s2), ("3", .s3)]
  out.putStrLn "| Space | Mode | Edits | Wrong | Client, resolution unchanged | `User` | `Near` | `Mid` | `Far` |"
  out.putStrLn "|---|---|---|---|---|---|---|---|---|"
  for (vn, v) in vs do
    for ms in ["today", "cheap", "searched", "names", "f2", "f3", "cheap+f2+f3",
        "cheap+f2+f3+narrowed", "cheap+f2+f3+narrowed+imports", "all+decls"] do
      let some md := Zinc.Names.Mode.parse ms | continue
      let c := Zinc.Names.cost md v
      out.putStrLn s!"| names, {vn} | `{ms}` | {c.edits} | {c.wrong} | {c.client} | {c.user} | | | |"
  for (vn, v) in vs do
    for ms in ["today", "cheap", "searched", "g", "g+narrowed", "g+narrowed+imports", "all",
        "all+narrowed+imports", "all+decls"] do
      let some md := Zinc.Names.Mode.parse ms | continue
      let c := Zinc.Givens.cost md v
      out.putStrLn s!"| givens, {vn} | `{ms}` | {c.edits} | {c.wrong} | {c.client} | | {c.near} | {c.mid} | {c.far} |"

section inlineOpaque
open Zinc.InlineOpaque

def ioEdit (cls cfg : String) (fs : List (String × String)) (files : List (String × Option String))
    (v : Verdict) : String :=
  "{\"cls\":" ++ jstr cls ++ ",\"cfg\":" ++ jstr cfg ++ ",\"factors\":" ++ jfactors fs ++
    ",\"files\":" ++ jfiles files ++ ",\"modelRecompiled\":" ++ jarr (v.recompiled.map jstr) ++
    ",\"modelClean\":" ++ toString v.clean ++ ",\"modelErrs\":[]}"

def ioBase (space id : String) (fs : List (String × String)) (files : List (String × String))
    (tiers : List (String × ℕ)) (es : List String) : String :=
  "{\"space\":" ++ jstr space ++ ",\"id\":" ++ jstr id ++ ",\"cfg\":" ++
    jstr (" ".intercalate (fs.map (·.2))) ++ ",\"factors\":" ++ jfactors fs ++
    ",\"files\":" ++ jfiles (files.map fun (f, s) => (f, some s)) ++ ",\"tiers\":" ++ jtiers tiers ++
    ",\"edits\":" ++ jarr es ++ "}"

def mainInline (m : Inl.Mode) : IO Unit := do
  let out ← IO.getStdout
  let mut i := 0
  for p in Inl.bases do
    let es := (Inl.edits p).map fun (e, p') =>
      ioEdit (Inl.editedFile p.ref) (e.str ++ ": " ++ " ".intercalate ((Inl.factors p).map (·.2)))
        (Inl.factors p' ++ [("edit", e.str)]) (Inl.fileEdits p p') (Inl.check m p p')
    out.putStrLn (ioBase "inline" ("i" ++ toString i) (Inl.factors p) (Inl.files p) (Inl.tiers p) es)
    i := i + 1

def mainOpaque (m : Opq.Mode) : IO Unit := do
  let out ← IO.getStdout
  let mut i := 0
  for p in Opq.bases do
    let es := (Opq.edits p).map fun (r, p') =>
      let fe := ((Opq.files p').filter fun f => !(Opq.files p).contains f).map fun (n, s) => (n, some s)
      ioEdit "O.scala" (p.rhs.str ++ " -> " ++ r.str ++ ": " ++ " ".intercalate ((Opq.factors p).map (·.2)))
        (Opq.factors p') fe (Opq.check m p p')
    out.putStrLn (ioBase "opaque" ("o" ++ toString i) (Opq.factors p) (Opq.files p) (Opq.tiers p) es)
    i := i + 1

end inlineOpaque

/-- `conformance companions [today|merkle|pre56]`: the companion-pair space of `Zinc/Companions.lean`. -/
def mainCompanions (m : Zinc.Companions.Mode) : IO Unit := do
  let out ← IO.getStdout
  let mut i := 0
  for p in Zinc.Companions.bases do
    let fs := Zinc.Companions.files p
    let es := (Zinc.Companions.edits p).map fun (e, p') =>
      let fe := ((Zinc.Companions.files p').filter fun f => !fs.contains f).map fun (n, s) => (n, some s)
      ioEdit (Zinc.Companions.editedFile e)
        (e.str ++ ": " ++ " ".intercalate ((Zinc.Companions.factors p).map (·.2)))
        (Zinc.Companions.factors p ++ [("edit", e.str)]) fe (Zinc.Companions.check m p e)
    out.putStrLn (ioBase "companions" ("c" ++ toString i) (Zinc.Companions.factors p) fs
      (Zinc.Companions.tiers p) es)
    i := i + 1

def main (args : List String) : IO Unit := do
  if args.contains "cost" then return (← mainCost)
  if args.contains "companions" then
    return (← mainCompanions ((args.drop 1).head?.bind Zinc.Companions.Mode.parse |>.getD .today))
  if args.contains "inline" then
    return (← mainInline (if args.contains "hashConsts" then .hashConsts
      else if args.contains "bodyDeps" then .bodyDeps else .today))
  if args.contains "opaque" then
    return (← mainOpaque (if args.contains "dep" then .dep else if args.contains "refine" then .refine
      else .today))
  let m : Zinc.Names.Mode := ((args.drop 2).head?.bind Zinc.Names.Mode.parse).getD .today
  let split : Option Zinc.Split.Mode := if !args.contains "split" then none
    else some (if args.contains "proposed" then .names else if args.contains "upstream" then .upstream
      else if args.contains "cheap" then .cheap else .today)
  if args.contains "names" then return (← mainNames m (if args.contains "3" then .s3 else .s2) split)
  if args.contains "givens" then return (← mainGivens m (if args.contains "3" then .s3 else .s2) split)
  let everything := args.contains "all"
  if args.contains "v" then return (← mainV everything)
  let out ← IO.getStdout
  let mut i := 0
  for k in cfgs do
    if everything || ((modelErrs k.src).isEmpty && resolves k.src && coherent k.src) then
      out.putStrLn ("{\"space\":\"flat\",\"id\":" ++ toString i ++ ",\"cfg\":" ++ jstr (cfgStr k) ++ ",\"factors\":" ++ factorsJson k ++
        ",\"prog\":" ++ progJson k.src ++
        ",\"edits\":" ++ jarr ((edits k).map fun (k', e) => editJson k k' e) ++ "}")
    i := i + 1
