import Zinc.FlatRules

/-! Dumps the program space of `Zinc/FlatRules.lean` as JSON lines, one line per base program
with all of its single-class edits, for the Zinc conformance harness (`Conformance` in Zinc's
`zincScripted` tests). The harness renders each program as Scala, builds the base, applies each
edit, and compares the incremental build's classfiles with a clean build of the edited program.

The programs are data in a generic shape (classes with a kind, parents with type arguments,
declared members, selections), so a later program space only has to supply its `Cls → Src`.
Each edit carries the model's verdict under the widened default rules: the classes the policy
recompiles besides the edited one, and whether the run equals the clean build.

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
def progJson (src : Cls → Src) : String :=
  jarr ((all.filter fun c => c != V || src V != { decl := {} }).map fun c => clsJson c (src c))

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

def editJsonSrc (src₀ src₁ : Cls → Src) (cfg factors : String) (e : Cls) : String :=
  let r := reportR clientOnly true allRules src₀ src₁ {e}
  let (recd, ok) := match r with
    | some r => (r.recompiled.map (jstr ∘ clsName), r.clean)
    | none => ([], false)
  "{\"cls\":" ++ jstr (clsName e) ++ ",\"cfg\":" ++ jstr cfg ++ ",\"factors\":" ++ factors ++
    ",\"prog\":" ++ progJson src₁ ++
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
        jstr (cfgVStr k) ++ ",\"factors\":" ++ factorsV k ++ ",\"prog\":" ++ progJson k.src ++
        ",\"edits\":" ++ jarr ((editsV k).map fun (k', e) =>
          editJsonSrc k.src k'.src (cfgVStr k') (factorsV k') e) ++ "}")
    i := i + 1

def main (args : List String) : IO Unit := do
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
