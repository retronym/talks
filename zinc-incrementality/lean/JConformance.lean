import Zinc.JavaNames
import Zinc.JavaSealed

/-! Dumps the Java spaces (`Zinc/JavaNames.lean`, `Zinc/JavaSealed.lean`) as JSON lines of source
files for the Zinc conformance harness, as `conformance names` does for Scala.

`jconformance names java|2|3 [cheap|fix] [pipe]`: the client in Java, Scala 2 or Scala 3, the
model's resolution before and after each edit and its verdict under Zinc today, retronym/zinc#34
(`cheap`) or the proposed Java fix (`fix`), with or without pipelining (`pipe`; the harness's
`--inc-option pipelining=` must match).

`jconformance sealed java|2|3 [permits|desc|fix] [pipe]`: the sealed hierarchies, with the verdict
under Zinc today, retronym/zinc#21 (`permits`), #21 with descendants (`desc`), or #21 with the
ancestors' users invalidated (`fix`). Scala clients
compile with `-Werror`. -/

def jstr (s : String) : String := "\"" ++ s ++ "\""

def jarr (l : List String) : String := "[" ++ ",".intercalate l ++ "]"

def jfiles (fs : List (String × Option String)) : String :=
  "{" ++ ",".intercalate (fs.map fun (f, s) =>
    jstr f ++ ":" ++ match s with
      | some s => "\"" ++ (s.replace "\n" "\\n").replace "\"" "\\\"" ++ "\""
      | none => "null") ++ "}"

def jfactors (fs : List (String × String)) : String :=
  "{" ++ ",".intercalate (fs.map fun (n, v) => jstr n ++ ":" ++ jstr v) ++ "}"

def langOf (args : List String) : Zinc.JavaNames.Lang :=
  if args.contains "java" then .java else if args.contains "3" then .s3 else .s2

section names
open Zinc.JavaNames

def stStr : St → String | .none => "-" | .foo => "Foo" | .bar => "Bar"

def namesFactors (p : Prog) : List (String × String) :=
  let c := p.cl
  [("pkg", c.pkg.str), ("inh", toString c.inh), ("expl", toString c.expl), ("wild", toString c.wild),
   ("wpkg", toString c.wpkg), ("opt", toString c.opt)] ++
  [Slot.inh, .expl, .wild, .wpkg, .inner, .outer].map fun s => ("s." ++ s.str, stStr (p.st s))

def mainNames (m : Mode) (pipe : Bool) (l : Lang) : IO Unit := do
  let out ← IO.getStdout
  let mut i := 0
  for p in bases l do
    let es := (edits p).map fun (e, p') =>
      let r := verdict m pipe l p p'
      "{\"cls\":" ++ jstr e.str ++ ",\"cfg\":" ++ jstr (e.str ++ ": " ++ r.before.str ++ " -> " ++ r.after.str) ++
        ",\"factors\":" ++ jfactors (namesFactors p') ++ ",\"files\":" ++ jfiles (fileEdits p p') ++
        ",\"modelRecompiled\":" ++ (if r.recompiled then "[\"Client\"]" else "[]") ++
        ",\"modelClean\":" ++ toString r.clean ++
        ",\"modelErrs\":" ++ jarr (match r.after with | .ok _ => [] | x => [jstr x.str]) ++ "}"
    out.putStrLn ("{\"space\":\"jnames\",\"id\":\"j" ++ toString i ++ "\",\"cfg\":" ++
      jstr (" ".intercalate ((namesFactors p).map (·.2))) ++
      ",\"factors\":" ++ jfactors (namesFactors p) ++ ",\"probe\":" ++ jstr (clientClass l p) ++
      ",\"files\":" ++ jfiles ((files l p).map fun (f, s) => (f, some s)) ++ ",\"edits\":" ++ jarr es ++ "}")
    i := i + 1

end names

section sealed
open Zinc.JavaSealed
open Zinc.JavaNames (Lang)

def sealedFactors (p : Prog) : List (String × String) :=
  [("defn", p.defn.str), ("two", toString p.two), ("c", (p.c.map Par.str).getD "-")]

def mainSealed (m : Mode) (pipe : Bool) (l : Lang) : IO Unit := do
  let out ← IO.getStdout
  let mut i := 0
  for p in bases l do
    let es := (edits p).map fun (e, p') =>
      let rc := recompiles m pipe l p e
      "{\"cls\":" ++ jstr e.str ++ ",\"cfg\":" ++ jstr e.str ++
        ",\"factors\":" ++ jfactors (sealedFactors p') ++ ",\"files\":" ++ jfiles (fileEdits p p') ++
        ",\"modelRecompiled\":" ++ (if rc then "[\"Client\"]" else "[]") ++
        ",\"modelClean\":" ++ toString (clean m pipe l p e) ++ ",\"modelErrs\":[\"Client\"]}"
    out.putStrLn ("{\"space\":\"jsealed\",\"id\":\"s" ++ toString i ++ "\",\"cfg\":" ++
      jstr (" ".intercalate ((sealedFactors p).map (·.2))) ++
      ",\"factors\":" ++ jfactors (sealedFactors p) ++ ",\"probe\":" ++
      jstr (if l == .java then "a/Client" else "a/Client$") ++
      (if l == .java then "" else ",\"scalacOptions\":\"-Werror\"") ++
      ",\"files\":" ++ jfiles ((allFiles l p).map fun (f, s) => (f, some s)) ++ ",\"edits\":" ++ jarr es ++ "}")
    i := i + 1

end sealed

def main (args : List String) : IO Unit := do
  let pipe := args.contains "pipe"
  let l := langOf args
  if args.contains "sealed" then
    let m : Zinc.JavaSealed.Mode :=
      if args.contains "fix" then .fix else if args.contains "desc" then .desc
      else if args.contains "permits" then .permits else .today
    mainSealed m pipe l
  else
    let m : Zinc.JavaNames.Mode :=
      if args.contains "fix" then .fix else if args.contains "cheap" then .cheap else .today
    mainNames m pipe l
