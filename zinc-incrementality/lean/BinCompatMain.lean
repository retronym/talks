import BinCompat
import Jvm.Dump

/-! `lake exe bincompat`, for `probes/mima`.

* `edits`: the edit space (`BinCompat/Edits.lean`) as `Jvm` case JSON lines (no client), for
  `probes/jvm/probe.sh` to render with `OUT=dir`;
* `mima`: the model's MiMa problems per edit and per `Jvm` catalogue case, as JSON lines;
* `verdicts`: per edit, the model's MiMa problems and whether some client of `spaceB` breaks or
  changes, as TSV. -/

open BinCompat Jvm.Catalogue Jvm.Clients

def jstr (s : String) : String := "\"" ++ s ++ "\""

def problemsJson (name : String) (ps : List Problem) : String :=
  "{\"name\":" ++ jstr name ++ ",\"problems\":[" ++ ",".intercalate (ps.map (jstr ∘ Problem.name)) ++ "]}"

def main (args : List String) : IO Unit := do
  if args.contains "edits" then
    for e in edits do IO.println (Jvm.Dump.caseJson e.case)
  else if args.contains "mima" then
    for e in edits do IO.println (problemsJson e.name (mima e.v0 e.v1))
    for k in all ++ j3 do IO.println (problemsJson k.name (mima k.v0 k.v1))
  else if args.contains "witness" then
    for e in edits do
      if args.contains e.name then
        match breaking e.case spaceB with
        | some cl => IO.println s!"{e.name}\t{Jvm.Dump.caseJson (e.case.withClient cl)}"
        | none => IO.println s!"{e.name}\tnone"
  else if args.contains "verdicts" then
    for e in edits do
      let k := e.case
      let br := breaking k spaceB
      let ch := changing k spaceB
      IO.println s!"{e.name}\t{",".intercalate ((mima e.v0 e.v1).map Problem.name)}\t{br.isSome}\t{ch.isSome}"
