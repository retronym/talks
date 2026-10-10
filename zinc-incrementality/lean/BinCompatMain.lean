import BinCompat
import Jvm.Dump
import Scala.Catalogue
import Scala.Space

/-! `lake exe bincompat`, for `probes/mima`.

* `edits`: the edit space (`BinCompat/Edits.lean`) as `Jvm` case JSON lines (no client), for
  `probes/jvm/probe.sh` to render with `OUT=dir`;
* `mima`: the model's MiMa problems per edit and per `Jvm` catalogue case, as JSON lines;
* `gaps`: the witnesses of `BinCompat/Keys.lean`, as `Jvm` case JSON lines;
* `scala OUT`: each `Scala/Catalogue.lean` case's library sources as `OUT/<case>/v0.scala` and
  `v1.scala` (package `p`), and per case a TSV line: name, expected MiMa problem, the model's
  outcome before, after and fresh;
* `verdicts`: per edit, the model's MiMa problems and whether some client of `spaceB` breaks or
  changes, as TSV. -/

open BinCompat Jvm.Catalogue Jvm.Clients

def jstr (s : String) : String := "\"" ++ s ++ "\""

def problemsJson (name : String) (ps : List Problem) : String :=
  "{\"name\":" ++ jstr name ++ ",\"problems\":[" ++ ",".intercalate (ps.map (jstr ∘ Problem.name)) ++ "]}"

def main (args : List String) : IO Unit := do
  if args.contains "gaps" then
    for (n, x) in [("finalField", finalField), ("shadowStatic", shadowStatic), ("shadowField", shadowField),
        ("overridePrivate", overridePrivate), ("ifaceField", ifaceField),
        ("defaultConflict", defaultConflict), ("protectedRemoved", protectedRemoved)] do
      IO.println (Jvm.Dump.caseJson { name := n, mima := none, v0 := x.o, v1 := x.n, client := x.client, prog := x.prog })
  else if args.contains "scala" then
    let out := args.getLast!
    for k in Scala.Catalogue.all do
      IO.FS.createDirAll s!"{out}/{k.name}"
      IO.FS.writeFile s!"{out}/{k.name}/v0.scala" (k.v0.show "p")
      IO.FS.writeFile s!"{out}/{k.name}/v1.scala" (k.v1.show "p")
      IO.println s!"{k.name}\t{k.mima.getD ""}\t{repr k.before}\t{repr k.after}\t{repr k.fresh}"
  else if args.contains "edits" then
    for e in edits do IO.println (Jvm.Dump.caseJson e.case)
  else if args.contains "mima" then
    for e in edits do IO.println (problemsJson e.name (mima e.v0 e.v1))
    for k in all ++ j3 do IO.println (problemsJson k.name (mima k.v0 k.v1))
  else if args.contains "unreported" then
    for b in [1, 2] do
      for c in [C.A, C.B, C.I, C.J] do
        IO.println s!"{b} {repr c} {nVariants b c} {unreported b c}"
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
      IO.println s!"{e.name}\t{",".intercalate ((mima e.v0 e.v1).map Problem.name)}\t{br.isSome}\t{ch.isSome}\t{",".intercalate ((extra e.v0 e.v1).map Extra.name)}"
