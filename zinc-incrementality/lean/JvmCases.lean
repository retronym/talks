import Jvm.Dump
import Jvm.Clients

/-! `lake exe jvmcases`: the catalogue (`Jvm/Catalogue.lean`) as JSON lines for `probes/jvm`.

`lake exe jvmcases space`: every catalogue edit with every well-typed client of `Jvm/Clients.lean`'s
space, named `<case>/<n>`, so the probe checks the model's outcome for each client, not only the
catalogue's own.

`lake exe jvmcases verdicts`: per edit, MiMa's problem, the J2 verdicts and the number of clients in
the space that break or change, as a markdown table. -/

open Jvm.Catalogue Jvm.Clients

def main (args : List String) : IO Unit := do
  if args.contains "j3" then
    for k in j3 do
      IO.println s!"{k.name}\t{repr k.before}\t{repr k.after}"
    return
  for k in all ++ (if args.contains "space" || args.contains "verdicts" then [] else j3) do
    if args.contains "verdicts" then
      let ok := space.filter fun cl => let k' := k.withClient cl; wellTyped k'.w0 cl.2 && links k'.w0 cl.2
      let br := ok.filter fun cl => !links (k.withClient cl).w1 cl.2
      let ch := ok.filter fun cl => let k' := k.withClient cl; links k'.w1 cl.2 && k'.before != k'.after
      IO.println s!"| `{k.name}` | {k.mima.getD "—"} | {breaksSomeClient k} | {changesSomeClient k} | {br.length}/{ok.length} | {ch.length}/{ok.length} |"
    else if args.contains "space" then
      for (cl, i) in space.zipIdx do
        let k' := k.withClient cl
        if wellTyped k'.w0 cl.2 then
          IO.println (Jvm.Dump.caseJson { k' with name := s!"{k.name}/{i}" })
    else
      IO.println (Jvm.Dump.caseJson k)
