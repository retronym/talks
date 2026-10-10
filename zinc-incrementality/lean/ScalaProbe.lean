import Scala.Space

/-! `scalaprobe OUT`: write each case of `Scala.space` as Scala source, and the model's
classfiles for each dialect as `OUT/expected-2.12.txt`, `OUT/expected-2.13.txt` and
`OUT/expected-3.txt`. Sources go to `OUT/src/pN.scala`, or `OUT/src3/` for Scala 3 syntax, or, for
a case compiled in two runs, `OUT/sep/lib/pN.scala` and `OUT/sep/client/pN.scala` (`sep3` for
Scala 3 syntax). -/

open Scala

def main (args : List String) : IO UInt32 := do
  let out := args.headD "out"
  for d in ["src", "src3", "sep/lib", "sep/client", "sep3/lib", "sep3/client"] do IO.FS.createDirAll s!"{out}/{d}"
  let mut index := ""
  for (c, i) in space.zipIdx do
    let pkg := s!"p{i}"
    if c.lib.isEmpty then
      IO.FS.writeFile s!"{out}/{if c.only3 then "src3" else "src"}/{pkg}.scala" (c.prog.show pkg)
    else
      let (l, r) := c.prog.partition fun s => c.lib.contains s.name
      let shw (us : Program) := s!"package {pkg}\n\n" ++ String.join (us.map (Src.show c.prog))
      let sep := if c.only3 then "sep3" else "sep"
      IO.FS.writeFile s!"{out}/{sep}/lib/{pkg}.scala" (shw l)
      IO.FS.writeFile s!"{out}/{sep}/client/{pkg}.scala" (shw r)
    index := index ++ s!"{pkg}\t{c.fam}\n"
  IO.FS.writeFile s!"{out}/index.txt" index
  for (dl, tag) in [(Dialect.s212, "2.12"), (.s213, "2.13"), (.s3, "3")] do
    let mut lines : Array String := #[]
    for (c, i) in space.zipIdx do
      if c.only3 && dl != .s3 then continue
      match c.lower dl with
      | .ok cs => for k in cs do lines := lines ++ (k.dump s!"p{i}").toArray
      | .error e => IO.eprintln s!"p{i}: {e}"; return 1
    IO.FS.writeFile s!"{out}/expected-{tag}.txt" ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"{space.length} programs"
  return 0
