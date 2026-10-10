import Scala.Space

/-! `scalaprobe OUT`: write each program of `Scala.space` as `OUT/src/pN.scala`, and the model's
classfiles for each dialect as `OUT/expected-2.13.txt` and `OUT/expected-3.txt`. -/

open Scala

def main (args : List String) : IO UInt32 := do
  let out := args.headD "out"
  IO.FS.createDirAll s!"{out}/src"
  let mut index := ""
  for ((fam, p), i) in space.zipIdx do
    IO.FS.writeFile s!"{out}/src/p{i}.scala" (p.show s!"p{i}")
    index := index ++ s!"p{i}\t{fam}\n"
  IO.FS.writeFile s!"{out}/index.txt" index
  for (dl, tag) in [(Dialect.s213, "2.13"), (.s3, "3")] do
    let mut lines : Array String := #[]
    for ((_, p), i) in space.zipIdx do
      match lowerProgram dl p with
      | .ok cs => for c in cs do lines := lines ++ (c.dump s!"p{i}").toArray
      | .error e => IO.eprintln s!"p{i}: {e}"; return 1
    IO.FS.writeFile s!"{out}/expected-{tag}.txt" ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"{space.length} programs"
  return 0
