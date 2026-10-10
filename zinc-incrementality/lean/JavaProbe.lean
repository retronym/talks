import Java.Space

/-! `javaprobe OUT`: write each case of `Java.space` as Java sources under `OUT/src/pN/` (one file
per compilation unit, named after its first type), the model's classfiles as `OUT/expected.txt`,
and each program's family as `OUT/index.txt`. -/

open Java

def main (args : List String) : IO UInt32 := do
  let out := args.headD "out"
  let mut index := ""
  let mut lines : Array String := #[]
  for (c, i) in space.zipIdx do
    let pkg := s!"p{i}"
    IO.FS.createDirAll s!"{out}/src/{pkg}"
    for u in c.prog do
      match u.head? with
      | some d => IO.FS.writeFile s!"{out}/src/{pkg}/{d.name}.java" (u.show pkg)
      | none => pure ()
    index := index ++ s!"{pkg}\t{c.fam}\n"
    match lowerProgram c.prog with
    | .ok cs => for k in cs do lines := lines ++ (k.dump pkg).toArray
    | .error e => IO.eprintln s!"{pkg}: {e}"; return 1
  IO.FS.writeFile s!"{out}/index.txt" index
  IO.FS.writeFile s!"{out}/expected.txt" ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"{space.length} programs"
  return 0
