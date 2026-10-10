import Jvm.Dump

/-! `lake exe jvmcases`: the catalogue (`Jvm/Catalogue.lean`) as JSON lines for `probes/jvm`. -/

def main (_args : List String) : IO Unit := do
  for k in Jvm.Catalogue.all do
    IO.println (Jvm.Dump.caseJson k)
