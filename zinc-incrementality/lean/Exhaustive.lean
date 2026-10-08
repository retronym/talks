import Zinc.FlatRules

/-! Runs the bounded exhaustive check of `Zinc/FlatRules.lean` as native code: for every rule set,
the number of unclean (base, edit) pairs and the smallest one. `exhaustive N` checks the first
`N` bases only. -/

open Zinc.Flat

/-- The rule sets checked: name, recorded key kinds, `abstractAll`, rules. -/
def ruleSets : List (String × (Kind → Bool) × Bool × List Rule) :=
  [("default (as stated)", clientOnly, false, allRules),
   ("default, abstract widened", clientOnly, true, allRules),
   ("none", clientOnly, false, [])] ++
  allRules.map (fun r => (s!"widened without {repr r}", clientOnly, true, allRules.filter (· != r))) ++
  [("widened without uses, self-uses recorded as keys", (fun k => k == .client || k == .uses), true,
     allRules.filter (· != .uses))]

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD cfgs.length
  let bases := cfgs.take n
  IO.println s!"{bases.length} bases, {(bases.flatMap edits).length} edits"
  let mut bad : Array (List (Cfg × Cfg × Zinc.Hier.Cls)) := ruleSets.toArray.map fun _ => []
  let mut i := 0
  for k in bases do
    for (k', e) in edits k do
      let mut j := 0
      for (_, E, ab, rs) in ruleSets do
        if !cleanRun E ab rs (init E k.src) k' e then bad := bad.modify j ((k, k', e) :: ·)
        j := j + 1
    i := i + 1
    if i % 500 == 0 then IO.println s!"... {i}"; (← IO.getStdout).flush
  let mut j := 0
  for (name, _, _, _) in ruleSets do
    let l := bad[j]!
    IO.println s!"{name}: {l.length} unclean"
    match minimal l with
    | some (k, k', e) => IO.println s!"  base {repr k}\n  edit {repr e} → {repr k'}"
    | none => pure ()
    j := j + 1
