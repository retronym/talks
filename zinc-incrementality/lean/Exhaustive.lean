import Zinc.FlatRules

/-! Runs the bounded exhaustive check of `Zinc/FlatRules.lean` as native code: for every rule set,
the number of unclean (base, edit) pairs and the smallest one. `exhaustive N` checks the first
`N` bases only. Chunks of bases are checked in parallel. -/

open Zinc.Flat

/-- The rule sets checked: name, recorded key kinds, `abstractAll`, rules. -/
def ruleSets : List (String × (Kind → Bool) × Bool × List Rule) :=
  [("default (as stated)", clientOnly, false, allRules),
   ("default, abstract widened", clientOnly, true, allRules),
   ("none", clientOnly, false, [])] ++
  allRules.map (fun r => (s!"widened without {repr r}", clientOnly, true, allRules.filter (· != r))) ++
  [("widened, trait narrowed to direct mixins", clientOnly, true,
     allRules.map (fun r => if r == .trait then .traitDirect else r)),
   ("widened, traitDirect blind to private members (no extraHash)", clientOnly, true,
     allRules.map (fun r => if r == .trait then .traitPub else r)),
   ("widened, macro-expansion keys dropped", (· == .client), true, allRules),
   ("widened without header, extends clauses recorded", (fun k => clientOnly k || k == .extends),
     true, allRules.filter (· != .header)),
   ("widened without uses, self-uses recorded as keys", (fun k => clientOnly k || k == .uses), true,
     allRules.filter (· != .uses))]

abbrev Bad := List (Cfg × Cfg × Zinc.Hier.Cls)

def checkChunk (bases : List Cfg) : Array Bad := Id.run do
  let mut bad : Array Bad := ruleSets.toArray.map fun _ => []
  for k in bases do
    for (k', e) in edits k do
      let mut j := 0
      for (_, E, ab, rs) in ruleSets do
        if !cleanRun E ab rs (init E k.src) k' e then bad := bad.modify j ((k, k', e) :: ·)
        j := j + 1
  return bad

def chunks (n : ℕ) : List Cfg → ℕ → List (List Cfg)
  | [], _ => []
  | l, 0 => [l]
  | l, fuel + 1 => l.take n :: chunks n (l.drop n) fuel

/-- The value-class space's rule sets. -/
def ruleSetsV : List (String × (Kind → Bool) × Bool × List Rule) :=
  [("default, abstract widened", clientOnly, true, allRules),
   ("default + erasure keys (codegen's reads of V recorded)",
     (fun k => clientOnly k || k == .erasure), true, allRules),
   ("none", clientOnly, false, [])] ++
  [Rule.overrides, .trait, .mirror].map (fun r =>
    (s!"+ erasure keys, without {repr r}", (fun k => clientOnly k || k == .erasure), true,
      allRules.filter (· != r)))

def checkChunkV (bases : List CfgV) : Array (List (CfgV × CfgV × Zinc.Hier.Cls)) := Id.run do
  let mut bad : Array (List (CfgV × CfgV × Zinc.Hier.Cls)) := ruleSetsV.toArray.map fun _ => []
  for k in bases do
    for (k', e) in editsV k do
      let mut j := 0
      for (_, E, ab, rs) in ruleSetsV do
        if !cleanRunSrc E ab rs (init E k.src) k'.src e then bad := bad.modify j ((k, k', e) :: ·)
        j := j + 1
  return bad

def chunksV (n : ℕ) : List CfgV → ℕ → List (List CfgV)
  | [], _ => []
  | l, 0 => [l]
  | l, fuel + 1 => l.take n :: chunksV n (l.drop n) fuel

def mainV : IO Unit := do
  IO.println s!"{cfgsV.length} value-class bases, {(cfgsV.flatMap editsV).length} edits"
  (← IO.getStdout).flush
  let results := ((chunksV 100 cfgsV cfgsV.length).map fun ch => Task.spawn fun _ => checkChunkV ch).map Task.get
  let mut j := 0
  for (name, _, _, _) in ruleSetsV do
    let l := results.flatMap fun r => r[j]!
    IO.println s!"{name}: {l.length} unclean"
    match l.head? with
    | some (k, k', e) => IO.println s!"  base {repr k}\n  edit {repr e} → {repr k'}"
    | none => pure ()
    j := j + 1

def main (args : List String) : IO Unit := do
  if args.head? == some "v" then return (← mainV)
  let n := (args.head? >>= String.toNat?).getD cfgs.length
  let bases := cfgs.take n
  IO.println s!"{bases.length} bases, {(bases.flatMap edits).length} edits"
  (← IO.getStdout).flush
  let tasks := (chunks 500 bases bases.length).map fun ch => Task.spawn fun _ => checkChunk ch
  let results := tasks.map Task.get
  let mut j := 0
  for (name, _, _, _) in ruleSets do
    let l := results.flatMap fun r => r[j]!
    IO.println s!"{name}: {l.length} unclean"
    match minimal l with
    | some (k, k', e) => IO.println s!"  base {repr k}\n  edit {repr e} → {repr k'}"
    | none => pure ()
    j := j + 1
