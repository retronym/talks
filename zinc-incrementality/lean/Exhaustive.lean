import Zinc.FlatRules
import Zinc.Erasure

/-! Runs the bounded exhaustive checks as native code.

* `exhaustive [N]`: `Zinc/FlatRules.lean`, for every rule set the number of unclean (base, edit)
  pairs and the smallest one. `N` checks the first `N` bases only. Chunks of bases are checked in
  parallel.
* `exhaustive v`: the value-class space of `Zinc/FlatRules.lean`.
* `exhaustive erasure [N]`: `Zinc/Erasure.lean`, for every rendering the unclean runs and the
  wasted recompiles, per class. -/

section rules
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

def mainRules (args : List String) : IO Unit := do
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

end rules

section erasure
open Zinc.Erasure

structure Tally where
  unclean : ℕ := 0
  noRun : ℕ := 0
  wrong : List (Cls × ℕ) := allCls.map (·, 0)
  wasted : List (Cls × ℕ) := allCls.map (·, 0)
  recompiled : ℕ := 0
  /-- Unclean runs by the class edited. -/
  byEdit : List (Cls × ℕ) := allCls.map (·, 0)
  smallest : Option (Cfg × Cfg × Cls) := none
  deriving Inhabited

def bump (l : List (Cls × ℕ)) (cs : List Cls) : List (Cls × ℕ) :=
  l.map fun (c, n) => (c, if cs.contains c then n + 1 else n)

def Tally.add (t : Tally) (k k' : Cfg) (e : Cls) : Option Report → Tally
  | none => { t with noRun := t.noRun + 1 }
  | some r =>
    let bad := !r.wrong.isEmpty
    { t with
      unclean := t.unclean + (if bad then 1 else 0)
      wrong := bump t.wrong r.wrong
      wasted := bump t.wasted r.wasted
      byEdit := if bad then bump t.byEdit [e] else t.byEdit
      recompiled := t.recompiled + r.recompiled.length
      smallest := if !bad then t.smallest else match t.smallest with
        | none => some (k, k', e)
        | some (b, b', _) =>
          if k.size < b.size || (k.size == b.size && k'.size < b'.size) then some (k, k', e)
          else t.smallest }

def cfgStr (k : Cfg) : String := (toString (repr k)).replace "\n" " " |>.replace "Zinc.Erasure." ""

def showCounts (l : List (Cls × ℕ)) : String :=
  ", ".intercalate ((l.filter (·.2 != 0)).map fun (c, n) => s!"{(toString (repr c)).replace "Zinc.Erasure.Cls." ""} {n}")

def mainErasure (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD cfgs.length
  let bases := cfgs.take n
  IO.println s!"{bases.length} bases, {(bases.flatMap edits).length} edits"
  let mut ts : Array Tally := variants.toArray.map fun _ => {}
  let mut i := 0
  let mut skipped := 0
  for k in bases do
    for (k', e) in edits k do
      if !k.legal || !k'.legal then skipped := skipped + 1; continue
      let mut j := 0
      for v in variants do
        ts := ts.modify j (·.add k k' e (runVariant v k k' e))
        j := j + 1
    i := i + 1
    if i % 1000 == 0 then IO.println s!"... {i}"; (← IO.getStdout).flush
  IO.println s!"{skipped} pairs skipped: base or edit does not compile"
  let mut j := 0
  for v in variants do
    let t := ts[j]!
    IO.println s!"{v.name}: {t.unclean} unclean, {t.noRun} out of fuel, {t.recompiled} recompiles"
    IO.println s!"  wrong: {showCounts t.wrong}"
    IO.println s!"  unclean by edited class: {showCounts t.byEdit}"
    IO.println s!"  wasted: {showCounts t.wasted}"
    match t.smallest with
    | some (k, k', e) => IO.println s!"  smallest: base {cfgStr k}\n    edit {repr e} → {cfgStr k'}"
    | none => pure ()
    j := j + 1

end erasure

def main (args : List String) : IO Unit :=
  match args with
  | "erasure" :: rest => mainErasure rest
  | "v" :: _ => mainV
  | _ => mainRules args
