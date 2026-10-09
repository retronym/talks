import Zinc.FlatRules
import Zinc.Erasure
import Zinc.ImplicitScope

/-! Runs the bounded exhaustive checks as native code.

* `exhaustive [N]`: `Zinc/FlatRules.lean`, for every rule set the number of unclean (base, edit)
  pairs and the smallest one. `N` checks the first `N` bases only. Chunks of bases are checked in
  parallel.
* `exhaustive v`: the value-class space of `Zinc/FlatRules.lean`.
* `exhaustive erasure [N]`: `Zinc/Erasure.lean`, for every rendering the unclean runs and the
  wasted recompiles, per class.
* `exhaustive implicit`: `Zinc/ImplicitScope.lean`, for every variant the unclean runs, the
  wasted recompiles, and the client recompiles against the in-project fallback. -/

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

def mergeCounts (l l' : List (Cls × ℕ)) : List (Cls × ℕ) :=
  l.map fun (c, n) => (c, n + ((l'.lookup c).getD 0))

def Tally.merge (t u : Tally) : Tally :=
  { unclean := t.unclean + u.unclean, noRun := t.noRun + u.noRun,
    wrong := mergeCounts t.wrong u.wrong, wasted := mergeCounts t.wasted u.wasted,
    recompiled := t.recompiled + u.recompiled, byEdit := mergeCounts t.byEdit u.byEdit,
    smallest := match t.smallest, u.smallest with
      | none, s => s
      | s, none => s
      | some (b, b', e), some (c, c', f) =>
        if c.size < b.size || (c.size == b.size && c'.size < b'.size) then some (c, c', f)
        else some (b, b', e) }

/-- Tallies per variant, and the number of skipped pairs, for a chunk of bases. -/
def checkChunkE (bases : List Cfg) : Array Tally × ℕ := Id.run do
  let mut ts : Array Tally := variants.toArray.map fun _ => {}
  let mut skipped := 0
  for k in bases do
    if !k.legal then skipped := skipped + (edits k).length; continue
    for (k', e) in edits k do
      if !k'.legal then skipped := skipped + 1; continue
      let mut j := 0
      for v in variants do
        ts := ts.modify j (·.add k k' e (runVariant v k k' e))
        j := j + 1
  return (ts, skipped)

def chunksE (n : ℕ) : List Cfg → ℕ → List (List Cfg)
  | [], _ => []
  | l, 0 => [l]
  | l, fuel + 1 => l.take n :: chunksE n (l.drop n) fuel

def mainErasure (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD cfgs.length
  let bases := cfgs.take n
  IO.println s!"{bases.length} bases, {(bases.flatMap edits).length} edits"
  (← IO.getStdout).flush
  let tasks := (chunksE 200 bases bases.length).map fun ch => Task.spawn fun _ => checkChunkE ch
  let results := tasks.map Task.get
  let skipped := (results.map (·.2)).sum
  IO.println s!"{skipped} pairs skipped: base or edit does not compile"
  let mut j := 0
  for v in variants do
    let t := results.foldl (fun acc r => acc.merge r.1[j]!) ({} : Tally)
    IO.println s!"{v.name}: {t.unclean} unclean, {t.noRun} out of fuel, {t.recompiled} recompiles"
    IO.println s!"  wrong: {showCounts t.wrong}"
    IO.println s!"  unclean by edited class: {showCounts t.byEdit}"
    IO.println s!"  wasted: {showCounts t.wasted}"
    match t.smallest with
    | some (k, k', e) => IO.println s!"  smallest: base {cfgStr k}\n    edit {repr e} → {cfgStr k'}"
    | none => pure ()
    j := j + 1

end erasure

section implicit
open Zinc.ImplicitScope

structure ITally where
  unclean : ℕ := 0
  noRun : ℕ := 0
  wrong : List (Cls × ℕ) := allCls.map (·, 0)
  wasted : List (Cls × ℕ) := allCls.map (·, 0)
  recompiled : List (Cls × ℕ) := allCls.map (·, 0)
  byEdit : List (Cls × ℕ) := allCls.map (·, 0)
  /-- Runs recompiling a client the baseline does not, and the reverse. -/
  moreClients : ℕ := 0
  fewerClients : ℕ := 0
  smallest : Option (Cfg × Cfg × Cls) := none
  smallestMore : Option (Cfg × Cfg × Cls) := none
  deriving Inhabited

def ibump (l : List (Cls × ℕ)) (cs : List Cls) : List (Cls × ℕ) :=
  l.map fun (c, n) => (c, if cs.contains c then n + 1 else n)

def smaller (k k' : Cfg) (e : Cls) : Option (Cfg × Cfg × Cls) → Option (Cfg × Cfg × Cls)
  | none => some (k, k', e)
  | some (b, b', e') =>
    if k.size < b.size || (k.size == b.size && k'.size < b'.size) then some (k, k', e)
    else some (b, b', e')

def ITally.add (t : ITally) (k k' : Cfg) (e : Cls) (base : Option Report) :
    Option Report → ITally
  | none => { t with noRun := t.noRun + 1 }
  | some r =>
    let bad := !r.wrong.isEmpty
    let cl := r.recompiled.filter isClient
    let bcl := ((base.map (·.recompiled)).getD []).filter isClient
    let more := cl.any (!bcl.contains ·)
    let fewer := bcl.any (!cl.contains ·)
    { t with
      unclean := t.unclean + (if bad then 1 else 0)
      wrong := ibump t.wrong r.wrong
      wasted := ibump t.wasted r.wasted
      recompiled := ibump t.recompiled r.recompiled
      byEdit := if bad then ibump t.byEdit [e] else t.byEdit
      moreClients := t.moreClients + (if more then 1 else 0)
      fewerClients := t.fewerClients + (if fewer then 1 else 0)
      smallest := if bad then smaller k k' e t.smallest else t.smallest
      smallestMore := if more then smaller k k' e t.smallestMore else t.smallestMore }

def icfgStr (k : Cfg) : String :=
  (toString (repr k)).replace "\n" " " |>.replace "Zinc.ImplicitScope." ""

def ishowCounts (l : List (Cls × ℕ)) : String :=
  ", ".intercalate ((l.filter (·.2 != 0)).map fun (c, n) =>
    s!"{(toString (repr c)).replace "Zinc.ImplicitScope.Cls." ""} {n}")

def mainImplicit : IO Unit := do
  IO.println s!"{cfgs.length} bases, {(cfgs.flatMap edits).length} edits"
  let mut ts : Array ITally := variants.toArray.map fun _ => {}
  for k in cfgs do
    for (k', e) in edits k do
      let rs := variants.map fun v => runVariant v k k' e
      let base := rs.head?.join
      let mut j := 0
      for r in rs do
        ts := ts.modify j (·.add k k' e base r)
        j := j + 1
  let mut j := 0
  for v in variants do
    let t := ts[j]!
    IO.println s!"{v.name}: {t.unclean} unclean, {t.noRun} out of fuel"
    IO.println s!"  wrong: {ishowCounts t.wrong}"
    IO.println s!"  unclean by edited class: {ishowCounts t.byEdit}"
    IO.println s!"  recompiled: {ishowCounts t.recompiled}"
    IO.println s!"  wasted: {ishowCounts t.wasted}"
    IO.println s!"  vs baseline: {t.moreClients} runs recompile a client it does not, {t.fewerClients} miss one it recompiles"
    match t.smallest with
    | some (k, k', e) => IO.println s!"  smallest unclean: base {icfgStr k}\n    edit {(toString (repr e)).replace "Zinc.ImplicitScope.Cls." ""} → {icfgStr k'}"
    | none => pure ()
    match t.smallestMore with
    | some (k, k', e) => IO.println s!"  smallest extra client: base {icfgStr k}\n    edit {(toString (repr e)).replace "Zinc.ImplicitScope.Cls." ""} → {icfgStr k'}"
    | none => pure ()
    j := j + 1

/-- Single loop with in-project rules vs one loop per project: do they agree run for run? -/
def mainComposed : IO Unit := do
  let cases : List (String × Ext × Layout × ℕ) :=
    [("develop, lib → app", develop, twoP, 2), ("develop, lib → mid → app", develop, threeP, 3),
     ("fix (stored), lib → app", stored, twoP, 2), ("fix (stored), lib → mid → app", stored, threeP, 3),
     ("fix (stored) without the fold, lib → mid → app", { stored with fold := false }, threeP, 3),
     ("develop, one project", develop, oneP, 1)]
  for (name, x, lay, nP) in cases do
    let mut runs := 0
    let mut wrongDiff := 0
    let mut clientDiff := 0
    let mut uncleanSingle := 0
    let mut uncleanComposed := 0
    let mut first : Option String := none
    for k in cfgs do
      for (k', e) in edits k do
        runs := runs + 1
        let a := report x (.proj lay) k.src k'.src {e}
        let b := reportComposed x lay nP k.src k'.src {e}
        let wa := (a.map (·.wrong)).getD []
        let wb := (b.map (·.wrong)).getD []
        if !wa.isEmpty then uncleanSingle := uncleanSingle + 1
        if !wb.isEmpty then uncleanComposed := uncleanComposed + 1
        let ca := ((a.map (·.recompiled)).getD []).filter isClient
        let cb := ((b.map (·.recompiled)).getD []).filter isClient
        if wa != wb then
          wrongDiff := wrongDiff + 1
          if first.isNone then
            first := some s!"base {icfgStr k}\n    edit {repr e} → {icfgStr k'}\n    single {repr wa}, composed {repr wb}"
        if ca != cb then clientDiff := clientDiff + 1
    IO.println s!"{name}: {runs} runs, unclean single {uncleanSingle} / composed {uncleanComposed}, wrong sets differ {wrongDiff}, client recompiles differ {clientDiff}"
    match first with
    | some str => IO.println s!"  first difference: {str}"
    | none => pure ()

end implicit

def main (args : List String) : IO Unit :=
  match args with
  | "erasure" :: rest => mainErasure rest
  | "implicit" :: _ => mainImplicit
  | "composed" :: _ => mainComposed
  | "v" :: _ => mainV
  | _ => mainRules args
