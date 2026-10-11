import ZincNames.Names
import ZincNames.Givens

/-!
# The name-resolution spaces, checked whole

Checks over every edit of `Names.lean`'s and `Givens.lean`'s bounded spaces (at most two bindings
per base, single edits), run compiled by `native_decide` (the `ZincNames` library is precompiled).
They are `example`s, not theorems: the general results, for every program and every edit, are in
`SplitProof.Spec` (names) and `SpecGivens.lean` (implicits). These check the enumerated model, which the harness checks against Zinc and the
compilers, and give the magnitudes (`conformance cost`).
-/

namespace Zinc.Names

/-- `cheap_added_clean`: Under the cheap fix, every edit that adds a top-level class is clean, but for the divergences
beside the client's resolution. -/
example : (bases.all fun p => (edits p).all fun (_, p') =>
    !f1 p p' || [Ver.s2, .s3].all fun v => (verdict .cheap v p p').clean ||
      besideResolution v p p' || separateInit v p' (recompiles .cheap v p p')) = true := by
  native_decide

/-- `searched_clean`: Every edit of the space, both versions, is clean when the lookup's misses are recorded, and
when the users of a name are invalidated on every added or removed binding; the stale mirror, the
missed clash and the trait initialiser are not about the client's resolution, and neither fix
touches them. -/
example : cleanOn .searched = true := by native_decide

/-- `names_clean`. -/
example : cleanOn .names = true := by native_decide

/-- `today_families`: Today, every wrong edit is in F1, F2 or F3, inherited bindings included. -/
example : (bases.all fun p => (edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => !wrong .today v p p' || f1 p p' || f2 p p' || f3 p p') = true := by
  native_decide

/-- `f2_leaves`: The F2 rule closes F2: what is left is F1 and F3. -/
example : (bases.all fun p => (edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => !wrong (.rules { f2 := true }) v p p' || f1 p p' || f3 p p') = true := by
  native_decide

/-- `f3_leaves`: The F3 rule closes F3: what is left is F1 and F2. -/
example : (bases.all fun p => (edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => !wrong (.rules { f3 := true }) v p p' || f1 p p' || f2 p p') = true := by
  native_decide

/-- `all_clean`. -/
example : cleanOn (.rules allRules) = true := by native_decide

/-- `composed_clean`: With composition against the run's baseline, #24 is clean on the whole space. -/
example : cleanOn (.rules { allRules with api := .composed }) = true := by native_decide

/-- Does a mode get exactly today's wrong edits in F2 with an inherited member wrong, and nothing else? -/
def leavesInherited (m : Mode) : Bool := bases.all fun p => (edits p).all fun (_, p') =>
  [Ver.s2, .s3].all fun v => wrong m v p p' == (wrong .today v p p' && f2 p p' && p.cl.pinh)

/-- `decls_leaves`: Without composition, what is left is exactly the inherited package object member. -/
example : leavesInherited (.rules { allRules with api := .decls }) = true := by native_decide

/-- `searched_spares_user`: The precise modes never recompile `User`. -/
example : (bases.all fun p => (edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v =>
      !userRecompiled .searched v p p' && !userRecompiled (.rules { f3 := true }) v p p') = true := by
  native_decide

/-- #34, F2 and F3 narrowed to the searched packages, with the bridge recording package imports. -/
def narrowedRules : Rules := { allRules with reach := .narrowed, imports := true }

/-- `narrowed_clean`. -/
example : cleanOn (.rules narrowedRules) = true := by native_decide

/-- `narrowed_without_imports`: without the recorded import, the narrowed rules miss exactly a class
added in the wildcard-imported package. -/
example : (bases.all fun p => (edits p).all fun (_, p') => [Ver.s2, .s3].all fun v =>
    !wrong (.rules { narrowedRules with imports := false }) v p p' ||
      (p.st .wpkg != .foo && p'.st .wpkg == .foo)) = true := by native_decide

example : cleanOn (.rules { narrowedRules with imports := false }) = false := by native_decide

end Zinc.Names

namespace Zinc.Givens

open Zinc.Names (Ver allRules)

/-- `searched_clean`: Recording the scopes searched is clean on the whole space, but for the classfile bytes of a
client compiled apart from its trait. -/
example : ([Ver.s2, .s3].all fun v => (bases v).all fun p =>
    (edits v p).all fun (_, p') =>
      (verdict .searched v p p').clean || separateInit v p p' (recompiles .searched v p p')) = true := by
  native_decide

/-- `cheap_is_today`: retronym/zinc#34's cheap fix changes nothing here: the only classes an edit adds are
`Inner$package` and `Outer$package`, whose names the client never uses. -/
example : ([Ver.s2, .s3].all fun v => (bases v).all fun p =>
    (edits v p).all fun (_, p') => recompiles .cheap v p p' == recompiles .today v p p') = true := by
  native_decide

/-- `g_clean`. -/
example : cleanOn (.rules { g := true }) = true := by native_decide

/-- `all_clean`: #34's other rules change nothing here: the client names no instance. -/
example : cleanOn (.rules allRules) = true := by native_decide

/-- `composed_clean`. -/
example : cleanOn (.rules { allRules with api := .composed }) = true := by
  native_decide

/-- `g_narrowed_clean`: the narrowed G rule with recorded package imports. -/
example : cleanOn (.rules { g := true, reach := .narrowed, imports := true }) = true := by native_decide

/-- `g_narrowed_without_imports`: without them, every wrong edit changes the instance in `a.q`. -/
example : ([Ver.s2, .s3].all fun v => (bases v).all fun p => (edits v p).all fun (_, p') =>
    (verdict (.rules { g := true, reach := .narrowed }) v p p').clean ||
      separateInit v p p' (recompiles (.rules { g := true, reach := .narrowed }) v p p') ||
      p.has .wpkg != p'.has .wpkg) = true := by native_decide

example : cleanOn (.rules { g := true, reach := .narrowed }) = false := by native_decide

end Zinc.Givens
