import ZincNames.Names
import ZincNames.Givens

/-!
# The name-resolution spaces, checked whole

The theorems over every edit of `Names.lean`'s and `Givens.lean`'s spaces, apart from the
definitions so that `native_decide` runs them compiled (the `ZincNames` library is precompiled).
-/

namespace Zinc.Names

/-- Under the cheap fix, every edit that adds a top-level class is clean, but for the divergences
beside the client's resolution. -/
theorem cheap_added_clean : (bases.all fun p => (edits p).all fun (_, p') =>
    !f1 p p' || [Ver.s2, .s3].all fun v => (verdict .cheap v p p').clean ||
      besideResolution v p p' || separateInit v p' (recompiles .cheap v p p')) = true := by
  native_decide

/-- Every edit of the space, both versions, is clean when the lookup's misses are recorded, and
when the users of a name are invalidated on every added or removed binding; the stale mirror, the
missed clash and the trait initialiser are not about the client's resolution, and neither fix
touches them. -/
theorem searched_clean : cleanOn .searched = true := by native_decide

theorem names_clean : cleanOn .names = true := by native_decide

/-- Today, every wrong edit is in F1, F2 or F3, inherited bindings included. -/
theorem today_families : (bases.all fun p => (edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => !wrong .today v p p' || f1 p p' || f2 p p' || f3 p p') = true := by
  native_decide

/-- The F2 rule closes F2: what is left is F1 and F3. -/
theorem f2_leaves : (bases.all fun p => (edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => !wrong (.rules { f2 := true }) v p p' || f1 p p' || f3 p p') = true := by
  native_decide

/-- The F3 rule closes F3: what is left is F1 and F2. -/
theorem f3_leaves : (bases.all fun p => (edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v => !wrong (.rules { f3 := true }) v p p' || f1 p p' || f2 p p') = true := by
  native_decide

theorem all_clean : cleanOn (.rules allRules) = true := by native_decide

/-- On develop the baseline does not matter in this space: a package object's stored API changes
only when it is recompiled, so the cycle that recompiles it sees the inherited name appear. -/
theorem all_cycle_clean : cleanOn (.rules { allRules with base := .cycle }) = true := by native_decide

/-- With composition against the run's baseline, #24 is clean on the whole space. -/
theorem composed_clean : cleanOn (.rules { allRules with api := .composed }) = true := by native_decide

/-- Does a mode get exactly today's wrong edits in F2 with an inherited member wrong, and nothing else? -/
def leavesInherited (m : Mode) : Bool := bases.all fun p => (edits p).all fun (_, p') =>
  [Ver.s2, .s3].all fun v => wrong m v p p' == (wrong .today v p p' && f2 p p' && p.cl.pinh)

/-- Without composition, or against the cycle before, what is left is exactly the inherited
package object member. -/
theorem decls_leaves : leavesInherited (.rules { allRules with api := .decls }) = true := by native_decide

theorem composed_cycle_leaves :
    leavesInherited (.rules { allRules with api := .composed, base := .cycle }) = true := by native_decide

/-- The precise modes never recompile `User`. -/
theorem searched_spares_user : (bases.all fun p => (edits p).all fun (_, p') =>
    [Ver.s2, .s3].all fun v =>
      !userRecompiled .searched v p p' && !userRecompiled (.rules { f3 := true }) v p p') = true := by
  native_decide

end Zinc.Names

namespace Zinc.Givens

open Zinc.Names (Ver allRules)

/-- Recording the scopes searched is clean on the whole space, but for the classfile bytes of a
client compiled apart from its trait. -/
theorem searched_clean : ([Ver.s2, .s3].all fun v => (bases v).all fun p =>
    (edits v p).all fun (_, p') =>
      (verdict .searched v p p').clean || separateInit v p p' (recompiles .searched v p p')) = true := by
  native_decide

/-- retronym/zinc#34's cheap fix changes nothing here: the only classes an edit adds are
`Inner$package` and `Outer$package`, whose names the client never uses. -/
theorem cheap_is_today : ([Ver.s2, .s3].all fun v => (bases v).all fun p =>
    (edits v p).all fun (_, p') => recompiles .cheap v p p' == recompiles .today v p p') = true := by
  native_decide

theorem g_clean : cleanOn (.rules { g := true }) = true := by native_decide

/-- #34's other rules change nothing here: the client names no instance. -/
theorem all_clean : cleanOn (.rules allRules) = true := by native_decide

theorem all_cycle_clean : cleanOn (.rules { allRules with base := .cycle }) = true := by
  native_decide

theorem composed_clean : cleanOn (.rules { allRules with api := .composed }) = true := by
  native_decide

end Zinc.Givens
