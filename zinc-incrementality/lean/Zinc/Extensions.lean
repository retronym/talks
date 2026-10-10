import Zinc.SpecGivens

/-!
# Member selection through extensions

`x.m` where `x : T` and `T` has no member `m` resolves through an extension: a Scala 3 `extension`
method or a Scala 2 implicit class / conversion visible in the lexical scope (a block, an import, a
package object, a top-level definition, a wildcard-imported package), and otherwise in the implicit
scope of `T` (its companion, and its ancestors' companions, Phase 7). Two candidates at one nesting
level are ambiguous. A member `m` added to `T` itself takes precedence over every extension.

This is `SpecGivens`' level-wise search (an `XCompiler`) with the extension's scopes. Each scope kind
is a `Scope` (whether Zinc pins an edge from the client to it) and a `GScope` (its level, whether it
is a package-level container, reached through a wildcard package import, inherited):

* `member`: `T`'s own member `m`; the client records `T` and the used name `m`: pinned.
* `block`, `importQual`: a block's or an import's qualifier: pinned (`Spec`'s import edges).
* `pkgObject`, `topLevel`: a package object's extension, a top-level extension in another file:
  package-level containers, reached through no edge (`F2`/`G1`, `G2`).
* `pkgImported`: the same in a wildcard-imported package (`F3`'s narrowed case).
* `companion`: `T`'s companion: pinned (Zinc keys the companion pair by `T`'s name, `ExtraHash`).
* `ancestorCompanion`: an ancestor's companion, in `T`'s implicit scope: neither pinned nor a
  package-level container (Phase 7, sbt/zinc#1845).

Results:

* `ext_rule_obligations`: with the G rule (global, or narrowed with recorded package imports) the
  obligations hold whenever every scope is pinned or a package-level container, so T3a; this is
  `SpecGivens.g_global_obligations` / `g_narrowed_obligations` for the extension layout.
* `ext_today_pkgObject`, `ext_today_topLevel`: today's keys fail coverage on a package object's
  or a top-level extension over the companion's.
* `ext_narrowed_without_imports`: the narrowed rule fails on a wildcard-imported package's.
* `ext_rule_ancestorCompanion`: even the global G rule fails on an ancestor's companion, which needs
  Phase 7's key (the ancestor companions, pinned).
-/

namespace Zinc.SplitProof.Spec.Extensions

open Zinc.SplitProof Zinc.SplitProof.Spec

inductive ExtScope
  | member | block | importQual | pkgObject | topLevel | pkgImported | companion | ancestorCompanion
  deriving DecidableEq, Repr

/-- Whether Zinc pins an edge from the client to the scope today. -/
def pinnedK : ExtScope → Bool
  | .member | .block | .importQual | .companion => true
  | _ => false

/-- The scope as `Spec` sees it. -/
def scopeOf (k : ExtScope) : Scope := ⟨pinnedK k, false, false, false⟩

/-- The scope as implicit search sees it, at nesting level `lvl`. -/
def gscopeOf (lvl : ℕ) : ExtScope → GScope
  | .pkgObject | .topLevel => ⟨lvl, true, false, false⟩
  | .pkgImported => ⟨lvl, true, true, false⟩
  | _ => ⟨lvl, false, false, false⟩

/-- An extension search: the scopes in order, each with its kind and nesting level. -/
structure Layout (n : ℕ) where
  kind : Fin n → ExtScope
  level : Fin n → ℕ

def Layout.sc {n : ℕ} (L : Layout n) : Fin n → Scope := fun i => scopeOf (L.kind i)
def Layout.gx {n : ℕ} (L : Layout n) : Fin n → GScope := fun i => gscopeOf (L.level i) (L.kind i)

/-- Every scope is pinned or a package-level container: no ancestor companion in the layout. -/
def Layout.Reached {n : ℕ} (L : Layout n) : Prop := ∀ i, L.kind i ≠ .ancestorCompanion

theorem givensScopes_of_reached {n : ℕ} (L : Layout n) (h : L.Reached) : GivensScopes L.gx L.sc := by
  intro i
  have hi := h i
  cases hk : L.kind i <;> simp_all [Layout.gx, Layout.sc, gscopeOf, scopeOf, pinnedK]

/-- **The G rule covers extension search** where every scope is pinned or package-level: global,
or narrowed with recorded package imports. -/
theorem ext_rule_obligations {n : ℕ} (L : Layout n) (h : L.Reached) :
    (gcompiler L.gx L.sc false (.rule true false)).Obligations ∧
      (gcompiler L.gx L.sc false (.rule false true)).Obligations :=
  ⟨g_global_obligations L.gx L.sc (givensScopes_of_reached L h),
   g_narrowed_obligations L.gx L.sc (givensScopes_of_reached L h)⟩

/-! ## Witnesses: scope 0 of the given kind, scope 1 `T`'s companion holding the extension -/

def two (k : ExtScope) (lvl : ℕ) : Layout 2 :=
  ⟨fun i => if i = 0 then k else .companion, fun i => if i = 0 then lvl else 1⟩

/-- **A package object's extension** (`F2`/`G1`) over the companion's: today's keys miss it. -/
theorem ext_today_pkgObject :
    ¬ (gcompiler (two .pkgObject 0).gx (two .pkgObject 0).sc false .today).Obligations :=
  g_not_obligations_of _ _ _ _ (by
    intro k hk
    simp [gkeys, resolvedKeys, gunit, gsearch, answer, compOnly, two, Layout.gx, Layout.sc, gscopeOf,
      scopeOf, pinnedK, List.finRange] at hk
    subst hk
    simp [gcovers])

/-- **A top-level extension in a new file** (`G2`). -/
theorem ext_today_topLevel :
    ¬ (gcompiler (two .topLevel 0).gx (two .topLevel 0).sc false .today).Obligations :=
  g_not_obligations_of _ _ _ _ (by
    intro k hk
    simp [gkeys, resolvedKeys, gunit, gsearch, answer, compOnly, two, Layout.gx, Layout.sc, gscopeOf,
      scopeOf, pinnedK, List.finRange] at hk
    subst hk
    simp [gcovers])

/-- **A wildcard-imported package's extension**: the narrowed rule without recorded imports. -/
theorem ext_narrowed_without_imports :
    ¬ (gcompiler (two .pkgImported 0).gx (two .pkgImported 0).sc false (.rule false false)).Obligations :=
  g_not_obligations_of _ _ _ _ (by
    intro k hk
    simp [gkeys, resolvedKeys, gunit, gsearch, answer, compOnly, two, Layout.gx, Layout.sc, gscopeOf,
      scopeOf, pinnedK, List.finRange] at hk
    rcases hk with rfl | rfl <;> simp [gcovers, gruled, two, Layout.gx, gscopeOf])

/-- **An ancestor's companion** (Phase 7): at the companion's level, neither pinned nor package-level,
so even the global G rule leaves it uncovered. -/
theorem ext_rule_ancestorCompanion :
    ¬ (gcompiler (two .ancestorCompanion 1).gx (two .ancestorCompanion 1).sc false (.rule true false)).Obligations :=
  g_not_obligations_of _ _ _ _ (by
    intro k hk
    simp [gkeys, resolvedKeys, gunit, gsearch, answer, compOnly, two, Layout.gx, Layout.sc, gscopeOf,
      scopeOf, pinnedK, List.finRange] at hk
    rcases hk with rfl | rfl <;> simp [gcovers, gruled, two, Layout.gx, gscopeOf])

end Zinc.SplitProof.Spec.Extensions
