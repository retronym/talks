/-!
# `asSeenFrom`, once, for any type language

scalac types a selection `pre.m` as `info(m).asSeenFrom(pre, owner(m))` (`TypeMaps.scala`,
`AsSeenFromMap`). The map rewrites two kinds of leaf and goes through everything else:

* a this-type `D.this` (`thisTypeAsSeen`), and
* a type parameter `D#i` of an enclosing class `D` (`classParameterAsSeen`).

Both are the same walk. Starting with the cursor at `clazz` and the prefix at `pre`: if the cursor
is `D` and `pre` has `D` as a base type, the leaf becomes `pre` (a this-type) or the `i`-th argument
of `pre baseType D` (a parameter); otherwise both step out together, the cursor to its owner and
the prefix to `(pre baseType cursor).prefix`; at a package, the leaf is left alone.

This file states that walk once, generic in the type language: a language supplies its leaves and
a `bind` that substitutes them (`Subst`, with the monad laws in `LawfulSubst`), and `asf pre c t` is
`bind t` of the walk. A class is its owner path, innermost first, so the walk is structural
recursion. The environment is a `World`: `bpre p c` is `(p baseType c).prefix`, `hasBase p c` says
`c` is a base class of `p`, `bargs p c` are the arguments of `p baseType c`.

From one assumption, **lockstep** (the map commutes with `bpre`, `hasBase` and `bargs`, which
scalac satisfies by construction), the composition law and "a chain of maps is one map" are
proved once (`compose`, `chain_is_single`). These are the TCK's theorems
(`scala-type-system-tck/lean/AsSeenFrom/Chain.lean`), generalised to type parameters and to any
type language; the TCK's `Ty` and the Scala layer's `Scala.Ty` are instances.

This file imports only Lean core, so a project without Mathlib can use it.
-/

namespace AsSeenFrom

/-- What a leaf is: a this-type, or the `i`-th type parameter of its class. -/
inductive Kind
  | this
  | param (i : Nat)
  deriving DecidableEq, Repr

/-- A leaf is anchored at a class (its owner path) and has a kind. -/
class Leafy (L : Type) (α : outParam Type) where
  cls : L → List α
  kind : L → Kind

/-- A type language whose leaves can be substituted. -/
class Subst (T : Type) (L : outParam Type) where
  leaf : L → T
  bind : T → (L → T) → T
  leaves : T → List L

/-- `bind` is substitution: the monad laws, and `bind` reads a substitution only on the leaves. -/
class LawfulSubst (T : Type) (L : outParam Type) [Subst T L] : Prop where
  bind_leaf : ∀ (l : L) (f : L → T), Subst.bind (Subst.leaf l) f = f l
  bind_bind : ∀ (t : T) (f g : L → T),
    Subst.bind (Subst.bind t f) g = Subst.bind t (fun l => Subst.bind (f l) g)
  bind_congr : ∀ (t : T) (f g : L → T),
    (∀ l ∈ Subst.leaves t, f l = g l) → Subst.bind t f = Subst.bind t g

/-- The standard leaves: `D.this` and `D#i`. -/
inductive Leaf (α : Type) where
  | this (c : List α)
  | param (c : List α) (i : Nat)
  deriving DecidableEq, Repr

instance {α : Type} : Leafy (Leaf α) α where
  cls | .this c => c | .param c _ => c
  kind | .this _ => .this | .param _ i => .param i

/-- The base-type facts the walk reads. -/
structure World (α T : Type) where
  bpre : T → List α → T
  hasBase : T → List α → Bool
  bargs : T → List α → List T := fun _ _ => []

section Walk

variable {α L T : Type} [DecidableEq α] [Leafy L α] [Subst T L] (W : World α T)

/-- Does the walk stop at cursor `c` over prefix `p`? (`matchesPrefixAndClass`) -/
def hit (l : L) (c : List α) (p : T) : Bool := decide (c = Leafy.cls l) && W.hasBase p c

/-- What a leaf becomes when the walk stops over `p` at `c`. A parameter whose argument is
missing stays put. -/
def atHit (l : L) (c : List α) (p : T) : T :=
  match Leafy.kind l with
  | .this => p
  | .param i => ((W.bargs p c)[i]?).getD (Subst.leaf l)

/-- Does the walk stop with a rewrite (not a missing argument)? -/
def okAt (l : L) (c : List α) (p : T) : Bool :=
  match Leafy.kind l with
  | .this => true
  | .param i => decide (i < (W.bargs p c).length)

/-- `thisTypeAsSeen` and `classParameterAsSeen`: the anchored walk, cursor `c`, prefix `p`. -/
def leafAsSeen (l : L) : List α → T → T
  | [], _ => Subst.leaf l
  | c@(_ :: rest), p => if hit W l c p then atHit W l c p else leafAsSeen l rest (W.bpre p c)

/-- `info.asSeenFrom(p, c)`. -/
def asf (p : T) (c : List α) (t : T) : T := Subst.bind t fun l => leafAsSeen W l c p

/-- `pre.memberType(m)` for a member `m` of class `owner` with declared type `info`. -/
def memberType (pre : T) (owner : List α) (info : T) : T := asf W pre owner info

/-- Does the walk anchored at `c` over `p` rewrite the leaf? -/
def rewrites (l : L) : List α → T → Bool
  | [], _ => false
  | c@(_ :: rest), p => if hit W l c p then okAt W l c p else rewrites l rest (W.bpre p c)

/-- `t` is in the view `(p, c)` resolves: every leaf is rewritten. -/
def inView (p : T) (c : List α) (t : T) : Prop := ∀ l ∈ Subst.leaves t, rewrites W l c p = true

end Walk

/-! ## Composition -/

section Compose

variable {α L T : Type} [DecidableEq α] [Leafy L α] [Subst T L] [LawfulSubst T L] (W : World α T)

/-- **Lockstep**: an `asSeenFrom` map commutes with the base-type facts. -/
class Lockstep : Prop where
  bpre_comm : ∀ p₂ c₂ p c, asf W p₂ c₂ (W.bpre p c) = W.bpre (asf W p₂ c₂ p) c
  hasBase_comm : ∀ p₂ c₂ p c, W.hasBase (asf W p₂ c₂ p) c = W.hasBase p c
  bargs_comm : ∀ p₂ c₂ p c, W.bargs (asf W p₂ c₂ p) c = (W.bargs p c).map (asf W p₂ c₂)

variable [Lockstep W]

omit [LawfulSubst T L] in
theorem hit_asf (l : L) (c : List α) (p₂ : T) (c₂ : List α) (p : T) :
    hit W l c (asf W p₂ c₂ p) = hit W l c p := by
  simp only [hit, Lockstep.hasBase_comm]

omit [LawfulSubst T L] in
theorem okAt_asf (l : L) (c : List α) (p₂ : T) (c₂ : List α) (p : T) :
    okAt W l c (asf W p₂ c₂ p) = okAt W l c p := by
  unfold okAt; split <;> simp [Lockstep.bargs_comm]

omit [LawfulSubst T L] in
/-- Whether a leaf is rewritten depends on the prefix's base types, which a later map keeps. -/
theorem rewrites_asf (l : L) (c : List α) (p₂ : T) (c₂ : List α) (p : T) :
    rewrites W l c (asf W p₂ c₂ p) = rewrites W l c p := by
  induction c generalizing p with
  | nil => rfl
  | cons x rest ih =>
    simp only [rewrites, hit_asf, okAt_asf]
    split
    · rfl
    · rw [← Lockstep.bpre_comm]; exact ih _

omit [LawfulSubst T L] in
theorem atHit_asf (l : L) (c : List α) (p₂ : T) (c₂ : List α) (p : T) (h : okAt W l c p = true) :
    asf W p₂ c₂ (atHit W l c p) = atHit W l c (asf W p₂ c₂ p) := by
  unfold okAt at h; unfold atHit
  cases hk : Leafy.kind l with
  | this => rfl
  | param i =>
    simp only [hk, decide_eq_true_eq] at h
    simp [Lockstep.bargs_comm, List.getElem?_eq_getElem h]

omit [LawfulSubst T L] in
/-- A leaf the first walk rewrites can be viewed again: the result is the first walk over the
mapped prefix. -/
theorem leafAsSeen_asf (l : L) (c : List α) (p₂ : T) (c₂ : List α) (p : T)
    (h : rewrites W l c p = true) :
    asf W p₂ c₂ (leafAsSeen W l c p) = leafAsSeen W l c (asf W p₂ c₂ p) := by
  induction c generalizing p with
  | nil => simp [rewrites] at h
  | cons x rest ih =>
    simp only [leafAsSeen, rewrites, hit_asf] at h ⊢
    by_cases hc : hit W l (x :: rest) p = true
    · simp only [hc, ↓reduceIte] at h ⊢; exact atHit_asf W l _ p₂ c₂ p h
    · simp only [hc] at h ⊢
      rw [← Lockstep.bpre_comm]; exact ih _ h

/-- **Composition law.** Two maps in sequence are one map, from the first prefix as seen by the
second map, provided the first map rewrote every leaf of its input. No condition on `c₂`: the
second anchor decides *which* prefix, not whether there is one. -/
theorem compose (p₁ : T) (c₁ : List α) (p₂ : T) (c₂ : List α) (t : T) (h : inView W p₁ c₁ t) :
    asf W p₂ c₂ (asf W p₁ c₁ t) = asf W (asf W p₂ c₂ p₁) c₁ t := by
  unfold asf
  rw [LawfulSubst.bind_bind]
  apply LawfulSubst.bind_congr
  intro l hl
  exact leafAsSeen_asf W l c₁ p₂ c₂ p₁ (h l hl)

/-- A link of a chain: a prefix and an anchor, as in IntelliJ's `ThisTypeSubstitution`. -/
structure Link (α T : Type) where
  pre : T
  anchor : List α

def applyChain (links : List (Link α T)) (t : T) : T :=
  links.foldl (fun acc l => asf W l.pre l.anchor acc) t

/-- The first link's prefix, viewed through the later links. -/
def composedPrefix : List (Link α T) → T → T
  | [], p => p
  | l :: ls, p => composedPrefix ls (asf W l.pre l.anchor p)

/-- **A chain is one `asSeenFrom`**, from the composed prefix, at the first anchor. -/
theorem chain_is_single (l : Link α T) (ls : List (Link α T)) (t : T)
    (h : inView W l.pre l.anchor t) :
    applyChain W (l :: ls) t = asf W (composedPrefix W ls l.pre) l.anchor t := by
  induction ls generalizing l with
  | nil => rfl
  | cons l₂ rest ih =>
    simp only [applyChain, List.foldl, composedPrefix] at *
    rw [compose W _ _ _ _ _ h]
    have h' : inView W (asf W l₂.pre l₂.anchor l.pre) l.anchor t := by
      intro d hd; rw [rewrites_asf]; exact h d hd
    exact ih ⟨asf W l₂.pre l₂.anchor l.pre, l.anchor⟩ h'

end Compose

end AsSeenFrom
