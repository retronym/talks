import BinCompat.ZincBridge

/-!
# B4 for a client of a library JAR

A library has classfiles and no Analysis: Zinc cannot see its sources, its name hashes or its
dependencies. It records, for each library a client read, the JAR's stamp, and invalidates the
client when the stamp moves (`Classpath.lean`'s library case).

**The bridge** (`compiler dl Lib`): a query on a library unit is covered by the unit's stamp key,
hashed by its whole interface; a query on a source unit by `ZincBridge`'s per-query key. A stamp
is a content hash of the JAR, so equal stamps mean equal interfaces; hashing the interface itself
is the coarsest such hash, and a finer one (the bytes) only adds invalidations. The bridge meets
the obligations (`obligations`); the stamp key alone covers every query on a library unit
(`stamp_covers`).

**The theorem** (`library_client`). The library `Lib` is upstream of the project `S`. From an up
to date build whose stamps are the old library's interfaces, put the edited JAR on the classpath
(`withUpstream`) and start Zinc's loop from the edited sources and the external invalidations
(the clients holding a stamp that moved). If the loop stops and never recompiled a client `c`, then
`c`'s old classfiles next to the new library link exactly as a fresh build of the project against
the new library does. It is `Zinc.XCompiler.inv_external` (T5a) followed by
`Zinc.XCompiler.untouched_eq_clean`.
-/

namespace BinCompat.ZincBridgeLibs

open Scala ZincBridge

/-- A key: the stamp of a library unit (`none`), or one side of a source unit. -/
abbrev LKey := Option Bool

/-- A hash: a stamp, or one side's declaration. -/
abbrev LHash := Iface ⊕ Option Decl

def π (I : String → Iface) (u : String) : LKey → LHash
  | none => .inl (I u)
  | some b => .inr (side I (u, b))

def key (Lib : Finset String) (q : FQ) : String × LKey :=
  if q.1 ∈ Lib then (q.1, none) else (q.1, some q.2)

def covers (q : FQ) (k : String × LKey) : Prop :=
  q.1 = k.1 ∧ (k.2 = none ∨ k.2 = some q.2)

/-- Lowering, with stamps for the library `Lib`. -/
def compiler (dl : Dialect) (Lib : Finset String) :
    Zinc.XCompiler String (Option Scala.Src) Out Iface LKey LHash Bool (fun _ => Option View) where
  unit := unit dl
  group := group dl
  iface := Out.iface
  answer := answer
  π := π
  hashDeps _ u := {u}
  keys _ _ tr := tr.toFinset.image (key Lib)
  covers _ q k := covers q k

theorem key_covers (Lib : Finset String) (q : FQ) : covers q (key Lib q) := by
  unfold key covers; split <;> simp

/-- Every query on a library unit is covered by that unit's stamp. -/
theorem stamp_covers (Lib : Finset String) (q : FQ) (hq : q.1 ∈ Lib) :
    key Lib q = (q.1, none) ∧ covers q (q.1, none) := by
  simp [key, covers, hq]

theorem answer_eq_of_side (I I' : String → Iface) (q : FQ) (h : side I q = side I' q) :
    answer I q = answer I' q := by
  show (side I q).map _ = (side I' q).map _
  rw [h]

theorem obligations (dl : Dialect) (Lib : Finset String) : (compiler dl Lib).Obligations where
  comp G src I u hu := (searched_obligations dl).comp G src I u hu
  coverage I _ s q hq := ⟨key Lib q, Finset.mem_image.2 ⟨q, List.mem_toFinset.2 hq, rfl⟩,
    key_covers Lib q⟩
  abstraction I I' k h q hc := by
    obtain ⟨u, k⟩ := k
    obtain ⟨q1, q2⟩ := q
    obtain ⟨rfl, hk⟩ := hc
    refine ⟨?_, ⟨rfl, hk⟩⟩
    apply answer_eq_of_side
    rcases hk with rfl | rfl
    · have : I q1 = I' q1 := Sum.inl.inj h
      simp only [side, this]
    · exact Sum.inr.inj h
  locality I I' c h k := by
    have hc := h c (Finset.mem_singleton_self c)
    cases k <;> simp only [compiler, π, side, hc]

/-- The stamps Zinc stored are the old library's interfaces: the snapshot is fresh. -/
theorem fresh_of_stamps (dl : Dialect) (Lib S : Finset String) (s : Zinc.Compiler.State String Out LKey)
    (snap : String → Iface) (hsnap : ∀ u ∈ Lib, snap u = (compiler dl Lib).ifaces s u) :
    (compiler dl Lib).Fresh Lib S s snap ∅ := by
  intro d _ _ k _
  have : (compiler dl Lib).snapView Lib s snap = (compiler dl Lib).ifaces s := by
    funext u
    simp only [Zinc.XCompiler.snapView]
    split
    · exact hsnap u ‹_›
    · rfl
  rw [this]

/-- **B4 for a client of an edited JAR.** Hypotheses: the library is disjoint from the project; the
old build is up to date with stamps from the old library; `D` covers the edited sources; the loop
starts from `D` and the external invalidations and stays inside `S` under a sound policy. Then a
project unit `c` the loop never recompiled links against the new JAR as in a fresh build. -/
theorem library_client (dl : Dialect) (us : List String) (Lib S : Finset String)
    (hdisj : Disjoint Lib S) (src₀ src : String → Option Scala.Src)
    (s : Zinc.Compiler.State String Out LKey) (snap : String → Iface) (o : String → Out)
    (hsnap : ∀ u ∈ Lib, snap u = (compiler dl Lib).ifaces s u)
    (D : Finset String) (hD : ∀ u, src₀ u ≠ src u → u ∈ D)
    (hInv : (compiler dl Lib).Inv S src₀ s ∅)
    (P : Zinc.Compiler.Policy String Out LKey) (hP : P.Sound S) (hPS : P.InS S) (fuel : ℕ)
    (R₀ : Finset String)
    (hR₀ : D ∪ (compiler dl Lib).extInvalidated Lib S s snap
      (Zinc.XCompiler.withUpstream Lib s o) ⊆ R₀)
    (hR₀S : R₀ ⊆ S)
    (s' : Zinc.Compiler.State String Out LKey)
    (h : (compiler dl Lib).zinc S src P fuel 0 R₀ (Zinc.XCompiler.withUpstream Lib s o) = some s')
    (c : String) (hcLib : c ∉ Lib)
    (hc : c ∉ (compiler dl Lib).recompiled S src P fuel 0 R₀ (Zinc.XCompiler.withUpstream Lib s o))
    (p : Jvm.Program String String String) :
    let clean := (compiler dl Lib).cleanFrom S src (Zinc.XCompiler.withUpstream Lib s o)
    Jvm.outcome (afterWorld us clean c (s.out c)) p = Jvm.outcome (worldOf us clean) p := by
  intro clean
  have ob := obligations dl Lib
  have hInv₁ := (compiler dl Lib).inv_external ob.abstraction Lib S hdisj src₀ src s snap o D hD hInv
    (fresh_of_stamps dl Lib S s snap hsnap)
  have := (compiler dl Lib).untouched_eq_clean ob ifaceSrc (fun sr I => iface_unit dl sr _) S src P
    hP hPS fuel R₀ _ _ hR₀ hR₀S hInv₁ s' h c hc
  rw [Zinc.XCompiler.withUpstream_out_of_not_mem _ _ _ _ hcLib] at this
  unfold afterWorld
  congr 2
  funext u
  split
  · subst_vars; exact this
  · rfl

end BinCompat.ZincBridgeLibs
