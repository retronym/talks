import Zinc.Hier

/-!
# The three hierarchy designs meet their obligations

* `D` (decls + walk): `Compiler.Obligations`, with source-determined interfaces, so T3 and the
  two-round bound apply.
* `W` (materialised members): `Compiler.Obligations`. Interfaces are not source-determined; the
  compositionality proof has to show that materialising members only reads declarations.
* `Mk` (Merkle): `GCompiler.Obligations`. Coverage is trace-dependent: the key `(c, m)` covers
  exactly the queries the walk from `c` for `m` issues under the current interfaces, and the hash
  is that walk's verifying trace.
-/

namespace Zinc.Hier

open Zinc.Task

/-! ## Traces of the walk -/

/-- The walk only asks `decl` and `parents`. -/
theorem trace_walkWith (r : Cls → Ty → T (Option Ty)) (e : Env)
    (hr : ∀ p parg q, q ∈ (r p parg).trace e → (∃ n, q.2 = .decl n) ∨ q.2 = .parents) :
    ∀ ps q, q ∈ (walkWith r ps).trace e → (∃ n, q.2 = .decl n) ∨ q.2 = .parents := by
  intro ps
  induction ps with
  | nil => intro q hq; simp [walkWith] at hq
  | cons p rest ih =>
    intro q hq
    obtain ⟨c, parg⟩ := p
    simp only [walkWith, bind_eq, trace_bind, List.mem_append] at hq
    rcases hq with hq | hq
    · exact hr c parg q hq
    · split at hq
      · simp at hq
      · exact ih q hq

theorem trace_resolve (e : Env) : ∀ fuel c n arg q, q ∈ (resolve fuel c n arg).trace e →
    (∃ n, q.2 = .decl n) ∨ q.2 = .parents := by
  intro fuel
  induction fuel with
  | zero => intro c n arg q hq; simp [resolve] at hq
  | succ fuel ih =>
    intro c n arg q hq
    simp only [resolve, bind_eq, trace_bind, trace_askQ, List.singleton_append, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Or.inl ⟨n, rfl⟩
    · split at hq
      · simp at hq
      · simp only [bind_eq, trace_bind, trace_askQ, List.singleton_append, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact Or.inr rfl
        · split at hq
          · exact trace_walkWith _ e (fun p parg q hq => ih p n _ q hq) _ q hq
          · simp at hq

theorem trace_resolveFrom (e : Env) (d : Decl) (n : Name) :
    ∀ q ∈ (resolveFrom d n).trace e, (∃ n, q.2 = .decl n) ∨ q.2 = .parents := by
  intro q hq
  simp only [resolveFrom] at hq
  split at hq
  · simp at hq
  · exact trace_walkWith _ e (fun p parg q hq => trace_resolve e 3 p n parg q hq) _ q hq

theorem trace_selectsMat (e : Env) : ∀ body q, q ∈ (selectsMat body).trace e →
    ∃ n, q.2 = .members n := by
  intro body
  induction body with
  | nil => intro q hq; simp [selectsMat] at hq
  | cons p rest ih =>
    intro q hq
    obtain ⟨c, n⟩ := p
    simp only [selectsMat, bind_eq, pure_eq, trace_bind, trace_askQ, trace_pure, List.append_nil, List.singleton_append,
      List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨n, rfl⟩
    · exact ih q hq

/-- Every query of a walk-based client is the marker of some selection, or in that selection's
walk. -/
theorem trace_selects (e : Env) : ∀ body q, q ∈ (selects body).trace e →
    ∃ c n, (c, n) ∈ body ∧ (q = (c, .select n) ∨ q ∈ (resolve 3 c n .param).trace e) := by
  intro body
  induction body with
  | nil => intro q hq; simp [selects] at hq
  | cons p rest ih =>
    intro q hq
    obtain ⟨c, n⟩ := p
    simp only [selects, bind_eq, pure_eq, trace_bind, trace_askQ, trace_pure, List.append_nil, List.singleton_append,
      List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact ⟨c, n, by simp, Or.inl rfl⟩
    · exact ⟨c, n, by simp, Or.inr hq⟩
    · obtain ⟨c', n', hm, h⟩ := ih q hq
      exact ⟨c', n', by simp [hm], h⟩

/-- The marker of every selection is in the trace. -/
theorem select_mem_trace_selects (e : Env) : ∀ body c n, (c, n) ∈ body →
    (c, Q.select n) ∈ (selects body).trace e := by
  intro body
  induction body with
  | nil => intro c n h; simp at h
  | cons p rest ih =>
    intro c n h
    obtain ⟨c', n'⟩ := p
    simp only [List.mem_cons, Prod.mk.injEq] at h
    simp only [selects, bind_eq, pure_eq, trace_bind, trace_askQ, trace_pure, List.append_nil, List.singleton_append,
      List.mem_cons, List.mem_append]
    rcases h with ⟨rfl, rfl⟩ | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (ih c n h))

/-! ## Interfaces -/

theorem iface_unitWalk (s : Src) (e : Env) : ((unitWalk s).run e).iface = ⟨s.decl, []⟩ := by
  simp [unitWalk]

theorem decl_unitMat (s : Src) (e : Env) : ((unitMat s).run e).iface.decl = s.decl := by
  simp [unitMat]

theorem mems_unitMat (s : Src) (e : Env) :
    ((unitMat s).run e).iface.mems =
      [(.m, (resolveFrom s.decl .m).run e), (.g, (resolveFrom s.decl .g).run e)] := by
  simp [unitMat]

/-- Two oracles that agree on `decl` and `parents` queries materialise the same members. -/
theorem resolveFrom_congr (d : Decl) (n : Name) (e e' : Env)
    (h : ∀ q : Cls × Q, ((∃ n, q.2 = .decl n) ∨ q.2 = .parents) → e q = e' q) :
    (resolveFrom d n).run e = (resolveFrom d n).run e' :=
  Task.run_congr _ e e' fun q hq => h q (trace_resolveFrom e d n q hq)

/-! ## `D`: decls + walk -/

theorem comp_src (unit : Src → T Out) (hi : ∀ s e, ((unit s).run e).iface = ⟨s.decl, []⟩)
    (Cp : Compiler Cls Src Out Iface K Iface Q Ans) (hu : Cp.unit = unit)
    (hg : Cp.group = groupSrc unit) (hif : Cp.iface = Out.iface) (ha : Cp.answer = answer) :
    ∀ (G : Finset Cls) (src : Cls → Src) (e : Env), ∀ d ∈ G, Cp.group G src e d =
      (Cp.unit (src d)).run (Cp.override e G (Cp.iface ∘ Cp.group G src e)) := by
  intro G src e d _
  rw [hg, hu]
  simp only [groupSrc]
  congr 1
  funext p
  simp only [Compiler.override, hif, ha, hg, Function.comp]
  split
  · rw [groupSrc, hi]
  · rfl

theorem D_obligations : D.Obligations where
  comp := comp_src unitWalk iface_unitWalk D rfl rfl rfl rfl
  coverage := by
    intro tr q hq
    refine ⟨(q.1, match q.2 with
      | .decl n => K.name n | .select n => K.name n | .members n => K.name n | .parents => K.parents),
      ?_, rfl, ?_⟩
    · show _ ∈ keysD tr
      simp only [keysD, List.mem_toFinset, List.mem_map]
      exact ⟨q, hq, rfl⟩
    · show CoversD q.2 _
      cases q.2 <;> constructor
  abstraction := by
    intro i i' k h q hc
    cases hc with
    | decl n =>
      simp only [D, πD, Iface.mk.injEq, Decl.mk.injEq, true_and] at h
      simp only [D, answer]; rw [h.1]
    | select n => rfl
    | members n =>
      simp only [D, πD, Iface.mk.injEq, Decl.mk.injEq, true_and] at h
      simp only [D, answer]; rw [h.2]
    | parents =>
      simp only [D, πD, Iface.mk.injEq, Decl.mk.injEq, and_true] at h
      simp only [D, answer]; rw [h]

theorem D_explicit : ∀ (s : Src) (e : Env), D.iface ((D.unit s).run e) = ⟨s.decl, []⟩ :=
  fun s e => iface_unitWalk s e

/-! ## `W`: materialised members -/

/-- Materialising against the group's declarations, or against the group's materialised
interfaces, gives the same members: only declarations are read. -/
theorem groupMat_iface (G : Finset Cls) (src : Cls → Src) (e : Env) (u : Cls) :
    (groupMat G src e u).iface = matIface G src e u := by
  have hagree : ∀ q : Cls × Q, ((∃ n, q.2 = .decl n) ∨ q.2 = .parents) →
      (fun p => if p.1 ∈ G then answer (matIface G src e p.1) p.2 else e p) q = matEnv G src e q := by
    intro q hq
    simp only [matEnv]
    split
    · rcases hq with ⟨n, hn⟩ | hn <;> rw [hn] <;> simp only [answer, matIface, decl_unitMat]
    · rfl
  show ((unitMat (src u)).run (fun p => if p.1 ∈ G then answer (matIface G src e p.1) p.2 else e p)).iface
    = ((unitMat (src u)).run (matEnv G src e)).iface
  apply Iface.ext
  · rw [decl_unitMat, decl_unitMat]
  · rw [mems_unitMat, mems_unitMat, resolveFrom_congr _ _ _ _ hagree, resolveFrom_congr _ _ _ _ hagree]

theorem W_comp : ∀ (G : Finset Cls) (src : Cls → Src) (e : Env), ∀ d ∈ G, W.group G src e d =
    (W.unit (src d)).run (W.override e G (W.iface ∘ W.group G src e)) := by
  intro G src e d _
  show groupMat G src e d =
    (unitMat (src d)).run (Compiler.override W e G (Out.iface ∘ groupMat G src e))
  conv_lhs => unfold groupMat
  congr 1
  funext p
  simp only [Compiler.override, W, Function.comp]
  split
  · rw [groupMat_iface]
  · rfl

theorem W_obligations : W.Obligations where
  comp := W_comp
  coverage := by
    intro tr q hq
    refine ⟨(q.1, match q.2 with | .members n => K.name n | _ => K.top), ?_, rfl, ?_⟩
    · show _ ∈ keysW tr
      simp only [keysW, List.mem_toFinset, List.mem_map]
      exact ⟨q, hq, rfl⟩
    · show CoversW q.2 _
      cases q.2 <;> constructor
  abstraction := by
    intro i i' k h q hc
    cases hc with
    | members n =>
      simp only [W, πW, Iface.mk.injEq, true_and] at h
      simp only [W, answer]; rw [h]
    | top q =>
      simp only [W, πW] at h
      simp only [W]; rw [h]

/-! ## `Mk`: Merkle -/

theorem Mk_comp : ∀ (G : Finset Cls) (src : Cls → Src) (e : Env), ∀ d ∈ G, Mk.group G src e d =
    (Mk.unit (src d)).run (Mk.override e G (Mk.iface ∘ Mk.group G src e)) := by
  intro G src e d _
  show groupSrc unitWalk G src e d =
    (unitWalk (src d)).run (GCompiler.override Mk e G (Out.iface ∘ groupSrc unitWalk G src e))
  conv_lhs => unfold groupSrc
  congr 1
  funext p
  simp only [GCompiler.override, Mk, Function.comp]
  split
  · rw [groupSrc, iface_unitWalk]
  · rfl

theorem trace_unitWalk (s : Src) (e : Env) :
    (unitWalk s).trace e = (selects s.body).trace e := by
  simp [unitWalk]

theorem Mk_obligations : Mk.Obligations where
  comp := Mk_comp
  coverage := by
    intro I s q hq
    change q ∈ (unitWalk s).trace (envOfI I) at hq
    rw [trace_unitWalk] at hq
    obtain ⟨c, n, hm, h⟩ := trace_selects (envOfI I) s.body q hq
    refine ⟨(c, K.name n), ?_, n, rfl, h⟩
    change _ ∈ keysM ((unitWalk s).trace (envOfI I))
    rw [trace_unitWalk]
    simp only [keysM, List.mem_toFinset, List.mem_filterMap]
    exact ⟨(c, .select n), select_mem_trace_selects _ _ c n hm, rfl⟩
  abstraction := by
    intro I I' k h q hc
    obtain ⟨n, hk, hq⟩ := hc
    have hπ : πM I k.1 (K.name n) = πM I' k.1 (K.name n) := by rw [← hk]; exact h
    simp only [πM] at hπ
    have htr : (resolve 3 k.1 n .param).trace (envOfI I) =
        (resolve 3 k.1 n .param).trace (envOfI I') := by
      have := congrArg (List.map Prod.fst) hπ
      simpa [List.map_map, Function.comp_def] using this
    refine ⟨?_, n, hk, ?_⟩
    · rcases hq with rfl | hq
      · rfl
      · have hmem : (q, envOfI I q) ∈ ((resolve 3 k.1 n .param).trace (envOfI I')).map
            fun q => (q, envOfI I' q) := by
          rw [← hπ]; exact List.mem_map.2 ⟨q, hq, rfl⟩
        obtain ⟨q', _, hq'⟩ := List.mem_map.1 hmem
        simp only [Prod.mk.injEq] at hq'
        obtain ⟨rfl, hans⟩ := hq'
        exact hans.symm
    · rcases hq with rfl | hq
      · exact Or.inl rfl
      · exact Or.inr (htr ▸ hq)
  locality := by
    intro I I' c h k
    have : I = I' := by
      funext d
      apply h
      cases d <;> simp [Mk, allCls]
    rw [this]
  rev := by intro c d _; cases c <;> simp [Mk, allCls]

end Zinc.Hier
