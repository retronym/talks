import Zinc.Pipelining

/-!
# Pipelining: the early output's lifecycle

An upstream unit's state is three views: the source of its last successful build, that build's
interface, and the interface its early output publishes. A run whose source is the last built one
does nothing; any other run writes its early output first, then succeeds (both views move) or fails
(Zinc rolls back the classfiles and the analysis, and the early output only with sbt/zinc#1843).
A downstream compiles against the early output and keeps its hash as a snapshot; its next build
invalidates when the early output's hash differs from the snapshot.

* `rollback_preserves`: with #1843 every run keeps `early = built` ("published = built").
* `noRollback_breaks`, `stale_after_revert`: without it a failed run publishes an interface that
  never built, and the revert, whose sources equal the last build's, leaves it there; a downstream
  that read it sees no hash change and keeps it. This is `Pipelining.stale_after_failed_upstream`
  for every interface and hash.
* `rollback_detects`: with #1843 the downstream's snapshot of the failed early output differs from
  the restored one, so its next build recompiles (`Pipelining.rollback_after_failed_upstream`).
* `downstream_reads_built`: under the invariant a downstream reads the last successful build.
* `partial_write`: a cancelled write (scala/scala3#27139) that left the early output between the old
  and the new is the same failure, and the same rollback restores the invariant.
-/

namespace Zinc.PipelineLifecycle

variable {Src Iface H : Type} [DecidableEq Src]

structure Views (Src Iface : Type) where
  src : Src
  built : Iface
  early : Iface

def Published (v : Views Src Iface) : Prop := v.early = v.built

/-- A run of the upstream with source `s`, whose fresh interface is `fresh`, succeeding or not;
`rollback` is #1843. -/
def run (rollback : Bool) (v : Views Src Iface) (s : Src) (fresh : Iface) (ok : Bool) : Views Src Iface :=
  if s = v.src then v
  else if ok then ⟨s, fresh, fresh⟩
  else ⟨v.src, v.built, if rollback then v.built else fresh⟩

/-- **#1843 keeps published = built.** -/
theorem rollback_preserves (v : Views Src Iface) (hv : Published v) (s : Src) (fresh : Iface) (ok : Bool) :
    Published (run true v s fresh ok) := by
  unfold run Published at *
  split
  · exact hv
  · split <;> rfl

/-- **Without it, a failed run publishes an interface that never built.** -/
theorem noRollback_breaks (v : Views Src Iface) (s : Src) (hs : s ≠ v.src) (fresh : Iface)
    (hf : fresh ≠ v.built) : ¬ Published (run false v s fresh false) := by
  simp [run, Published, hs, hf]

/-- **Stale after the revert.** A failed run with source `s`, then the source reverted to the last
built one: the early output still publishes the failed run's interface, and its hash is the one the
downstream stored during the failed run, so nothing invalidates the downstream. -/
theorem stale_after_revert (h : Iface → H) (v : Views Src Iface) (s : Src) (hs : s ≠ v.src)
    (fresh : Iface) (hf : fresh ≠ v.built) :
    let v₁ := run false v s fresh false
    let v₂ := run false v₁ v.src v.built true
    v₂.early = fresh ∧ ¬ Published v₂ ∧ h v₂.early = h v₁.early := by
  simp [run, hs, Published, hf]

/-- **#1843 makes the stale snapshot visible.** After a failed run whose early output the
downstream read, the restored early output's hash differs from that snapshot whenever the hash
tells the failed interface from the built one. -/
theorem rollback_detects (h : Iface → H) (v : Views Src Iface) (s : Src) (hs : s ≠ v.src)
    (fresh : Iface) (hh : h fresh ≠ h v.built) :
    let snapshot := h fresh
    h (run true v s fresh false).early ≠ snapshot := by
  simp [run, hs, Ne.symm hh]

/-- **Under the invariant the downstream reads the last successful build**: its oracle on the
upstream's units is the built one, so `Classpath.downstream_sound` holds relative to it. -/
theorem downstream_reads_built {U Q : Type} {A : Q → Type} (answer : Iface → (q : Q) → A q)
    (views : U → Views Src Iface) (hp : ∀ u, Published (views u)) :
    (fun p : U × Q => answer (views p.1).early p.2) = (fun p : U × Q => answer (views p.1).built p.2) := by
  funext p
  rw [hp p.1]

/-- **A partial write** (scala/scala3#27139): a cancelled run leaves an early output `partial` that
is neither interface (`part`); rolling back the write is the same fix. -/
theorem partial_write (v : Views Src Iface) (part : Iface) (hpart : part ≠ v.built) :
    ¬ Published { v with early := part } ∧ Published { v with early := v.built } :=
  ⟨hpart, rfl⟩

end Zinc.PipelineLifecycle
