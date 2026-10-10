import BinCompat.Edits

/-!
# MiMa as a bridge design: keys, covering, and its gaps

In `DESIGN-spec.md`'s terms, MiMa is a bridge between two versions of a library. Its *keys* are
what it compares (`Key`, per class public in the old library); a key's comparison is `check`,
which reports problems; and `mima` reports every key's problems. A client's linkage *queries* are
`Jvm.Q`: a class's header, whether it declares a method or a field, its declared methods. A key
*covers* a query if its comparison reads that entry of the class table (`covers`).

MiMa's obligation, for every client `p` that links against the old library: if no key reports a
problem, `p` still links against the new one. By `Jvm.link_congr`, a client that stops linking
has a footprint query whose answer changed (`miss_changes_footprint`); so every miss is one of:

* a **coverage** gap: the changed query is covered by no key (MiMa never looks there);
* an **abstraction** gap: a key covers it, and its comparison passes although the answer changed
  in a way that matters (MiMa looks, and calls it compatible).

MiMa compares by a relation, not by equality (an added method is a changed answer, and fine), so
abstraction is "the comparison is strong enough for linking", not "equal facts". The witnesses
below are confirmed on HotSpot 21, 25 and 27 by `probes/jvm`, and MiMa 1.2.1 reports nothing for
each (`probes/mima`).
-/

namespace BinCompat

open Jvm Jvm.Catalogue Jvm.Clients

/-- The class-table entries a key's comparison reads. A field key looks the name up in the
class and its superclasses; a method key also in the superinterfaces. -/
def covers (o : Lib) : Key → Q C N D → Bool
  | .template c, .header x => x == c
  | .field c n _, .field x n' _ => n == n' && (c :: supers o fuel c).contains x
  | .method c n _, .method x n' _ =>
    n == n' && (c :: supers o fuel c ++ allIfaces o fuel c).contains x
  | _, _ => false

/-- A library edit and a client of it. -/
structure Witness where
  o : Lib
  n : Lib
  client : Lib := []
  prog : P

def Witness.w0 (x : Witness) : W := world (x.client ++ x.o)
def Witness.w1 (x : Witness) : W := world (x.client ++ x.n)

/-- MiMa reports nothing, and the client links before and not after. -/
def Witness.missed (x : Witness) : Bool :=
  mima x.o x.n == [] && (outcome x.w0 x.prog).toBool && !(outcome x.w1 x.prog).toBool

/-- `q` is in the client's footprint, its answer changed, and no MiMa key covers it. -/
def Witness.uncovered (x : Witness) (q : Q C N D) : Bool :=
  (footprint x.w0 x.prog).contains q && !agrees x.w0 x.w1 q && (keys x.o).all (!covers x.o · q)

/-- `q` is in the client's footprint, its answer changed, and MiMa's key `k` covers it and
passes. -/
def Witness.passes (x : Witness) (q : Q C N D) (k : Key) : Bool :=
  (footprint x.w0 x.prog).contains q && !agrees x.w0 x.w1 q && (keys x.o).contains k &&
    covers x.o k q && check x.o x.n k == []

/-- Every key passes when MiMa is silent. -/
theorem check_nil_of_mima_nil {o n : Lib} (h : mima o n = []) {k : Key} (hk : k ∈ keys o) :
    check o n k = [] := by
  unfold mima at h
  exact List.flatMap_eq_nil_iff.mp h k hk

/-- **A miss changes the footprint.** A client that links against the old library and not
against the new one asks some query whose answer changed (the contrapositive of `link_congr`).
So a miss is a coverage gap or, when a key covers that query, an abstraction gap. -/
theorem miss_changes_footprint (x : Witness) (h0 : (outcome x.w0 x.prog).toBool = true)
    (h1 : (outcome x.w1 x.prog).toBool = false) :
    ∃ q ∈ footprint x.w0 x.prog, answer x.w0 q ≠ answer x.w1 q := by
  by_contra hne
  push Not at hne
  have := link_congr x.w0 x.w1 x.prog hne
  rw [this] at h0
  rw [h0] at h1
  exact Bool.noConfusion h1

/-! ## The gaps, each with a witness -/

def pubM : MethodInfo := {}

/-- **F1, final fields.** A public field becomes `final`; a client's `putfield` now fails with
`IllegalAccessError`. MiMa's field key covers the query and does not compare `final`. -/
def finalField : Witness where
  o := base1
  n := replace base1 .A (setField ((get base1 .A).getD {}) (some { isFinal := true }))
  prog := { sites := [.putfield .A .m .s .A] }

example : finalField.missed = true ∧ finalField.passes (.field .A .m .s) (.field .A .m .s) = true := by
  decide +kernel

/-- **M1, a subclass's member shadows an inherited one.** `B` gains a static `m()V` that hides
`A.m()V`; `invokevirtual B.m` now resolves to it and fails (`IncompatibleClassChangeError`).
MiMa checks only the members a class declares: no key covers `B.m`. Any access and any of
`static`/`final` breaks some client the same way, and so do fields. -/
def shadowStatic : Witness where
  o := base1
  n := replace base1 .B (setMethod ((get base1 .B).getD {}) .v (some { isStatic := true }))
  prog := { sites := [.invokevirtual .B .m .v .B] }

example : shadowStatic.missed = true ∧ shadowStatic.uncovered (.method .B .m .v) = true := by
  decide +kernel

/-- **M1 with a field**: `B` gains a static field `m` that hides `A.m`; `getfield B.m` fails. -/
def shadowField : Witness where
  o := base1
  n := replace base1 .B (setField ((get base1 .B).getD {}) (some { isStatic := true }))
  prog := { sites := [.getfield .B .m .s .B] }

example : shadowField.missed = true ∧ shadowField.uncovered (.field .B .m .s) = true := by
  decide +kernel

/-- **M1, as an abstraction gap**: an override becomes private. MiMa's key for `B.m` covers the
query, but MiMa's class file parser drops private methods, so its lookup finds the inherited
`A.m` and passes; resolution finds the private `B.m` (`IllegalAccessError`). -/
def overridePrivate : Witness where
  o := base2
  n := replace base2 .B (setMethod ((get base2 .B).getD {}) .v (some { access := .priv }))
  prog := { sites := [.invokevirtual .B .m .v .B] }

example : overridePrivate.missed = true ∧
    overridePrivate.passes (.method .B .m .v) (.method .B .m .v) = true := by
  decide +kernel

/-- **F2, an interface field comes first.** `I` gains a constant `m`. A client class extending
`A` and implementing `I` resolves `X.m` to `I.m` now (superinterfaces before the superclass),
which is static: `getfield X.m` fails. MiMa's field lookup never reads an interface. -/
def ifaceField : Witness where
  o := base1
  n := replace base1 .I (setField ((get base1 .I).getD {}) (some { isStatic := true, isFinal := true }))
  client := [(.X, { header := { super := some .A, ifaces := [.I] } })]
  prog := { loads := [.X], sites := [.getfield .X .m .s .X] }

example : ifaceField.missed = true ∧ ifaceField.uncovered (.field .I .m .s) = true := by
  decide +kernel

/-- **D1, conflicting defaults.** `J` gains a default `m()V` that `I` also has; a client class
implementing both now has two maximally-specific methods (`IncompatibleClassChangeError`; on JDK
21, `AbstractMethodError`, JDK-8356942). MiMa's `checkNew` reads only abstract methods. -/
def defaultConflict : Witness where
  o := base1
  n := replace base1 .J (setMethod ((get base1 .J).getD {}) .v (some {}))
  client := [(.X, { header := { ifaces := [.I, .J] } })]
  prog := { loads := [.X], sites := [.invokeinterface .I .m .v .X] }

example : defaultConflict.missed = true ∧ defaultConflict.uncovered (.method .J .m .v) = true := by
  decide +kernel

end BinCompat
