import Jvm.Link

/-!
# A catalogue of library edits, linked

Each case is a library edit (`v0` → `v1`) and a client compiled against `v0`. The client's
classes and sites are fixed; only the library's classfiles change. Each case states the outcome
before and after, by kernel `decide` (no `native_decide`), and names the MiMa problem that reports it where there is one.
`lake exe jvmcases` dumps the cases; `probes/jvm` renders them to classfiles and checks the outcomes on
HotSpot.

Classes: `A`, `B` (library classes), `I`, `J` (library interfaces), `X` (the client's class).
-/

namespace Jvm.Catalogue

inductive C | A | B | I | J | X
  deriving DecidableEq, Repr

inductive N | m
  deriving DecidableEq, Repr

/-- `v` is `()V`, `i` is `()I`; `s` is a field of type `String`. -/
inductive D | v | i | s
  deriving DecidableEq, Repr

abbrev W := World C N D
abbrev P := Program C N D

def world (l : List (C × Classfile C N D)) : W := fun c => (l.find? (·.1 = c)).map (·.2)

def inst : MethodInfo := {}
def abs : MethodInfo := { isAbstract := true }

structure Case where
  name : String
  /-- The MiMa problem that reports the edit, if any. -/
  mima : Option String
  v0 : List (C × Classfile C N D)
  v1 : List (C × Classfile C N D)
  client : List (C × Classfile C N D) := []
  prog : P

def Case.w0 (k : Case) : W := world (k.client ++ k.v0)
def Case.w1 (k : Case) : W := world (k.client ++ k.v1)
def Case.before (k : Case) := outcome k.w0 k.prog
def Case.after (k : Case) := outcome k.w1 k.prog

open Site

def methodRemoved : Case where
  name := "methodRemoved"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, {})]
  prog := { sites := [invokevirtual .A .m .v .A] }

def resultTypeChanged : Case where
  name := "resultTypeChanged"
  mima := some "IncompatibleResultTypeProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .i, inst)] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

/-- `A` becomes an interface that `B` implements; the client's `A a = new B(); a.m()` still
verifies (an interface target is assignable) and fails to resolve `A.m` as a class method. -/
def classBecomesInterface : Case where
  name := "classBecomesInterface"
  mima := some "IncompatibleTemplateDefProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A } })]
  v1 := [(.A, { header := { isInterface := true }, methods := [(.m, .v, inst)] }),
         (.B, { header := { super := none, ifaces := [.A] } })]
  prog := { sites := [invokevirtual .A .m .v .B] }

def becomesStatic : Case where
  name := "becomesStatic"
  mima := some "VirtualStaticMemberProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, { isStatic := true })] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

def becomesAbstract : Case where
  name := "becomesAbstract"
  mima := some "AbstractClassProblem"
  v0 := [(.A, {})]
  v1 := [(.A, { header := { isAbstract := true } })]
  prog := { sites := [new .A] }

def becomesFinal : Case where
  name := "becomesFinal"
  mima := some "FinalClassProblem"
  v0 := [(.A, {})]
  v1 := [(.A, { header := { isFinal := true } })]
  client := [(.X, { header := { super := some .A } })]
  prog := { loads := [.X] }

def methodBecomesFinal : Case where
  name := "methodBecomesFinal"
  mima := some "FinalMethodProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, { isFinal := true })] })]
  client := [(.X, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  prog := { loads := [.X] }

def superclassRemoved : Case where
  name := "superclassRemoved"
  mima := some "MissingTypesProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A } })]
  v1 := [(.A, { methods := [(.m, .v, inst)] }), (.B, {})]
  prog := { sites := [invokevirtual .B .m .v .B] }

/-- A default method becomes abstract; the client's class implements the interface and never
declared the method, so a call through the interface finds nothing to run. -/
def defaultRemoved : Case where
  name := "defaultRemoved"
  mima := some "DirectAbstractMethodProblem"
  v0 := [(.I, { header := { isInterface := true }, methods := [(.m, .v, inst)] })]
  v1 := [(.I, { header := { isInterface := true }, methods := [(.m, .v, abs)] })]
  client := [(.X, { header := { ifaces := [.I] } })]
  prog := { loads := [.X], sites := [invokeinterface .I .m .v .X] }

/-- A second interface of the client's class gains a default method of the same signature: two
maximally-specific non-abstract methods. -/
def defaultConflict : Case where
  name := "defaultConflict"
  mima := none
  v0 := [(.I, { header := { isInterface := true }, methods := [(.m, .v, inst)] }),
         (.J, { header := { isInterface := true } })]
  v1 := [(.I, { header := { isInterface := true }, methods := [(.m, .v, inst)] }),
         (.J, { header := { isInterface := true }, methods := [(.m, .v, inst)] })]
  client := [(.X, { header := { ifaces := [.I, .J] } })]
  prog := { loads := [.X], sites := [invokeinterface .I .m .v .X] }

/-- An override added to a subclass: still links, and the call now runs `B.m`. Compatible, but
not footprint-equal. -/
def overrideAdded : Case where
  name := "overrideAdded"
  mima := none
  v0 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A } })]
  v1 := [(.A, { methods := [(.m, .v, inst)] }),
         (.B, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  prog := { sites := [invokevirtual .B .m .v .B] }

/-- A method moves up from `B` to its superclass: links, the same code runs from a new owner. -/
def pulledUp : Case where
  name := "pulledUp"
  mima := none
  v0 := [(.A, {}), (.B, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A } })]
  prog := { sites := [invokevirtual .B .m .v .B] }

/-! ## J3: access, `invokespecial` and private methods, interface statics, fields

Packages: `pkg := 1` is `p1`; a site without `within` runs from a class of its own in the unnamed
package. -/

def p1 : Header C := { pkg := 1 }
def iface : Header C := { isInterface := true }

def methodBecomesPrivate : Case where
  name := "methodBecomesPrivate"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, { access := .priv })] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

def methodBecomesPackagePrivate : Case where
  name := "methodBecomesPackagePrivate"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .pkg })] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

def classBecomesPackagePrivate : Case where
  name := "classBecomesPackagePrivate"
  mima := some "InaccessibleClassProblem"
  v0 := [(.A, { header := p1 })]
  v1 := [(.A, { header := { p1 with isPublic := false } })]
  prog := { sites := [new .A] }

/-- `public` to `protected`, called from a class that is not a subclass. -/
def methodBecomesProtected : Case where
  name := "methodBecomesProtected"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .prot })] })]
  prog := { sites := [invokevirtual .A .m .v .A] }

/-- The same edit, called from a subclass on itself: still links. -/
def methodBecomesProtectedSub : Case where
  name := "methodBecomesProtectedSub"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .prot })] })]
  client := [(.X, { header := { super := some .A } })]
  prog := { sites := [within .X (invokevirtual .X .m .v .X)] }

/-- The same edit, called from a subclass on an `A` that is not an `X`: §5.4.4 allows it, but the
verifier's protected check (§4.10.1.8) rejects the client. -/
def methodBecomesProtectedOther : Case where
  name := "methodBecomesProtectedOther"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .prot })] })]
  client := [(.X, { header := { super := some .A } })]
  prog := { sites := [within .X (invokevirtual .A .m .v .A)] }

/-- `A.m` becomes package-private; the client's override `X.m` in another package stops overriding
it, so a call from `A`'s package runs `A.m`: links, runs different code. -/
def overrideCutByPackage : Case where
  name := "overrideCutByPackage"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1, methods := [(.m, .v, { access := .pkg })] })]
  client := [(.X, { header := { super := some .A }, methods := [(.m, .v, inst)] }), (.B, { header := p1 })]
  prog := { sites := [within .B (invokevirtual .A .m .v .X)] }

/-- An override becomes private: a private method does not override, so `A.m` runs. A client
calling `B.m` itself breaks instead (`Jvm.Clients`): resolution finds the private `B.m` first. -/
def overrideBecomesPrivate : Case where
  name := "overrideBecomesPrivate"
  mima := none
  v0 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, inst)] }),
         (.B, { header := { super := some .A }, methods := [(.m, .v, { access := .priv })] })]
  prog := { sites := [invokevirtual .A .m .v .B] }

/-- `super.m()` from `X extends B extends A` is `invokespecial B.m`; `m` moves from `B` up to `A`. -/
def superCallPulledUp : Case where
  name := "superCallPulledUp"
  mima := none
  v0 := [(.A, {}), (.B, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods := [(.m, .v, inst)] }), (.B, { header := { super := some .A } })]
  client := [(.X, { header := { super := some .B } })]
  prog := { sites := [within .X (invokespecial .B .m .v false)] }

def superCallRemoved : Case where
  name := "superCallRemoved"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, {}), (.B, { header := { super := some .A }, methods := [(.m, .v, inst)] })]
  v1 := [(.A, {}), (.B, { header := { super := some .A } })]
  client := [(.X, { header := { super := some .B } })]
  prog := { sites := [within .X (invokespecial .B .m .v false)] }

def superCallAbstract : Case where
  name := "superCallAbstract"
  mima := some "AbstractClassProblem"
  v0 := [(.B, { methods := [(.m, .v, inst)] })]
  v1 := [(.B, { header := { isAbstract := true }, methods := [(.m, .v, abs)] })]
  client := [(.X, { header := { super := some .B }, methods := [(.m, .v, inst)] })]
  prog := { sites := [within .X (invokespecial .B .m .v false)] }

/-- `I.super.m()` from `X implements I`, and the default becomes abstract. -/
def defaultSuperCallAbstract : Case where
  name := "defaultSuperCallAbstract"
  mima := some "DirectAbstractMethodProblem"
  v0 := [(.I, { header := iface, methods := [(.m, .v, inst)] })]
  v1 := [(.I, { header := iface, methods := [(.m, .v, abs)] })]
  client := [(.X, { header := { ifaces := [.I] }, methods := [(.m, .v, inst)] })]
  prog := { sites := [within .X (invokespecial .I .m .v true)] }

def staticIfaceMethodRemoved : Case where
  name := "staticIfaceMethodRemoved"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.I, { header := iface, methods := [(.m, .v, { isStatic := true })] })]
  v1 := [(.I, { header := iface })]
  prog := { sites := [invokestaticIface .I .m .v] }

/-- A static method moves from a class to an interface it implements: interface statics are not
inherited. -/
def staticMovedToIface : Case where
  name := "staticMovedToIface"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.A, { methods := [(.m, .v, { isStatic := true })] })]
  v1 := [(.I, { header := iface, methods := [(.m, .v, { isStatic := true })] }),
         (.A, { header := { ifaces := [.I] } })]
  prog := { sites := [invokestatic .A .m .v] }

def defaultBecomesStatic : Case where
  name := "defaultBecomesStatic"
  mima := some "VirtualStaticMemberProblem"
  v0 := [(.I, { header := iface, methods := [(.m, .v, inst)] })]
  v1 := [(.I, { header := iface, methods := [(.m, .v, { isStatic := true })] })]
  client := [(.X, { header := { ifaces := [.I] } })]
  prog := { sites := [invokeinterface .I .m .v .X] }

def defaultBecomesPrivate : Case where
  name := "defaultBecomesPrivate"
  mima := some "DirectMissingMethodProblem"
  v0 := [(.I, { header := iface, methods := [(.m, .v, inst)] })]
  v1 := [(.I, { header := iface, methods := [(.m, .v, { access := .priv })] })]
  client := [(.X, { header := { ifaces := [.I] } })]
  prog := { sites := [invokeinterface .I .m .v .X] }

def fld : FieldInfo := {}
def sfld : FieldInfo := { isStatic := true }

def fieldRemoved : Case where
  name := "fieldRemoved"
  mima := some "MissingFieldProblem"
  v0 := [(.A, { fields := [(.m, .s, fld)] })]
  v1 := [(.A, {})]
  prog := { sites := [getfield .A .m .s .A] }

def fieldBecomesStatic : Case where
  name := "fieldBecomesStatic"
  mima := some "VirtualStaticMemberProblem"
  v0 := [(.A, { fields := [(.m, .s, fld)] })]
  v1 := [(.A, { fields := [(.m, .s, sfld)] })]
  prog := { sites := [getfield .A .m .s .A] }

def fieldBecomesFinal : Case where
  name := "fieldBecomesFinal"
  mima := none
  v0 := [(.A, { fields := [(.m, .s, fld)] })]
  v1 := [(.A, { fields := [(.m, .s, { isFinal := true })] })]
  prog := { sites := [putfield .A .m .s .A] }

def fieldBecomesPrivate : Case where
  name := "fieldBecomesPrivate"
  mima := some "MissingFieldProblem"
  v0 := [(.A, { fields := [(.m, .s, fld)] })]
  v1 := [(.A, { fields := [(.m, .s, { access := .priv })] })]
  prog := { sites := [getfield .A .m .s .A] }

/-- A subclass gains a field of the same name: fields do not override, and the client's `B.m` now
resolves to `B`'s. -/
def fieldShadowed : Case where
  name := "fieldShadowed"
  mima := none
  v0 := [(.A, { fields := [(.m, .s, fld)] }), (.B, { header := { super := some .A } })]
  v1 := [(.A, { fields := [(.m, .s, fld)] }),
         (.B, { header := { super := some .A }, fields := [(.m, .s, fld)] })]
  prog := { sites := [getfield .B .m .s .B] }

/-- An interface of `B` gains a static field: field resolution searches superinterfaces before the
superclass. A client writing `B.m` breaks (`Jvm.Clients`): interface fields are final. -/
def fieldIfaceBeforeSuper : Case where
  name := "fieldIfaceBeforeSuper"
  mima := none
  v0 := [(.A, { fields := [(.m, .s, sfld)] }), (.I, { header := iface }),
         (.B, { header := { super := some .A, ifaces := [.I] } })]
  v1 := [(.A, { fields := [(.m, .s, sfld)] }),
         (.I, { header := iface, fields := [(.m, .s, { isStatic := true, isFinal := true })] }),
         (.B, { header := { super := some .A, ifaces := [.I] } })]
  prog := { sites := [getstatic .B .m .s] }

def putstaticBecomesFinal : Case where
  name := "putstaticBecomesFinal"
  mima := none
  v0 := [(.A, { fields := [(.m, .s, sfld)] })]
  v1 := [(.A, { fields := [(.m, .s, { isStatic := true, isFinal := true })] })]
  prog := { sites := [putstatic .A .m .s] }

def j3 : List Case :=
  [methodBecomesPrivate, methodBecomesPackagePrivate, classBecomesPackagePrivate,
   methodBecomesProtected, methodBecomesProtectedSub, methodBecomesProtectedOther,
   overrideCutByPackage, overrideBecomesPrivate, superCallPulledUp, superCallRemoved,
   superCallAbstract, defaultSuperCallAbstract, staticIfaceMethodRemoved, staticMovedToIface,
   defaultBecomesStatic, defaultBecomesPrivate, fieldRemoved, fieldBecomesStatic,
   fieldBecomesFinal, fieldBecomesPrivate, fieldShadowed, fieldIfaceBeforeSuper,
   putstaticBecomesFinal]

def all : List Case :=
  [methodRemoved, resultTypeChanged, classBecomesInterface, becomesStatic, becomesAbstract,
   becomesFinal, methodBecomesFinal, superclassRemoved, defaultRemoved, defaultConflict,
   overrideAdded, pulledUp]

example : classBecomesInterface.before = .ok [.A] := by decide
example : methodRemoved.before = .ok [.A] ∧ methodRemoved.after = .error .noSuchMethod := by
  decide
example : resultTypeChanged.after = .error .noSuchMethod := by decide
example : classBecomesInterface.after = .error .incompatibleClassChange := by decide
example : becomesStatic.after = .error .incompatibleClassChange := by decide
example : becomesAbstract.after = .error .instantiation := by decide
example : becomesFinal.before = .ok [] ∧ becomesFinal.after = .error .finalSuper := by
  decide
example : methodBecomesFinal.after = .error .finalOverride := by decide
example : superclassRemoved.after = .error .noSuchMethod := by decide
example : defaultRemoved.before = .ok [.I] ∧ defaultRemoved.after = .error .abstractMethod := by
  decide
example : defaultConflict.before = .ok [.I] ∧
    defaultConflict.after = .error .incompatibleClassChange := by decide
example : overrideAdded.before = .ok [.A] ∧ overrideAdded.after = .ok [.B] := by decide
example : pulledUp.before = .ok [.B] ∧ pulledUp.after = .ok [.A] := by decide

/-- The two compatible edits change the footprint: `link_congr` does not apply, and a Zinc-style
"same answers on the trace" test would flag them. -/
example : (footprint overrideAdded.w0 overrideAdded.prog).any
    (fun q => !agrees overrideAdded.w0 overrideAdded.w1 q) = true := by
  decide

example : methodBecomesPrivate.before = .ok [.A] ∧ methodBecomesPrivate.after = .error .illegalAccess := by decide
example : methodBecomesPackagePrivate.before = .ok [.A] ∧ methodBecomesPackagePrivate.after = .error .illegalAccess := by decide
example : classBecomesPackagePrivate.before = .ok [.A] ∧ classBecomesPackagePrivate.after = .error .illegalAccess := by decide
example : methodBecomesProtected.before = .ok [.A] ∧ methodBecomesProtected.after = .error .illegalAccess := by decide
example : methodBecomesProtectedSub.before = .ok [.A] ∧ methodBecomesProtectedSub.after = .ok [.A] := by decide
example : methodBecomesProtectedOther.before = .ok [.A] ∧ methodBecomesProtectedOther.after = .error .verify := by decide
example : overrideCutByPackage.before = .ok [.X] ∧ overrideCutByPackage.after = .ok [.A] := by decide
example : overrideBecomesPrivate.before = .ok [.B] ∧ overrideBecomesPrivate.after = .ok [.A] := by decide
example : superCallPulledUp.before = .ok [.B] ∧ superCallPulledUp.after = .ok [.A] := by decide
example : superCallRemoved.before = .ok [.B] ∧ superCallRemoved.after = .error .noSuchMethod := by decide
example : superCallAbstract.before = .ok [.B] ∧ superCallAbstract.after = .error .abstractMethod := by decide
example : defaultSuperCallAbstract.before = .ok [.I] ∧ defaultSuperCallAbstract.after = .error .abstractMethod := by decide
example : staticIfaceMethodRemoved.before = .ok [.I] ∧ staticIfaceMethodRemoved.after = .error .noSuchMethod := by decide
example : staticMovedToIface.before = .ok [.A] ∧ staticMovedToIface.after = .error .noSuchMethod := by decide
example : defaultBecomesStatic.before = .ok [.I] ∧ defaultBecomesStatic.after = .error .incompatibleClassChange := by decide
example : defaultBecomesPrivate.before = .ok [.I] ∧ defaultBecomesPrivate.after = .error .illegalAccess := by decide
example : fieldRemoved.before = .ok [.A] ∧ fieldRemoved.after = .error .noSuchField := by decide
example : fieldBecomesStatic.before = .ok [.A] ∧ fieldBecomesStatic.after = .error .incompatibleClassChange := by decide
example : fieldBecomesFinal.before = .ok [.A] ∧ fieldBecomesFinal.after = .error .illegalAccess := by decide
example : fieldBecomesPrivate.before = .ok [.A] ∧ fieldBecomesPrivate.after = .error .illegalAccess := by decide
example : fieldShadowed.before = .ok [.A] ∧ fieldShadowed.after = .ok [.B] := by decide
example : fieldIfaceBeforeSuper.before = .ok [.A] ∧ fieldIfaceBeforeSuper.after = .ok [.I] := by decide
example : putstaticBecomesFinal.before = .ok [.A] ∧ putstaticBecomesFinal.after = .error .illegalAccess := by decide

end Jvm.Catalogue
