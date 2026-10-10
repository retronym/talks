import Jvm.Link

/-!
# A catalogue of library edits, linked

Each case is a library edit (`v0` → `v1`) and a client compiled against `v0`. The client's
classes and sites are fixed; only the library's classfiles change. Each case states the outcome
before and after, by evaluation, and names the MiMa problem that reports it where there is one.
`lake exe jvmcases` dumps the cases; `probes/jvm` renders them to classfiles and checks the outcomes on
HotSpot.

Classes: `A`, `B` (library classes), `I`, `J` (library interfaces), `X` (the client's class).
-/

namespace Jvm.Catalogue

inductive C | A | B | I | J | X
  deriving DecidableEq, Repr

inductive N | m
  deriving DecidableEq, Repr

/-- `v` is `()V`, `i` is `()I`. -/
inductive D | v | i
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

def classBecomesInterface : Case where
  name := "classBecomesInterface"
  mima := some "IncompatibleTemplateDefProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := { isInterface := true }, methods := [(.m, .v, inst)] }),
         (.B, { header := { super := none, ifaces := [.A] } })]
  prog := { sites := [invokevirtual .A .m .v .A] }

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
  mima := some "ReversedMissingMethodProblem"
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

def all : List Case :=
  [methodRemoved, resultTypeChanged, classBecomesInterface, becomesStatic, becomesAbstract,
   becomesFinal, methodBecomesFinal, superclassRemoved, defaultRemoved, defaultConflict,
   overrideAdded, pulledUp]

example : methodRemoved.before = .ok [.A] ∧ methodRemoved.after = .error .noSuchMethod := by
  native_decide
example : resultTypeChanged.after = .error .noSuchMethod := by native_decide
example : classBecomesInterface.after = .error .incompatibleClassChange := by native_decide
example : becomesStatic.after = .error .incompatibleClassChange := by native_decide
example : becomesAbstract.after = .error .instantiation := by native_decide
example : becomesFinal.before = .ok [] ∧ becomesFinal.after = .error .finalSuper := by
  native_decide
example : methodBecomesFinal.after = .error .finalOverride := by native_decide
example : superclassRemoved.after = .error .noSuchMethod := by native_decide
example : defaultRemoved.before = .ok [.I] ∧ defaultRemoved.after = .error .abstractMethod := by
  native_decide
example : defaultConflict.before = .ok [.I] ∧
    defaultConflict.after = .error .incompatibleClassChange := by native_decide
example : overrideAdded.before = .ok [.A] ∧ overrideAdded.after = .ok [.B] := by native_decide
example : pulledUp.before = .ok [.B] ∧ pulledUp.after = .ok [.A] := by native_decide

/-- The two compatible edits change the footprint: `link_congr` does not apply, and a Zinc-style
"same answers on the trace" test would flag them. -/
example : (footprint overrideAdded.w0 overrideAdded.prog).any
    (fun q => !agrees overrideAdded.w0 overrideAdded.w1 q) = true := by
  native_decide

end Jvm.Catalogue
