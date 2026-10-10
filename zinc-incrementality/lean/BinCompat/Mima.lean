import Jvm.Catalogue

/-!
# MiMa's checks, as a function of the library's classfiles

A model of `mima-core` 1.2.1's `Analyzer` for the classfiles the `Jvm` catalogue universe can
express (Java classfiles: no pickles, TASTy, generic signatures or mixin forwarders). It reads the
old and new library tables only, never a client, and reports problems by MiMa's class names.
Calibrated against MiMa itself by `probes/mima` (the table in ROADMAP §B).

What MiMa reads, per class `c` that is public in the old library:

* the class's own facts: interface or class, public, abstract, final, its superclasses and all
  its superinterfaces (`TemplateChecker`, first problem only);
* each public field of `c`, looked up by name in `c` and its superclasses, never its interfaces
  (`FieldChecker`);
* each public method of `c`, looked up by name in `c`, its superclasses and (for abstract methods,
  or default methods of a class) its superinterfaces (`MethodChecker.checkExisting`);
* each abstract method of the new `c`, and each abstract method of a supertype the new `c` gained
  (`MethodChecker.checkNew`).

The class file parser drops private methods and fields, so no lookup sees them; a protected member
is never checked.
-/

namespace BinCompat

open Jvm Jvm.Catalogue

inductive Problem
  | missingClass
  | incompatibleTemplateDef
  | inaccessibleClass
  | abstractClass
  | finalClass
  | missingTypes
  | missingField
  | inaccessibleField
  | incompatibleFieldType
  | staticVirtualMember
  | virtualStaticMember
  | directMissingMethod
  | incompatibleResultType
  | inaccessibleMethod
  | finalMethod
  | directAbstractMethod
  | reversedMissingMethod
  | reversedAbstractMethod
  | inheritedNewAbstractMethod
  deriving DecidableEq, Repr

/-- MiMa's class name for a problem. -/
def Problem.name : Problem → String
  | .missingClass => "MissingClassProblem"
  | .incompatibleTemplateDef => "IncompatibleTemplateDefProblem"
  | .inaccessibleClass => "InaccessibleClassProblem"
  | .abstractClass => "AbstractClassProblem"
  | .finalClass => "FinalClassProblem"
  | .missingTypes => "MissingTypesProblem"
  | .missingField => "MissingFieldProblem"
  | .inaccessibleField => "InaccessibleFieldProblem"
  | .incompatibleFieldType => "IncompatibleFieldTypeProblem"
  | .staticVirtualMember => "StaticVirtualMemberProblem"
  | .virtualStaticMember => "VirtualStaticMemberProblem"
  | .directMissingMethod => "DirectMissingMethodProblem"
  | .incompatibleResultType => "IncompatibleResultTypeProblem"
  | .inaccessibleMethod => "InaccessibleMethodProblem"
  | .finalMethod => "FinalMethodProblem"
  | .directAbstractMethod => "DirectAbstractMethodProblem"
  | .reversedMissingMethod => "ReversedMissingMethodProblem"
  | .reversedAbstractMethod => "ReversedAbstractMethodProblem"
  | .inheritedNewAbstractMethod => "InheritedNewAbstractMethodProblem"

/-- A library: its class table. -/
abbrev Lib := List (C × Classfile C N D)

section
variable (l : Lib)

def get (c : C) : Option (Classfile C N D) := (l.find? (·.1 = c)).map (·.2)

def fuel : ℕ := 6

/-- The superclass chain of `c`, nearest first, without `Object`. -/
def supers : ℕ → C → List C
  | 0, _ => []
  | k + 1, c => match (get l c).bind (·.header.super) with
    | some s => s :: supers k s
    | none => []

/-- All superinterfaces of `c`: its superclass's, its own, and theirs (`ClassInfo.allInterfaces`). -/
def allIfaces : ℕ → C → List C
  | 0, _ => []
  | k + 1, c =>
    let h := (get l c).map (·.header)
    let up := match h.bind (·.super) with
      | some s => allIfaces k s
      | none => []
    let is := (h.map (·.ifaces)).getD []
    up ++ is ++ is.flatMap (allIfaces k)

/-- The methods MiMa sees in `c`: not private. -/
def meths (c : C) : List (N × D × MethodInfo) :=
  (((get l c).map (·.methods)).getD []).filter (·.2.2.access != .priv)

def flds (c : C) : List (N × D × FieldInfo) :=
  (((get l c).map (·.fields)).getD []).filter (·.2.2.access != .priv)

def named (c : C) (n : N) : List (C × D × MethodInfo) :=
  ((meths l c).filter (·.1 = n)).map fun m => (c, m.2.1, m.2.2)

def lookupClassMethods (c : C) (n : N) (static : Bool) : List (C × D × MethodInfo) :=
  if static then named l c n else (c :: supers l fuel c).flatMap fun x => named l x n

def lookupIfaceMethods (c : C) (n : N) (static : Bool) : List (C × D × MethodInfo) :=
  if static then [] else (allIfaces l fuel c).flatMap fun x => named l x n

def lookupMethods (c : C) (n : N) (static : Bool) : List (C × D × MethodInfo) :=
  lookupClassMethods l c n static ++ lookupIfaceMethods l c n static

def lookupConcreteIfaceMethods (c : C) (n : N) (static : Bool) : List (C × D × MethodInfo) :=
  (lookupIfaceMethods l c n static).filter fun m => !m.2.2.isAbstract

def lookupClassFields (c : C) (n : N) : List (C × D × FieldInfo) :=
  (c :: supers l fuel c).flatMap fun x =>
    ((flds l x).filter (·.1 = n)).map fun f => (x, f.2.1, f.2.2)

def ancestors (c : C) : List C := supers l fuel c ++ allIfaces l fuel c

end

/-- `TemplateChecker.check`: the first problem only. -/
def template (o n : Lib) (c : C) (ho hn : Header C) : Option Problem :=
  if ho.isInterface != hn.isInterface then some .incompatibleTemplateDef
  else if !hn.isPublic && ho.isPublic then some .inaccessibleClass
  else if !(ho.isAbstract || ho.isInterface) && (hn.isAbstract || hn.isInterface) then
    some .abstractClass
  else if !ho.isFinal && hn.isFinal then some .finalClass
  else if (supers o fuel c).any (fun s => !(supers n fuel c).contains s) then some .missingTypes
  else if (allIfaces o fuel c).any (fun s => !(allIfaces n fuel c).contains s) then some .missingTypes
  else none

def lessVisible (n o : Access) : Bool :=
  (n != .pub && o == .pub) || (n == .priv && o == .prot)

/-- MiMa's keys: what it compares, per class public in the old library. -/
inductive Key
  /-- The class's own facts and its supertypes (`TemplateChecker`). -/
  | template (c : C)
  /-- A public field declared in `c`, looked up by name from `c` (`FieldChecker`). -/
  | field (c : C) (n : N) (d : D)
  /-- A public method declared in `c`, looked up by name from `c` (`checkExisting`). -/
  | method (c : C) (n : N) (d : D)
  /-- The abstract methods of the new `c` and of the supertypes it gained (`checkNew`). -/
  | newMethods (c : C)
  deriving DecidableEq, Repr

def keys (o : Lib) : List Key :=
  o.flatMap fun (c, cf) =>
    if !cf.header.isPublic then []
    else [.template c] ++
      ((flds o c).filter (·.2.2.access == .pub)).map (fun f => .field c f.1 f.2.1) ++
      ((meths o c).filter (·.2.2.access == .pub)).map (fun m => .method c m.1 m.2.1) ++
      [.newMethods c]

def fieldCheck (n : Lib) (c : C) (fn : N) (fd : D) (fi : FieldInfo) : Option Problem :=
  match lookupClassFields n c fn with
  | [] => some .missingField
  | (_, d', fi') :: _ =>
    if fi'.access != .pub then some .inaccessibleField
    else if d' != fd then some .incompatibleFieldType
    else if fi.isStatic && !fi'.isStatic then some .staticVirtualMember
    else if !fi.isStatic && fi'.isStatic then some .virtualStaticMember
    else none

def methodCheck (o n : Lib) (c : C) (ho hn : Header C) (mn : N) (md : D) (mi : MethodInfo) :
    Option Problem :=
  let lookup (l : Lib) : List (C × D × MethodInfo) :=
    if !hn.isInterface then
      if mi.isAbstract then lookupMethods l c mn mi.isStatic
      else lookupClassMethods l c mn mi.isStatic ++ lookupConcreteIfaceMethods l c mn mi.isStatic
    else lookupMethods l c mn mi.isStatic
  let news := lookup n
  match news.find? (·.2.1 = md) with
  | some (_, _, mi') =>
    if lessVisible mi'.access mi.access then some .inaccessibleMethod
    else if !mi.isFinal && mi'.isFinal && !ho.isFinal then some .finalMethod
    else if !mi.isAbstract && mi'.isAbstract then some .directAbstractMethod
    else if mi.isStatic && !mi'.isStatic then some .staticVirtualMember
    else if !mi.isStatic && mi'.isStatic then some .virtualStaticMember
    else none
  | none =>
    let olds := (lookup o).map (·.2.1)
    if news.all (fun m => olds.contains m.2.1) then some .directMissingMethod
    else some .incompatibleResultType

def newMethodProblems (o n : Lib) (c : C) (hn : Header C) : List Problem :=
  let deferred := (meths n c).filterMap fun (mn, md, mi) =>
    if !mi.isAbstract then none
    else match (lookupMethods o c mn false).find? (·.2.1 = md) with
      | none => some .reversedMissingMethod
      | some (_, _, mo) => if !hn.isInterface && !mo.isAbstract then some .reversedAbstractMethod else none
  let gained := (ancestors n c).dedup.filter fun t => !(ancestors o c).contains t
  let inherited := gained.flatMap fun t =>
    (meths n t).filterMap fun (mn, _, mi) =>
      if !mi.isAbstract then none
      else if (lookupMethods o c mn false).any (·.1 != t) then none
      else if (lookupMethods n c mn false).any (fun m => m.1 != t && !m.2.2.isAbstract) then none
      else some .inheritedNewAbstractMethod
  deferred ++ inherited

/-- The headers of `c` in both libraries, unless MiMa stops at `c`: missing in the new one, or
interface ↔ class (`Analyzer.analyze` checks nothing further then). -/
def bothChecked (o n : Lib) (c : C) : Option (Header C × Header C) :=
  match get o c, get n c with
  | some co, some cn =>
    if template o n c co.header cn.header = some .incompatibleTemplateDef then none
    else some (co.header, cn.header)
  | _, _ => none

/-- What MiMa reports for one key. -/
def check (o n : Lib) : Key → List Problem
  | .template c =>
    match get o c, get n c with
    | some co, some cn => (template o n c co.header cn.header).toList
    | some _, none => [.missingClass]
    | none, _ => []
  | .field c fn fd =>
    match bothChecked o n c, (flds o c).find? (fun f => f.1 = fn ∧ f.2.1 = fd) with
    | some _, some (_, _, fi) => (fieldCheck n c fn fd fi).toList
    | _, _ => []
  | .method c mn md =>
    match bothChecked o n c, (meths o c).find? (fun m => m.1 = mn ∧ m.2.1 = md) with
    | some (ho, hn), some (_, _, mi) => (methodCheck o n c ho hn mn md mi).toList
    | _, _ => []
  | .newMethods c =>
    match bothChecked o n c with
    | some (_, hn) => newMethodProblems o n c hn
    | none => []

/-- MiMa's problems for a library edit `o` → `n`: every key's. -/
def mima (o n : Lib) : List Problem := (keys o).flatMap (check o n)

end BinCompat
