import Zinc.Task
import Mathlib.Data.List.Dedup

/-!
# JVM linkage as a query tree

A client links against a class table: loading checks a class's supertypes, and each call site
resolves a symbolic reference (JVMS §5.4.3.3 for a class, §5.4.3.4 for an interface) and then
selects a method on the receiver's class (§5.4.6); fields resolve by §5.4.3.2, and access is
checked by §5.4.4 and the verifier's rules for receivers, `invokespecial` and protected members. The
model writes linking as a `Task` whose queries are the class table's entries: a class's header,
and whether it declares a method or field of a name and descriptor. So linking has a trace, the *linkage footprint*, and T1 applies to it
unchanged: a library edit that agrees with the old library on a client's footprint links that
client the same way (`link_congr`).

That is the bridge to Zinc. Zinc asks whether a source must be *recompiled*; binary
compatibility asks whether its old classfile still *links* (and selects the same methods) against
the new library. Both are questions about a task's trace against an edited environment.

The model is generic in class, method-name and descriptor types. Calibrated against HotSpot 21, 25
and 27 by `probes/jvm`. Not modelled: nestmates (private access is same-class only), method bodies
(a library method's own calls), signature-polymorphic methods, `Object`'s methods in interface
resolution, loader constraints, class initialisation, and transitive overriding through an
intermediate package-private method (§5.4.5's second case). Linking is lazy, as on the JVM: an error is raised by
the first site that hits it; a class is loaded, with its loading checks, when it is first referred
to, and each site is verified just before it runs (as if each site were its own method).
-/

namespace Jvm

variable {C N D : Type} [DecidableEq C] [DecidableEq N] [DecidableEq D]

/-- A member's access (JVMS §4.6, §5.4.4). -/
inductive Access | pub | prot | pkg | priv
  deriving DecidableEq, Repr

/-- `pkg` is the class's runtime package (0 is the unnamed one). A class's package is part of its
name, so it must not differ between the class tables a model compares. -/
structure Header (C : Type) where
  isInterface : Bool := false
  isAbstract : Bool := false
  isFinal : Bool := false
  super : Option C := none
  ifaces : List C := []
  isPublic : Bool := true
  pkg : ℕ := 0
  deriving DecidableEq, Repr

structure MethodInfo where
  isStatic : Bool := false
  isAbstract : Bool := false
  isFinal : Bool := false
  access : Access := .pub
  deriving DecidableEq, Repr

structure FieldInfo where
  isStatic : Bool := false
  isFinal : Bool := false
  access : Access := .pub
  deriving DecidableEq, Repr

structure Classfile (C N D : Type) where
  header : Header C := {}
  methods : List (N × D × MethodInfo) := []
  fields : List (N × D × FieldInfo) := []
  deriving Repr

/-- A class table: the library's classfiles and the client's. -/
abbrev World (C N D : Type) := C → Option (Classfile C N D)

inductive Q (C N D : Type)
  | header (c : C)
  | method (c : C) (n : N) (d : D)
  | declared (c : C)
  | field (c : C) (n : N) (d : D)
  deriving DecidableEq, Repr

def Ans {C N D : Type} : Q C N D → Type
  | .header _ => Option (Header C)
  | .method .. => Option MethodInfo
  | .declared _ => List (N × D × MethodInfo)
  | .field .. => Option FieldInfo

def answer (w : World C N D) : (q : Q C N D) → Ans q
  | .header c => (w c).map (·.header)
  | .method c n d => (w c).bind fun cf => (cf.methods.find? fun m => m.1 = n ∧ m.2.1 = d).map (·.2.2)
  | .declared c => ((w c).map (·.methods)).getD []
  | .field c n d => (w c).bind fun cf => (cf.fields.find? fun m => m.1 = n ∧ m.2.1 = d).map (·.2.2)

/-- Do two class tables give the same answer to `q`? -/
def agrees (w w' : World C N D) : Q C N D → Bool
  | .header c => decide ((w c).map (·.header) = (w' c).map (·.header))
  | .method c n d =>
    let f : Classfile C N D → Option MethodInfo :=
      fun cf => (cf.methods.find? fun m => m.1 = n ∧ m.2.1 = d).map (·.2.2)
    decide ((w c).bind f = (w' c).bind f)
  | .declared c => decide (((w c).map (·.methods)).getD [] = ((w' c).map (·.methods)).getD [])
  | .field c n d =>
    let f : Classfile C N D → Option FieldInfo :=
      fun cf => (cf.fields.find? fun m => m.1 = n ∧ m.2.1 = d).map (·.2.2)
    decide ((w c).bind f = (w' c).bind f)

theorem agrees_iff (w w' : World C N D) (q : Q C N D) :
    agrees w w' q = true ↔ answer w q = answer w' q := by
  cases q <;> simp only [agrees, answer, decide_eq_true_eq] <;> exact Iff.rfl

/-- The `LinkageError`s the model raises. `probes/jvm/Run.java` maps each to the JVM's class, calibrated on
HotSpot 21, 25 and 27: `finalSuper` and `finalOverride` are `IncompatibleClassChangeError`s. -/
inductive LinkError
  | noClassDef
  | incompatibleClassChange
  | noSuchMethod
  | abstractMethod
  | instantiation
  | finalSuper
  | finalOverride
  /-- A receiver not assignable to the site's owner, or a bad `invokespecial`: the verifier rejects
  the client. -/
  | verify
  /-- A class or member the site's class may not access (§5.4.4), or a write to a final field. -/
  | illegalAccess
  | noSuchField
  deriving DecidableEq, Repr

abbrev L (C N D : Type) := Zinc.Task (Q C N D) Ans

abbrev M (C N D : Type) := ExceptT LinkError (L C N D)

def askHeader (c : C) : M C N D (Option (Header C)) :=
  ExceptT.lift (Zinc.Task.ask (.header c) Zinc.Task.pure : L C N D (Option (Header C)))

def askMethod (c : C) (n : N) (d : D) : M C N D (Option MethodInfo) :=
  ExceptT.lift (Zinc.Task.ask (.method c n d) Zinc.Task.pure : L C N D (Option MethodInfo))

def askDeclared (c : C) : M C N D (List (N × D × MethodInfo)) :=
  ExceptT.lift (Zinc.Task.ask (.declared c) Zinc.Task.pure : L C N D (List (N × D × MethodInfo)))

def askField (c : C) (n : N) (d : D) : M C N D (Option FieldInfo) :=
  ExceptT.lift (Zinc.Task.ask (.field c n d) Zinc.Task.pure : L C N D (Option FieldInfo))

def hdr (c : C) : M C N D (Header C) := do
  match ← askHeader c with
  | some h => pure h
  | none => throw .noClassDef

/-- Bound on the depth of a hierarchy walk. -/
def depth : ℕ := 6

/-- The superinterfaces of `c`, through its superclasses and transitively; with repeats. -/
def ifacesOf : ℕ → C → M C N D (List C)
  | 0, _ => pure []
  | k + 1, c => do
    let h ← hdr c
    let up ← match h.super with
      | none => pure []
      | some s => ifacesOf k s
    let ii ← h.ifaces.mapM fun i => do
      let r ← ifacesOf k i
      pure (i :: r)
    pure (ii.flatten ++ up)

/-- `x` is `c` or a subclass of `c`, by superclasses. -/
def subclassOf (c : C) : ℕ → C → M C N D Bool
  | 0, _ => pure false
  | k + 1, x => do
    if x = c then return true
    match (← hdr x).super with
    | none => pure false
    | some s => subclassOf c k s

/-- Look a method up in `c` and its superclasses (resolution, §5.4.3.3 step 2, which finds static
and private methods too). -/
def chain (inst : Bool) (n : N) (d : D) : ℕ → C → M C N D (Option (C × MethodInfo))
  | 0, _ => pure none
  | k + 1, c => do
    let h ← hdr c
    match ← askMethod c n d with
    | some i =>
      if inst && i.isStatic then
        match h.super with
        | none => pure none
        | some s => chain inst n d k s
      else pure (some (c, i))
    | none =>
      match h.super with
      | none => pure none
      | some s => chain inst n d k s

/-- Does `(x, mi)` override `(a, ma)` (§5.4.5, without the transitive case)? Private and static
methods neither override nor are overridden; a package-private method only from its package. -/
def overrides (x : C) (mi : MethodInfo) (a : C) (ma : MethodInfo) : M C N D Bool := do
  if mi.isStatic || mi.access = .priv || ma.isStatic || ma.access = .priv then return false
  if ma.access = .pkg then return (← hdr x).pkg = (← hdr a).pkg
  pure true

/-- Selection's walk (§5.4.6 step 2): the first declaration in `c` or a superclass that overrides
the resolved method `(a, ma)`. -/
def chainOver (n : N) (d : D) (a : C) (ma : MethodInfo) :
    ℕ → C → M C N D (Option (C × MethodInfo))
  | 0, _ => pure none
  | k + 1, c => do
    let h ← hdr c
    let here ← match ← askMethod c n d with
      | some i => if c = a then pure (some (c, i))
                  else if ← overrides c i a ma then pure (some (c, i)) else pure none
      | none => pure none
    match here with
    | some r => pure (some r)
    | none =>
      match h.super with
      | none => pure none
      | some s => chainOver n d a ma k s

/-- Load a class, and first its superinterfaces and superclass (HotSpot's class file parser resolves
them in that order): each superinterface must be an interface, the superclass a non-final class,
both accessible from the class, and none of the class's instance methods may override a final one. The JVM loads a class when a
site, the verifier or a subclass first refers to it; the model loads it at each such reference,
which repeats queries but not answers. -/
def loadK : ℕ → C → M C N D Unit
  | 0, _ => pure ()
  | k + 1, x => do
    let h ← hdr x
    for i in h.ifaces do
      loadK k i
      if !(← hdr i).isInterface then throw .incompatibleClassChange
    match h.super with
    | none => pure ()
    | some s =>
      loadK k s
      let hs ← hdr s
      if hs.isInterface then throw .incompatibleClassChange
      if hs.isFinal then throw .finalSuper
      if !hs.isPublic && hs.pkg != h.pkg then throw .illegalAccess
      for i in h.ifaces do
        let hi ← hdr i
        if !hi.isPublic && hi.pkg != h.pkg then throw .illegalAccess
      for (n, d, mi) in ← askDeclared x do
        if let some (a, si) ← chain true n d depth s then
          if si.isFinal && (← overrides x mi a si) then throw .finalOverride

def load (x : C) : M C N D Unit := loadK depth x

/-- A class's header, after loading it. -/
def cls (c : C) : M C N D (Header C) := do
  load c
  hdr c

/-- The class whose code executes a site: `none` is a class of its own in the unnamed package. -/
abbrev Cur (C : Type) := Option C

def curPkg : Cur C → M C N D ℕ
  | none => pure 0
  | some x => do pure (← hdr x).pkg

/-- Resolve a class reference from `cur` (§5.4.3.1): load it, and check it is accessible. -/
def resolveCls (cur : Cur C) (c : C) : M C N D (Header C) := do
  let h ← cls c
  if !h.isPublic && h.pkg != (← curPkg cur) then throw .illegalAccess
  pure h

/-- Member access from `cur` to a member of `decl` (§5.4.4). Private access is same-class only:
nestmates are not modelled. -/
def accessible (cur : Cur C) (decl : C) (acc : Access) : M C N D Bool := do
  match acc with
  | .pub => pure true
  | .priv => pure (cur = some decl)
  | .pkg => pure ((← hdr decl).pkg = (← curPkg cur))
  | .prot =>
    if (← hdr decl).pkg = (← curPkg cur) then return true
    match cur with
    | none => pure false
    | some x => subclassOf decl depth x

/-- The maximally-specific superinterface methods of `c` for `n` and `d` (§5.4.3.3): instance
methods, not private, declared in a superinterface of `c` that no other such method's interface
extends. -/
def maxSpecific (c : C) (n : N) (d : D) : M C N D (List (C × MethodInfo)) := do
  let is ← ifacesOf depth c
  let cands ← is.dedup.filterMapM fun i => do
    let m ← askMethod i n d
    pure ((m.filter fun mi => !mi.isStatic && mi.access != .priv).map fun mi => (i, mi))
  cands.filterM fun p => do
    let below ← cands.anyM fun q => do
      if q.1 = p.1 then pure false
      else pure ((← ifacesOf depth q.1).contains p.1)
    pure !below

/-- Step 3 of §5.4.3.3 and §5.4.3.4: a unique non-abstract maximally-specific method, else any
superinterface method. -/
def fromIfaces (c : C) (n : N) (d : D) : M C N D (C × MethodInfo) := do
  let ms ← maxSpecific c n d
  match ms.filter fun p => !p.2.isAbstract with
  | [r] => pure r
  | _ =>
    match ms with
    | r :: _ => pure r
    | [] => throw .noSuchMethod

def checkAccess (cur : Cur C) (r : C × MethodInfo) : M C N D (C × MethodInfo) := do
  if !(← accessible cur r.1 r.2.access) then throw .illegalAccess
  pure r

/-- Method resolution against a class, §5.4.3.3. -/
def resolveClass (cur : Cur C) (c : C) (n : N) (d : D) : M C N D (C × MethodInfo) := do
  let h ← resolveCls cur c
  if h.isInterface then throw .incompatibleClassChange
  match ← chain false n d depth c with
  | some r => checkAccess cur r
  | none => checkAccess cur (← fromIfaces c n d)

/-- Interface method resolution, §5.4.3.4. -/
def resolveIface (cur : Cur C) (c : C) (n : N) (d : D) : M C N D (C × MethodInfo) := do
  let h ← resolveCls cur c
  if !h.isInterface then throw .incompatibleClassChange
  match ← askMethod c n d with
  | some i => checkAccess cur (c, i)
  | none => checkAccess cur (← fromIfaces c n d)

/-- Method selection on the receiver's class `r` for the resolved method `(a, ma)`, §5.4.6, with
`invokevirtual`'s and `invokeinterface`'s errors. A private resolved method is selected itself. -/
def select (r : C) (n : N) (d : D) (a : C) (ma : MethodInfo) : M C N D C := do
  if ma.access = .priv then return a
  match ← chainOver n d a ma depth r with
  | some (o, i) => if i.isAbstract then throw .abstractMethod else pure o
  | none =>
    let ms ← maxSpecific r n d
    match ms.filter fun p => !p.2.isAbstract with
    | [p] => pure p.1
    | [] => throw .abstractMethod
    | _ => throw .incompatibleClassChange

/-- Field resolution, §5.4.3.2: `c`, then its superinterfaces, then its superclass. -/
def lookupField (n : N) (d : D) : ℕ → C → M C N D (Option (C × FieldInfo))
  | 0, _ => pure none
  | k + 1, c => do
    if let some f ← askField c n d then return some (c, f)
    let h ← hdr c
    for i in h.ifaces do
      if let some r ← lookupField n d k i then return some r
    match h.super with
    | none => pure none
    | some s => lookupField n d k s

def resolveField (cur : Cur C) (c : C) (n : N) (d : D) : M C N D (C × FieldInfo) := do
  discard <| resolveCls cur c
  match ← lookupField n d depth c with
  | none => throw .noSuchField
  | some (a, f) =>
    if !(← accessible cur a f.access) then throw .illegalAccess
    pure (a, f)

/-- A call site, as javac emits it for `new R().m()` with the static receiver type `C` (an upcast
`C c = new R(); c.m()` when `R ≠ C`), or a `new C()`; field accesses likewise.
`invokespecial` is a `super` call (`iface` for `I.super.m()`) from the site's class, so it is wrapped in a
`within`. `within x s` runs `s` from a static method of the client's class `x`. -/
inductive Site (C N D : Type)
  | invokestatic (c : C) (n : N) (d : D)
  | invokevirtual (c : C) (n : N) (d : D) (recv : C)
  | invokeinterface (c : C) (n : N) (d : D) (recv : C)
  | new (c : C)
  /-- `invokestatic` of an interface method (an `InterfaceMethodref`). -/
  | invokestaticIface (c : C) (n : N) (d : D)
  | invokespecial (c : C) (n : N) (d : D) (iface : Bool)
  | getfield (c : C) (n : N) (d : D) (recv : C)
  | putfield (c : C) (n : N) (d : D) (recv : C)
  | getstatic (c : C) (n : N) (d : D)
  | putstatic (c : C) (n : N) (d : D)
  | within (x : C) (s : Site C N D)
  deriving DecidableEq, Repr

/-- The verifier's assignability of class type `r` to `c` (JVMS §4.10.1.2, as HotSpot checks it):
equal names pass without loading; otherwise `c` is loaded, an interface passes, and a class must be
a superclass of `r`. -/
def assignable (r c : C) : M C N D Unit := do
  if r = c then return
  if (← cls c).isInterface then return
  discard <| cls r
  if !(← subclassOf c depth r) then throw .verify

/-- `new c`: resolve it; it must be a concrete class. -/
def instantiate (cur : Cur C) (c : C) : M C N D Unit := do
  let h ← resolveCls cur c
  if h.isInterface || h.isAbstract then throw .instantiation

/-- The verifier's rule for `invokespecial` from `x` to `c` (HotSpot's `verify_invoke_instructions`):
`x` itself, its direct superclass or a direct superinterface pass by name; otherwise `x` must be
assignable to `c`, and `c` must not be an interface (an indirect superinterface). Calibrated on
HotSpot: what matters is whether `c` is an interface, not the constant's tag; an
`InterfaceMethodref` to a class passes here and fails in resolution. -/
def verifySpecial (x c : C) : M C N D Unit := do
  let h ← hdr x
  if c = x || h.super = some c || h.ifaces.contains c then return
  assignable x c
  if (← hdr c).isInterface then throw .verify

/-- The verifier's protected check (§4.10.1.8, HotSpot's `verify_protected_access`): from `x`, a
reference through a proper superclass `c` of `x` to a protected member declared in another package
needs a receiver `r` that is an `x`. `acc` looks the member up from `c`. -/
def verifyProtected (cur : Cur C) (c r : C) (acc : M C N D (Option (C × Access))) :
    M C N D Unit := do
  let some x := cur | return
  if c = x then return
  let some s := (← hdr x).super | return
  if !(← subclassOf c depth s) then return
  let some (a, .prot) ← acc | return
  if (← hdr a).pkg = (← hdr x).pkg then return
  if !(← subclassOf x depth r) then throw .verify

/-- Execute a site from `cur`; the result is the class whose method runs, whose field is accessed,
or that is instantiated. The verifier checks the receiver's upcast before the site runs; then the
receiver is instantiated, the member resolved and selected. -/
def runSiteK (cur : Cur C) : Site C N D → M C N D C
  | .invokestatic c n d => do
    let (o, i) ← resolveClass cur c n d
    if !i.isStatic then throw .incompatibleClassChange
    pure o
  | .invokestaticIface c n d => do
    let (o, i) ← resolveIface cur c n d
    if !i.isStatic then throw .incompatibleClassChange
    pure o
  | .invokevirtual c n d r => do
    assignable r c
    verifyProtected cur c r do
      pure ((← chain false n d depth c).map fun (a, i) => (a, i.access))
    instantiate cur r
    let (a, i) ← resolveClass cur c n d
    if i.isStatic then throw .incompatibleClassChange
    select r n d a i
  | .invokeinterface c n d r => do
    assignable r c
    instantiate cur r
    let (a, i) ← resolveIface cur c n d
    if i.isStatic then throw .incompatibleClassChange
    if !(← ifacesOf depth r).contains c then throw .incompatibleClassChange
    select r n d a i
  | .new c => do
    instantiate cur c
    pure c
  | .invokespecial c n d iface => do
    -- `this` is an instance of the site's class.
    let x ← match cur with
      | some x => pure x
      | none => throw .verify
    verifySpecial x c
    instantiate cur x
    let (a, i) ← if iface then resolveIface cur c n d else resolveClass cur c n d
    if i.isStatic then throw .incompatibleClassChange
    let hc ← hdr c
    let start ← if !hc.isInterface && c != x && (← subclassOf c depth x) then
        match (← hdr x).super with
        | some s => pure s
        | none => pure c
      else pure c
    match ← chain true n d depth start with
    | some (o, i) => if i.isAbstract then throw .abstractMethod else pure o
    | none =>
      let ms ← maxSpecific start n d
      match ms.filter fun p => !p.2.isAbstract with
      | [p] => pure p.1
      | [] => if i.isAbstract then throw .abstractMethod else pure a
      | _ => throw .incompatibleClassChange
  | .getfield c n d r => do
    assignable r c
    verifyProtected cur c r do
      pure ((← lookupField n d depth c).map fun (a, f) => (a, f.access))
    instantiate cur r
    let (a, f) ← resolveField cur c n d
    if f.isStatic then throw .incompatibleClassChange
    pure a
  | .putfield c n d r => do
    assignable r c
    verifyProtected cur c r do
      pure ((← lookupField n d depth c).map fun (a, f) => (a, f.access))
    instantiate cur r
    let (a, f) ← resolveField cur c n d
    if f.isStatic then throw .incompatibleClassChange
    if f.isFinal then throw .illegalAccess
    pure a
  | .getstatic c n d => do
    let (a, f) ← resolveField cur c n d
    if !f.isStatic then throw .incompatibleClassChange
    pure a
  | .putstatic c n d => do
    let (a, f) ← resolveField cur c n d
    if !f.isStatic then throw .incompatibleClassChange
    if f.isFinal then throw .illegalAccess
    pure a
  | .within x s => do
    discard <| resolveCls cur x
    runSiteK (some x) s

def runSite : Site C N D → M C N D C := runSiteK none

/-- A client: the classes it loads, then the sites it executes, in order. -/
structure Program (C N D : Type) where
  loads : List C := []
  sites : List (Site C N D) := []
  deriving Repr

def link (p : Program C N D) : M C N D (List C) := do
  for x in p.loads do load x
  p.sites.mapM runSite

/-- The outcome of linking `p` in `w`: the first error, or the class each site ran. -/
def outcome (w : World C N D) (p : Program C N D) : Except LinkError (List C) :=
  (link p).run.run (answer w)

/-- The linkage footprint: every entry of the class table linking `p` read. -/
def footprint (w : World C N D) (p : Program C N D) : List (Q C N D) :=
  (link p).run.trace (answer w)

/-- **T1 for linkage.** An edited class table that agrees with the old one on a client's footprint
links the client the same way. -/
theorem link_congr (w w' : World C N D) (p : Program C N D)
    (h : ∀ q ∈ footprint w p, answer w q = answer w' q) : outcome w p = outcome w' p :=
  Zinc.Task.run_congr _ _ _ h

/-- MiMa's question for one client: an edit is *linkage-compatible* for `p` if `p` still links
whenever it did. Agreement on the footprint is sufficient (`link_congr`), not necessary: adding a
method changes the answer to a query and leaves the client linking. -/
def Compatible (w₀ w₁ : World C N D) (p : Program C N D) : Prop :=
  (outcome w₀ p).toBool = true → (outcome w₁ p).toBool = true

theorem compatible_of_footprint (w₀ w₁ : World C N D) (p : Program C N D)
    (h : ∀ q ∈ footprint w₀ p, answer w₀ q = answer w₁ q) : Compatible w₀ w₁ p := by
  intro h0; rwa [← link_congr w₀ w₁ p h]

end Jvm
