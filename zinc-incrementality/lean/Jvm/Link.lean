import Zinc.Task
import Mathlib.Data.List.Dedup

/-!
# JVM linkage as a query tree

A client links against a class table: loading checks a class's supertypes, and each call site
resolves a symbolic reference (JVMS §5.4.3.3 for a class, §5.4.3.4 for an interface) and then
selects a method on the receiver's class (§5.4.6). The model writes linking as a `Task` whose
queries are the class table's entries: a class's header, and whether it declares a method of a
name and descriptor. So linking has a trace, the *linkage footprint*, and T1 applies to it
unchanged: a library edit that agrees with the old library on a client's footprint links that
client the same way (`link_congr`).

That is the bridge to Zinc. Zinc asks whether a source must be *recompiled*; binary
compatibility asks whether its old classfile still *links* (and selects the same methods) against
the new library. Both are questions about a task's trace against an edited environment.

The model is generic in class, method-name and descriptor types. Not modelled: access control,
private methods and `invokespecial`, fields, signature-polymorphic methods, `Object`'s methods in
interface resolution, static interface methods. Linking is lazy, as on the JVM: an error is raised by
the first site that hits it; a class is loaded, with its loading checks, when it is first referred
to, and each site is verified just before it runs (as if each site were its own method).
-/

namespace Jvm



variable {C N D : Type} [DecidableEq C] [DecidableEq N] [DecidableEq D]

structure Header (C : Type) where
  isInterface : Bool := false
  isAbstract : Bool := false
  isFinal : Bool := false
  super : Option C := none
  ifaces : List C := []
  deriving DecidableEq, Repr

structure MethodInfo where
  isStatic : Bool := false
  isAbstract : Bool := false
  isFinal : Bool := false
  deriving DecidableEq, Repr

structure Classfile (C N D : Type) where
  header : Header C := {}
  methods : List (N × D × MethodInfo) := []
  deriving Repr

/-- A class table: the library's classfiles and the client's. -/
abbrev World (C N D : Type) := C → Option (Classfile C N D)

inductive Q (C N D : Type)
  | header (c : C)
  | method (c : C) (n : N) (d : D)
  | declared (c : C)
  deriving DecidableEq, Repr

def Ans {C N D : Type} : Q C N D → Type
  | .header _ => Option (Header C)
  | .method .. => Option MethodInfo
  | .declared _ => List (N × D × MethodInfo)

def answer (w : World C N D) : (q : Q C N D) → Ans q
  | .header c => (w c).map (·.header)
  | .method c n d => (w c).bind fun cf => (cf.methods.find? fun m => m.1 = n ∧ m.2.1 = d).map (·.2.2)
  | .declared c => ((w c).map (·.methods)).getD []

/-- Do two class tables give the same answer to `q`? -/
def agrees (w w' : World C N D) : Q C N D → Bool
  | .header c => decide ((w c).map (·.header) = (w' c).map (·.header))
  | .method c n d =>
    let f : Classfile C N D → Option MethodInfo :=
      fun cf => (cf.methods.find? fun m => m.1 = n ∧ m.2.1 = d).map (·.2.2)
    decide ((w c).bind f = (w' c).bind f)
  | .declared c => decide (((w c).map (·.methods)).getD [] = ((w' c).map (·.methods)).getD [])

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
  /-- A receiver not assignable to the site's owner: the verifier rejects the client. -/
  | verify
  deriving DecidableEq, Repr

abbrev L (C N D : Type) := Zinc.Task (Q C N D) Ans

abbrev M (C N D : Type) := ExceptT LinkError (L C N D)

def askHeader (c : C) : M C N D (Option (Header C)) :=
  ExceptT.lift (Zinc.Task.ask (.header c) Zinc.Task.pure : L C N D (Option (Header C)))

def askMethod (c : C) (n : N) (d : D) : M C N D (Option MethodInfo) :=
  ExceptT.lift (Zinc.Task.ask (.method c n d) Zinc.Task.pure : L C N D (Option MethodInfo))

def askDeclared (c : C) : M C N D (List (N × D × MethodInfo)) :=
  ExceptT.lift (Zinc.Task.ask (.declared c) Zinc.Task.pure : L C N D (List (N × D × MethodInfo)))

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

/-- Look a method up in `c` and its superclasses. With `inst`, static methods are skipped (they do
not override, §5.4.6). -/
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

/-- Load a class, and first its superinterfaces and superclass (HotSpot's class file parser resolves
them in that order): each superinterface must be an interface, the superclass a non-final class,
and none of the class's instance methods may override a final one. The JVM loads a class when a
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
      for (n, d, mi) in ← askDeclared x do
        if !mi.isStatic then
          if let some (_, si) ← chain true n d depth s then
            if si.isFinal then throw .finalOverride

def load (x : C) : M C N D Unit := loadK depth x

/-- A class's header, after loading it. -/
def cls (c : C) : M C N D (Header C) := do
  load c
  hdr c

/-- The maximally-specific superinterface methods of `c` for `n` and `d` (§5.4.3.3): instance
methods declared in a superinterface of `c` that no other such method's interface extends. -/
def maxSpecific (c : C) (n : N) (d : D) : M C N D (List (C × MethodInfo)) := do
  let is ← ifacesOf depth c
  let cands ← is.dedup.filterMapM fun i => do
    let m ← askMethod i n d
    pure ((m.filter fun mi => !mi.isStatic).map fun mi => (i, mi))
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

/-- Method resolution against a class, §5.4.3.3. -/
def resolveClass (c : C) (n : N) (d : D) : M C N D (C × MethodInfo) := do
  let h ← cls c
  if h.isInterface then throw .incompatibleClassChange
  match ← chain false n d depth c with
  | some r => pure r
  | none => fromIfaces c n d

/-- Interface method resolution, §5.4.3.4. -/
def resolveIface (c : C) (n : N) (d : D) : M C N D (C × MethodInfo) := do
  let h ← cls c
  if !h.isInterface then throw .incompatibleClassChange
  match ← askMethod c n d with
  | some i => pure (c, i)
  | none => fromIfaces c n d

/-- Method selection on the receiver's class `r`, §5.4.6, with `invokevirtual`'s and
`invokeinterface`'s errors. -/
def select (r : C) (n : N) (d : D) : M C N D C := do
  match ← chain true n d depth r with
  | some (o, i) => if i.isAbstract then throw .abstractMethod else pure o
  | none =>
    let ms ← maxSpecific r n d
    match ms.filter fun p => !p.2.isAbstract with
    | [p] => pure p.1
    | [] => throw .abstractMethod
    | _ => throw .incompatibleClassChange

/-- A call site, as javac emits it for `new R().m()` with the static receiver type `C` (an upcast
`C c = new R(); c.m()` when `R ≠ C`), or a `new C()`. -/
inductive Site (C N D : Type)
  | invokestatic (c : C) (n : N) (d : D)
  | invokevirtual (c : C) (n : N) (d : D) (recv : C)
  | invokeinterface (c : C) (n : N) (d : D) (recv : C)
  | new (c : C)
  deriving DecidableEq, Repr

/-- The verifier's assignability of class type `r` to `c` (JVMS §4.10.1.2, as HotSpot checks it):
equal names pass without loading; otherwise `c` is loaded, an interface passes, and a class must be
a superclass of `r`. -/
def assignable (r c : C) : M C N D Unit := do
  if r = c then return
  if (← cls c).isInterface then return
  discard <| cls r
  let rec up : ℕ → C → M C N D Bool
    | 0, _ => pure false
    | k + 1, x => do
      if x = c then return true
      match (← hdr x).super with
      | none => pure false
      | some s => up k s
  if !(← up depth r) then throw .verify

/-- `new c`: load it; it must be a concrete class. -/
def instantiate (c : C) : M C N D Unit := do
  let h ← cls c
  if h.isInterface || h.isAbstract then throw .instantiation

/-- Execute a site; the result is the class whose method runs (or that is instantiated). The
verifier checks the receiver's upcast before the site runs; then the receiver is instantiated, the
method resolved and selected. -/
def runSite : Site C N D → M C N D C
  | .invokestatic c n d => do
    let (o, i) ← resolveClass c n d
    if !i.isStatic then throw .incompatibleClassChange
    pure o
  | .invokevirtual c n d r => do
    assignable r c
    instantiate r
    let (_, i) ← resolveClass c n d
    if i.isStatic then throw .incompatibleClassChange
    select r n d
  | .invokeinterface c n d r => do
    assignable r c
    instantiate r
    let (_, i) ← resolveIface c n d
    if i.isStatic then throw .incompatibleClassChange
    if !(← ifacesOf depth r).contains c then throw .incompatibleClassChange
    select r n d
  | .new c => do
    instantiate c
    pure c

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
