import Zinc.Task
import Jvm.Link
import Java.Syntax

/-!
# Lowering a Java subset to classfiles, as a `Task`

Lowering a compilation unit reads other types' interfaces (`Q.decl`), which is what javac reads
from their classfiles: a supertype's methods for bridges, an enum's or record's shape, the values
of other types' constants for folding. So a unit's lowering has a trace, and T1 (`lower_congr`)
says an environment that agrees on it gives the same classfiles. A constant read is part of the
trace: a client's classfile changes with the *value* of a constant it uses (JLS §13.4.9).

The output is a `Jvm.Classfile` (`ClassOut.toJvm`) plus what `Jvm` does not model: field
`ConstantValue`s, `ACC_BRIDGE`/`ACC_SYNTHETIC`/`ACC_ENUM`, `PermittedSubclasses`, the `Record`
attribute, and the `getstatic`/invoke instructions of the bodies the model knows (synthesized
methods, constructors, and user bodies, which return an expression over fields). Instructions on
`java/` classes are left out, as the probe leaves them out.
-/

namespace Java

inductive Q | decl (n : String)
  deriving DecidableEq, Repr

def Ans : Q → Type
  | .decl _ => Option Decl

def Program.env (p : Program) : (q : Q) → Ans q
  | .decl n => p.find n

abbrev M := ExceptT String (Zinc.Task Q Ans)

def askDecl (n : String) : M (Option Decl) :=
  ExceptT.lift (Zinc.Task.ask (Q.decl n) Zinc.Task.pure : Zinc.Task Q Ans (Option Decl))

def need (n : String) : M Decl := do
  match ← askDecl n with
  | some d => pure d
  | none => throw s!"not found: {n}"

def fuel : ℕ := 6

/-! ## Constants (JLS §15.29) -/

inductive CVal | int (n : Int) | str (s : String)
  deriving DecidableEq, Repr

def CVal.show : CVal → String
  | .int n => s!"int {n}"
  | .str s => s!"String {s}"

def CVal.asStr : CVal → String
  | .int n => toString n
  | .str s => s

/-- A constant variable: `static final` (or an interface field), of type `int` or `String`, with a
constant initialiser. -/
def isConstVar (d : Decl) (f : Field) : Bool :=
  (f.final || d.kind == .iface) && (f.ty == .int || f.ty == .str) && f.init.isSome

/-- The value of a constant expression, reading other types' constants; `none` if it is not one. -/
def eval : ℕ → Expr → M (Option CVal)
  | 0, _ => pure none
  | _ + 1, .int n => pure (some (.int n))
  | _ + 1, .str s => pure (some (.str s))
  | _ + 1, .call => pure none
  | k + 1, .field o n => do
    let d ← need o
    match d.fields.find? (·.name == n) with
    | some f => match f.init with
      | some e => if isConstVar d f then eval k e else pure none
      | none => pure none
    | none => pure none
  | k + 1, .add a b => do
    match ← eval k a, ← eval k b with
    | some (.int x), some (.int y) => pure (some (.int (x + y)))
    | some x, some y => pure (some (.str (x.asStr ++ y.asStr)))
    | _, _ => pure none
  | k + 1, .shl a b => do
    match ← eval k a, ← eval k b with
    | some (.int x), some (.int y) => pure (some (.int (x * 2 ^ y.toNat)))
    | _, _ => pure none

/-! ## Erasure -/

def jname (n : String) : String := s!"L{n};"

def erase : Ty → String
  | .int => "I"
  | .bool => "Z"
  | .void => "V"
  | .str => "Ljava/lang/String;"
  | .obj | .tp => "Ljava/lang/Object;"
  | .ref n => jname n

def descOf (ps : List Ty) (r : Ty) : String :=
  s!"({String.join (ps.map erase)}){erase r}"

def Meth.desc (m : Meth) : String := descOf m.params m.res

/-! ## Output -/

structure Insn where
  op : String
  owner : String
  name : String
  desc : String
  deriving DecidableEq, Repr

inductive Acc | pub | priv | pkg
  deriving DecidableEq, Repr

structure MOut where
  name : String
  desc : String
  acc : Acc := .pub
  static : Bool := false
  abs : Bool := false
  final : Bool := false
  bridge : Bool := false
  synthetic : Bool := false
  /-- The `getstatic`s and invokes of the body, on classes outside `java/`. -/
  calls : List Insn := []
  /-- The `int` and `String` constants the body pushes (`iconst`, `bipush`, `sipush`, `ldc`), in
  order: where a client's copy of another type's constant shows up (JLS §13.1). -/
  pushes : List CVal := []
  deriving DecidableEq, Repr

structure FOut where
  name : String
  desc : String
  acc : Acc := .pub
  static : Bool := false
  final : Bool := false
  synthetic : Bool := false
  enum : Bool := false
  const : Option CVal := none
  deriving DecidableEq, Repr

structure ClassOut where
  name : String
  pub : Bool := true
  itf : Bool := false
  abs : Bool := false
  final : Bool := false
  enum : Bool := false
  super : String := "java/lang/Object"
  ifaces : List String := []
  methods : List MOut := []
  fields : List FOut := []
  permitted : List String := []
  /-- A record's components. -/
  record : Option (List (String × String)) := none
  deriving DecidableEq, Repr

/-- The class's linkage view. JDK supertypes (`Object`, `Enum`, `Record`) are outside the class
table, so a class extending one is a root. -/
def ClassOut.toJvm (c : ClassOut) : Jvm.Classfile String String String where
  header := { isInterface := c.itf, isAbstract := c.abs, isFinal := c.final,
              super := if c.itf || c.super.startsWith "java/" then none else some c.super,
              ifaces := c.ifaces, isPublic := c.pub,
              permitted := if c.permitted.isEmpty then none else some c.permitted }
  methods := c.methods.map fun m =>
    (m.name, m.desc, { isStatic := m.static, isAbstract := m.abs, isFinal := m.final,
                       access := match m.acc with | .pub => .pub | .priv => .priv | .pkg => .pkg })
  fields := c.fields.map fun f =>
    (f.name, f.desc, { isStatic := f.static, isFinal := f.final,
                       access := match f.acc with | .pub => .pub | .priv => .priv | .pkg => .pkg })

def toWorld (cs : List ClassOut) : Jvm.World String String String :=
  fun n => (cs.find? (·.name == n)).map ClassOut.toJvm

/-! ## Lowering -/

def isJava (n : String) : Bool := n.startsWith "java/"

/-- The `getstatic`s a body or initialiser runs: none for a constant expression (folded), else one
per non-constant field it reads, in evaluation order. -/
def reads : ℕ → Expr → M (List Insn)
  | 0, _ => pure []
  | k + 1, e => do
    if (← eval fuel e).isSome then return []
    match e with
    | .field o n => do
      let d ← need o
      match d.fields.find? (·.name == n) with
      | some f => pure [⟨"getstatic", o, n, erase f.ty⟩]
      | none => throw s!"not found: {o}.{n}"
    | .add a b | .shl a b => pure ((← reads k a) ++ (← reads k b))
    | _ => pure []

/-- The constants a body or initialiser pushes: a constant expression's value, folded, else those
of its operands; `Integer.parseInt("1")` pushes `"1"`. -/
def pushes : ℕ → Expr → M (List CVal)
  | 0, _ => pure []
  | k + 1, e => do
    if let some v ← eval fuel e then return [v]
    match e with
    | .add a b | .shl a b => pure ((← pushes k a) ++ (← pushes k b))
    | .call => pure [.str "1"]
    | _ => pure []

def defaultPushes : Ty → List CVal
  | .int | .bool => [.int 0]
  | _ => []

/-- A supertype as seen from the type being lowered: its declaration and its type argument. -/
abbrev Anc := Decl × Option Ty

def seen (outer : Option Ty) : Option Ty → Option Ty
  | some t => some (match outer with | some a => t.subst a | none => t)
  | none => none

def parentsOf (d : Decl) : List Parent := d.super.toList ++ d.ifaces

/-- Every proper supertype of `d`, with type arguments composed; with repeats. -/
def supers : ℕ → Decl → Option Ty → M (List Anc)
  | 0, _, _ => pure []
  | k + 1, d, a => do
    let mut out : List Anc := []
    for (p, pa) in parentsOf d do
      let pd ← need p
      let a' := seen a pa
      out := out ++ (pd, a') :: (← supers k pd a')
    pure out

/-- Bridges in `d`: for each method `d` declares and each method of a supertype it overrides (the
same name, and parameters equal once the supertype's type parameter is substituted) whose erased
descriptor differs. -/
def bridges (d : Decl) (ms : List MOut) : M (List MOut) := do
  let ss ← supers fuel d none
  let mut out := ms
  for m in d.methods do
    if m.static || m.priv then continue
    for (a, arg) in ss do
      for m' in a.methods do
        if m'.static || m'.priv || m'.name != m.name then continue
        let subst := fun t => match arg with | some x => t.subst x | none => t
        if m'.params.map subst != m.params then continue
        let e := m'.desc
        if e == m.desc || out.any fun x => x.name == m.name && x.desc == e then continue
        let op := if d.kind == .iface then "invokeinterface" else "invokevirtual"
        out := out ++ [{ name := m.name, desc := e, bridge := true, synthetic := true,
                         calls := [⟨op, d.name, m.name, m.desc⟩] }]
  pure out

def userMethod (m : Meth) : M MOut := do
  let calls ← match m.ret with
    | some e => reads fuel e
    | none => pure []
  let ps ← match m.ret with
    | some e => pushes fuel e
    | none => pure (defaultPushes m.res)
  pure { name := m.name, desc := m.desc, acc := if m.priv then .priv else .pub, static := m.static,
         abs := m.abs, final := m.final, calls := if m.abs then [] else calls,
         pushes := if m.abs then [] else ps }

def fieldOut (d : Decl) (f : Field) : M FOut := do
  let itf := d.kind == .iface
  let c ← match f.init with
    | some e => if isConstVar d f then eval fuel e else pure none
    | none => pure none
  pure { name := f.name, desc := erase f.ty, static := f.static || itf, final := f.final || itf, const := c }

/-- The static initialiser, if a static field has an initialiser that is not a constant. -/
def clinit (d : Decl) (fs : List FOut) : M (List MOut) := do
  let dyn := (d.fields.zip fs).filter fun (f, o) => (f.static || d.kind == .iface) && f.init.isSome && o.const.isNone
  if dyn.isEmpty then return []
  let calls ← dyn.flatMapM fun (f, _) => match f.init with
    | some e => reads fuel e
    | none => pure []
  let ps ← dyn.flatMapM fun (f, _) => match f.init with
    | some e => pushes fuel e
    | none => pure []
  pure [{ name := "<clinit>", desc := "()V", acc := .pkg, static := true, calls := calls, pushes := ps }]

def permitted (unit : List Decl) (d : Decl) : List String :=
  match d.sealing with
  | .explicit ps => ps
  | .inferred => (unit.filter fun x => (parentsOf x).any (·.1 == d.name)).map (·.name)
  | _ => []

def lowerDecl (unit : List Decl) (pub : Bool) (d : Decl) : M ClassOut := do
  let fs ← d.fields.mapM (fieldOut d)
  let ms ← d.methods.mapM userMethod
  let base : ClassOut := { name := d.name, pub := pub, ifaces := d.ifaces.map (·.1),
                           permitted := permitted unit d }
  match d.kind with
  | .iface =>
    pure { base with itf := true, abs := true, methods := (← bridges d ms) ++ (← clinit d fs), fields := fs }
  | .cls =>
    let sup := (d.super.map (·.1)).getD "java/lang/Object"
    let ctor : MOut := { name := "<init>", desc := "()V", acc := if pub then .pub else .pkg,
                         calls := if isJava sup then [] else [⟨"invokespecial", sup, "<init>", "()V"⟩] }
    pure { base with abs := d.abs, final := d.final, super := sup,
                     methods := [ctor] ++ (← bridges d ms) ++ (← clinit d fs), fields := fs }
  | .enum =>
    let self := jname d.name
    let arr := "[" ++ self
    let consts : List FOut := d.consts.map fun c =>
      { name := c, desc := self, static := true, final := true, enum := true }
    let values : FOut := { name := "$VALUES", desc := arr, acc := .priv, static := true, final := true, synthetic := true }
    let ctorD := "(Ljava/lang/String;I)V"
    let ms' : List MOut :=
      [{ name := "values", desc := s!"(){arr}", static := true,
         calls := [⟨"getstatic", d.name, "$VALUES", arr⟩] },
       { name := "valueOf", desc := s!"(Ljava/lang/String;){self}", static := true },
       { name := "<init>", desc := ctorD, acc := .priv },
       { name := "$values", desc := s!"(){arr}", acc := .priv, static := true, synthetic := true,
         calls := d.consts.map fun c => ⟨"getstatic", d.name, c, self⟩,
         pushes := .int d.consts.length :: (List.range d.consts.length).map fun i => .int i },
       { name := "<clinit>", desc := "()V", acc := .pkg, static := true,
         calls := (d.consts.map fun _ => ⟨"invokespecial", d.name, "<init>", ctorD⟩) ++
                  [⟨"invokestatic", d.name, "$values", s!"(){arr}"⟩] ++
                  (← d.fields.flatMapM fun f => match f.init with
                     | some e => do if (← eval fuel e).isSome then pure [] else reads fuel e
                     | none => pure []),
         pushes := (d.consts.zipIdx.flatMap fun (c, i) => [.str c, .int i]) ++
                   (← d.fields.flatMapM fun f => match f.init with
                     | some e => do if (← eval fuel e).isSome then pure [] else pushes fuel e
                     | none => pure []) }]
    pure { base with final := true, enum := true, super := "java/lang/Enum",
                     methods := ms' ++ (← bridges d ms), fields := consts ++ fs ++ [values] }
  | .record =>
    let fsR : List FOut := d.comps.map fun (n, t) => { name := n, desc := erase t, acc := .priv, final := true }
    let accessors : List MOut := (d.comps.filter fun (n, _) => !d.methods.any (·.name == n)).map
      fun (n, t) => { name := n, desc := s!"(){erase t}" }
    let objs : List MOut :=
      [{ name := "toString", desc := "()Ljava/lang/String;", final := true },
       { name := "hashCode", desc := "()I", final := true },
       { name := "equals", desc := "(Ljava/lang/Object;)Z", final := true }]
    -- the implicit canonical constructor has the record's access (JLS §8.10.4)
    let ctor : MOut := { name := "<init>", desc := s!"({String.join (d.comps.map (erase ·.2))})V",
                         acc := if pub then .pub else .pkg }
    pure { base with final := true, super := "java/lang/Record",
                     methods := [ctor] ++ objs ++ accessors ++ (← bridges d ms) ++ (← clinit d fs),
                     fields := fsR ++ fs, record := some (d.comps.map fun (n, t) => (n, erase t)) }

def lowerUnit (u : CUnit) : M (List ClassOut) :=
  u.zipIdx.mapM fun (d, i) => lowerDecl u (i == 0) d

/-- Lower a compilation unit against an environment of interfaces. -/
def lower (u : CUnit) (env : (q : Q) → Ans q) : Except String (List ClassOut) :=
  (lowerUnit u).run.run env

def trace (u : CUnit) (env : (q : Q) → Ans q) : List Q :=
  (lowerUnit u).run.trace env

/-- **T1 for lowering.** An environment that agrees on a unit's trace lowers it to the same
classfiles. -/
theorem lower_congr (u : CUnit) (e e' : (q : Q) → Ans q)
    (h : ∀ q ∈ trace u e, e q = e' q) : lower u e = lower u e' :=
  (Zinc.Task.run_eq_of_trace _ e e' h).1

def lowerProgram (p : Program) : Except String (List ClassOut) := do
  let cs ← p.mapM fun u => lower u p.env
  pure cs.flatten

end Java
