import Jvm.Catalogue

/-!
# JSON dump of catalogue cases, for the HotSpot probe

One JSON object per line: the case's class tables, the client program, and the model's outcome
before and after. `probes/jvm` renders the classfiles and checks the outcomes on a JVM.
-/

namespace Jvm.Dump

open Jvm.Catalogue

def jstr (s : String) : String := "\"" ++ s ++ "\""
def jarr (l : List String) : String := "[" ++ ",".intercalate l ++ "]"
def jbool (b : Bool) : String := if b then "true" else "false"

def cBase : C → String | .A => "A" | .B => "B" | .I => "I" | .J => "J" | .X => "X"

/-- The package of each class, from the first table that has it (packages are part of a name and
must agree between tables). -/
def pkgIn (l : List (C × Classfile C N D)) (c : C) : ℕ :=
  ((l.find? (·.1 = c)).map (·.2.header.pkg)).getD 0

/-- The binary name: package `n > 0` is `p<n>`. -/
def qual (pk : C → ℕ) (c : C) : String :=
  if pk c = 0 then cBase c else s!"p{pk c}.{cBase c}"
def nName : N → String | .m => "m"
def dName : D → String | .v => "()V" | .i => "()I" | .s => "Ljava/lang/String;"

def accName : Access → String | .pub => "public" | .prot => "protected" | .pkg => "package" | .priv => "private"

def errName : LinkError → String
  | .noClassDef => "noClassDef"
  | .incompatibleClassChange => "incompatibleClassChange"
  | .noSuchMethod => "noSuchMethod"
  | .abstractMethod => "abstractMethod"
  | .instantiation => "instantiation"
  | .finalSuper => "finalSuper"
  | .finalOverride => "finalOverride"
  | .verify => "verify"
  | .illegalAccess => "illegalAccess"
  | .noSuchField => "noSuchField"

def methodJson (m : N × D × MethodInfo) : String :=
  "{\"name\":" ++ jstr (nName m.1) ++ ",\"desc\":" ++ jstr (dName m.2.1) ++
  ",\"static\":" ++ jbool m.2.2.isStatic ++ ",\"abstract\":" ++ jbool m.2.2.isAbstract ++
  ",\"final\":" ++ jbool m.2.2.isFinal ++ ",\"access\":" ++ jstr (accName m.2.2.access) ++ "}"

def fieldJson (m : N × D × FieldInfo) : String :=
  "{\"name\":" ++ jstr (nName m.1) ++ ",\"desc\":" ++ jstr (dName m.2.1) ++
  ",\"static\":" ++ jbool m.2.2.isStatic ++ ",\"final\":" ++ jbool m.2.2.isFinal ++
  ",\"access\":" ++ jstr (accName m.2.2.access) ++ "}"

section
variable (pk : C → ℕ)

def classJson (c : C × Classfile C N D) : String :=
  let h := c.2.header
  let cName := qual pk
  "{\"name\":" ++ jstr (cName c.1) ++ ",\"interface\":" ++ jbool h.isInterface ++
  ",\"abstract\":" ++ jbool h.isAbstract ++ ",\"final\":" ++ jbool h.isFinal ++
  ",\"public\":" ++ jbool h.isPublic ++
  ",\"super\":" ++ (match h.super with | some s => jstr (cName s) | none => "null") ++
  ",\"ifaces\":" ++ jarr (h.ifaces.map (jstr ∘ cName)) ++
  ",\"methods\":" ++ jarr (c.2.methods.map methodJson) ++
  ",\"fields\":" ++ jarr (c.2.fields.map fieldJson) ++ "}"

def member (op : String) (c : C) (n : N) (d : D) : String :=
  "{\"op\":" ++ jstr op ++ ",\"owner\":" ++ jstr (qual pk c) ++ ",\"name\":" ++ jstr (nName n) ++
  ",\"desc\":" ++ jstr (dName d)

def withRecv (s : String) (r : C) : String := s ++ ",\"recv\":" ++ jstr (qual pk r) ++ "}"

def siteJson : Site C N D → String
  | .invokestatic c n d => member pk "invokestatic" c n d ++ "}"
  | .invokestaticIface c n d => member pk "invokestaticIface" c n d ++ "}"
  | .invokevirtual c n d r => withRecv pk (member pk "invokevirtual" c n d) r
  | .invokeinterface c n d r => withRecv pk (member pk "invokeinterface" c n d) r
  | .getfield c n d r => withRecv pk (member pk "getfield" c n d) r
  | .putfield c n d r => withRecv pk (member pk "putfield" c n d) r
  | .getstatic c n d => member pk "getstatic" c n d ++ "}"
  | .putstatic c n d => member pk "putstatic" c n d ++ "}"
  | .invokespecial c n d i => member pk "invokespecial" c n d ++ ",\"iface\":" ++ jbool i ++ "}"
  | .new c => "{\"op\":\"new\",\"owner\":" ++ jstr (qual pk c) ++ "}"
  | .within x s => "{\"op\":\"at\",\"cls\":" ++ jstr (qual pk x) ++ ",\"site\":" ++ siteJson s ++ "}"

def outcomeJson : Except LinkError (List C) → String
  | .ok l => "{\"ok\":" ++ jarr (l.map (jstr ∘ qual pk)) ++ "}"
  | .error e => "{\"error\":" ++ jstr (errName e) ++ "}"

def tableJson (l : List (C × Classfile C N D)) : String := jarr (l.map (classJson pk))
end

def caseJson (k : Case) : String :=
  let pk := pkgIn (k.client ++ k.v0 ++ k.v1)
  let cName := qual pk
  let tableJson := tableJson pk
  let siteJson := siteJson pk
  let outcomeJson := outcomeJson pk
  "{\"name\":" ++ jstr k.name ++
  ",\"mima\":" ++ (match k.mima with | some s => jstr s | none => "null") ++
  ",\"v0\":" ++ tableJson k.v0 ++ ",\"v1\":" ++ tableJson k.v1 ++
  ",\"client\":" ++ tableJson k.client ++
  ",\"loads\":" ++ jarr (k.prog.loads.map (jstr ∘ cName)) ++
  ",\"sites\":" ++ jarr (k.prog.sites.map siteJson) ++
  ",\"before\":" ++ outcomeJson k.before ++ ",\"after\":" ++ outcomeJson k.after ++ "}"

end Jvm.Dump
