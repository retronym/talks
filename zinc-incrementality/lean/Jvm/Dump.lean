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

def cName : C → String | .A => "A" | .B => "B" | .I => "I" | .J => "J" | .X => "X"
def nName : N → String | .m => "m"
def dName : D → String | .v => "()V" | .i => "()I"

def errName : LinkError → String
  | .noClassDef => "noClassDef"
  | .incompatibleClassChange => "incompatibleClassChange"
  | .noSuchMethod => "noSuchMethod"
  | .abstractMethod => "abstractMethod"
  | .instantiation => "instantiation"
  | .finalSuper => "finalSuper"
  | .finalOverride => "finalOverride"
  | .verify => "verify"

def methodJson (m : N × D × MethodInfo) : String :=
  "{\"name\":" ++ jstr (nName m.1) ++ ",\"desc\":" ++ jstr (dName m.2.1) ++
  ",\"static\":" ++ jbool m.2.2.isStatic ++ ",\"abstract\":" ++ jbool m.2.2.isAbstract ++
  ",\"final\":" ++ jbool m.2.2.isFinal ++ "}"

def classJson (c : C × Classfile C N D) : String :=
  let h := c.2.header
  "{\"name\":" ++ jstr (cName c.1) ++ ",\"interface\":" ++ jbool h.isInterface ++
  ",\"abstract\":" ++ jbool h.isAbstract ++ ",\"final\":" ++ jbool h.isFinal ++
  ",\"super\":" ++ (match h.super with | some s => jstr (cName s) | none => "null") ++
  ",\"ifaces\":" ++ jarr (h.ifaces.map (jstr ∘ cName)) ++
  ",\"methods\":" ++ jarr (c.2.methods.map methodJson) ++ "}"

def siteJson : Site C N D → String
  | .invokestatic c n d =>
    "{\"op\":\"invokestatic\",\"owner\":" ++ jstr (cName c) ++ ",\"name\":" ++ jstr (nName n) ++
    ",\"desc\":" ++ jstr (dName d) ++ "}"
  | .invokevirtual c n d r =>
    "{\"op\":\"invokevirtual\",\"owner\":" ++ jstr (cName c) ++ ",\"name\":" ++ jstr (nName n) ++
    ",\"desc\":" ++ jstr (dName d) ++ ",\"recv\":" ++ jstr (cName r) ++ "}"
  | .invokeinterface c n d r =>
    "{\"op\":\"invokeinterface\",\"owner\":" ++ jstr (cName c) ++ ",\"name\":" ++ jstr (nName n) ++
    ",\"desc\":" ++ jstr (dName d) ++ ",\"recv\":" ++ jstr (cName r) ++ "}"
  | .new c => "{\"op\":\"new\",\"owner\":" ++ jstr (cName c) ++ "}"

def outcomeJson : Except LinkError (List C) → String
  | .ok l => "{\"ok\":" ++ jarr (l.map (jstr ∘ cName)) ++ "}"
  | .error e => "{\"error\":" ++ jstr (errName e) ++ "}"

def tableJson (l : List (C × Classfile C N D)) : String := jarr (l.map classJson)

def caseJson (k : Case) : String :=
  "{\"name\":" ++ jstr k.name ++
  ",\"mima\":" ++ (match k.mima with | some s => jstr s | none => "null") ++
  ",\"v0\":" ++ tableJson k.v0 ++ ",\"v1\":" ++ tableJson k.v1 ++
  ",\"client\":" ++ tableJson k.client ++
  ",\"loads\":" ++ jarr (k.prog.loads.map (jstr ∘ cName)) ++
  ",\"sites\":" ++ jarr (k.prog.sites.map siteJson) ++
  ",\"before\":" ++ outcomeJson k.before ++ ",\"after\":" ++ outcomeJson k.after ++ "}"

end Jvm.Dump
