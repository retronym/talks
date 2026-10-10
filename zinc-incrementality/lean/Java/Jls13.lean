import Java.Catalogue

/-!
# JLS chapter 13, checked against `Jvm` linkage

Each example takes a rule of JLS chapter 13 (binary compatibility) and checks it on a case of
`Java/Catalogue.lean`: the library and client are lowered with `Java.lower` (calibrated against
javac by `probes/java`), then linked with `Jvm.outcome`. Where the client's linkage footprint is
unchanged by the edit, compatibility is `Jvm.compatible_of_footprint` rather than a run.
All by kernel `decide`.

The chapter's rules are about linking, and the JVM model answers them; the one thing it does not
see is §13.1's: a constant is a client's own copy. There, the claim is about the client's
classfile (what lowering pushes) and its lowering trace (what Zinc must record as a dependency).
-/

namespace Java.Jls13

open Catalogue

/-! ## §13.1, §13.4.9: constants are copied into clients -/

def xK : CUnit := (constantValueChanged.client.head?).getD []

/-- javac folds `A.K` into the client: it pushes `1` and has no reference to `A`. -/
example : (lower xK constantValueChanged.v0.env).map (fun cs => cs.flatMap fun c =>
    c.methods.filter (·.name == "k") |>.map fun m => (m.calls, m.pushes)) = .ok [([], [.int 1])] := by
  decide +kernel

/-- Lowering the client read `A`: the dependency Zinc must record, though the classfile does not
name `A`. -/
example : (trace xK constantValueChanged.v0.env).contains (.decl "A") = true := by decide +kernel

/-- Changing a constant's value links before and after (the client never touches `A`), and a
clean build changes the client: binary compatible, but Zinc must recompile the client. -/
example : constantValueChanged.before = .ok (.ok ["X", "X"]) ∧
    constantValueChanged.after = .ok (.ok ["X", "X"]) ∧
    constantValueChanged.recompiles = true := by decide +kernel

/-- …and the compatibility is footprint agreement: nothing linking reads changes. -/
example : Jvm.Compatible constantValueChanged.w0 constantValueChanged.w1 constantValueChanged.p0 :=
  compatible_of_agrees _ _ _ (by decide +kernel)

/-- Through an interface constant `J.L = A.K + 1`: the client names only `J`, but its lowering read
`A`, and a change to `A.K` changes the client's classfile. -/
example : (trace ((constantThroughInterface.client.head?).getD []) constantThroughInterface.v0.env).contains
      (.decl "A") = true ∧
    constantThroughInterface.recompiles = true := by decide +kernel

/-- A constant that stops being one: the old client keeps its copy and never reads the field; a
fresh one reads it. -/
example : constantBecomesNonConstant.after = .ok (.ok ["X", "X"]) ∧
    constantBecomesNonConstant.fresh = .ok (.ok ["X", "X", "A"]) := by decide +kernel

/-- Deleting a constant is binary compatible for a client that only used its value (it links, with
the old value), though the client no longer compiles. -/
example : constantRemoved.after = .ok (.ok ["X", "X"]) ∧
    constantRemoved.fresh = .error "not found: A.K" := by decide +kernel

/-- Deleting a field that is not a constant breaks a client that reads it (§13.4.8). -/
example : nonConstantRemoved.before = .ok (.ok ["X", "X", "A"]) ∧
    nonConstantRemoved.after = .ok (.error .noSuchField) := by decide +kernel

/-! ## §13.4.15, §13.4.5: method results, generics and bridges -/

/-- Removing an override that narrowed a generic method's result breaks a call through the
subclass: it names `get()String`, and erasure leaves only `get()Object`. -/
example : narrowedOverrideRemoved.before = .ok (.ok ["Q"]) ∧
    narrowedOverrideRemoved.after = .ok (.error .noSuchMethod) := by decide +kernel

/-- Through the superclass the same edit links: `get()Object` selected `Q`'s bridge, now `P`'s
method. -/
example : narrowedOverrideRemovedViaP.before = .ok (.ok ["Q"]) ∧
    narrowedOverrideRemovedViaP.after = .ok (.ok ["P"]) := by decide +kernel

/-- Adding the override: the old call names the inherited `get()Object`, which is now `Q`'s
bridge. -/
example : narrowedOverrideAdded.before = .ok (.ok ["P"]) ∧
    narrowedOverrideAdded.after = .ok (.ok ["Q"]) := by decide +kernel

/-! ## §13.5.3, §13.5.6: interface members -/

/-- Adding an abstract method to an interface breaks an implementation compiled before it, when
the method is invoked. -/
example : abstractAddedToInterface.after = .ok (.error .abstractMethod) := by decide +kernel

/-- Adding a default method does not; the old implementation inherits it. -/
example : defaultAddedToInterface.after = .ok (.ok ["I"]) := by decide +kernel

/-- Adding a private interface method is invisible to the client's footprint. -/
example : Jvm.Compatible privateAddedToInterface.w0 privateAddedToInterface.w1 privateAddedToInterface.p0 :=
  compatible_of_agrees _ _ _ (by decide +kernel)

/-! ## §13.4.26: enum classes -/

/-- Adding an enum constant is binary compatible, by footprint. -/
example : Jvm.Compatible enumConstantAdded.w0 enumConstantAdded.w1 enumConstantAdded.p0 :=
  compatible_of_agrees _ _ _ (by decide +kernel)

/-- Removing one breaks a client that reads it. -/
example : enumConstantRemoved.after = .ok (.error .noSuchField) := by decide +kernel

/-! ## §13.4.27: record classes -/

/-- Removing a component removes its accessor. -/
example : recordComponentRemoved.before = .ok (.ok ["R", "R"]) ∧
    recordComponentRemoved.after = .ok (.error .noSuchMethod) := by decide +kernel

/-- Adding one leaves the old accessors' footprint unchanged. -/
example : Jvm.Compatible recordComponentAdded.w0 recordComponentAdded.w1 recordComponentAdded.p0 :=
  compatible_of_agrees _ _ _ (by decide +kernel)

/-! ## §13.4.2.1: sealed classes -/

/-- Making a class `sealed` without permitting an existing subclass is not binary compatible: HotSpot
refuses to load the subclass. `Jvm` does not model `PermittedSubclasses`, so the model loads it;
lowering does emit the attribute. -/
example : classBecomesSealed.after = .ok (.ok []) ∧
    (lowerProgram classBecomesSealed.v1).map (·.map (·.permitted)) = .ok [["B"], []] := by
  decide +kernel

end Java.Jls13
