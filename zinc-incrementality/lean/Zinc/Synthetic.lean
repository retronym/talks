import Mathlib.Data.List.Basic

/-!
# Constructors and synthetic case-class members

Zinc's keys for a client of class `C` are used names, checked against `C`'s name hashes; a used
name does not say which class it came from. A mangling names each member of a class, once on the
definition side (the API's name hashes) and once on the use side (the client's used names). A
client that depends on `C` is invalidated when a name it used hashes differently in `C`'s new API;
it needs to be when the signature it used changed.

* `sound_of_agree`: one mangling on both sides: a changed signature invalidates the client.
* `under_of_disagree`: two manglings that disagree on a member: its change invalidates nothing
  (scala/scala3#12401, #19910/sbt/zinc#1334).
* `over_plain` (sbt/zinc#97), `over_default` (#1324): one name for every class's constructor (or
  default getter) invalidates a client of another class's constructor; class-mangled names do not.
* `unapply_26231`: the synthetic `unapply : (C): C` keeps its signature when the fields change;
  keying the pattern on `unapply` alone misses the change, keying it also on `C;init;` catches it.
* `apply_572`: a synthetic companion left out of the API has no hash for `apply`.
-/

namespace Zinc.Synthetic

/-- Members of a class and its companion. -/
inductive Mem | ctor | default1 | apply | unapply | copy | field (n : String)
  deriving DecidableEq, Repr

def mems : List Mem := [.ctor, .default1, .apply, .unapply, .copy]

structure Cls where
  pkg : String
  name : String
  deriving DecidableEq, Repr

/-- A member's signature in an API; `none`: not in the API. -/
abbrev Api := Mem → Option (List String)

abbrev Mangling := Cls → Mem → String

/-- `<init>` and `<init>$default$1` for every class. -/
def plain : Mangling := fun _ m => match m with
  | .ctor => "<init>" | .default1 => "<init>$default$1" | .apply => "apply" | .unapply => "unapply"
  | .copy => "copy" | .field n => n

/-- sbt/zinc#288: the class's name in the constructor's. -/
def m288 : Mangling := fun c m => match m with
  | .ctor => c.name ++ ";init;" | m => plain c m

/-- sbt/zinc#1324: also in the default getters'. -/
def m1324 : Mangling := fun c m => match m with
  | .default1 => c.name ++ ";init;$default$1" | m => m288 c m

/-- scala/scala3#19910: the definition side spelled with the package. -/
def withPkg : Mangling := fun c m => match m with
  | .ctor => c.pkg ++ ";" ++ c.name ++ ";init;" | m => m288 c m

/-- A name's hash in an API: the members with that name and their signatures. -/
def nameHash (mg : Mangling) (c : Cls) (api : Api) (n : String) : List (Mem × Option (List String)) :=
  (mems.filter fun m => mg c m == n).map fun m => (m, api m)

/-- Zinc invalidates a client of `c` with used names `used` when one of them hashes differently. -/
def invalidated (mg : Mangling) (c : Cls) (api api' : Api) (used : List String) : Bool :=
  used.any fun n => nameHash mg c api n != nameHash mg c api' n

theorem nameHash_ne (mg : Mangling) (c : Cls) (api api' : Api) (m : Mem) (hm : m ∈ mems)
    (h : api m ≠ api' m) : nameHash mg c api (mg c m) ≠ nameHash mg c api' (mg c m) := by
  intro he
  have hin : (m, api m) ∈ nameHash mg c api (mg c m) := by
    simp only [nameHash, List.mem_map, List.mem_filter]
    exact ⟨m, ⟨hm, beq_self_eq_true _⟩, rfl⟩
  rw [he] at hin
  simp only [nameHash, List.mem_map, List.mem_filter, Prod.mk.injEq] at hin
  obtain ⟨m', _, rfl, h'⟩ := hin
  exact h h'.symm

/-- **One mangling on both sides is sound**: a client that used member `m` of `c` is invalidated
when `m`'s signature changes. -/
theorem sound_of_agree (mg : Mangling) (c : Cls) (api api' : Api) (m : Mem) (hm : m ∈ mems)
    (used : List String) (hu : mg c m ∈ used) (h : api m ≠ api' m) :
    invalidated mg c api api' used = true := by
  simp only [invalidated, List.any_eq_true, bne_iff_ne, ne_eq]
  exact ⟨mg c m, hu, nameHash_ne mg c api api' m hm h⟩

/-- `p.C` with one constructor of one parameter, then two. -/
def c : Cls := ⟨"p", "C"⟩
def b : Cls := ⟨"p", "B"⟩
def api₀ : Api := fun m => match m with
  | .ctor => some ["Int"] | .apply => some ["Int"] | .unapply => some ["C"] | .copy => some ["Int"]
  | .default1 => some [] | .field _ => none
def api₁ : Api := fun m => match m with
  | .ctor => some ["Int", "String"] | .apply => some ["Int", "String"] | .unapply => some ["C"]
  | .copy => some ["Int", "String"] | .default1 => some [] | .field _ => none

/-- **scala/scala3#19910**: the definition side spells `p;C;init;`, the use side `C;init;`; adding
a constructor parameter invalidates nothing (`new C(1)` is now an error in a clean build). -/
theorem under_of_disagree :
    invalidated withPkg c api₀ api₁ [m288 c .ctor] = false := by decide

/-- **scala/scala3#12401** (before #12712): the API names constructors `<init>`, the use side
mangles them. -/
theorem under_12401 : invalidated plain c api₀ api₁ [m288 c .ctor] = false := by decide

/-- With both sides mangled alike, it is caught. -/
example : invalidated m288 c api₀ api₁ [m288 c .ctor] = true := by decide

/-- `C`'s copy method only, its constructor changed: a client that calls `new B` and `c.copy` uses
the names `<init>` (from `B`) and `copy`. -/
def apiCopyKept : Api := fun m => match m with
  | .ctor => some ["Int", "String"] | m => api₀ m

/-- **sbt/zinc#97**: with `<init>` for every class, `C`'s constructor change invalidates the client
of `B`'s constructor, although the member it used from `C` (`copy`) did not change. -/
theorem over_plain :
    invalidated plain c api₀ apiCopyKept [plain b .ctor, plain c .copy] = true ∧
      api₀ .copy = apiCopyKept .copy := by decide

/-- #288's class-mangled names remove it. -/
example : invalidated m288 c api₀ apiCopyKept [m288 b .ctor, m288 c .copy] = false := by decide

def apiDefault : Api := fun m => match m with
  | .default1 => some ["Int"] | m => api₀ m

/-- **sbt/zinc#1324**: the same through `<init>$default$1`, which #288 left unmangled. -/
theorem over_default :
    invalidated m288 c api₀ apiDefault [m288 b .default1, m288 c .copy] = true ∧
      invalidated m1324 c api₀ apiDefault [m1324 b .default1, m1324 c .copy] = false := by decide

/-- A field added: the constructor changes, the synthetic `unapply : (C): C` does not. -/
def apiField : Api := fun m => match m with
  | .ctor => some ["Int", "String"] | .apply => some ["Int", "String"] | .copy => some ["Int", "String"]
  | m => api₀ m

/-- **scala/scala3#26231**: a pattern `case C(a)` keyed on `unapply` misses the field change (its
`_1`, `_2` are read after typer); keyed also on `C;init;`, it is invalidated. -/
theorem unapply_26231 :
    invalidated m288 c api₀ apiField [m288 c .unapply] = false ∧
      invalidated m288 c api₀ apiField [m288 c .unapply, m288 c .ctor] = true := by decide

/-- The API without the synthetic companion (sbt/zinc#572 before its fix). -/
def dropCompanion (api : Api) : Api := fun m => match m with
  | .apply => none | .unapply => none | .copy => none | m => api m

/-- **sbt/zinc#572**: a client of `C(1)` (the synthetic `apply`) is not invalidated when `apply`
changes, because the API left the synthetic companion out; with it, it is. -/
theorem apply_572 :
    invalidated m288 c (dropCompanion api₀) (dropCompanion api₁) [m288 c .apply] = false ∧
      invalidated m288 c api₀ api₁ [m288 c .apply] = true := by decide

end Zinc.Synthetic
