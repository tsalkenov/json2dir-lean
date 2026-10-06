import Lean

namespace Json2Dir

open Lean

/-- A name that cannot denote a root, parent, current directory, or nested path. -/
def safeComponent (part : String) : Bool :=
  !part.isEmpty && part != "." && part != ".." && !part.contains '/'

inductive NameError where
  | multipleComponents
  | nonRegularComponent

private def interpretParts (parts : List String) (hasPrefix : Bool) : Except NameError String :=
  if parts.length + (if hasPrefix then 1 else 0) != 1 then .error .multipleComponents
  else if hasPrefix || parts == [".."] then .error .nonRegularComponent
  else match parts with
    | [part] => if safeComponent part then .ok part else .error .nonRegularComponent
    | _ => .error .multipleComponents

private theorem interpretParts_safe {parts : List String} {hasPrefix : Bool} {part : String}
    (h : interpretParts parts hasPrefix = .ok part) :
    safeComponent part = true := by
  cases hasPrefix with
  | true =>
    cases parts <;> simp [interpretParts] at h
  | false =>
    cases parts with
    | nil => simp [interpretParts] at h
    | cons first rest =>
      cases rest with
      | nil =>
        by_cases hdot : first = ".."
        · simp [interpretParts, hdot] at h
        · by_cases hs : safeComponent first = true
          · simp [interpretParts, hdot, hs] at h
            simpa [h] using hs
          · simp [interpretParts, hdot, hs] at h
      | cons second remaining => simp [interpretParts] at h

/-- Interpret a JSON key using the path-component rules of the reference CLI. -/
def parseName (name : String) : Except NameError String :=
  let parts := (name.splitOn "/").filter (fun part => !part.isEmpty && part != ".")
  let hasPrefix := name.startsWith "/" || name.startsWith "./" || name == "."
  interpretParts parts hasPrefix

/-- Every accepted key resolves to exactly one safe relative component. -/
theorem parseName_safe {name part : String} (h : parseName name = .ok part) :
    safeComponent part = true :=
  interpretParts_safe h

/-- Accepted keys cannot resolve to empty, dot, parent, or nested components. -/
theorem parseName_noTraversal {name part : String} (h : parseName name = .ok part) :
    part.isEmpty = false ∧ part != "." ∧ part != ".." ∧ part.contains '/' = false := by
  have hs := parseName_safe h
  simp only [safeComponent, Bool.and_eq_true] at hs
  cases hEmpty : part.isEmpty <;> cases hSlash : part.contains '/' <;> simp_all

inductive Entry where
  | directory (children : Std.TreeMap.Raw String Json)
  | file (content : String)
  | link (target : String)
  | script (content : String)

inductive EntryError where
  | invalidPart
  | invalidArray
  | invalidArrayKind

/-- The complete JSON value conversion table, before filesystem effects. -/
def classify : Json → Except EntryError Entry
  | .obj children => .ok (.directory children)
  | .str content => .ok (.file content)
  | .arr values =>
    match values.toList with
    | [.str "link", .str target] => .ok (.link target)
    | [.str "script", .str content] => .ok (.script content)
    | [.str _, .str _] => .error .invalidArrayKind
    | _ => .error .invalidArray
  | _ => .error .invalidPart

theorem classify_directory (children : Std.TreeMap.Raw String Json) :
    classify (.obj children) = .ok (.directory children) := rfl

theorem classify_file (content : String) :
    classify (.str content) = .ok (.file content) := rfl

theorem classify_link (target : String) :
    classify (.arr #[.str "link", .str target]) = .ok (.link target) := rfl

theorem classify_script (content : String) :
    classify (.arr #[.str "script", .str content]) = .ok (.script content) := rfl

theorem classify_unknown_kind (kind payload : String)
    (notLink : kind ≠ "link") (notScript : kind ≠ "script") :
    classify (.arr #[.str kind, .str payload]) = .error .invalidArrayKind := by
  simp_all [classify]

theorem classify_empty_array : classify (.arr #[]) = .error .invalidArray := rfl

theorem classify_null : classify .null = .error .invalidPart := rfl
theorem classify_bool (b : Bool) : classify (.bool b) = .error .invalidPart := rfl
theorem classify_num (n : JsonNumber) : classify (.num n) = .error .invalidPart := rfl

end Json2Dir
