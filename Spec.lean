import Lean.Data.Json.Parser

namespace Json2Dir

open Lean

/-- A name that cannot denote a root, parent, current directory, or nested path,
    and contains no NUL byte. -/
def safeComponent (part : String) : Bool :=
  !part.isEmpty && part != "." && part != ".." &&
    !part.contains '/' && !part.contains '\x00'

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

/-- Accepted keys cannot resolve to empty, dot, parent, nested, or NUL components. -/
theorem parseName_noTraversal {name part : String} (h : parseName name = .ok part) :
    part.isEmpty = false ∧ part != "." ∧ part != ".." ∧
      part.contains '/' = false ∧ part.contains '\x00' = false := by
  have hs := parseName_safe h
  simp only [safeComponent, Bool.and_eq_true] at hs
  cases hEmpty : part.isEmpty <;>
    cases hSlash : part.contains '/' <;>
    cases hNul : part.contains '\x00' <;> simp_all

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def codeUnit? : List Char → Option (Nat × List Char)
  | a :: b :: c :: d :: rest => do
    let a ← hexDigit? a
    let b ← hexDigit? b
    let c ← hexDigit? c
    let d ← hexDigit? d
    return (a * 4096 + b * 256 + c * 16 + d, rest)
  | _ => none

mutual

private partial def scanOutside : List Char → Bool
  | [] => true
  | '"' :: rest => scanInside rest
  | _ :: rest => scanOutside rest

private partial def scanInside : List Char → Bool
  | [] => true
  | '"' :: rest => scanOutside rest
  | '\\' :: 'u' :: rest =>
    match codeUnit? rest with
    | none => false
    | some (unit, rest) =>
      if 0xD800 ≤ unit && unit ≤ 0xDBFF then
        match rest with
        | '\\' :: 'u' :: rest =>
          match codeUnit? rest with
          | some (low, rest) =>
            if 0xDC00 ≤ low && low ≤ 0xDFFF then scanInside rest else false
          | none => false
        | _ => false
      else if 0xDC00 ≤ unit && unit ≤ 0xDFFF then false
      else scanInside rest
  | '\\' :: _ :: rest => scanInside rest
  | '\\' :: [] => false
  | _ :: rest => scanInside rest

end

/-- Reject unpaired surrogate escapes before Lean's permissive JSON parser replaces them. -/
def validUnicodeEscapes (input : String) : Bool := scanOutside input.toList

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
