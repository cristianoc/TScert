import Lean.Data.Json

/-! # Shared decoding plumbing

Not a language. Every other file named after a language in this directory
defines one; this file defines none. It holds what the claim, fragment, cell
and operation decoders all need to read a JSON document: source spans, and the
field accessors that turn a missing or ill-typed field into a message instead
of a default.

Nothing here knows what it is decoding. A decoder that does belongs in its own
language's file. -/
namespace Verification
open Lean

/-- A half-open span of the source, in UTF-16 code units. Several languages
carry spans, so the abbreviation belongs to none of them. -/
abbrev Span := Nat × Nat

def spanStr (p : Span) : String := s!"[{p.1},{p.2})"

/-! ### JSON accessors -/

def jField (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error e => .error s!"missing field '{k}': {e}"

def jStr (j : Json) : Except String String := j.getStr?
def jArr (j : Json) (k : String) : Except String (List Json) := do
  let a ← (← jField j k).getArr?
  return a.toList

def jSpan (j : Json) (k : String) : Except String Span := do
  let a ← (← jField j k).getArr?
  if h : a.size = 2 then
    let s ← a[0].getNat?
    let e ← a[1].getNat?
    return (s, e)
  else .error s!"field '{k}' is not a [start, end] pair"

/-- An object with exactly the fields `keys`, each once. -/
def fieldsExactly (j : Json) (keys : List String) : Except String Unit := do
  let fields ← j.getObj?
  if fields.toList.length != keys.length || !(fields.toList.all (fun p => keys.contains p.1)) then
    throw s!"unexpected fields: expected {keys}, got {fields.toList.map Prod.fst}"

end Verification
