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

/-- A source endpoint. A file range uses UTF-16 offsets. In a checked
unit, its declaration and an endpoint's ordinal give the lexical order
of its syntax. A generated endpoint can follow that point by a fixed
number of UTF-16 code units. -/
inductive SourcePoint where
  | offset (n : Nat)
  | occurrence (owner : String) (index : Nat) (advance : Nat := 0)
  deriving DecidableEq, Ord, Repr, Inhabited

instance : Hashable SourcePoint where
  hash
    | .offset n => hash n
    | .occurrence owner i delta => hash (owner, i, delta)

instance : Coe Nat SourcePoint := ⟨.offset⟩
instance {n : Nat} : OfNat SourcePoint n := ⟨.offset n⟩
instance : LT SourcePoint := ⟨fun a b => compare a b = .lt⟩
instance : LE SourcePoint := ⟨fun a b => compare a b ≠ .gt⟩
instance (a b : SourcePoint) : Decidable (a < b) := inferInstanceAs (Decidable (compare a b = .lt))
instance (a b : SourcePoint) : Decidable (a ≤ b) := inferInstanceAs (Decidable (compare a b ≠ .gt))
instance : Min SourcePoint := ⟨fun a b => if a ≤ b then a else b⟩
instance : Max SourcePoint := ⟨fun a b => if a ≤ b then b else a⟩
instance : HAdd SourcePoint Nat SourcePoint where
  hAdd
    | .offset n, k => .offset (n+k)
    | .occurrence o i d, k => .occurrence o i (d+k)

instance : ToJson SourcePoint where
  toJson
    | .offset n => toJson n
    | .occurrence o i d => toJson (o,i,d)

instance : FromJson SourcePoint where
  fromJson? j := do
    if let .ok n := j.getNat? then return .offset n
    let (o,i,d) ← fromJson? j
    return .occurrence o i d

instance : ToString SourcePoint where
  toString
    | .offset i => toString i
    | p => (toJson p).compress

abbrev Span := SourcePoint × SourcePoint

def Span.offsets? : Span → Option (Nat × Nat)
  | (.offset start, .offset stop) => some (start, stop)
  | _ => none

def spanStr (p : Span) : String := s!"[{p.1},{p.2})"

/-! ### JSON accessors -/

def jField (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error e => .error s!"missing field '{k}': {e}"

def jStr (j : Json) : Except String String := j.getStr?
def jNat (j : Json) (k : String) : Except String Nat := do
  match (← jField j k).getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"field '{k}' is not a natural number"
def jArr (j : Json) (k : String) : Except String (List Json) := do
  let a ← (← jField j k).getArr?
  return a.toList

def jSpan (j : Json) (k : String) : Except String Span := do
  let a ← (← jField j k).getArr?
  if h : a.size = 2 then
    let s ← fromJson? a[0]
    let e ← fromJson? a[1]
    return (s, e)
  else .error s!"field '{k}' is not a [start, end] pair"

/-- An object with exactly the fields `keys`, each once. -/
def fieldsExactly (j : Json) (keys : List String) : Except String Unit := do
  let fields ← j.getObj?
  if fields.toList.length != keys.length || !(fields.toList.all (fun p => keys.contains p.1)) then
    throw s!"unexpected fields: expected {keys}, got {fields.toList.map Prod.fst}"

end Verification
