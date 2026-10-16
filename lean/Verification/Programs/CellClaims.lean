import Verification.Source.SourceTypes

/-! Single-field record claims at the invariant-cell boundary. This module does
not lower TypeScript objects. It validates a bounded export and refuses to pick
one side when a claim's read and write types differ. The plain-cell interpretation
excludes arrays, callable objects, accessors and hidden object behavior. -/
namespace Verification.CellClaims
open Lean ProgramTyping PositiveRules SourceTypes LabelStore
open EquationGraphs (Tree)

private def plainMode (j : Json) (name : String) : Except String Unit := do
  let mode ← jStr (← jField j name)
  if mode != "unknown" && mode != "absent" then throw s!"unsupported cell object mode: {name}"

def primitive (j : Json) : Except String Claim.Ty := do
  fieldsExactly j ["top","atoms"]
  for atom in ← jArr j "atoms" do
    let tag ← jStr (← jField atom "a")
    if ["booleanlit","stringlit","numberlit","bigintlit"].contains tag then
      fieldsExactly atom ["a","v"]
    else fieldsExactly atom ["a"]
  decodeTy j

/-- The accepted record is interpreted as one required slot per named field.
The schema cannot distinguish data properties from accessors; the source gate
must establish plain-data allocation before using this interpretation. Positive
call, construct, array, index, symbol and extra-field requirements are excluded
by this bounded schema. Synthetic index markers describe exporter bookkeeping,
not runtime permissions; their internal inference variables are not interpreted.
Absence and unknown modes have the same interpretation
within the plain-cell fragment; this is not full TypeScript object semantics. -/
def decodeFields (j : Json) : Except String (List (PropKey × Json × Json × Bool)) := do
  fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then throw "top is not a cell contract"
  let atoms ← jArr j "atoms"
  let atom ← match atoms with
    | [a] => pure a
    | _ => throw "expected a single record atom"
  fieldsExactly atom ["a","fields","indexes","call","construct","array"]
  if (← jStr (← jField atom "a")) != "record" then throw "expected a record atom"
  let indexes ← jField atom "indexes"
  fieldsExactly indexes ["string","number","symbol"]
  for kind in ["string","number","symbol"] do
    let mode ← jStr (← jField indexes kind)
    if mode != "absent" && mode != "synthetic" then
      throw "real index signatures are not invariant cells"
  plainMode atom "call"
  plainMode atom "construct"
  plainMode atom "array"
  let fields ← jArr atom "fields"
  if fields.isEmpty then throw "a record with no field has no location"
  let out ← fields.mapM fun field => do
    fieldsExactly field ["name","optional","read","write"]
    let name ← PropKey.decode (← jField field "name")
    return (name, ← jField field "read", ← jField field "write",
      ← (← jField field "optional").getBool?)
  let names := out.map Prod.fst
  if names.eraseDups.length != names.length then throw "duplicate field name in a record"
  return out

/-- A record's required fields: an optional one is refused where only
required cells are read. -/
def decodeShapes (j : Json) : Except String (List (PropKey × Json × Json)) := do
  (← decodeFields j).mapM fun (name, read, write, optional) => do
    if optional then throw "optional fields are not invariant cells"
    return (name, read, write)

/-- A conjunction is written inside the atom that carries one, as `and`. The
operands are the same single-contract atoms, decoded by the same decoder: the
key is removed and each part checked on its own, so nothing here relaxes what a
contract may be. -/
def conjuncts (atom : Json) : Except String (List Json) := do
  let fields ← atom.getObj?
  let plain := Json.mkObj (fields.toList.filter (fun p => p.1 != "and"))
  match atom.getObjVal? "and" with
  | .error _ => return [plain]
  | .ok rest =>
    let others ← rest.getArr?
    if others.isEmpty then throw "an empty conjunction is not a contract"
    for other in others.toList do
      if (other.getObjVal? "and").toOption.isSome then
        throw "nested conjunction in a cell contract"
    return plain :: others.toList

section
variable {ι : Type} [Labels ι]

/-- The label of a location under one record contract. -/
def reference (fs : List (PropKey × Ty Tree)) : Lowering Tree := use (.refs fs [] [])

/-- The label of a location under one record contract with readonly views:
the invariant fields and, separately, the fields read through a capability. -/
def viewReference (fs vs : List (PropKey × Ty Tree)) : Lowering Tree := use (.refs fs [] vs)

/-- Field maps compare by name first, then by the labels their contracts got. -/
def beforeFields : List (PropKey × Ty ι) → List (PropKey × Ty ι) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    a.1.before b.1 || (a.1 == b.1 && (Labels.before a.2 b.2 || (a.2 == b.2 && beforeFields as bs)))

end

end Verification.CellClaims
