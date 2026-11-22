import Verification.Source.Claims.CallbackInterfaceCheck

namespace Verification.SourceClaimJson.CallbackPublication
open Lean RequestJson

structure Outcome where
  location : String
  name : String
  position : Nat × Nat
  dependent : Bool
  checked : Option CallbackInterfaceCheck.Published

def emitDeclaration (location : String) (required : List (String × String)) (interfaces : List Json)
    (fn : Json) : Except String Json := do
  let name ← fn.getObjValAs? String "name"
  let position ← fn.getObjValAs? (Nat × Nat) "namePos"
  let iface := interfaces.find? fun j => (j.getObjValAs? String "name").toOption == some name &&
    (j.getObjValAs? (Nat × Nat) "position").toOption == some position
  let status := if !required.contains (location,name) then "ordinary" else if iface.isSome then "checked" else "refused"
  return Json.mkObj [("name",toJson name),("namePos",toJson position),("status",toJson status),
    ("interface",iface.getD .null)]

def decodeDeclaration (location : String) (pair : Json × Json) : Except String Outcome := do
  let (fn,d) := pair
  fieldsExactly d ["name","namePos","status","interface"]
  let name ← fn.getObjValAs? String "name"
  let pos ← fn.getObjValAs? (Nat × Nat) "namePos"
  if (← d.getObjValAs? String "name") != name || (← d.getObjValAs? (Nat × Nat) "namePos") != pos then
    throw s!"mismatched callback outcome for {location}#{name}"
  let iface ← jField d "interface"
  match ← d.getObjValAs? String "status" with
  | "checked" =>
    let published ← CallbackInterfaceCheck.Published.ofJson iface
    let params ← jArr fn "params"
    let headers ← params.mapM fun param => do
      let name ← param.getObjValAs? String "name"
      let rest ← match param.getObjVal? "rest" with
        | .ok value => fromJson? (α := Bool) value
        | .error _ => pure false
      pure (name, rest)
    let width := (headers.takeWhile (!·.2)).length
    let receiver := headers.head?.any (·.1 == "this")
    if published.formals != width || published.receiver != receiver then
      throw s!"mismatched callback parameter layout for {name}"
    if published.name != name || published.position != some pos then throw s!"mismatched callback interface for {name}"
    return (⟨location,name,pos,true,some published⟩ : Outcome)
  | "ordinary" =>
    if iface != .null then throw s!"unexpected callback interface for {name}"
    return ⟨location,name,pos,false,none⟩
  | "refused" =>
    if iface != .null then throw s!"unexpected callback interface for {name}"
    return ⟨location,name,pos,true,none⟩
  | _ => throw s!"invalid callback outcome for {location}#{name}"

/-- Decode producer classifications using declaration headers. No body is
part of the identity or required to interpret a checked demand. -/
def decodeDeclarations (location : String) (functions : List Json) (outcomes : Json) : Except String (List Outcome) := do
  fieldsExactly outcomes ["declarations"]
  let declarations ← jArr outcomes "declarations"
  if functions.length != declarations.length then throw s!"incomplete callback outcomes for {location}"
  (functions.zip declarations).mapM (decodeDeclaration location)

/-- Resolve one imported declaration using its module, name and declaration
span. The returned outcome belongs to the producer; the alias is local. -/
def selectBinding (available : List Outcome) (name loc target : String) (span : Nat × Nat) :
    Option (String × Option CallbackInterfaceCheck.Published) := Id.run do
  let entries := available.filter fun r => r.location == loc && r.name == target
  if entries.isEmpty then
    if !available.any (·.location == loc) then return some (name,none)
    return none
  let matching := entries.filter fun row => span.1 ≤ row.position.1 && row.position.2 ≤ span.2
  if let [row] := matching then
    if row.dependent then return some (name,row.checked.map fun iface => {iface with name,position := none})
    return none
  if entries.any (·.dependent) then return some (name,none)
  return none

def importBinding (locations : List String) (available : List Outcome) (value : Json) :
    Option (String × Option CallbackInterfaceCheck.Published) := do
  let binding ← (value.getObjVal? "binding").toOption
  let name ← (binding.getObjValAs? String "local").toOption
  let declaration ← (value.getObjVal? "declaration").toOption
  let loc ← (declaration.getObjValAs? String "module").toOption
  if !locations.contains loc then none else
    let target ← (declaration.getObjValAs? String "name").toOption
    let span ← (declaration.getObjValAs? (Nat × Nat) "span").toOption
    selectBinding available name loc target span

def importedOutcomes (document : Json) (locations : List String) (available : List Outcome) :
    List (String × Option CallbackInterfaceCheck.Published) :=
  (((jArr (document.getObjValD "declarations") "values").toOption.getD []).filterMap
    (importBinding locations available)).reverse

end Verification.SourceClaimJson.CallbackPublication
