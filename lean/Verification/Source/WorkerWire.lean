import Lean.Data.Json
import Verification.Types.Decode

/-! The lines of mode 8's commands (docs/REQUEST-PROTOCOL.md, "The file
worker"): a unit's verdict, the file worker's preparation, and a request the
file worker reads. `pipeline/stage-execution.mts` declares the same lines
(`WorkerLine`, `WorkerRequest`); `tests/json-field-names.mts` compares their
field names. -/
namespace Verification.WorkerWire
open Lean

/-- A unit's verdict line: `{"unit","members","accepted","depends"}`, its
group accepted with the units its verdict rests on, or
`{"unit","members","refusal"}`. -/
def verdictLine (unit : String) (members : List String) (verdict : Except String (List String)) : String :=
  (match verdict with
    | .ok deps => Json.mkObj [("unit", toJson unit), ("members", toJson members), ("accepted", toJson true),
        ("depends", toJson deps)]
    | .error reason => Json.mkObj [("unit", toJson unit), ("members", toJson members),
        ("refusal", toJson reason)]).compress

/-- The file worker's preparation line: `{"selected","established","extraction"}`,
the units the selection checks in the order their checks run, each
`{"unit","members"}`; the module units the interfaces establish; and the
first extraction refusal among the selected groups, or null. -/
def preparedLine (selected : List (String × List String)) (established : List String)
    (extraction : Option String) : String :=
  (Json.mkObj [("selected", Json.arr (selected.map fun (u, ms) =>
      Json.mkObj [("unit", toJson u), ("members", toJson ms)]).toArray),
    ("established", toJson established),
    ("extraction", match extraction with | some r => toJson r | none => Json.null)]).compress

/-- A request line the file worker reads: `{"units"}`, the units to check by
their identities, or null for every selected unit in order. Any other shape
is refused. -/
def decodeRequest (text : String) : Except String (Option (List String)) := do
  let j ← Json.parse text
  fieldsExactly j ["units"]
  let u ← j.getObjVal? "units"
  if u.isNull then return none
  return some (← fromJson? u)

end Verification.WorkerWire
