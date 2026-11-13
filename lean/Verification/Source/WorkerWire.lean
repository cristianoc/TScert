import Lean.Data.Json
import Verification.Types.Decode

/-! The lines of mode 8's commands (docs/REQUEST-PROTOCOL.md, "The file
worker"): a unit's verdict, the file worker's preparation, and a request the
file worker reads. `pipeline/stage-execution.mts` declares the same lines
(`WorkerLine`, `WorkerRequest`); `tests/json-field-names.mts` compares their
field names. -/
namespace Verification.WorkerWire
open Lean

/-- A unit's verdict line: `{"unit","members","accepted","depends","extraction"}`,
its group accepted with the units its verdict rests on, or
`{"unit","members","refusal","extraction"}`; `extraction` the first
extraction refusal among its group's members, or null. -/
def verdictLine (unit : String) (members : List String) (verdict : Except String (List String))
    (extraction : Option String) : String :=
  let ext := ("extraction", match extraction with | some r => toJson r | none => Json.null)
  (match verdict with
    | .ok deps => Json.mkObj [("unit", toJson unit), ("members", toJson members), ("accepted", toJson true),
        ("depends", toJson deps), ext]
    | .error reason => Json.mkObj [("unit", toJson unit), ("members", toJson members),
        ("refusal", toJson reason), ext]).compress

/-- A verdict line's extraction refusal (`verdictLine`). -/
def lineExtraction (line : String) : Except String (Option String) := do
  let j ← Json.parse line
  let e ← j.getObjVal? "extraction"
  if e.isNull then return none
  return some (← fromJson? e)

/-- The file worker's preparation line: `{"selected","established"}`, the
units the selection checks in the order their checks run, each
`{"unit","members"}`; and the module units the interfaces establish. -/
def preparedLine (selected : List (String × List String)) (established : List String) : String :=
  (Json.mkObj [("selected", Json.arr (selected.map fun (u, ms) =>
      Json.mkObj [("unit", toJson u), ("members", toJson ms)]).toArray),
    ("established", toJson established)]).compress

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
