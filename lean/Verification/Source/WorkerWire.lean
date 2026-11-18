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
its group accepted with the units its verdict rests on;
`{"unit","members","acceptedUnderClientTrust","depends","extraction"}`, its
group accepted for the executions in which outside code keeps a member's
client obligation (`trusted`, `FilePlans.clientTrust`); or
`{"unit","members","refusal","extraction"}`; `extraction` the first
extraction refusal among its group's members, or null. -/
def verdictLine (unit : String) (members : List String) (verdict : Except String (List String))
    (extraction : Option String) (trusted : Bool) : String :=
  let ext := ("extraction", match extraction with | some r => toJson r | none => Json.null)
  (match verdict with
    | .ok deps => Json.mkObj ([("unit", toJson unit), ("members", toJson members)] ++
        (if trusted then [("acceptedUnderClientTrust", toJson true)] else [("accepted", toJson true)]) ++
        [("depends", toJson deps), ext])
    | .error reason => Json.mkObj [("unit", toJson unit), ("members", toJson members),
        ("refusal", toJson reason), ext]).compress

/-- Whether a verdict line accepts its unit under client trust
(`verdictLine`). -/
def lineTrusted (line : String) : Bool :=
  match Json.parse line with
  | .ok j => (j.getObjVal? "acceptedUnderClientTrust").toOption.isSome
  | .error _ => false

/-- A verdict line's extraction refusal (`verdictLine`). -/
def lineExtraction (line : String) : Except String (Option String) := do
  let j ← Json.parse line
  let e ← j.getObjVal? "extraction"
  if e.isNull then return none
  return some (← fromJson? e)

/-- The file worker's preparation line: `{"selected","established","components"}`,
the units the selection checks in the order their checks run, each
`{"unit","members"}`; the module units the interfaces establish; and each
component's outcome of the read-only frame's checks, each
`{"component","kind","location","protocol","guarantee","frames","refusals"}` (`componentOutcome`). -/
def preparedLine (selected : List (String × List String)) (established : List String) (components : Json) : String :=
  (Json.mkObj [("selected", Json.arr (selected.map fun (u, ms) =>
      Json.mkObj [("unit", toJson u), ("members", toJson ms)]).toArray),
    ("established", toJson established), ("components", components)]).compress

/-- A component's outcome of the read-only frame's checks
(`ComponentChecks.familyOutcome`):
`{"component","kind","location","protocol","guarantee","frames","refusals"}`,
its certificate held where `refusals` is empty. -/
def componentOutcome (component : Nat) (kind location : String) (refusals protocol guarantee frames : List String) : Json :=
  Json.mkObj [("component", toJson component), ("kind", toJson kind), ("location", toJson location),
    ("protocol", toJson protocol), ("guarantee", toJson guarantee), ("frames", toJson frames),
    ("refusals", toJson refusals)]

/-- Mode 8's line of the components' outcomes: `{"components"}`, as the
preparation line states them. -/
def componentsLine (components : Json) : String :=
  (Json.mkObj [("components", components)]).compress

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
