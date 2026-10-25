import Verification.Source.FlowJson

namespace Verification.SourceFlow
open Lean RequestJson Fragment

/-- Diagnostic planning preserves source positions and records each excluded
literal-key test as an opaque expression before constructing execution plans.
The test’s outer fields and key are decoded before recovery. This operation
belongs to diagnostic planning. -/
private partial def diagnosticSyntax : Json → Except String (Json × List (Span × String))
  | .arr xs => do
    let results ← xs.toList.mapM diagnosticSyntax
    return (.arr (results.map Prod.fst).toArray, results.flatMap Prod.snd)
  | .obj fields => do
    let j := Json.obj fields
    if (j.getObjValAs? String "k").toOption == some "inTest" then
      fieldsExactly j ["k", "pos", "key", "e"]
      let pos ← jSpan j "pos"
      let key ← decodeExpr (← jField j "key")
      if let .lit _ (.vstr key) := key then
        if let some reason := inKeyRefusal key then
          return (Json.mkObj [("k", toJson "lit"), ("pos", toJson pos),
            ("lit", Json.mkObj [("a", toJson "undefined")])],
            [(pos, s!"`in` with the key '{key}': {reason}")])
    let results ← fields.toList.mapM fun (key, value) => do
      let (value, holes) ← diagnosticSyntax value
      pure ((key, value), holes)
    return (Json.mkObj (results.map Prod.fst), results.flatMap Prod.snd)
  | j => pure (j, [])

/-- The diagnostic planner returns its approximated syntax with the graph so
proposal and typed extraction consume the same operations. -/
def diagnosticDocument (ast : Json) : Except String Json := do
  let (ast, holes) ← diagnosticSyntax ast
  let graph ← document ast
  return Json.mkObj [("diagnostic", ast), ("graph", graph),
    ("occurrences", toJson (holes.map fun (pos, reason) =>
      Json.mkObj [("pos", toJson pos), ("reason", toJson reason)]))]

end Verification.SourceFlow
