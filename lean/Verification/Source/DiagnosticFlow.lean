import Verification.Source.FlowJson

namespace Verification.SourceFlow
open Lean RequestJson Fragment

private abbrev Recovery := Json × List (Span × String)

/-- Each boundary attempts its ordinary operation on the retained children.
Failure records the entire replaced region and retries its opaque substitute.
Only the diagnostic planner can construct this recovery result. -/
private def attempt (pos : Span) (j replacement : Json)
    (check : Json → Except String Unit) : Except String Recovery := do
  match check j with
  | .ok _ => return (j, [])
  | .error reason =>
    check replacement
    return (replacement, [(pos, reason)])

private def opaqueExpression (pos : Span) : Json :=
  Json.mkObj [("k", toJson "lit"), ("pos", toJson pos),
    ("lit", Json.mkObj [("a", toJson "undefined")])]

private def opaqueStatement (pos : Span) : Json :=
  Json.mkObj [("k", toJson "block"), ("pos", toJson pos),
    ("label", Json.null), ("body", toJson ([] : List Json))]

/-- Statement and binding-pattern tags distinguish the syntax categories.
Type payloads have spans under `span`, rather than executable `pos` fields. -/
private def statementKinds : List String :=
  ["return", "effect", "const", "let", "destructure", "break", "continue",
   "throw", "try", "while", "block", "closing", "forOf", "if"]

private partial def diagnosticSyntax : Json → Except String Recovery
  | .arr xs => do
    let results ← xs.toList.mapM diagnosticSyntax
    return (.arr (results.map Prod.fst).toArray, results.flatMap Prod.snd)
  | .obj fields => do
    let results ← fields.toList.mapM fun (key, value) => do
      let (value, holes) ← diagnosticSyntax value
      pure ((key, value), holes)
    let j := Json.mkObj (results.map Prod.fst)
    let holes := results.flatMap Prod.snd
    let some kind := (j.getObjValAs? String "k").toOption | return (j, holes)
    let some pos := (jSpan j "pos").toOption | return (j, holes)
    -- Binding patterns belong to their enclosing declaration's transaction.
    if ["name", "object", "array"].contains kind then return (j, holes)
    let (j, own) ← if statementKinds.contains kind then
      attempt pos j (opaqueStatement pos) (fun raw => do let _ ← decodeStmt raw; pure ())
    else
      attempt pos j (opaqueExpression pos) (fun raw => do
        let _ ← decodeExpr raw
        let _ ← nestedGraphs raw
        pure ())
    return (j, holes ++ own)
  | j => pure (j, [])

private def withField (j : Json) (key : String) (value : Json) : Except String Json := do
  let fields ← j.getObj?
  return Json.mkObj ((fields.toList.filter (·.1 != key)) ++ [(key, value)])

private partial def region (j : Json) (fallback : Span) : Span :=
  match j with
  | .arr xs => xs.foldl (fun pos value => region value pos) fallback
  | .obj fields =>
    let own := ((jSpan j "pos").toOption).getD fallback
    fields.toList.foldl (fun pos (_, value) => region value pos)
      (min fallback.1 own.1, max fallback.2 own.2)
  | _ => fallback

/-- Planning a whole execution body is a transaction too. Its fallback has
no statements and retains its declared interface; siblings receive independent
attempts. Expression-owned bodies are handled by `diagnosticSyntax`. -/
private def diagnosticBodies (ast : Json) : Except String Recovery := do
  let empty := toJson ([] : List Json)
  let shell ← withField (← withField ast "functions" empty) "init" empty
  let functions ← (← jArr ast "functions").mapM fun fn => do
    let pos := region (← jField fn "body") (← jSpan fn "namePos")
    attempt pos fn (← withField fn "body" empty) (fun raw => do
      let _ ← document (← withField shell "functions" (toJson [raw]))
      pure ())
  let init ← jField ast "init"
  let (init, holes) ← attempt (region init (0,0)) init empty (fun raw => do
    let _ ← document (← withField shell "init" raw)
    pure ())
  let ast ← withField (← withField ast "init" init) "functions" (toJson (functions.map Prod.fst))
  return (ast, functions.flatMap Prod.snd ++ holes)

/-- Proposal and extraction consume the same recovered syntax and graph.
This envelope has no conversion to source acceptance. -/
def diagnosticDocument (ast : Json) : Except String Json := do
  let (ast, syntaxHoles) ← diagnosticSyntax ast
  let (ast, bodyHoles) ← diagnosticBodies ast
  let graph ← document ast
  return Json.mkObj [("diagnostic", ast), ("graph", graph),
    ("occurrences", toJson ((syntaxHoles ++ bodyHoles).map fun (pos, reason) =>
      Json.mkObj [("pos", toJson pos), ("reason", toJson reason)]))]

end Verification.SourceFlow
