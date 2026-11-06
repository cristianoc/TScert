import Verification.Source.Demo

open Lean Verification

/-- Unit evidence is the verifier's strict JSON-line format. -/
def readEvidence (path : String) : IO (List Json) := do
  let contents ← IO.FS.readFile path
  match (contents.splitOn "\n" |>.filter (· != "")).mapM Json.parse with
  | .ok lines => return lines
  | .error e => throw (IO.userError e)

def readArtifact (directory name : String) : IO Json := do
  let contents ← IO.FS.readFile (directory ++ "/" ++ name)
  match Json.parse contents with
  | .ok j => return j
  | .error e => throw (IO.userError e)

/-- Exit zero is exactly `Demo.Input.accepted = true`. The pure decision
rechecks the retained units, constructs their concrete closures and entry
slots, and runs the proved body, assembly and attachment checkers. -/
def main (args : List String) : IO UInt32 := do
  try
    let [rustDirectory, callerDirectory] := args
      | throw (IO.userError "expected Rust and caller artifact directories")
    let input : Demo.Input := {
      rustAst := ← readArtifact rustDirectory "fragment.json"
      rustClaims := ← readArtifact rustDirectory "claims.json"
      rustEvidence := ← readEvidence (rustDirectory ++ "/evidence.json")
      callerAst := ← readArtifact callerDirectory "fragment.json"
      callerClaims := ← readArtifact callerDirectory "claims.json"
      callerEvidence := ← readEvidence (callerDirectory ++ "/evidence.json") }
    if input.accepted then
      IO.println "linked"
      return 0
    else
      match input.run with
      | .error e => IO.eprintln e
      | .ok _ => IO.eprintln "boundary refused"
      return 1
  catch e => IO.eprintln e.toString; return 2
