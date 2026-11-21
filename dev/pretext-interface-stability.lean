import Verification.Source.Claims.Imports

open Lean Verification SourceClaimJson

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "expected one module file")
  let bytes ← IO.FS.readFile path
  let result : Except String (List String) := do
    let json ← Json.parse bytes
    let m ← Fragment.decodeModule json
    let some code := (ModuleCode.of [m])[m.location]? | throw "missing module"
    return (← code.get).stable
  match result with
  | .ok names =>
    IO.println (toJson names).compress
    return 0
  | .error s => throw (IO.userError s)
