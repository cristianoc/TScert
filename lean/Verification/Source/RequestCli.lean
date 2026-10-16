-- FlowJson.lean supplies the claim-independent graphs the producer analyzes.
import Verification.Source.FlowJson
import Verification.Source.SourceClaimJson

/-! File interface to the source adapter. Source parsing remains external;
checking reconstructs each unit's request from the fragment and its claims. -/
namespace Verification.RequestCli
open Lean RequestJson

def readJson (path : String) : IO (Except String Json) := do
  try
    return Json.parse (← IO.FS.readFile path)
  catch e => return .error s!"cannot read {path}: {e}"

/-- Export the same execution graph constructor used by typed extraction. -/
def flowFile (astPath : String) : IO UInt32 := do
  let ast ← readJson astPath
  match ast >>= SourceFlow.document with
  | .ok graph => IO.println graph.compress; return 0
  | .error reason => IO.eprintln s!"reject: {reason}"; return 1

/-- Print the program graph each unit lowers to (`SourceClaimJson.lowerJson`). -/
def lowerFile (astPath claimsPath fileKey : String) : IO UInt32 := do
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match do SourceClaimJson.lowerJson (← ast) (← claims) fileKey with
  | .ok j => IO.println j.compress; return 0
  | .error e => IO.eprintln s!"reject: {e}"; return 1

def sourceFiles (astPath claimsPath fileKey evidencePath : String)
    (fuel : Option Nat)
    (budget : PositiveCertificates.SearchBudget := {}) : IO UInt32 := do
  if fuel.isSome && (evidencePath == astPath || evidencePath == claimsPath) then
    IO.eprintln "reject: evidence output must differ from the input files"
    return 1
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match fuel with
  | none =>
    let evidence ← readJson evidencePath
    let checked := do
      SourceClaimJson.checkJson (← ast) (← claims) fileKey (← evidence) budget
    match checked with
    | .ok () => IO.println s!"accept: stateful source {fileKey}"; return 0
    | .error e => IO.eprintln s!"reject: {e}"; return 1
  | some depth =>
    let produced := do
      SourceClaimJson.produceJson (← ast) (← claims) fileKey depth budget
    match produced with
    | .error e => IO.eprintln s!"reject: {e}"; return 1
    | .ok evidence =>
      try
        IO.FS.writeFile evidencePath (evidence.compress ++ "\n")
        IO.println s!"checked source evidence written: {evidencePath}"
        return 0
      catch e => IO.eprintln s!"reject: cannot write {evidencePath}: {e}"; return 1

end Verification.RequestCli
