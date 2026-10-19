-- FlowJson.lean supplies the claim-independent graphs the producer analyzes.
import Verification.Source.FlowJson
import Verification.Source.Claims.Json

/-! File interface to the source adapter. Source parsing remains external;
checking reconstructs each unit's request from the fragment and its claims. -/
namespace Verification.RequestCli
open Lean RequestJson

/-- Four hexadecimal digits' value. -/
def hex4 (cs : List Char) : Option Nat :=
  cs.foldlM (fun v c =>
    if '0' ≤ c ∧ c ≤ '9' then some (v * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (v * 16 + (c.toNat - 'a'.toNat + 10))
    else if 'A' ≤ c ∧ c ≤ 'F' then some (v * 16 + (c.toNat - 'A'.toNat + 10))
    else none) 0

/-- A lone surrogate escape of a JSON text's strings, if it has one. Every
wire string is well-formed Unicode (HOST-FAMILIES.md, "Tag sets"): Lean's
JSON parser reads a lone surrogate as U+FFFD, a different string, so a text
holding one is refused before it is parsed; `IO.FS.readFile` refuses a text
that is not valid UTF-8. -/
partial def loneSurrogate (cs : List Char) (inString : Bool := false) : Option String :=
  match cs, inString with
  | [], _ => none
  | '"' :: rest, b => loneSurrogate rest !b
  | '\\' :: 'u' :: a :: b :: c :: d :: rest, true =>
    match hex4 [a, b, c, d] with
    | some u =>
      if 0xD800 ≤ u ∧ u ≤ 0xDBFF then
        match rest with
        | '\\' :: 'u' :: e :: f :: g :: h :: more =>
          match hex4 [e, f, g, h] with
          | some v => if 0xDC00 ≤ v ∧ v ≤ 0xDFFF then loneSurrogate more true else some "a lone high surrogate"
          | none => some "a lone high surrogate"
        | _ => some "a lone high surrogate"
      else if 0xDC00 ≤ u ∧ u ≤ 0xDFFF then some "a lone low surrogate"
      else loneSurrogate rest true
    | none => loneSurrogate rest true
  | '\\' :: _ :: rest, true => loneSurrogate rest true
  | _ :: rest, b => loneSurrogate rest b

def readJson (path : String) : IO (Except String Json) := do
  try
    let text ← IO.FS.readFile path
    if let some what := loneSurrogate text.toList then
      return .error s!"{path}: a string that is not well-formed Unicode, {what}, is refused"
    return Json.parse text
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
