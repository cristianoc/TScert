/- Produce and independently check evidence for source claims. -/
import Verification.Source.RequestCli

open Verification Lean

/-- The command: a refusal exits 1 with its record (`RequestCli.refuse`), a
usage error 2, and an operational failure (a file it cannot read or write,
any exception) 3, with a first line `error: `. -/
def command (args : List String) : IO UInt32 := do
  let (budget, args) ← match args with
    | "--subtype-rounds" :: rounds :: rest => do
      match rounds.toNat? with
      | some n => pure (({ rounds := n } : Verification.PositiveCertificates.SearchBudget), rest)
      | none => IO.eprintln "usage: subtype rounds must be a natural number"; return 2
    | _ => pure ({}, args)
  match args with
  | ["--lower-control-flow", astPath] =>
      Verification.RequestCli.flowFile astPath
  | ["--lower-program", astPath, claimsPath, fileKey] =>
      Verification.RequestCli.lowerFile astPath claimsPath fileKey
  | ["--plan-imports", astPath, claimsPath] =>
      Verification.RequestCli.planFile astPath claimsPath
  | "--units" :: astPath :: claimsPath :: fileKey :: names =>
      if names.length > 1 then usage
      else Verification.RequestCli.unitsFile astPath claimsPath fileKey names.head? budget
  | "--produce-units" :: astPath :: claimsPath :: fileKey :: evidencePath :: depth :: names =>
      if names.length > 1 then usage
      else match depth.toNat? with
        | some fuel =>
          Verification.RequestCli.produceUnitsFile astPath claimsPath fileKey evidencePath fuel names.head? budget
        | none => do IO.eprintln "usage: search depth must be a natural number"; return 2
  | "--check-units" :: astPath :: claimsPath :: fileKey :: evidencePath :: names =>
      if names.length > 1 then usage
      else Verification.RequestCli.checkUnitsFile astPath claimsPath fileKey evidencePath names.head? budget
  | _ => usage
where
  usage : IO UInt32 := do
    IO.eprintln "usage: verifier --lower-control-flow <ast.json>"
    IO.eprintln "       verifier --lower-program <ast.json> <source-claims.json> <file-key>"
    IO.eprintln "       verifier --plan-imports <ast.json> <source-claims.json>"
    IO.eprintln "       verifier --units <ast.json> <source-claims.json> <file-key> [<names>]"
    IO.eprintln "       verifier --produce-units <ast.json> <source-claims.json> <file-key> <evidence.json> <depth> [<names>]"
    IO.eprintln "       verifier --check-units <ast.json> <source-claims.json> <file-key> <evidence.json> [<names>]"
    IO.eprintln "       (any mode may be preceded by --subtype-rounds <rounds>; <names> selects units by a member's name, comma-separated)"
    return 2

def main (args : List String) : IO UInt32 := do
  try
    command args
  catch e =>
    IO.eprintln s!"error: {e}"
    return 3
