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
  | "--produce-unit" :: slicePath :: claimsPath :: qualifiedPath :: evidencePath :: depth :: names =>
      if names.length > 1 then usage
      else match depth.toNat? with
        | some fuel =>
          Verification.RequestCli.produceUnitFile slicePath claimsPath qualifiedPath evidencePath fuel names.head? budget
        | none => do IO.eprintln "usage: search depth must be a natural number"; return 2
  | "--check-units" :: astPath :: claimsPath :: fileKey :: evidencePath :: names =>
      if names.length > 1 then usage
      else Verification.RequestCli.checkUnitsFile astPath claimsPath fileKey evidencePath names.head? budget
  | "--verify-units" :: mode :: astPath :: claimsPath :: fileKey :: depth :: names =>
      if names.length > 1 then usage
      else match depth.toNat? with
        | some fuel => Verification.RequestCli.verifyUnitsFile astPath claimsPath fileKey fuel names.head? (mode.toNat?.getD 0) budget
        | none => do IO.eprintln "usage: search depth must be a natural number"; return 2
  | ["--module-runs", astPath, claimsPath] =>
      Verification.RequestCli.moduleRunsFile astPath claimsPath
  | ["--check-module", runPath, evidencePath] =>
      Verification.RequestCli.checkModuleFile runPath evidencePath budget
  | _ => usage
where
  usage : IO UInt32 := do
    IO.eprintln "usage: verifier --lower-control-flow <ast.json>"
    IO.eprintln "       verifier --lower-program <ast.json> <source-claims.json> <file-key>"
    IO.eprintln "       verifier --plan-imports <ast.json> <source-claims.json>"
    IO.eprintln "       verifier --produce-unit <slice.json> <slice-claims.json> <qualified.json> <evidence.json> <depth> [<names>]"
    IO.eprintln "       verifier --check-units <ast.json> <source-claims.json> <file-key> <evidence.json> [<names>]"
    IO.eprintln "       verifier --verify-units <ast.json> <source-claims.json> <file-key> <depth> [<names>]"
    IO.eprintln "       verifier --module-runs <ast.json> <source-claims.json>"
    IO.eprintln "       verifier --check-module <module-run.json> <evidence.json>"
    IO.eprintln "       (any mode may be preceded by --subtype-rounds <rounds>; <names> selects units by a member's name, comma-separated)"
    return 2

def main (args : List String) : IO UInt32 := do
  try
    command args
  catch e =>
    IO.eprintln s!"error: {e}"
    return 3
