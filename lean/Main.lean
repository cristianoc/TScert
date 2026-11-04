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
  | ["--produce-run", runPath, fileKey, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => Verification.RequestCli.runFile runPath fileKey evidencePath fuel budget
      | none => IO.eprintln "usage: search depth must be a natural number"; return 2
  | ["--check-source-claims", astPath, claimsPath, fileKey, evidencePath] =>
      Verification.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none budget
  | ["--produce-source-claims", astPath, claimsPath, fileKey, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => Verification.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel) budget
      | none => IO.eprintln "usage: search depth must be a natural number"; return 2
  | ["--units", astPath, claimsPath, fileKey] =>
      Verification.RequestCli.unitsFile astPath claimsPath fileKey budget
  | ["--produce-unit", astPath, claimsPath, fileKey, evidencePath, unit, depth] =>
      match depth.toNat? with
      | some fuel => Verification.RequestCli.produceUnitFile astPath claimsPath fileKey evidencePath unit fuel budget
      | none => IO.eprintln "usage: search depth must be a natural number"; return 2
  | ["--check-unit", astPath, claimsPath, fileKey, evidencePath, unit] =>
      Verification.RequestCli.checkUnitFile astPath claimsPath fileKey evidencePath unit budget
  | _ =>
      IO.eprintln "usage: verifier --lower-control-flow <ast.json>"
      IO.eprintln "       verifier --units <ast.json> <source-claims.json> <file-key>"
      IO.eprintln "       verifier --produce-unit <ast.json> <source-claims.json> <file-key> <evidence.json> <unit> <depth>"
      IO.eprintln "       verifier --check-unit <ast.json> <source-claims.json> <file-key> <evidence.json> <unit>"
      IO.eprintln "       verifier --lower-program <ast.json> <source-claims.json> <file-key>"
      IO.eprintln "       verifier --produce-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json> <depth>"
      IO.eprintln "       verifier --plan-imports <ast.json> <source-claims.json>"
      IO.eprintln "       verifier --produce-run <run.json> <file-key> <evidence.json> <depth>"
      IO.eprintln "       verifier --check-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json>"
      IO.eprintln "       (any mode may be preceded by --subtype-rounds <rounds>)"
      return 2

def main (args : List String) : IO UInt32 := do
  try
    command args
  catch e =>
    IO.eprintln s!"error: {e}"
    return 3
