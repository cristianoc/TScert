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
  | ["--diagnose-source-claims-local", astPath, claimsPath, fileKey, depth] =>
      match depth.toNat? with
      | some fuel => Verification.RequestCli.diagnosticFile astPath claimsPath fileKey fuel budget false
      | none => IO.eprintln "usage: search depth must be a natural number"; return 2
  | ["--diagnose-source-claims", astPath, claimsPath, fileKey, depth] =>
      match depth.toNat? with
      | some fuel => Verification.RequestCli.diagnosticFile astPath claimsPath fileKey fuel budget
      | none => IO.eprintln "usage: search depth must be a natural number"; return 2
  | ["--diagnostic-control-flow", astPath] =>
      Verification.RequestCli.diagnosticFlowFile astPath
  | ["--lower-control-flow", astPath] =>
      Verification.RequestCli.flowFile astPath
  | ["--lower-program", astPath, claimsPath, fileKey] =>
      Verification.RequestCli.lowerFile astPath claimsPath fileKey
  | ["--check-source-claims", astPath, claimsPath, fileKey, evidencePath] =>
      Verification.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none budget
  | ["--produce-source-claims", astPath, claimsPath, fileKey, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => Verification.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel) budget
      | none => IO.eprintln "usage: search depth must be a natural number"; return 2
  | _ =>
      IO.eprintln "usage: verifier --lower-control-flow <ast.json>"
      IO.eprintln "       verifier --lower-program <ast.json> <source-claims.json> <file-key>"
      IO.eprintln "       verifier --produce-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json> <depth>"
      IO.eprintln "       verifier --check-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json>"
      IO.eprintln "       (any mode may be preceded by --subtype-rounds <rounds>)"
      return 2

def main (args : List String) : IO UInt32 := do
  try
    command args
  catch e =>
    IO.eprintln s!"error: {e}"
    return 3
