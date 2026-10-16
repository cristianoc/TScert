/- Produce and independently check evidence for source claims. -/
import Verification.Source.RequestCli

open Verification Lean

def main (args : List String) : IO UInt32 := do
  let (budget, args) ← match args with
    | "--subtype-rounds" :: rounds :: rest => do
      match rounds.toNat? with
      | some n => pure (({ rounds := n } : Verification.PositiveCertificates.SearchBudget), rest)
      | none => IO.eprintln "reject: subtype rounds must be a natural number"; return 2
    | _ => pure ({}, args)
  match args with
  | ["--lower-control-flow", astPath] =>
      Verification.RequestCli.flowFile astPath
  | ["--lower-program", astPath, claimsPath, fileKey] =>
      Verification.RequestCli.lowerFile astPath claimsPath fileKey
  | ["--check-source-claims", astPath, claimsPath, fileKey, evidencePath] =>
      Verification.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none budget
  | ["--produce-source-claims", astPath, claimsPath, fileKey, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => Verification.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel) budget
      | none => IO.eprintln "reject: search depth must be a natural number"; return 2
  | _ =>
      IO.eprintln "usage: verifier --lower-control-flow <ast.json>"
      IO.eprintln "       verifier --lower-program <ast.json> <source-claims.json> <file-key>"
      IO.eprintln "       verifier --produce-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json> <depth>"
      IO.eprintln "       verifier --check-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json>"
      IO.eprintln "       (any mode may be preceded by --subtype-rounds <rounds>)"
      return 2
