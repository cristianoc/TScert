/- Produce and independently check evidence for source claims. -/
import Verification.Source.RequestCli

open Verification Lean

/-- `--verify-units`: modes 8 and 9 read the fragment alone
(`<ast> <file-key> <depth> [<names>]`); every other mode reads the claims
(`<ast> <claims> <file-key> <depth> [<names>]`). -/
def verifyUnits (budget : Verification.PositiveCertificates.SearchBudget)
    (mode astPath second third : String) (rest : List String) : IO UInt32 :=
  let usage : IO UInt32 := do IO.eprintln "usage: verifier --verify-units <mode> <ast.json> [<source-claims.json>] <file-key> <depth> [<names>]"; return 2
  match (mode == "8" || mode == "9"), third.toNat?, rest with
  | true, some fuel, names =>
    if names.length > 1 then usage
    else Verification.RequestCli.verifyUnitsFile astPath none second fuel names.head? (mode.toNat?.getD 8) budget
  | _, _, depth :: names =>
    match depth.toNat? with
    | some fuel =>
      if names.length > 1 then usage
      else Verification.RequestCli.verifyUnitsFile astPath (some second) third fuel names.head? (mode.toNat?.getD 0) budget
    | none => usage
  | _, _, [] => usage

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
  | ["--module-interface-plan", astPath, selection] =>
      Verification.RequestCli.interfacePlanFile astPath selection
  | ["--module-interface", request] =>
      Verification.RequestCli.interfaceFile request budget
  | ["--verify-interface-stage", mode, ast, interfaces, key, depth, names] =>
      match mode.toNat?, depth.toNat? with
      | some m, some fuel =>
        if m != 8 && m != 9 then return 2
        -- Quiet but where its counts are asked (`TSCERT_COUNTS`, dev/perf-gate.mts).
        let quiet := (← IO.getEnv "TSCERT_COUNTS").isNone
        Verification.RequestCli.verifyUnitsFile ast none key fuel (if names.isEmpty then none else some names) m budget (some interfaces) none none quiet
      | _, _ => return 2
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
  -- Modes 8 and 9 read the fragment alone: `<ast> <file-key> <depth>`;
  -- every other mode `<ast> <claims> <file-key> <depth>`.
  | "--verify-units" :: mode :: astPath :: second :: third :: rest =>
      verifyUnits budget mode astPath second third rest
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
    IO.eprintln "       verifier --verify-units <mode> <ast.json> <source-claims.json> <file-key> <depth> [<names>]"
    IO.eprintln "       verifier --verify-units 8|9 <ast.json> <file-key> <depth> [<names>]"
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
