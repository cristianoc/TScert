/- Check a source file's units by the single pass (mode 8), and the module
interfaces its imports read. -/
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
  | ["--module-interface-plan", astPath, selection] =>
      Verification.RequestCli.interfacePlanFile astPath selection
  | ["--module-interface", request] =>
      Verification.RequestCli.interfaceFile request budget
  | ["--verify-interface-stage", mode, ast, interfaces, key, depth, names] =>
      match mode, depth.toNat? with
      | "8", some fuel =>
        -- Quiet but where its counts are asked (`TSCERT_COUNTS`, dev/perf-gate.mts).
        let quiet := (← IO.getEnv "TSCERT_COUNTS").isNone
        Verification.RequestCli.verifyUnitsFile ast key fuel (if names.isEmpty then none else some names) budget interfaces quiet
      | _, _ => usage
  | ["--lower-control-flow", astPath] =>
      Verification.RequestCli.flowFile astPath
  | _ => usage
where
  usage : IO UInt32 := do
    IO.eprintln "usage: verifier --verify-interface-stage 8 <ast.json> <interfaces.json> <file-key> <depth> <names>"
    IO.eprintln "       verifier --module-interface-plan <ast.json> <selection.json>"
    IO.eprintln "       verifier --module-interface <request.json>"
    IO.eprintln "       verifier --lower-control-flow <ast.json>"
    IO.eprintln "       (any mode may be preceded by --subtype-rounds <rounds>; <names> selects units by a member's name, comma-separated)"
    return 2

def main (args : List String) : IO UInt32 := do
  -- The work table recorded where profiling (`TSCERT_PROFILE`), written at
  -- the end (`RequestCli.writeWork`).
  Verification.SinglePass.profiling.set (← IO.getEnv "TSCERT_PROFILE").isSome
  let start ← IO.monoNanosNow
  try
    let code ← command args
    Verification.RequestCli.writeWork start
    return code
  catch e =>
    IO.eprintln s!"error: {e}"
    return 3
