import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Compiler.CSimpAttr
import Verification.Source.Claims.Json
import Verification.Source.RequestCli
import Verification.Source.Demo
import Verification.Source.LinkedRuntime
import Verification.Source.Claims.Invocation
import Verification.Programs.LinkAssembly
import Verification.Source.PrimitiveAttachment

/-!
Acceptance and the linking, integer-boundary and runtime theorems rest on
Lean's standard axioms alone. The build fails when any audited declaration
depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`
(`sorryAx`, or one the project declares):

- `SourceClaimJson.checkUnitJson_safe`, the acceptance theorem, of which every
  accepted function's safety is a consequence;
- the stable-linking, accepted-code, primitive-transport, integer/adapter and
  runtime-composition theorems named below;
- each `@[csimp]` lemma of the project's modules the verifier imports
  (`Verification.Source.RequestCli`, what `Main` imports): the compiled
  verifier runs a lemma's right-hand side in place of the definition the
  proofs reason about, so its equation is part of what acceptance uses.
-/

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.SourceClaimJson.checkUnitJson_safe
  check ``Verification.LinkingCaptures.no_two_way_links
  check ``Verification.LinkingCaptures.no_capture_cycle
  check ``Verification.Linking.exports_safe
  check ``Verification.Linking.entry_env
  check ``Verification.Linking.code_of_accepted_request
  check ``Verification.Linking.code_of_top_level_request
  check ``Verification.Linking.code_of_adapted_request
  check ``Verification.Linking.code_of_capture_free_request
  check ``Verification.Linking.code_of_effectful_adapted_request
  check ``Verification.Linking.return_frame_post
  check ``Verification.Linking.return_frame_safe
  check ``Verification.Linking.projected_env
  check ``Verification.Linking.Assembly.check_sound
  check ``Verification.PrimitiveBoundary.attachmentCheck_sound
  check ``Verification.PrimitiveBoundary.no_attachment_without_arrow_rows
  check ``Verification.PrimitiveBoundary.exceptions_eq_of_no_builtins
  check ``Verification.Linking.code_of_checked_table
  check ``Verification.Linking.entries_safe
  check ``Verification.PrimitiveBoundary.compare_sound
  check ``Verification.PrimitiveBoundary.check_sound
  check ``Verification.PrimitiveBoundary.transport
  check ``Verification.LinkedRuntime.Machine.canRun_safe
  check ``Verification.LinkedRuntime.Simulation.canRun
  check ``Verification.LinkedRuntime.graph_safe
  check ``Verification.Demo.rowCheck_sound
  check ``Verification.Demo.Candidate.bodyCheck_sound
  check ``Verification.Demo.assemblyCheck_sound
  check ``Verification.Demo.CheckedAssembly.linked
  check ``Verification.Demo.Link.transport
  check ``Verification.Demo.Entry.slots
  check ``Verification.Demo.Entry.closed
  check ``Verification.Demo.linked_safe
  check ``Verification.LinkedRuntime.end_to_end
  check ``Verification.I64.wrap_range
  check ``Verification.I64.wrap_identity
  check ``Verification.I64.decode_encode
  check ``Verification.I64.encode_decode
  check ``Verification.I64.wrap_idempotent
  check ``Verification.I64.wrap_congr
  check ``Verification.I64.wrap_mod
  check ``Verification.I64.jsWrap_eq_wrap
  check ``Verification.I64.tdiv_range
  check ``Verification.I64.tmod_range
  check ``Verification.I64.divRem_exact
  check ``Verification.I64.lt_correct
  check ``Verification.I64.le_correct
  check ``Verification.I64.checked_exact
  check ``Verification.I64.checked_overflow
  check ``Verification.I64.divRem_zero
  check ``Verification.I64.divRem_min
  check ``Verification.I64.adapter_result
  check ``Verification.I64.adapter_effect
  check ``Verification.I64.adapter_error
  let env ← getEnv
  let project (decl : Name) : Bool := match env.getModuleIdxFor? decl with
    | some i => (`Verification).isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let lemmas := (Compiler.CSimp.ext.getState env).thmNames.toList.filter project
  if lemmas.isEmpty then throwError "no @[csimp] lemma of the project found"
  for decl in lemmas do check decl
