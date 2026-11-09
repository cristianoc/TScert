import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Compiler.CSimpAttr
import Verification.Source.Claims.Json
import Verification.Source.RequestCli
import Verification.Semantics.ArgumentStoreRegions
import Verification.Semantics.FootprintNatives
import Verification.Programs.ArgumentPathTracking
import Verification.Programs.ArgumentRegionCertificates
import Verification.Programs.ArgumentStoreSeparation

/-!
Acceptance rests on Lean's standard axioms alone. The build fails when any of
the following depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`
(`sorryAx`, or one the project declares):

- `SourceClaimJson.checkUnitJson_safe`, the acceptance theorem, of which every
  accepted function's and module run's safety is a consequence;
- the regional footprint's transport and composition, cell provenance, and the
  argument-store region composition, framing and stable separation theorems;
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
  check ``Verification.Footprints.transport_sound
  check ``Verification.Footprints.Sep.sound
  check ``Verification.Footprints.Post.mono
  check ``Verification.Footprints.keep_across_call
  check ``Verification.Footprints.StoreApart.sep
  check ``Verification.CallEffects.Effect.within_iff_closed
  check ``Verification.CallEffects.Effect.within_closed
  check ``Verification.CallEffects.Effect.within_iff_regions
  check ``Verification.CallEffects.Effect.within_prefix
  check ``Verification.CallEffects.Effect.frameCovers_sound
  check ``Verification.Footprints.Closed.post_extra_any
  check ``Verification.Footprints.Post.compose
  check ``Verification.Footprints.Region.sub_mem
  check ``Verification.Footprints.CellsFrom.of_post
  check ``Verification.Footprints.CellsFrom.trans
  check ``Verification.Footprints.placeAt_cells
  check ``Verification.Footprints.Arr.Within.cells
  check ``Verification.Footprints.ArgumentStoreRegionsWithin.iff_post
  check ``Verification.Footprints.ArgumentStoreRegionsWithin.trans
  check ``Verification.Footprints.ArgumentStoreRegionsWithin.frame_length
  check ``Verification.Footprints.ArgumentStoreRegionsWithin.frame_densePrefix
  check ``Verification.Footprints.StoreApart.stable_frame
  check ``Verification.Footprints.StablePath.frame
  check ``Verification.Footprints.ArgumentStoreRegionsWithin.nested
  check ``Verification.Footprints.StoreApart.stable_path_frame
  check ``Verification.Footprints.StoreApart.not_alias
  check ``Verification.GraphCode.ArgumentPathTracking.checkEntry_sound
  check ``Verification.GraphCode.ArgumentPathTracking.checkEdges_sound
  check ``Verification.GraphCode.ArgumentPathTracking.checkHandler_sound
  check ``Verification.GraphCode.ArgumentPathTracking.stableField_path
  check ``Verification.GraphCode.ArgumentPathTracking.read_stable
  check ``Verification.GraphCode.ArgumentPathTracking.receiver_call
  check ``Verification.GraphCode.ArgumentPathTracking.checkReceiver_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.nodeWithin_of_closed
  check ``Verification.GraphCode.ArgumentRegionGraph.checkReceiverCall_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.firstRefusedNode_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.checkEntry_reassign
  check ``Verification.GraphCode.ArgumentRegionGraph.checkNodes_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.checkEntry_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.goto_bounded
  check ``Verification.ArgumentStoreSeparation.checkMap_sound
  check ``Verification.ArgumentStoreSeparation.frame
  check ``Verification.ArgumentStoreSeparation.of_separation
  check ``Verification.ArgumentStoreSeparation.prepend
  check ``Verification.ArgumentStoreSeparation.frame_length
  check ``Verification.ArgumentStoreSeparation.checkFrame_not_alias
  let env ← getEnv
  let project (decl : Name) : Bool := match env.getModuleIdxFor? decl with
    | some i => (`Verification).isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let lemmas := (Compiler.CSimp.ext.getState env).thmNames.toList.filter project
  if lemmas.isEmpty then throwError "no @[csimp] lemma of the project found"
  for decl in lemmas do check decl
