import Verification.Programs.TolerantFramesExitStructural
import Verification.Programs.TolerantFramesExitHeadExtraction
import Verification.Programs.TolerantFramesExitNonHeadExtraction
import Verification.Programs.TolerantFramesExitsYield
import Verification.Programs.TolerantFramesExitYieldCache
import Verification.Programs.TolerantFramesExitHeadChecks
import Verification.Programs.TolerantFramesExitRecords
import Verification.Programs.TolerantFramesExitExecution
import Verification.Programs.TolerantFramesExitTypeChecks
import Verification.Programs.TolerantFramesExitVacuity
import Verification.Programs.TolerantFramesDriverExitTrace
import Verification.Programs.TolerantFramesExitAux
import Verification.Programs.TolerantFramesMapNames
import Verification.Programs.SinglePassClose
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Compiler.CSimpAttr
import Verification.Source.Claims.Json
import Verification.Source.RequestCli
import Verification.Source.Claims.PassUnitObligations
import Verification.Source.Claims.PassUnitInterfaces
import Verification.Source.Claims.PassUnitSignatures
import Verification.Source.Claims.PassUnitCross
import Verification.Source.Claims.PassUnitWrapper
import Verification.Source.Claims.PassUnitMemberRun
import Verification.Source.Claims.PassUnitVerdict
import Verification.Types.StoreMapsBuiltins
import Verification.Source.Claims.PassUnitInit
import Verification.Semantics.ArgumentStoreRegions
import Verification.Semantics.FootprintNatives
import Verification.Programs.ArgumentPathTracking
import Verification.Programs.ArgumentRegionCertificates
import Verification.Semantics.TolerantFrames
import Verification.Programs.TolerantFramesRuns
import Verification.Programs.TolerantFramesNamed
import Verification.Semantics.TolerantFramesCells
import Verification.Programs.TolerantFramesInvocation
import Verification.Programs.TolerantFramesExamples
import Verification.Programs.TolerantFramesSteps
import Verification.Programs.TolerantFramesWrites
import Verification.Programs.TolerantFramesSelect
import Verification.Programs.TolerantFramesFootprint
import Verification.Programs.TolerantFramesElems
import Verification.Programs.TolerantFramesState
import Verification.Programs.TolerantFramesMaterialize
import Verification.Programs.TolerantFramesDelta
import Verification.Programs.TolerantFramesStore
import Verification.Programs.TolerantFramesEntry
import Verification.Programs.TolerantFramesMerge
import Verification.Programs.TolerantFramesModelLoop
import Verification.Programs.TolerantFramesModelTyped
import Verification.Programs.TolerantFramesModelRules
import Verification.Programs.TolerantFramesMergeHead
import Verification.Programs.TolerantFramesStoreOpsBelow
import Verification.Programs.TolerantFramesStepLinkSound
import Verification.Programs.TolerantFramesEdge
import Verification.Programs.TolerantFramesStepLinkReturns
import Verification.Programs.TolerantFramesGuarantee
import Verification.Programs.TolerantFramesStoreOpsEdge
import Verification.Programs.TolerantFramesNodeWalk
import Verification.Programs.TolerantFramesStoreOpsBelowNames
import Verification.Programs.TolerantFramesWalkReassign
import Verification.Programs.TolerantFramesWalkReassignNodes
import Verification.Programs.TolerantFramesWalkReassignCall
import Verification.Programs.TolerantFramesWalkReassignSelect
import Verification.Programs.TolerantFramesWalkReassignStep
import Verification.Programs.TolerantFramesWalkReassignWalk
import Verification.Programs.TolerantFramesRunSound
import Verification.Programs.TolerantFramesDriverWalk
import Verification.Programs.TolerantFramesDriverHeadsFuel
import Verification.Programs.TolerantFramesDriverSummaries
import Verification.Programs.TolerantFramesDriverRecords
import Verification.Programs.TolerantFramesDriverReached
import Verification.Programs.TolerantFramesWalkJoined
import Verification.Programs.TolerantFramesGuaranteeWalk
import Verification.Programs.TolerantFramesMergeBelow
import Verification.Programs.TolerantFramesMergeGuarded
import Verification.Programs.TolerantFramesMergeEntailed
import Verification.Programs.TolerantFramesMergeNear
import Verification.Programs.TolerantFramesMergeChecked
import Verification.Programs.TolerantFramesNodeBound
import Verification.Programs.TolerantFramesNodeReturns
import Verification.Programs.TolerantFramesNodeAsserted
import Verification.Programs.TolerantFramesComposeEdges
import Verification.Programs.TolerantFramesComposeShape
import Verification.Programs.TolerantFramesRegionalNode
import Verification.Programs.TolerantFramesRegionalRuns
import Verification.Programs.TolerantFramesNodeAsserts
import Verification.Programs.TolerantFramesNodeGoals
import Verification.Programs.TolerantFramesNodeCallFresh
import Verification.Programs.TolerantFramesComposeRunSound
import Verification.Programs.TolerantFramesNodeJoined
import Verification.Programs.TolerantFramesNodeYields
import Verification.Programs.TolerantFramesNodeYielded
import Verification.Programs.TolerantFramesNodeRefined
import Verification.Programs.TolerantFramesComposeYields
import Verification.Source.Claims.PassUnitRun
import Verification.Programs.TolerantFramesSinglePassSound
import Verification.Programs.TolerantFramesMergeExits
import Verification.Programs.TolerantFramesMergeNearRounds
import Verification.Programs.TolerantFramesExitTypes
import Verification.Programs.TolerantFramesExitTyped
import Verification.Programs.TolerantFramesExitChecks
import Verification.Programs.TolerantFramesExitFresh
import Verification.Programs.TolerantFramesDriverSetup

/-!
Acceptance rests on Lean's standard axioms alone. The build fails when any of
the following depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`
(`sorryAx`, or one the project declares):

- `SourceClaimJson.PassUnit.mode8Accepted_sound`, the acceptance theorem: a
  unit printed accepted at either of mode 8's print sites (the file's own
  check, `--verify-interface-stage 8`, and a module's in the interface stage,
  `--module-interface`) has every member of its group safe, of which every
  accepted function's safety is a consequence;
- the single pass's unit theorem at mode 8's verdict,
  `SourceClaimJson.PassUnit.passUnitVerdict_safe`, `passUnit_safe` and
  the wrapper, code-table, plan, linking and realization theorems it rests on,
  the file-level theorem `SourceClaimJson.PassUnit.passFile_safe` and the
  modules' linking theorems;
- the regional footprint's transport and composition, cell provenance, and the
  argument-store region composition, framing and stable separation theorems;
- the tolerant-frame development's admissibility, adequacy, modal-law and
  atom theorems (`Verification.TolerantFrames`);
- each `@[csimp]` lemma of the project's modules the verifier imports
  (`Verification.Source.RequestCli`, what `Main` imports): the compiled
  verifier runs a lemma's right-hand side in place of the definition the
  proofs reason about, so its equation is part of what acceptance uses.
-/

set_option maxRecDepth 4096 in
open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.SourceClaimJson.PassUnit.passUnitVerdict_safe
  check ``Verification.SourceClaimJson.PassUnit.passUnit_safe
  check ``Verification.SourceClaimJson.PassUnit.member_safe
  check ``Verification.SourceClaimJson.PassUnit.ordinary_requestSafe
  check ``Verification.SourceClaimJson.PassUnit.qualified_requestSafe
  check ``Verification.SourceClaimJson.PassUnit.codesAccepted_sound
  check ``Verification.SourceClaimJson.PassUnit.codesAccepted_guarantees
  check ``Verification.SourceClaimJson.PassUnit.codeSpec_of_guarantee
  check ``Verification.SourceClaimJson.PassUnit.footprint_of_bound
  check ``Verification.SourceClaimJson.PassUnit.footprint_of_fallback
  check ``Verification.SourceClaimJson.PassUnit.main_guarantee
  check ``Verification.SourceClaimJson.PassUnit.summaries_of_checked
  check ``Verification.SourceClaimJson.PassUnit.fragmentPlans_overStore
  check ``Verification.SourceClaimJson.PassUnit.fragmentPlans_modules
  check ``Verification.SourceClaimJson.PassUnit.withHeadFacts_overStore
  check ``Verification.SourceClaimJson.PassUnit.fragmentPlansCore_shape
  check ``Verification.SourceClaimJson.PassUnit.fragmentPlansCore_overStore
  check ``Verification.SourceClaimJson.PassUnit.fragmentPlansCore_modules
  check ``Verification.SourceClaimJson.PassUnit.closedUnits_closed
  check ``Verification.SourceClaimJson.PassUnit.link
  check ``Verification.SourceClaimJson.PassUnit.closedUnits_linked
  check ``Verification.SourceClaimJson.PassUnit.closedUnits_safe
  check ``Verification.SourceClaimJson.PassUnit.envOk_of_linked
  check ``Verification.SourceClaimJson.PassUnit.codeSpec_of_clauses
  check ``Verification.SourceClaimJson.PassUnit.closure_meets_below
  check ``Verification.SourceClaimJson.PassUnit.rowSpec_of_requestSafe
  check ``Verification.SourceClaimJson.PassUnit.rowSpec_of_clauses
  check ``Verification.SourceClaimJson.PassUnit.rowSpec_plain_of_promise
  check ``Verification.SourceClaimJson.PassUnit.promiseAdmits_result
  check ``Verification.SourceClaimJson.PassUnit.codeRun_of_clauses
  check ``Verification.SourceClaimJson.PassUnit.row_invoke_at
  check ``Verification.SourceClaimJson.PassUnit.safePostExc_and
  check ``Verification.CallEffects.Effect.post_take_row
  check ``Verification.CallEffects.Effect.ensures_frame
  check ``Verification.SourceClaimJson.PassUnit.codeBound_some
  check ``Verification.SourceClaimJson.PassUnit.captures_envOk
  check ``Verification.SourceClaimJson.PassUnit.approx_meets
  check ``Verification.SourceClaimJson.PassUnit.approx_captures_envOk
  check ``Verification.SourceClaimJson.PassUnit.approx_link
  check ``Verification.SourceClaimJson.PassUnit.approxEnv_value
  check ``Verification.SourceClaimJson.PassUnit.requestSafe_of_member
  check ``Verification.SourceClaimJson.PassUnit.closedUnits_selected_safe
  check ``Verification.SourceClaimJson.PassUnit.passFile_safe
  check ``Verification.SourceClaimJson.PassUnit.linkModules
  check ``Verification.SourceClaimJson.PassUnit.published_holds
  check ``Verification.SourceClaimJson.PassUnit.obligations_sound
  check ``Verification.SourceClaimJson.PassUnit.member_async
  check ``Verification.SourceClaimJson.PassUnit.codes_async
  check ``Verification.SourceClaimJson.PassUnit.outsideContracts_of_kinds
  check ``Verification.SourceClaimJson.PassUnit.standIns_vacuous
  check ``Verification.SourceClaimJson.PassUnit.passPlans_safe
  check ``Verification.SourceClaimJson.PassUnit.passGroupOver_safe
  check ``Verification.SourceClaimJson.PassUnit.interface_entry_meets
  check ``Verification.SourceClaimJson.PassUnit.entry_met
  check ``Verification.SourceClaimJson.PassUnit.established_met
  check ``Verification.SourceClaimJson.PassUnit.step_units_safe
  check ``Verification.SourceClaimJson.PassUnit.passFile_safe_kinds
  check ``Verification.SourceClaimJson.PassUnit.fragmentPlansFromInterfaces_overStore
  check ``Verification.SourceClaimJson.PassUnit.fragmentPlansWithModules_overStore
  check ``Verification.SourceClaimJson.PassUnit.withFalseStartFact_overStore
  check ``Verification.SourceClaimJson.PassUnit.passUnitCli_safe
  check ``Verification.StoreMaps.StoreMap.meaning_eq
  check ``Verification.StoreMaps.StoreMap.meaning_eq_of_mem
  check ``Verification.StoreMaps.StoreMap.denote_eq
  check ``Verification.StoreMaps.StoreMap.normalDenote_eq
  check ``Verification.StoreMaps.StoreMap.related_assign
  check ``Verification.StoreMaps.ordinary_allowed
  check ``Verification.SourceClaimJson.PassUnit.signatureAgrees_of_storeMap
  check ``Verification.StoreMaps.checkMap_sound
  check ``Verification.StoreMaps.matchStores_sound
  check ``Verification.StoreMaps.StoreMap.excOf_eq
  check ``Verification.StoreMaps.StoreMap.builtins_isSome
  check ``Verification.StoreMaps.matchStores_none_of_builtins
  check ``Verification.StoreMaps.matchStores_sound_builtins
  check ``Verification.StoreMaps.env_empty_agree
  check ``Verification.SourceClaimJson.PassUnit.graphOf_env
  check ``Verification.SourceClaimJson.PassUnit.storeMapAgrees_of_check
  check ``Verification.SourceClaimJson.PassUnit.signatureAgrees_of_checks
  check ``Verification.SourceClaimJson.PassUnit.signatureAgrees_of_rows
  check ``Verification.SourceClaimJson.PassUnit.moduleUnitId_inj
  check ``Verification.SourceClaimJson.PassUnit.entryRealized_of_step
  check ``Verification.SourceClaimJson.PassUnit.realized_of_established
  check ``Verification.SourceClaimJson.PassUnit.entries_realized
  check ``Verification.SourceClaimJson.PassUnit.established_of_provenance
  check ``Verification.SourceClaimJson.PassUnit.establishedSlots_of_chosen
  check ``Verification.SourceClaimJson.PassUnit.crossModule_safe
  check ``Verification.SourceClaimJson.PassUnit.rowRealized_spec
  check ``Verification.SourceClaimJson.PassUnit.layout_realizes
  check ``Verification.SourceClaimJson.PassUnit.receiverless_indices
  check ``Verification.SourceClaimJson.PassUnit.passGroup_members
  check ``Verification.SourceClaimJson.PassUnit.passGroupChecks_of_sound
  check ``Verification.SourceClaimJson.PassUnit.passGroupChecks
  check ``Verification.SourceClaimJson.PassUnit.refuseRows_plans
  check ``Verification.SourceClaimJson.PassUnit.refuseUnbound_plans
  check ``Verification.SourceClaimJson.PassUnit.passMember_sound
  check ``Verification.SourceClaimJson.PassUnit.codesInOrder_accepted
  check ``Verification.SourceClaimJson.PassUnit.init_asserted
  check ``Verification.Footprints.transport_sound
  check ``Verification.Footprints.Sep.sound
  check ``Verification.Footprints.Post.mono
  check ``Verification.Footprints.keep_across_call
  check ``Verification.CallEffects.Effect.within_iff_closed
  check ``Verification.CallEffects.Effect.within_closed
  check ``Verification.CallEffects.Effect.within_iff_regions
  check ``Verification.CallEffects.Effect.within_prefix
  check ``Verification.CallEffects.Effect.frameCovers_sound
  check ``Verification.Footprints.Closed.post_extra_any
  check ``Verification.Footprints.Post.compose
  check ``Verification.Footprints.Region.sub_mem
  check ``Verification.Footprints.CellsFrom.of_post
  check ``Verification.Footprints.ArgumentStoreRegionsWithin.iff_post
  check ``Verification.Footprints.ArgumentStoreRegionsWithin.trans
  check ``Verification.Footprints.StoreApart.stable_frame
  check ``Verification.Footprints.StablePath.frame
  check ``Verification.Footprints.StoreApart.stable_path_frame
  check ``Verification.GraphCode.ArgumentPathTracking.checkEntry_sound
  check ``Verification.GraphCode.ArgumentPathTracking.checkEdges_sound
  check ``Verification.GraphCode.ArgumentPathTracking.checkHandler_sound
  check ``Verification.GraphCode.ArgumentPathTracking.stableField_path
  check ``Verification.GraphCode.ArgumentPathTracking.read_stable
  check ``Verification.GraphCode.ArgumentPathTracking.checkEntryFields_sound
  check ``Verification.GraphCode.ArgumentPathTracking.read_now
  check ``Verification.GraphCode.ArgumentRegionGraph.checkRead_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.checkCopy_sound
  check ``Verification.PromiseCalls.regionFirst_kept
  check ``Verification.PromiseCalls.effectKept_holds
  check ``Verification.PromiseCalls.storeHeld_sound
  check ``Verification.HeapKnowledge.storeFollows_sound
  check ``Verification.HeapKnowledge.restateStores_holds
  check ``Verification.HeapKnowledge.indicesCheckWith_sound
  check ``Verification.HeapKnowledge.lowerAtoms_holds
  check ``Verification.KnowledgeExpand.released_holds
  check ``Verification.KnowledgeExpand.expandLinks_holds
  check ``Verification.HeapKnowledge.typeAtoms_sound
  check ``Verification.HeapExpressionRules.stableFirst_frame
  check ``Verification.Footprints.rebase_sound
  check ``Verification.Footprints.Post.compose_at
  check ``Verification.GraphCode.ArgumentPathTracking.StableNow.agree
  check ``Verification.GraphCode.ArgumentRegionGraph.nodeRebase_ok
  check ``Verification.GraphCode.ArgumentRegionGraph.nodeWithin_of_step
  check ``Verification.GraphCode.ArgumentRegionGraph.closedStep_ok
  check ``Verification.GraphCode.ArgumentRegionGraph.callStep_ok
  check ``Verification.GraphCode.ArgumentRegionGraph.writeStep_ok
  check ``Verification.ExpressionEffects.writeStep_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.firstRefusedNode_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.checkEntry_reassign
  check ``Verification.GraphCode.ArgumentRegionGraph.checkNodes_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.checkEntry_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.goto_bounded
  check ``Verification.GraphCode.ArgumentRegionFresh.alloc_fresh
  check ``Verification.GraphCode.ArgumentRegionFresh.cellAlloc_fresh
  check ``Verification.GraphCode.ArgumentRegionFresh.cellRead_fresh
  check ``Verification.GraphCode.ArgumentRegionFresh.freshWrite_cells
  check ``Verification.GraphCode.ArgumentRegionFresh.CellFresh.post
  check ``Verification.GraphCode.ArgumentRegionGraph.checkFresh_sound
  check ``Verification.GraphCode.edgesFresh_holds
  check ``Verification.GraphCode.handlerFresh_holds
  check ``Verification.TolerantFrames.Admissible.trans
  check ``Verification.TolerantFrames.Admissible.length_le
  check ``Verification.TolerantFrames.Admissible.stable_value
  check ``Verification.TolerantFrames.Admissible.readPath
  check ``Verification.TolerantFrames.run
  check ``Verification.TolerantFrames.run_normal
  check ``Verification.TolerantFrames.run_throw
  check ``Verification.TolerantFrames.safe_run
  check ``Verification.TolerantFrames.transition_det
  check ``Verification.TolerantFrames.graph_run
  check ``Verification.TolerantFrames.box_elim
  check ``Verification.TolerantFrames.box_and
  check ``Verification.TolerantFrames.box_mono
  check ``Verification.TolerantFrames.box_anti
  check ``Verification.TolerantFrames.action_le
  check ``Verification.TolerantFrames.action_le_closed
  check ``Verification.TolerantFrames.box_or
  check ``Verification.TolerantFrames.box_idem
  check ``Verification.TolerantFrames.invariant_iff_top
  check ``Verification.TolerantFrames.closed_rigid
  check ``Verification.TolerantFrames.elems_not_rigid
  check ``Verification.TolerantFrames.action_normal
  check ``Verification.TolerantFrames.action_throw
  check ``Verification.TolerantFrames.stable_rigid
  check ``Verification.TolerantFrames.action_throw_top
  check ``Verification.TolerantFrames.graph_safe
  check ``Verification.TolerantFrames.graph_safe_at
  check ``Verification.TolerantFrames.transfer
  check ``Verification.TolerantFrames.grow_write_judgment
  check ``Verification.TolerantFrames.loop_write_obligations
  check ``Verification.TolerantFrames.loop_back_edge
  check ``Verification.TolerantFrames.tolerant_frame
  check ``Verification.TolerantFrames.kept_box
  check ``Verification.TolerantFrames.grow
  check ``Verification.TolerantFrames.grow_path
  check ``Verification.TolerantFrames.field_write_keeps_bound
  check ``Verification.TolerantFrames.atomHolds_extend
  check ``Verification.TolerantFrames.atomHolds_heapFree
  check ``Verification.TolerantFrames.atomHolds_congr
  check ``Verification.TolerantFrames.named_set
  check ``Verification.TolerantFrames.named_keep_box
  check ``Verification.TolerantFrames.named_any_box
  check ``Verification.TolerantFrames.named_le_box
  check ``Verification.TolerantFrames.preserving_normal
  check ``Verification.TolerantFrames.preserving_throw
  check ``Verification.TolerantFrames.inspection_keeps
  check ``Verification.TolerantFrames.keepsCall_keeps
  check ``Verification.TolerantFrames.freshCall_keeps
  check ``Verification.TolerantFrames.keepsCall_frame
  check ``Verification.TolerantFrames.slotless_not_framed
  check ``Verification.TolerantFrames.listT_cells
  check ``Verification.TolerantFrames.cellsCtr_of_listT
  check ``Verification.TolerantFrames.storeCells_invariant
  check ``Verification.TolerantFrames.rootCells_of_storeCells
  check ``Verification.TolerantFrames.rootCells_box
  check ``Verification.TolerantFrames.storeCells_of_listT
  check ``Verification.TolerantFrames.rootCells_not_invariant
  check ``Verification.TolerantFrames.alloc_apart
  check ``Verification.TolerantFrames.growOne_keeps_store
  check ``Verification.TolerantFrames.apart_grow_keep
  check ``Verification.TolerantFrames.graph_step
  check ``Verification.TolerantFrames.graph_inv_run
  check ``Verification.TolerantFrames.invocation_done
  check ``Verification.TolerantFrames.invocation_raised
  check ``Verification.TolerantFrames.invocation_action
  check ``Verification.TolerantFrames.invocation_box
  check ``Verification.TolerantFrames.invocation_throw_action
  check ``Verification.TolerantFrames.bound_step
  check ``Verification.TolerantFrames.bound_step_fresh
  check ``Verification.TolerantFrames.adminClosed_bound
  check ``Verification.TolerantFrames.action_compose_at
  check ``Verification.TolerantFrames.rebaseOk_stable
  check ``Verification.TolerantFrames.box_idem_on
  check ``Verification.TolerantFrames.rigidOn_domain
  check ``Verification.TolerantFrames.path_mem_eq
  check ``Verification.TolerantFrames.path_rigid_on
  check ``Verification.TolerantFrames.pathLowerBound_iff
  check ``Verification.TolerantFrames.grow_path_fact
  check ``Verification.TolerantFrames.throw_nul_safe
  check ``Verification.TolerantFrames.handled_safe
  check ``Verification.TolerantFrames.escaping_checked
  check ``Verification.TolerantFrames.escaping_safe
  check ``Verification.TolerantFrames.escaping_raised
  check ``Verification.TolerantFrames.oneBits_safe
  check ``Verification.TolerantFrames.increment_judgment
  check ``Verification.TolerantFrames.increment_checked
  check ``Verification.TolerantFrames.pure_inspect
  check ``Verification.TolerantFrames.created_keeps
  check ``Verification.TolerantFrames.base_shape
  check ``Verification.TolerantFrames.base_keeps
  check ``Verification.TolerantFrames.elementsCall_keeps
  check ``Verification.TolerantFrames.requiresCall_keeps
  check ``Verification.TolerantFrames.callKeepsHeap_keeps
  check ``Verification.TolerantFrames.ordinary_run_base
  check ``Verification.TolerantFrames.withSubtyping_run_base
  check ``Verification.TolerantFrames.passPreserving_keeps
  check ``Verification.TolerantFrames.preserving_step_frame
  check ``Verification.TolerantFrames.pass_preserving_frame
  check ``Verification.TolerantFrames.atom_kept
  check ``Verification.TolerantFrames.named_kept_box
  check ``Verification.TolerantFrames.lowerBound_keptBy_grow
  check ``Verification.TolerantFrames.lowerBound_keptBy_field
  check ``Verification.TolerantFrames.safePost_grow
  check ``Verification.TolerantFrames.judgment_with_output
  check ``Verification.TolerantFrames.top_judgment
  check ``Verification.TolerantFrames.write_judgment
  check ``Verification.TolerantFrames.field_write_judgment
  check ``Verification.TolerantFrames.element_write_judgment
  check ``Verification.TolerantFrames.preserving_judgment
  check ``Verification.TolerantFrames.writing_frame
  check ``Verification.TolerantFrames.storeCells_of_arrayInvariant
  check ``Verification.TolerantFrames.passTreeOk_of_tree
  check ``Verification.TolerantFrames.requiresApp_term
  check ``Verification.TolerantFrames.requiresTree_term
  check ``Verification.TolerantFrames.checkedOutput_value_tree
  check ``Verification.TolerantFrames.select_value_eq
  check ``Verification.TolerantFrames.select_claim_term
  check ``Verification.TolerantFrames.select_call_none
  check ``Verification.TolerantFrames.passSteps_value
  check ``Verification.TolerantFrames.passSteps_sound
  check ``Verification.TolerantFrames.ordinary_select_eq
  check ``Verification.TolerantFrames.select_run
  check ``Verification.TolerantFrames.ordinary_select_sound
  check ``Verification.TolerantFrames.withSubtyping_select
  check ``Verification.TolerantFrames.ordinaryOver_run_base
  check ``Verification.TolerantFrames.passSteps_keeps
  check ``Verification.TolerantFrames.passPreserving_keeps_select
  check ``Verification.TolerantFrames.pass_preserving_frame_select
  check ``Verification.TolerantFrames.preserving_judgment_select
  check ``Verification.TolerantFrames.passTreeCheck_ok
  check ``Verification.TolerantFrames.passWholeCheck_ok
  check ``Verification.TolerantFrames.pass_select_run
  check ``Verification.TolerantFrames.pass_select_narrow
  check ``Verification.TolerantFrames.pass_select_whole
  check ``Verification.TolerantFrames.pass_select_sound
  check ``Verification.TolerantFrames.passPreserving_keeps_pass
  check ``Verification.TolerantFrames.pass_preserving_frame_pass
  check ``Verification.TolerantFrames.preserving_judgment_pass
  check ``Verification.TolerantFrames.passWrites_sound
  check ``Verification.TolerantFrames.selected_within_on
  check ``Verification.TolerantFrames.pass_within_normal
  check ``Verification.TolerantFrames.pass_within_throw
  check ``Verification.TolerantFrames.pass_within_entry
  check ``Verification.TolerantFrames.pass_write_judgment
  check ``Verification.TolerantFrames.keptBy_keptByElems
  check ``Verification.TolerantFrames.atom_keptByElems
  check ``Verification.TolerantFrames.named_keptByElems_box
  check ``Verification.TolerantFrames.elem_keptByElems_empty
  check ``Verification.TolerantFrames.every_keptBy_init
  check ``Verification.TolerantFrames.StateWF.fresh_result
  check ``Verification.TolerantFrames.forIn_idx
  check ``Verification.TolerantFrames.forIn_idx_bind
  check ``Verification.TolerantFrames.forIn_inv
  check ``Verification.TolerantFrames.atomHolds_canon
  check ``Verification.TolerantFrames.atomHolds_rename
  check ``Verification.TolerantFrames.mapM_mem
  check ``Verification.TolerantFrames.mem_keysOf
  check ``Verification.TolerantFrames.mem_valsOf
  check ``Verification.TolerantFrames.keys_insert
  check ``Verification.TolerantFrames.keys_erase
  check ``Verification.TolerantFrames.vals_insert
  check ``Verification.TolerantFrames.findD_vals
  check ``Verification.TolerantFrames.toList_eq
  check ``Verification.TolerantFrames.about_storeAll
  check ``Verification.TolerantFrames.toList_storeAll
  check ``Verification.TolerantFrames.vals_foldl
  check ``Verification.TolerantFrames.storeOk_of
  check ``Verification.TolerantFrames.addRaw_ok
  check ``Verification.TolerantFrames.remove_ok
  check ``Verification.TolerantFrames.foldl_remove_ok
  check ``Verification.TolerantFrames.addBound_ok
  check ``Verification.TolerantFrames.foldl_addBound_ok
  check ``Verification.TolerantFrames.add_ok
  check ``Verification.TolerantFrames.materialize_eq
  check ``Verification.TolerantFrames.selectedAtoms_whole
  check ``Verification.TolerantFrames.slotTable_get
  check ``Verification.TolerantFrames.aliasLinksOf_holds
  check ``Verification.TolerantFrames.derivedOf_holds
  check ``Verification.TolerantFrames.ofAtoms_eq
  check ``Verification.TolerantFrames.ofStep_mem
  check ``Verification.TolerantFrames.ofAtoms_holds
  check ``Verification.TolerantFrames.atomsOf_holds
  check ``Verification.TolerantFrames.table_named
  check ``Verification.TolerantFrames.materializeFrom_holds
  check ``Verification.TolerantFrames.materializeFrom_pairs
  check ``Verification.TolerantFrames.materializeFrom_table
  check ``Verification.TolerantFrames.stateHolds_materialize_whole
  check ``Verification.TolerantFrames.stateHolds_materialize
  check ``Verification.TolerantFrames.foldl_inv
  check ``Verification.TolerantFrames.selectRound_about
  check ``Verification.TolerantFrames.selectFrom_about
  check ``Verification.TolerantFrames.selectedFromIndex
  check ``Verification.TolerantFrames.stateHolds_stepKnowledge
  check ``Verification.TolerantFrames.applyDelta_eq
  check ``Verification.TolerantFrames.forIn_inv_bind
  check ``Verification.TolerantFrames.deltaRemove_sub
  check ``Verification.TolerantFrames.deltaRemove_ok
  check ``Verification.TolerantFrames.deltaAdd_ok
  check ``Verification.TolerantFrames.deltaRestate_ok
  check ``Verification.TolerantFrames.applyDelta_ok
  check ``Verification.TolerantFrames.applyDelta_preserving
  check ``Verification.TolerantFrames.inverse_foldl
  check ``Verification.TolerantFrames.inverse_get
  check ``Verification.TolerantFrames.passBack_ok
  check ``Verification.TolerantFrames.impliesOk_admissible
  check ``Verification.TolerantFrames.stateHolds_after
  check ``Verification.TolerantFrames.stateHolds_fresh_result
  check ``Verification.TolerantFrames.stateHolds_reused_name
  check ``Verification.TolerantFrames.stateHolds_copy
  check ``Verification.TolerantFrames.mapM_mem_fwd
  check ``Verification.TolerantFrames.atomHolds_rename_rev
  check ``Verification.TolerantFrames.rename_succ_total
  check ``Verification.TolerantFrames.applyDelta_writing
  check ``Verification.TolerantFrames.canon_canon
  check ``Verification.TolerantFrames.nodup_eraseDups
  check ``Verification.TolerantFrames.getD_foldl_insert
  check ``Verification.TolerantFrames.contains_foldl_insert
  check ``Verification.TolerantFrames.storeAll_live
  check ``Verification.TolerantFrames.storeAll_canon
  check ``Verification.TolerantFrames.addRaw_wf
  check ``Verification.TolerantFrames.remove_wf
  check ``Verification.TolerantFrames.foldl_remove_wf
  check ``Verification.TolerantFrames.addBound_wf
  check ``Verification.TolerantFrames.foldl_addBound_wf
  check ``Verification.TolerantFrames.add_wf
  check ``Verification.TolerantFrames.remove_sub
  check ``Verification.TolerantFrames.remove_absent
  check ``Verification.TolerantFrames.deltaRemove_wf
  check ``Verification.TolerantFrames.removedLeave
  check ``Verification.TolerantFrames.dropHeap_eq
  check ``Verification.TolerantFrames.dropStep_wf
  check ``Verification.TolerantFrames.foldl_dropStep
  check ``Verification.TolerantFrames.dropHeap_cover
  check ``Verification.TolerantFrames.handedSet_mem
  check ``Verification.TolerantFrames.applyDelta_dropHeap
  check ``Verification.TolerantFrames.entryRefusal_ok
  check ``Verification.TolerantFrames.union_holds
  check ``Verification.TolerantFrames.startGiven_holds
  check ``Verification.TolerantFrames.headEntry_start_names
  check ``Verification.TolerantFrames.storeOk_empty
  check ``Verification.TolerantFrames.storeWF_empty
  check ``Verification.TolerantFrames.headStore_ok
  check ``Verification.TolerantFrames.entry_stateHolds

set_option maxRecDepth 4096 in
open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.IndexWrites.index_safeInt
  check ``Verification.IndexWrites.boundedCells_sound
  check ``Verification.HeapExpressionRules.keptCells_holds
  check ``Verification.IndexWrites.growOutput_sound
  check ``Verification.PromiseCalls.withGrown_holds
  check ``Verification.TolerantFrames.index_int
  check ``Verification.TolerantFrames.integral_int
  check ``Verification.TolerantFrames.mergeEqAtoms_holds
  check ``Verification.TolerantFrames.zip_tail_eq
  check ``Verification.TolerantFrames.mergeEqual_holds
  -- the model-side supports (TolerantFramesModel*)
  check ``Verification.TolerantFrames.alloc_step
  -- The model rules of the note "Tolerant frames", which cites them: its
  -- atoms' axioms, its rules and its worked loop stated in the indexed model,
  -- or a counter-model where the note's statement needs a premise
  -- (Semantics/TolerantFrames, Programs/TolerantFramesModel*). Roots of
  -- their own, kept whether or not the verifier reaches them.
  -- (Dense)
  check ``Verification.TolerantFrames.dense
  -- (View)
  check ``Verification.TolerantFrames.view_box
  check ``Verification.TolerantFrames.viewStable_invariant
  check ``Verification.TolerantFrames.viewStable_of_typed
  check ``Verification.TolerantFrames.view_not_invariant
  -- (Init)
  check ``Verification.TolerantFrames.init_box
  check ``Verification.TolerantFrames.init_path
  -- (Rigid) and fresh(x)
  check ``Verification.TolerantFrames.stableAt_invariant
  check ``Verification.TolerantFrames.stableAt_of_stableField
  check ``Verification.TolerantFrames.stableAt_of_stableFirst
  check ``Verification.TolerantFrames.stableAt_cons
  check ``Verification.TolerantFrames.grow_path_typed
  check ``Verification.TolerantFrames.fresh_invariant
  -- well-formed states and law (c) from a typed state
  check ``Verification.TolerantFrames.storeCells_of_typed
  check ``Verification.TolerantFrames.storeCells_of_storeField
  check ``Verification.TolerantFrames.storeCells_of_builtins
  check ``Verification.TolerantFrames.apart_grow_keep_typed
  check ``Verification.TolerantFrames.valueClass_ok
  check ``Verification.TolerantFrames.storeClass_ok
  check ``Verification.TolerantFrames.action_le_valueClass
  -- Call
  check ``Verification.TolerantFrames.call_rule
  -- Alloc
  check ``Verification.TolerantFrames.alloc_post
  check ``Verification.TolerantFrames.alloc_apart_typed
  check ``Verification.TolerantFrames.apart_not_kept_fresh
  -- Seq-Eff
  check ``Verification.TolerantFrames.seq_eff
  check ``Verification.TolerantFrames.rebaseAll_labels
  check ``Verification.TolerantFrames.rebase_elems
  -- Fresh-Eff
  check ``Verification.TolerantFrames.fresh_eff
  check ``Verification.TolerantFrames.fresh_eff_bound
  check ``Verification.TolerantFrames.fresh_cells_not_erased
  -- Loop and Transfer: the worked loop of the note's example in full
  check ``Verification.TolerantFrames.loop_safe
  check ``Verification.TolerantFrames.loop_done
  check ``Verification.TolerantFrames.loop_no_raise
  check ``Verification.TolerantFrames.loop_checked
  check ``Verification.TolerantFrames.read_safe
  check ``Verification.TolerantFrames.write_safe
  check ``Verification.TolerantFrames.arrAt_invariant
  check ``Verification.TolerantFrames.alias_entry
  check ``Verification.TolerantFrames.alias_loop_safe
  -- Leg 8: the merge and forgetting names (TolerantFramesMerge*, TolerantFramesStoreOps*)
  check ``Verification.TolerantFrames.mergeState_state
  check ``Verification.TolerantFrames.mergeState_implies
  check ``Verification.TolerantFrames.mergeState_fresh
  check ``Verification.TolerantFrames.keepFirst_sub
  check ``Verification.TolerantFrames.keptAliasOf_eq
  check ``Verification.TolerantFrames.dropDerived_holds
  check ``Verification.TolerantFrames.drop_holds
  check ``Verification.TolerantFrames.drop_wf
  check ``Verification.TolerantFrames.slotsInv_step
  check ``Verification.TolerantFrames.mergeSlots_inv
  check ``Verification.TolerantFrames.slots_same
  check ``Verification.TolerantFrames.mergeVal_slots
  check ``Verification.TolerantFrames.mergeVal_rename
  check ``Verification.TolerantFrames.rename_key_below
  check ``Verification.TolerantFrames.remove_live
  check ``Verification.TolerantFrames.diffRemove_live
  check ``Verification.TolerantFrames.mergeCommon_live
  check ``Verification.TolerantFrames.renameEach_holds
  check ``Verification.TolerantFrames.OnPath.variants_ok
  check ``Verification.TolerantFrames.mergeMeet_inv
  check ``Verification.TolerantFrames.mergeMet0_wf
  check ``Verification.TolerantFrames.OnPath.met0_ok
  check ``Verification.TolerantFrames.OnPath.diffs_ok
  check ``Verification.TolerantFrames.normalize_vars
  check ``Verification.TolerantFrames.linear_weaken
  check ``Verification.TolerantFrames.boundsOf_get
  check ``Verification.TolerantFrames.weakestStep_cases
  check ``Verification.TolerantFrames.mergeBounds_inv
  check ``Verification.TolerantFrames.holds_sound
  check ``Verification.TolerantFrames.mergeEntailed_inv
  check ``Verification.TolerantFrames.mergeAddGuarded_inv
  check ``Verification.TolerantFrames.OnPath.bounds_ok
  check ``Verification.TolerantFrames.OnPath.guarded_ok
  check ``Verification.TolerantFrames.OnPath.fresh_ok
  check ``Verification.TolerantFrames.mergeImplies_ok
  check ``Verification.TolerantFrames.mergeState_wf
  check ``Verification.TolerantFrames.nodeObligations_mono
  check ``Verification.TolerantFrames.passPre_adminClosed
  check ``Verification.TolerantFrames.entries_of_traversed
  check ``Verification.TolerantFrames.start_passPre
  check ``Verification.TolerantFrames.headVal_start
  check ``Verification.TolerantFrames.headVal_fresh
  check ``Verification.TolerantFrames.headEntry_slots
  check ``Verification.TolerantFrames.headEntry_holds
  check ``Verification.TolerantFrames.canon_names
  check ``Verification.TolerantFrames.addRaw_below
  check ``Verification.TolerantFrames.remove_below
  check ``Verification.TolerantFrames.addBound_below
  check ``Verification.TolerantFrames.add_below
  -- Leg 9, the step and the edge: `checkedStep` read as its conditions and its step theorem
  check ``Verification.TolerantFrames.checkedStep_ok
  check ``Verification.TolerantFrames.stateHolds_pushed
  check ``Verification.TolerantFrames.stateHolds_throw
  check ``Verification.TolerantFrames.preserving_store
  check ``Verification.TolerantFrames.writing_store
  check ``Verification.TolerantFrames.preserving_judgment_two
  check ``Verification.TolerantFrames.stepExits_of
  check ``Verification.TolerantFrames.checkedStep_sound
  check ``Verification.TolerantFrames.drop_ok
  check ``Verification.TolerantFrames.edgeStore_observed
  check ``Verification.TolerantFrames.edgeStore_promote
  check ``Verification.TolerantFrames.stateHolds_handler
  check ``Verification.TolerantFrames.edgeTransfer_ok
  check ``Verification.TolerantFrames.edge_normal_sound
  check ``Verification.TolerantFrames.edge_handler_sound
  check ``Verification.TolerantFrames.freshImpl_ok
  check ``Verification.TolerantFrames.head_query_sound
  check ``Verification.TolerantFrames.plain_return
  check ``Verification.TolerantFrames.pass_return_ensures
  check ``Verification.TolerantFrames.pass_footprint_exits
  -- Leg 10, the walk and the guarantee: the run properties beside the graph invariant and each field
  check ``Verification.TolerantFrames.keeps_step
  check ``Verification.TolerantFrames.keeps_postExc
  check ``Verification.TolerantFrames.reached_pre
  check ``Verification.TolerantFrames.nodesChecked_of_walk
  check ``Verification.TolerantFrames.run_guarantee
  check ``Verification.TolerantFrames.deltaAdd_wf
  check ``Verification.TolerantFrames.deltaRestate_wf
  check ``Verification.TolerantFrames.applyDelta_wf
  check ``Verification.TolerantFrames.edgeStoreOf_wf
  check ``Verification.TolerantFrames.edgeTransfer_wf
  check ``Verification.TolerantFrames.edgeTransfer_width
  -- Leg 11: one obligation per node (TolerantFramesNode*)
  check ``Verification.TolerantFrames.safePostExc_trace
  check ``Verification.TolerantFrames.envOk_admissible
  check ``Verification.TolerantFrames.passPreT_adminClosed
  check ``Verification.TolerantFrames.run_sound_of_walk_typed
  check ``Verification.TolerantFrames.headsEntered_of_recorded
  check ``Verification.TolerantFrames.nodeObligations_of_parts
  check ``Verification.TolerantFrames.checkedStep_parts
  check ``Verification.TolerantFrames.stateHolds_freshImpl
  check ``Verification.TolerantFrames.edgeStore_normal
  check ``Verification.TolerantFrames.normal_edge_delivers
  check ``Verification.TolerantFrames.handler_edge_delivers
  check ``Verification.TolerantFrames.headEstablishes_of_edge
  check ``Verification.TolerantFrames.normalTarget_of_exits
  check ``Verification.TolerantFrames.exitDelivers_of_edge
  check ``Verification.TolerantFrames.exitDelivers_head
  check ``Verification.TolerantFrames.handlerDelivers_of_edge
  check ``Verification.TolerantFrames.stepEdgesSound_of
  check ``Verification.TolerantFrames.footprintCheck_sound
  check ``Verification.TolerantFrames.footprint_exits
  check ``Verification.TolerantFrames.returnCheck_plain
  check ``Verification.TolerantFrames.typedRead_optional_sound
  check ``Verification.TolerantFrames.namesBelow_step
  check ``Verification.TolerantFrames.width_step
  -- Leg 12: the facts' names below the counter (TolerantFramesStoreOps*), the merge, the reassignment
  check ``Verification.TolerantFrames.atom_rename_names
  check ``Verification.TolerantFrames.termDefined_named
  check ``Verification.TolerantFrames.eliminateLinear_named
  check ``Verification.TolerantFrames.eliminateIndices_named
  check ``Verification.TolerantFrames.restateReads_named
  check ``Verification.TolerantFrames.restateStores_named
  check ``Verification.TolerantFrames.dropDerived_below
  check ``Verification.TolerantFrames.keptAliasOf_named
  check ``Verification.TolerantFrames.drop_below
  check ``Verification.TolerantFrames.applyDelta_below
  check ``Verification.TolerantFrames.slotTable_keys
  check ``Verification.TolerantFrames.materialize_table_keys
  check ``Verification.TolerantFrames.inverse_keys
  check ``Verification.TolerantFrames.dropHeap_below
  check ``Verification.TolerantFrames.back_below
  check ``Verification.TolerantFrames.edgeStoreOf_below
  check ``Verification.TolerantFrames.mapNames_mem
  check ``Verification.TolerantFrames.edgeTransfer_below
  check ``Verification.TolerantFrames.headEntry_below
  check ``Verification.TolerantFrames.passBack_below
  check ``Verification.TolerantFrames.start_passPreT
  check ``Verification.TolerantFrames.codesSound_reassign
  -- Leg 13: the pass's checks at a reassignment (TolerantFramesWalkReassignChecks, TolerantFramesWalkReassignNodes)
  check ``Verification.TolerantFrames.footprintCheck_reassign
  check ``Verification.TolerantFrames.searching_reassign
  check ``Verification.TolerantFrames.unifiedInstance_reassign
  check ``Verification.TolerantFrames.searchReads_reassign
  check ``Verification.TolerantFrames.searchFree_reassign
  check ``Verification.TolerantFrames.matchRow_reassign
  check ``Verification.TolerantFrames.matchSig_reassign
  check ``Verification.TolerantFrames.matchRest_reassign
  check ``Verification.TolerantFrames.matchedInstance_reassign
  check ``Verification.TolerantFrames.instantiationUsing_reassign
  check ``Verification.TolerantFrames.instanceCandidates_reassign
  check ``Verification.TolerantFrames.rowInstances_reassign
  check ``Verification.TolerantFrames.subtypeSearch_reassign
  check ``Verification.TolerantFrames.subtypeUsing_reassign
  check ``Verification.TolerantFrames.foldl_map_state
  check ``Verification.TolerantFrames.emptyType_reassign
  check ``Verification.TolerantFrames.typeSets_reassign
  check ``Verification.TolerantFrames.onlyBoolean_reassign
  check ``Verification.TolerantFrames.onlyUndef_reassign
  check ``Verification.TolerantFrames.impossible_reassign
  check ``Verification.TolerantFrames.returnCheck_reassign
  check ``Verification.TolerantFrames.edgeStoreOf_reassign
  check ``Verification.TolerantFrames.entryRefusal_reassign
  -- Leg 14a: the step at a reassignment (TolerantFramesWalkReassignCall, TolerantFramesWalkReassignStep)
  check ``Verification.TolerantFrames.forIn_map_state
  check ``Verification.TolerantFrames.directCall_reassign
  check ``Verification.TolerantFrames.stepsSelect_reassign
  check ``Verification.TolerantFrames.ordinarySelect_reassign
  check ``Verification.TolerantFrames.passCheckerReassign_ordinary
  check ``Verification.TolerantFrames.passCheckerReassign_qualified
  check ``Verification.TolerantFrames.stepAccepted_reassign
  check ``Verification.TolerantFrames.stepChecked_of_step
  check ``Verification.TolerantFrames.stepChecked_reassign
  check ``Verification.TolerantFrames.stepChecked_parts
  check ``Verification.TolerantFrames.stepChecked_sound
  check ``Verification.TolerantFrames.nodeChecked_reassign
  check ``Verification.TolerantFrames.passCheckerReassign_lexical
  check ``Verification.TolerantFrames.headQuery_reassign
  check ``Verification.TolerantFrames.assertionQuery_reassign
  check ``Verification.TolerantFrames.edgeEvidenceChecked_reassign
  -- Leg 14c: the merge's remaining premises (TolerantFramesMergeBelow and the modules after it)
  check ``Verification.TolerantFrames.renameEach_names
  check ``Verification.TolerantFrames.mergeEqual_names
  check ``Verification.TolerantFrames.PredsBelow.store
  check ``Verification.TolerantFrames.mergeState_factsBelow
  check ``Verification.TolerantFrames.mergeState_below
  check ``Verification.TolerantFrames.guardReads_path
  check ``Verification.TolerantFrames.lowerRead_holds
  check ``Verification.TolerantFrames.lowerGuards_holds
  check ``Verification.TolerantFrames.check_holds
  check ``Verification.TolerantFrames.guardedHolds_of_path
  check ``Verification.TolerantFrames.termValue_value_undef
  check ``Verification.TolerantFrames.termValue_length_num
  check ``Verification.TolerantFrames.checked_bound_holds
  check ``Verification.TolerantFrames.OnPath.entailed_ok_checked
  check ``Verification.TolerantFrames.linearNearFuel_sound
  check ``Verification.TolerantFrames.linearNearSound_of_eq
  check ``Verification.TolerantFrames.linearNearFuelEq
  check ``Verification.TolerantFrames.slotsOfNames_get
  check ``Verification.TolerantFrames.atSlots_ok
  check ``Verification.TolerantFrames.meetImplications_ok_of_check
  check ``Verification.TolerantFrames.mergeImplies_ok_of_check
  check ``Verification.TolerantFrames.mergeState_holdsAt_checked
  check ``Verification.TolerantFrames.mergeState_holds_checked
  -- Leg 14b: the per-node hypotheses of the guarantee's fields (TolerantFramesNode*, TolerantFramesRegional*, TolerantFramesCompose*)
  check ``Verification.TolerantFrames.freshOk_recv
  check ``Verification.TolerantFrames.copyFresh
  check ``Verification.TolerantFrames.contKeeps_of
  check ``Verification.TolerantFrames.footprintKept_of
  check ``Verification.TolerantFrames.passTracked_names
  check ``Verification.TolerantFrames.returnCheck_ensures
  check ``Verification.TolerantFrames.returnsEnsured_of
  check ``Verification.TolerantFrames.assertion_query_sound
  check ``Verification.TolerantFrames.edgeEvidenceChecked_env
  check ``Verification.TolerantFrames.checkedEdge_env
  check ``Verification.TolerantFrames.start_entered_passPreT
  check ``Verification.TolerantFrames.branchShape_of
  check ``Verification.TolerantFrames.nodeShape_of
  check ``Verification.GraphCode.ArgumentRegionGraph.checkNode_sound
  check ``Verification.GraphCode.ArgumentRegionGraph.checkNode_mono
  check ``Verification.GraphCode.ArgumentRegionGraph.meet_sub
  -- Leg 15b: the node obligations at every continuation, the regional check along a run, the stated assertions, the guard goals, a call's fresh result
  check ``Verification.TolerantFrames.ofNode_flags
  -- Leg 16: the graph theorem in the unit lane's statement (TolerantFramesGuaranteeTarget, TolerantFramesRunSound)
  check ``Verification.TolerantFrames.stepEdgesSound_of_checked
  check ``Verification.TolerantFrames.transitions_of_reachesIn
  check ``Verification.TolerantFrames.GraphGuarantee.toTarget
  check ``Verification.TolerantFrames.mergeState_reassign
  check ``Verification.TolerantFrames.Traversed.reassign
  check ``Verification.TolerantFrames.scope_reassign
  check ``Verification.TolerantFrames.StartEntered.entered
  check ``Verification.TolerantFrames.passPreU_adminClosed
  check ``Verification.TolerantFrames.nodesKeep_anti
  check ``Verification.TolerantFrames.PassWalkSound.start
  check ``Verification.TolerantFrames.checkEntryFields_reassign
  check ``Verification.TolerantFrames.contKeeps_regionX
  check ``Verification.TolerantFrames.regionsKept_of
  check ``Verification.TolerantFrames.regionalTyped_of_tree
  check ``Verification.TolerantFrames.regionNodeEntry_of
  check ``Verification.TolerantFrames.regionX_start
  check ``Verification.TolerantFrames.nodesChecked_stable
  check ``Verification.TolerantFrames.passPreA_adminClosed
  check ``Verification.TolerantFrames.nodesChecked_of_walkA
  check ``Verification.TolerantFrames.holds_of_assertsAt
  check ``Verification.TolerantFrames.holds_of_indices_append
  check ``Verification.TolerantFrames.assertsAt_of_edge
  check ``Verification.TolerantFrames.assertsAt_of_head
  check ``Verification.TolerantFrames.assertsAt_start
  check ``Verification.TolerantFrames.exitDeliversA_of
  check ``Verification.TolerantFrames.edgeFacts_holds
  check ``Verification.TolerantFrames.returnWithin_sound
  check ``Verification.TolerantFrames.returnGuard_of_check
  check ``Verification.TolerantFrames.returnAssert_of_check
  check ``Verification.TolerantFrames.slot_start
  check ``Verification.TolerantFrames.passHeld_argument
  check ``Verification.TolerantFrames.goalHolds_at
  check ``Verification.TolerantFrames.returnOk_of_check
  check ``Verification.TolerantFrames.goalHolds_of_return
  check ``Verification.TolerantFrames.callFresh_of_checked
  -- Leg 17a: the per-node hypotheses of run_sound from the pass's checks (TolerantFramesNode*, TolerantFramesCompose*)
  check ``Verification.TolerantFrames.passOutFreshChecked_cases
  check ``Verification.TolerantFrames.passOutFreshChecked_reassign
  check ``Verification.TolerantFrames.BoundChecked.reassign
  check ``Verification.TolerantFrames.ReturnChecked.reassign
  check ``Verification.TolerantFrames.joinedAt_of_exit
  check ``Verification.TolerantFrames.SafePostExc.conj_post
  check ``Verification.TolerantFrames.checkedYields_follows
  check ``Verification.TolerantFrames.stepYields_judgment
  check ``Verification.TolerantFrames.exitDeliversY_of_edge
  check ``Verification.TolerantFrames.nodeObligations_of_partsY
  check ``Verification.TolerantFrames.stepEdgesSound_of_yields
  check ``Verification.TolerantFrames.regionalTyped_copy
  -- Leg 18a: the per-node side (TolerantFramesNode*, TolerantFramesCompose*)
  check ``Verification.TolerantFrames.yieldsJudged_of_follows
  check ``Verification.PromiseCalls.promiseCall_yields_local
  check ``Verification.PromiseCalls.promiseCall_yields_checked
  check ``Verification.TolerantFrames.slotImplOf_mem
  check ``Verification.TolerantFrames.slotImplOf_ok
  check ``Verification.TolerantFrames.slotImplOf_entry
  check ``Verification.TolerantFrames.yieldsOk_passReturnYields
  check ``Verification.TolerantFrames.yieldsJudged_of_promise
  check ``Verification.TolerantFrames.yieldsJudged_nil
  check ``Verification.TolerantFrames.promiseDerivChecked_of
  check ``Verification.TolerantFrames.yieldsJudged_of_checked
  check ``Verification.TolerantFrames.goalHolds_of_returnY
  check ``Verification.TolerantFrames.passShapeCheck'_reassign
  check ``Verification.TolerantFrames.nodup_of_eraseDups
  check ``Verification.TolerantFrames.byLabel_size
  check ``Verification.TolerantFrames.byLabel_cons
  check ``Verification.TolerantFrames.byLabel_of_nodup
  check ``Verification.TolerantFrames.assertionsLabelled_of_checked
  check ``Verification.TolerantFrames.setup_labels
  check ``Verification.TolerantFrames.setup_of_walk
  check ``Verification.TolerantFrames.labelsChecked
  check ``Verification.TolerantFrames.truthy_arm
  check ``Verification.TolerantFrames.passRefined_env
  check ``Verification.TolerantFrames.checkedEdge_env_none
  check ``Verification.TolerantFrames.refinedEdge_env
  check ``Verification.TolerantFrames.exitJoinedY
  check ``Verification.TolerantFrames.exitDeliversAJ_of
  check ``Verification.TolerantFrames.nodeYielded_of_checks
  check ``Verification.TolerantFrames.footprintKept_of_walk
  check ``Verification.TolerantFrames.returnsEnsured_of_walk
  check ``Verification.TolerantFrames.run_sound_checked
  check ``Verification.TolerantFrames.run_traversedC
  check ``Verification.TolerantFrames.run_sound_pass

  -- Leg 17b: the walk side of the graph theorem (TolerantFramesMergeExits, TolerantFramesMergeNearRounds)
  check ``Verification.TolerantFrames.entry_of_edge
  check ``Verification.TolerantFrames.joined_of_exit
  check ``Verification.TolerantFrames.entries_of_traversedJ
  check ``Verification.TolerantFrames.nearRound_progress
  check ``Verification.TolerantFrames.nearLoop_stable
  check ``Verification.TolerantFrames.linearNearFuel_rounds
  -- Leg 18b: the driver's record read as the walk, a merge's joined implications on the exits, the loop heads (TolerantFramesDriver*, TolerantFramesMergeWritten, TolerantFramesWalk*)
  check ``Verification.TolerantFrames.withWritten_holds
  check ``Verification.TolerantFrames.withWritten_wf
  check ``Verification.TolerantFrames.TraversedA.reassign
  check ``Verification.TolerantFrames.entry_of_edgeA
  check ``Verification.TolerantFrames.passPreA_of_edgeAJ
  check ``Verification.TolerantFrames.drives_of_drive
  check ``Verification.TolerantFrames.Drives.queue
  check ``Verification.TolerantFrames.Drives.inv
  check ``Verification.TolerantFrames.walk_of_accepts'
  check ``Verification.TolerantFrames.walk_of_accepts
  check ``Verification.TolerantFrames.ofPass_heads
  check ``Verification.TolerantFrames.run_traversedA
  check ``Verification.TolerantFrames.stepEdgesSound_of_checkedAt
  check ``Verification.TolerantFrames.NodeMeaning.withJoined
  check ``Verification.TolerantFrames.nodesChecked_of_walkJ
  check ``Verification.TolerantFrames.FramesOk.mono
  check ``Verification.TolerantFrames.dfsStep_inv
  check ``Verification.TolerantFrames.dfsLoop_inv
  check ``Verification.TolerantFrames.dfsInit_inv
  check ``Verification.TolerantFrames.Path.rank_lt
  check ``Verification.TolerantFrames.dfs_cuts
  check ``Verification.TolerantFrames.loopHeads_cuts
  check ``Verification.TolerantFrames.HeadsCutCycles.mono
  check ``Verification.TolerantFrames.passHeads_cuts
  let env ← getEnv
  let project (decl : Name) : Bool := match env.getModuleIdxFor? decl with
    | some i => (`Verification).isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let lemmas := (Compiler.CSimp.ext.getState env).thmNames.toList.filter project
  if lemmas.isEmpty then throwError "no @[csimp] lemma of the project found"
  for decl in lemmas do check decl

-- The graph proof's walk and per-node theorems (Leg 19b), in a second command
-- so that one command's compilation stays within its limits.
set_option maxRecDepth 4096 in
open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  -- Leg 19b: the walk's premises from the driver (TolerantFramesDriverHeadsFuel)
  check ``Verification.TolerantFrames.zeroWeight_upd
  check ``Verification.TolerantFrames.dfsStep_measure
  check ``Verification.TolerantFrames.dfsLoop_ends
  check ``Verification.TolerantFrames.dfsInit_measure
  check ``Verification.TolerantFrames.dfsLoop_init_ends
  check ``Verification.TolerantFrames.dfsStep_clear
  check ``Verification.TolerantFrames.dfsLoop_clear
  check ``Verification.TolerantFrames.dfsInit_clear
  check ``Verification.TolerantFrames.walkStopsRefuse
  check ``Verification.TolerantFrames.keep_prefix
  check ``Verification.TolerantFrames.Drives.keeps
  check ``Verification.TolerantFrames.drive_stop_keeps
  check ``Verification.TolerantFrames.setup_answers
  check ``Verification.TolerantFrames.visitsKeepSummaries
  check ``Verification.TolerantFrames.walk_keeps
  check ``Verification.TolerantFrames.runKeepsSummaries
  check ``Verification.TolerantFrames.filter_eq_of_le
  check ``Verification.TolerantFrames.filter_flip
  check ``Verification.TolerantFrames.sum_drop
  check ``Verification.TolerantFrames.RecInv.all_visited
  check ``Verification.TolerantFrames.RecInv.visited_of_incoming
  check ``Verification.TolerantFrames.recordSound_of_inv
  check ``Verification.TolerantFrames.Settled.frame
  check ``Verification.TolerantFrames.recInv_visit
  check ``Verification.TolerantFrames.walk_inv
  check ``Verification.TolerantFrames.recordsSound_of
  check ``Verification.TolerantFrames.recordsChecked_of
  check ``Verification.TolerantFrames.passLiveHandler_toList
  check ``Verification.TolerantFrames.boundChecked_of_bounded
  check ``Verification.TolerantFrames.nodePassChecked_of
  check ``Verification.TolerantFrames.visit_ok
  check ``Verification.TolerantFrames.visitResult_labels
  check ``Verification.TolerantFrames.visitResult_size
  check ``Verification.TolerantFrames.visitResult_visits
  check ``Verification.TolerantFrames.visitsRecord_of
  check ``Verification.TolerantFrames.exitTypes_core
  check ``Verification.TolerantFrames.assertionExit_core
  check ``Verification.TolerantFrames.headExit_core
  check ``Verification.TolerantFrames.pushExit_fields
  check ``Verification.TolerantFrames.exitStep_effect
  check ``Verification.TolerantFrames.ExitsFold.cons
  check ``Verification.TolerantFrames.exitsFold_of
  check ``Verification.TolerantFrames.visitExits_fold
  check ``Verification.TolerantFrames.exitLabels_ofNode
  check ``Verification.TolerantFrames.visitEntry_merge
  check ``Verification.TolerantFrames.visitsRest_of
  check ``Verification.TolerantFrames.stepRun_ok
  check ``Verification.TolerantFrames.visitStep_ok
  check ``Verification.TolerantFrames.checkedStep_fresh
  check ``Verification.TolerantFrames.entryStart_fresh
  check ``Verification.TolerantFrames.stepFresh
  check ``Verification.TolerantFrames.pushOk_of_exit
  check ``Verification.TolerantFrames.withWritten_below
  check ``Verification.TolerantFrames.headEntry_wf
  check ``Verification.TolerantFrames.checkedStep_store
  check ``Verification.TolerantFrames.entryStart_cases
  check ``Verification.TolerantFrames.entryStart_ok
  check ``Verification.TolerantFrames.withStated_ok
  check ``Verification.TolerantFrames.visitEntry_ok
  check ``Verification.TolerantFrames.visitStep_thrown
  check ``Verification.TolerantFrames.ofNode_handler
  check ``Verification.TolerantFrames.exitsPushOk_of
  check ``Verification.TolerantFrames.dfsStep_seen
  check ``Verification.TolerantFrames.dfsLoop_seen
  check ``Verification.TolerantFrames.dfs_closed
  check ``Verification.TolerantFrames.dfsLoop_init_start
  check ``Verification.TolerantFrames.dfsLoop_init_closed
  check ``Verification.TolerantFrames.succCount_nodeSucc
  check ``Verification.TolerantFrames.dfsFuel_ge
  check ``Verification.TolerantFrames.loopHeadsWalk_ends
  check ``Verification.TolerantFrames.loopHeadsRun_ended
  check ``Verification.TolerantFrames.loopHeadsWalk_clear
  check ``Verification.TolerantFrames.loopHeads_heads
  check ``Verification.TolerantFrames.loopHeads_reached
  check ``Verification.TolerantFrames.loopHeads_reached_size
  check ``Verification.TolerantFrames.loopHeads_closed
  check ``Verification.TolerantFrames.filter_id_length
  check ``Verification.TolerantFrames.envFacts_of_loopHeads
  check ``Verification.TolerantFrames.orderedSuffix_down
  check ``Verification.TolerantFrames.foldl_push_size
  check ``Verification.TolerantFrames.mapNames_length
  check ``Verification.TolerantFrames.derivChecked_reassign
  check ``Verification.TolerantFrames.promiseDerivChecked_reassign
  check ``Verification.TolerantFrames.checkedYields_reassign
  check ``Verification.TolerantFrames.NodeYieldChecks.reassign
  check ``Verification.TolerantFrames.nodesYield_of
  check ``Verification.TolerantFrames.checkNode_reassign
  check ``Verification.TolerantFrames.regionalDerivChecked_reassign
  check ``Verification.TolerantFrames.regionsTyped_of_tree
  check ``Verification.TolerantFrames.regionsHeld_of
  -- Successful visits settle their recorded node, start and entry.
  check ``Verification.TolerantFrames.renamedImplication_names
  check ``Verification.TolerantFrames.headEntry_impNames
  check ``Verification.TolerantFrames.mergeState_impNames
  check ``Verification.TolerantFrames.entryStart_impBelow
  check ``Verification.TolerantFrames.visitEntry_names
  check ``Verification.TolerantFrames.implArrayBelow_modify
  check ``Verification.TolerantFrames.edgeTransfer_impBelow
  check ``Verification.TolerantFrames.freshImpl_below
  check ``Verification.TolerantFrames.exitStep_impBelow
  check ``Verification.TolerantFrames.exitsFold_impBelow
  check ``Verification.TolerantFrames.visitExits_impBelow
  check ``Verification.TolerantFrames.EnvFacts.context
  check ``Verification.TolerantFrames.VisitParts.entryNames
  check ``Verification.TolerantFrames.visitsImplications
  check ``Verification.TolerantFrames.visitResult_record
  check ``Verification.TolerantFrames.ofPass_visitRecord
  check ``Verification.TolerantFrames.visitStart_entered
  check ``Verification.TolerantFrames.zip_map_fst_eq
  check ``Verification.TolerantFrames.entryStart_incoming
  check ``Verification.TolerantFrames.visitEntry_settled
  check ``Verification.TolerantFrames.visitCheck_true
  check ``Verification.TolerantFrames.stepRun_shape
  check ``Verification.TolerantFrames.visitStep_checks
  check ``Verification.TolerantFrames.returnOk_check
  check ``Verification.TolerantFrames.stepYields_kept
  check ``Verification.TolerantFrames.visitStep_yields
  check ``Verification.TolerantFrames.StepChecked.summaries
  check ``Verification.TolerantFrames.visitStep_node
  check ``Verification.TolerantFrames.visitsSettle_of
  check ``Verification.TolerantFrames.differing_eq
  check ``Verification.TolerantFrames.differing_cover
  check ``Verification.TolerantFrames.foldl_flag
  check ``Verification.TolerantFrames.diffSubtypes_pairs
  check ``Verification.TolerantFrames.mixed_fold
  check ``Verification.TolerantFrames.WalkExtends.refl
  check ``Verification.TolerantFrames.WalkExtends.trans
  check ``Verification.TolerantFrames.WalkExtends.incoming_mem
  check ``Verification.TolerantFrames.WalkExtends.merge_mem
  check ``Verification.TolerantFrames.WalkExtends.edge_mem
  check ``Verification.TolerantFrames.modify_cons_suffix
  check ``Verification.TolerantFrames.pushExit_mergeGrowth
  check ``Verification.TolerantFrames.exitStep_mergeGrowth
  check ``Verification.TolerantFrames.exitsFold_mergeGrowth
  check ``Verification.TolerantFrames.visitExits_mergeGrowth
  check ``Verification.TolerantFrames.visitExits_extends
  check ``Verification.TolerantFrames.exitsFold_extends
  check ``Verification.TolerantFrames.exitsFold_checked
  check ``Verification.TolerantFrames.visitExits_checked
  check ``Verification.TolerantFrames.yieldsAtSlots_ok
  check ``Verification.TolerantFrames.visitStep_outFresh
  check ``Verification.TolerantFrames.passOutFreshChecked_fresh
  check ``Verification.TolerantFrames.visitEntry_here
  check ``Verification.TolerantFrames.cursor_get
  check ``Verification.TolerantFrames.cursor_fold
  check ``Verification.TolerantFrames.mapNames_some
  check ``Verification.TolerantFrames.orderedSuffix_run
  check ``Verification.TolerantFrames.mapNamesSound_of_lt
  check ``Verification.TolerantFrames.yieldsOk_atSlots
  check ``Verification.TolerantFrames.outFreshOf_eq
  check ``Verification.TolerantFrames.subtypesPass_of
  check ``Verification.TolerantFrames.edgeFound_of_checked
  check ``Verification.TolerantFrames.mixedOf_mixedContext
  check ``Verification.TolerantFrames.ExitTyped.reassign
  check ``Verification.TolerantFrames.edgeFound_env
  check ``Verification.TolerantFrames.ExitTyped.env
  check ``Verification.TolerantFrames.HereEmpty.reassign
  check ``Verification.TolerantFrames.hereEmpty_false
  check ``Verification.TolerantFrames.vacuous_false
  check ``Verification.TolerantFrames.slotsNamed_tail
  check ``Verification.TolerantFrames.NonHeadExitChecked.reassign
  check ``Verification.TolerantFrames.nonHeadExit_delivers
  check ``Verification.TolerantFrames.HeadExitChecked.reassign
  check ``Verification.TolerantFrames.headExit_delivers
  check ``Verification.TolerantFrames.SubtypesPass.reassign
  check ``Verification.TolerantFrames.EdgeFound.reassign
  check ``Verification.TolerantFrames.HandlerExitChecked.reassign
  check ``Verification.TolerantFrames.handlerExit_delivers
  check ``Verification.TolerantFrames.IncomingRecorded.mem
  check ``Verification.TolerantFrames.MergeRecorded.mem
  check ``Verification.TolerantFrames.ExitChecks.site_of_trace
  check ``Verification.TolerantFrames.ExitChecks.assemble
  check ``Verification.TolerantFrames.nodeExitsYF_of_checks

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.TolerantFrames.safePostExc_trace_lt
  check ``Verification.TolerantFrames.nodeObligations_marked
  check ``Verification.TolerantFrames.NodeExitsChecked.reassign
  check ``Verification.TolerantFrames.nodeExitsY_of_checks
  check ``Verification.TolerantFrames.exitsYields_source
  check ``Verification.TolerantFrames.exitTypes_checked
  check ``Verification.TolerantFrames.assertionExit_checked
  check ``Verification.TolerantFrames.exitUnsatAnswer_sound
  check ``Verification.TolerantFrames.visitEntry_hereEmpty
  check ``Verification.TolerantFrames.CachedVacuity.set
  check ``Verification.TolerantFrames.exitTypes_unsat
  check ``Verification.TolerantFrames.headExit_unsat
  check ``Verification.TolerantFrames.assertionExit_unsat
  check ``Verification.TolerantFrames.exitStep_cachedVacuity
  check ``Verification.TolerantFrames.exitsFold_cachedVacuity
  check ``Verification.TolerantFrames.visitExits_cachedVacuity
  check ``Verification.TolerantFrames.cachedVacuity_empty
  check ``Verification.TolerantFrames.keepSummaries_self
  check ``Verification.TolerantFrames.keepSummaries_sound
  check ``Verification.TolerantFrames.setup_ok
  check ``Verification.TolerantFrames.setupGiven_get
  check ``Verification.TolerantFrames.getElem!_eq_getD_none
  check ``Verification.TolerantFrames.SetupOk.startClaim
  check ``Verification.TolerantFrames.SetupOk.envFacts
  check ``Verification.TolerantFrames.inDeg_inner
  check ``Verification.TolerantFrames.zipIdx_range
  check ``Verification.TolerantFrames.inDegrees_get
  check ``Verification.TolerantFrames.visB_replicate
  check ``Verification.TolerantFrames.SetupOk.recInv
  check ``Verification.TolerantFrames.setupRecords_of
  check ``Verification.TolerantFrames.sumsPrefix_keep
  check ``Verification.TolerantFrames.stepChecked_of_final
  check ``Verification.TolerantFrames.sumsPrefix_fold
  check ``Verification.TolerantFrames.stepYields_prefix
  check ``Verification.TolerantFrames.returnRun_prefix
  check ``Verification.TolerantFrames.stepYields_prefix_of
  check ``Verification.TolerantFrames.visitStep_prefix
  check ``Verification.TolerantFrames.exitsYields_prefix
  check ``Verification.TolerantFrames.diffSubtypes_prefix
  check ``Verification.TolerantFrames.impliesHeld_prefix
  check ``Verification.TolerantFrames.headImplies_prefix
  check ``Verification.TolerantFrames.keepSummaries_table
  check ``Verification.TolerantFrames.checkedStep_prefix
  check ``Verification.TolerantFrames.visitStep_input_prefix
  check ``Verification.TolerantFrames.exitsFold_prefix
  check ``Verification.TolerantFrames.visitExits_prefix
  check ``Verification.TolerantFrames.visitStepPrefix_of_exitStep
  check ``Verification.TolerantFrames.subtypeAnswersAll
  check ``Verification.TolerantFrames.regionalTyped_of_requires
  check ``Verification.TolerantFrames.regionalTyped_of_derivation
  check ``Verification.TolerantFrames.regionalAt_checks
  check ``Verification.TolerantFrames.visitResult_region
  check ``Verification.TolerantFrames.subtypeAnswersSound
  check ``Verification.TolerantFrames.exitStep_mappingWidth
  check ``Verification.TolerantFrames.exitsFold_mappingWidth
  check ``Verification.TolerantFrames.exitsWidth
  check ``Verification.TolerantFrames.exitTypes_exits
  check ``Verification.TolerantFrames.headExit_exits
  check ``Verification.TolerantFrames.assertionExit_exits
  check ``Verification.TolerantFrames.exitStep_record
  check ``Verification.TolerantFrames.exitsFold_records_prefix
  check ``Verification.TolerantFrames.exitsFold_records_checked
  check ``Verification.TolerantFrames.visitExits_records
  check ``Verification.SourceClaimJson.PassUnit.passUnitVerdict_safe_run
  check ``Verification.SourceClaimJson.PassUnit.passUnitVerdict_sound
  check ``Verification.SourceClaimJson.PassUnit.freshModuleVerdict_sound
  check ``Verification.SourceClaimJson.PassUnit.mode8Accepted_sound

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.TolerantFrames.ExitYieldSource.trans
  check ``Verification.TolerantFrames.exitTypes_yields_source
  check ``Verification.TolerantFrames.headExit_yields
  check ``Verification.TolerantFrames.assertionExit_yields
  check ``Verification.TolerantFrames.exitStep_yields_source
  check ``Verification.TolerantFrames.exitsFold_records_yields
  check ``Verification.TolerantFrames.visitExits_records_yields
  check ``Verification.TolerantFrames.impliesHeld_checked
  check ``Verification.TolerantFrames.headImplies_checked
  check ``Verification.TolerantFrames.headExit_checked
  check ``Verification.TolerantFrames.exitTypes_handler_checked
  check ``Verification.TolerantFrames.exitsYield_of_checks
  check ``Verification.TolerantFrames.StepChecked.fresh_le
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_fresh
  check ``Verification.TolerantFrames.ExitChecks.Site.kept_yields
  check ``Verification.TolerantFrames.ExitChecks.Site.ysA_eq
  check ``Verification.TolerantFrames.ExitChecks.Site.source_eq
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_here
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_widths
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_thrownBelow
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_handler

-- Head and handler exit extraction.
-- Non-head exit extraction and the incoming-array witnesses it consumes.

  check ``Verification.TolerantFrames.mixedContext_prefix
  check ``Verification.TolerantFrames.exitTypes_prefix
  check ``Verification.TolerantFrames.headExit_prefix
  check ``Verification.TolerantFrames.assertionExit_answers
  check ``Verification.TolerantFrames.exitStepPrefix
  check ``Verification.TolerantFrames.separation_union_holds
  check ``Verification.TolerantFrames.regionNodeEntry_checked
  check ``Verification.TolerantFrames.stepChecked_safe
  check ``Verification.TolerantFrames.regionalTyped_of_step
  check ``Verification.TolerantFrames.regionalAt_start
  check ``Verification.TolerantFrames.regionsRecorded_of_visitTables
  check ``Verification.TolerantFrames.regionsTyped_of_visitTables
  check ``Verification.TolerantFrames.regionalStepFacts_of_relations

  check ``Verification.TolerantFrames.expandedLinks_recover
  check ``Verification.TolerantFrames.regionalJoin_right
  check ``Verification.TolerantFrames.regionalLinks_recover
  check ``Verification.TolerantFrames.separation_union_right
  check ``Verification.TolerantFrames.separation_norm_partners
  check ``Verification.TolerantFrames.materialize_separation_partners
  check ``Verification.TolerantFrames.visitStep_separation_partners
  check ``Verification.TolerantFrames.exitTypes_regional
  check ``Verification.TolerantFrames.headExit_regional
  check ``Verification.TolerantFrames.assertionExit_regional
  check ``Verification.TolerantFrames.exitStep_regional
  check ``Verification.TolerantFrames.exitsFold_regional
  check ``Verification.TolerantFrames.visitExits_regionalCheck
  check ``Verification.TolerantFrames.RecInv.regionalWitness
  check ``Verification.TolerantFrames.recordedRegion_at

  check ``Verification.TolerantFrames.visitExits_regional_prefix
  check ``Verification.TolerantFrames.visitExits_answers_prefix
  check ``Verification.TolerantFrames.checkedWalk_final
  check ``Verification.TolerantFrames.checkedWalk_nodeAlignment
  check ``Verification.TolerantFrames.RecInv.regionalWitnessSound
  check ``Verification.TolerantFrames.regionalVisitTables_of_recordedAgreement

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.TolerantFrames.headExit_contract
  check ``Verification.TolerantFrames.exitStep_head_checks
  check ``Verification.TolerantFrames.exitStep_handler_checks
  check ``Verification.TolerantFrames.thrownTyOf_admits
  check ``Verification.TolerantFrames.visitStep_handler_admits
  check ``Verification.TolerantFrames.ExitChecks.Site.headFlag
  check ``Verification.TolerantFrames.ExitChecks.Site.targetContext
  check ``Verification.TolerantFrames.ExitChecks.Site.argumentInput
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_head
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_handler_edges
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_handler_of_records

-- Structural extraction from the final walk and its setup provenance.
  check ``Verification.TolerantFrames.pushExit_incoming_mem
  check ``Verification.TolerantFrames.pushExit_merge_mem
  check ``Verification.TolerantFrames.exitStep_nonHead_checked
  check ``Verification.TolerantFrames.exitStep_arraySizes
  check ``Verification.TolerantFrames.exitsFold_indexed_arrays
  check ``Verification.TolerantFrames.visitExits_indexed_arrays
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_nonHead

-- Setup allocation, incoming multiplicities, and extraction from recorded implications.
  check ``Verification.TolerantFrames.exitTypes_regionIn
  check ``Verification.TolerantFrames.headExit_regionIn
  check ``Verification.TolerantFrames.assertionExit_regionIn
  check ``Verification.TolerantFrames.exitStep_regionIn
  check ``Verification.TolerantFrames.exitsFold_regionIn
  check ``Verification.TolerantFrames.regionIn_modify_mono
  check ``Verification.TolerantFrames.regionalFold_inputs
  check ``Verification.TolerantFrames.regionalFold_entries
  check ``Verification.TolerantFrames.sparseFold_frame
  check ``Verification.TolerantFrames.sparse_own
  check ``Verification.TolerantFrames.regionalAt_inputs
  check ``Verification.TolerantFrames.visitExits_inputs
  check ``Verification.TolerantFrames.setup_regional_no_start
  check ``Verification.TolerantFrames.visitExits_regionalInputs
  check ``Verification.TolerantFrames.RecInv.regionalInputWitness
  check ``Verification.TolerantFrames.RegionBelow.trans
  check ``Verification.TolerantFrames.regionalAt_state
  check ``Verification.TolerantFrames.regionalAt_names
  check ``Verification.TolerantFrames.RecInv.regional_nonhead_bound
  check ``Verification.TolerantFrames.RecInv.regional_head_bound
  check ``Verification.TolerantFrames.RecInv.successor_visited
  check ``Verification.TolerantFrames.sparse_region_own
  check ``Verification.TolerantFrames.regionalAt_own_no_self
  check ``Verification.TolerantFrames.returnedWalk_successor_visited
  check ``Verification.TolerantFrames.regionalRecordedTableAgreement

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.TolerantFrames.exitStep_handler_arrays
  check ``Verification.TolerantFrames.visitEntry_head_pair
  check ``Verification.TolerantFrames.setup_startEntered
  check ``Verification.TolerantFrames.exit_target_labels
  check ``Verification.TolerantFrames.ExitChecks.Site.handler_record
  check ``Verification.TolerantFrames.ExitChecks.handlerRecords_of_checked
  check ``Verification.TolerantFrames.ExitChecks.Site.setup
  check ``Verification.TolerantFrames.ExitChecks.Site.startBelow
  check ``Verification.TolerantFrames.ExitChecks.Site.env_eq
  check ``Verification.TolerantFrames.ExitChecks.Site.head_written
  check ``Verification.TolerantFrames.ExitChecks.Site.head_incoming
  check ``Verification.TolerantFrames.ExitChecks.Site.exit_noninitial
  check ``Verification.TolerantFrames.ExitChecks.headEntryContract_of_checked
  check ``Verification.TolerantFrames.ExitChecks.headEntryContract_nonstart
  check ``Verification.TolerantFrames.ExitChecks.headEntries_of_checked
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_head_structural
  check ``Verification.TolerantFrames.ExitChecks.exitChecks_handler_structural
  check ``Verification.TolerantFrames.passMerging_of_degree
  check ``Verification.TolerantFrames.WalkChecked.givenAgreement
  check ``Verification.TolerantFrames.WalkChecked.mergingOfIncoming
  check ``Verification.TolerantFrames.exitsFold_arraySizes
  check ``Verification.TolerantFrames.visitExits_arraySizes
  check ``Verification.TolerantFrames.ExitChecks.Site.arrayAllocation
  check ``Verification.TolerantFrames.ExitChecks.Site.mergingOfIncoming


-- Handler transfer and the composition of remaining semantic premises.
open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.TolerantFrames.exitsYield_of_kept

-- Start contracts and their semantic projection to written assertions.
open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.TolerantFrames.union_keeps_left
  check ``Verification.TolerantFrames.startWrittenImpliesStated
  check ``Verification.TolerantFrames.WalkChecked.startWrittenImpliesStated
  check ``Verification.TolerantFrames.startWritten_projection_counterexample
  check ``Verification.TolerantFrames.ExitChecks.Site.start_given
  check ``Verification.TolerantFrames.ExitChecks.Site.head_written_coherent
  check ``Verification.TolerantFrames.sparseFold_pick
  check ``Verification.TolerantFrames.sparse_region_target
  check ``Verification.TolerantFrames.regionalFold_retains_target
  check ``Verification.TolerantFrames.regionalAt_nonhead_target
  check ``Verification.TolerantFrames.regionalAt_head_target
  check ``Verification.TolerantFrames.regionalAt_entry_header
  check ``Verification.TolerantFrames.regionalAt_own_head
  check ``Verification.TolerantFrames.returnedWalk_setup
  check ``Verification.TolerantFrames.returnedWalk_setup_inv
  check ``Verification.TolerantFrames.returnedWalk_self_head
  check ``Verification.TolerantFrames.returnedWalk_regional_no_start
  check ``Verification.TolerantFrames.RecInv.regionalInputReadback
  check ``Verification.TolerantFrames.regionalRecorded_nonhead_of_inputs

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.TolerantFrames.regionalRecordedReadback
  check ``Verification.TolerantFrames.regionalFold_size
  check ``Verification.TolerantFrames.regionalAt_size
  check ``Verification.TolerantFrames.visitExits_regionSize
  check ``Verification.TolerantFrames.visitStep_regional_relations
  check ``Verification.TolerantFrames.regionalFacts_holds
  check ``Verification.TolerantFrames.regionalSeparation_recover
  check ``Verification.TolerantFrames.regionalStepBridge

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let check (decl : Name) : CommandElabM Unit := do
    for axiom_ in ← liftCoreM <| collectAxioms decl do
      unless standard.contains axiom_ do
        throwError "{decl} depends on the axiom {axiom_}"
  check ``Verification.TolerantFrames.run_sound_single_pass_of_exits
  check ``Verification.TolerantFrames.run_sound_single_pass
  check ``Verification.TolerantFrames.regionalAt_header
  check ``Verification.SinglePass.visitStep_rebound
  check ``Verification.SinglePass.drive_rebound
  check ``Verification.SinglePass.runWalk_rebound
  check ``Verification.SinglePass.run_rebound
