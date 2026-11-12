import Verification.Programs.TolerantFramesWalkReassignNodes

/-! # Tolerant frames: the ordinary checker's `select` at a reassignment

The pass applies the output of its checker's `select` (`SinglePass.checkedStep`).
For the ordinary checker (`Checker.ordinary`), `select` is each layer's
choice over the steps' rules with the tree taken as given
(`checkStepResult … (tree := false)`); each layer's decision is a function
`Parametricity` proves equal at the reassigned graph (`keepsCall_reassign`,
`ownCall_reassign`, `freshCall_reassign`, `requiresCall_reassign`,
`elementsCall_reassign`, `ensuresCall_reassign`, `boundedWriteCheck_reassign`),
so `select` is the same result at `reassign G η` with the image check
`images.reassign η` (`ordinarySelect_reassign`), layer by layer as
`Parametricity.boundedWrites_value_reassign` gives it for `run`. -/
namespace Verification.TolerantFrames
open Verification PositiveGraphs PositiveRules PositiveCertificates ProgramTyping ProgramCertificates SinglePass CertificateProducer
open HeapExpressionRules

section
variable {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
  (images : InstanceImageCheck G)

/-- The subtype check's result, its exhaustion included. -/
theorem checkSubtypeResult_reassign (A B : Ty ι) (p : SubtypeChoices ι) :
    ProgramCertificates.checkSubtypeUsing (reassign G η) (images.reassign η) A B p =
      ProgramCertificates.checkSubtypeUsing G images A B p := by
  simp only [ProgramCertificates.checkSubtypeUsing, Parametricity.proposal_reassign, Parametricity.compareUsing_reassign,
    Parametricity.budget_reassign]

/-- The observed-subtype check's result. -/
theorem checkObservedSubResult_reassign (A B : Ty ι) (o : BranchRefinement.Observation) (p : SubtypeChoices ι) :
    BranchRefinement.checkObservedSubResult (reassign G η) (images.reassign η) A B o p =
      BranchRefinement.checkObservedSubResult G images A B o p := by
  cases o <;> simp only [BranchRefinement.checkObservedSubResult, checkSubtypeResult_reassign,
    Parametricity.arraySlice_reassign] <;> rfl

/-- A derivation's output with its tree taken as given. -/
theorem checkedOutput_select_reassign (e : ProgramCertificates.Evidence ι) (b : Bool) (out : HeapKnowledge.Knowledge)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    checkedOutput (reassign G η) (images.reassign η) e b out codes sums false = checkedOutput G images e b out codes sums false := by
  simp only [checkedOutput, treeChecked, Bool.false_eq_true, if_false]

/-- The steps' rules with the tree taken as given. -/
theorem stepsSelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    checkStepResult (reassign G η) (images.reassign η) j k e codes sums false =
      checkStepResult G images j k e codes sums false := by
  cases e <;> simp only [checkStepResult, checkSubtypeResult_reassign, checkObservedSubResult_reassign,
    checkedOutput_select_reassign, treeChecked, Bool.false_eq_true, if_false] <;> rfl

theorem stepsSel_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.steps (reassign G η) (images.reassign η)).select j k e codes sums =
      (Checker.steps G images).select j k e codes sums :=
  stepsSelect_reassign G η images j k e codes sums

theorem keepingCallsSelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.steps (reassign G η) (images.reassign η)).keepingCalls.select j k e codes sums =
      (Checker.steps G images).keepingCalls.select j k e codes sums := by
  simp only [Checker.keepingCalls, stepsSel_reassign, Parametricity.keepsCall_reassign]
  all_goals rfl

theorem keepingOwnCallsSelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.select j k e codes sums =
      (Checker.steps G images).keepingCalls.keepingOwnCalls.select j k e codes sums := by
  simp only [Checker.keepingOwnCalls, keepingCallsSelect_reassign, Parametricity.ownCall_reassign]
  all_goals rfl

theorem allocatingCallsSelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.select j k e codes sums =
      (Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.select j k e codes sums := by
  simp only [Checker.allocatingCalls, keepingOwnCallsSelect_reassign, Parametricity.freshCall_reassign]
  all_goals rfl

theorem requiringCallsSelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.select j k e codes sums =
      (Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.select j k e codes sums := by
  simp only [Checker.requiringCalls, allocatingCallsSelect_reassign, Parametricity.requiresCall_reassign]
  all_goals rfl

theorem elementCallsSelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.select j k e codes sums =
      (Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.select j k e codes sums := by
  simp only [Checker.elementCalls, requiringCallsSelect_reassign, Parametricity.elementsCall_reassign]
  all_goals rfl

theorem ensuringCallsSelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls.select j k e codes sums =
      (Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls.select j k e codes sums := by
  simp only [Checker.ensuringCalls, elementCallsSelect_reassign, Parametricity.ensuresCall_reassign, Parametricity.writeViews_reassign, Parametricity.stableFirst_reassign, Parametricity.grownRegions_reassign]
  all_goals rfl

theorem negatingSlotsSelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls.negatingSlots.select j k e codes sums =
      (Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls.negatingSlots.select j k e codes sums := by
  simp only [Checker.negatingSlots, ensuringCallsSelect_reassign]
  all_goals rfl

theorem indexingSelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls.negatingSlots.indexing.select j k e codes sums =
      (Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls.negatingSlots.indexing.select j k e codes sums := by
  simp only [Checker.indexing, negatingSlotsSelect_reassign, Checker.emptyArrays]
  all_goals rfl

theorem boundedWritesSelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls.negatingSlots.indexing.boundedWrites.select j k e codes sums =
      (Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls.negatingSlots.indexing.boundedWrites.select j k e codes sums := by
  simp only [Checker.boundedWrites, indexingSelect_reassign, Parametricity.boundedWriteCheck_reassign, Parametricity.keepsLengths_reassign, Parametricity.writeAtoms_reassign, Parametricity.growOutput_reassign, Parametricity.stableFirst_reassign]
  all_goals rfl

/-- **The ordinary checker's `select` at a reassigned graph** is its
`select` at the graph. -/
theorem ordinarySelect_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (Checker.ordinary (reassign G η) (images.reassign η)).select j k e codes sums =
      (Checker.ordinary G images).select j k e codes sums := by
  simp only [Checker.ordinary, Checker.keepingStable, boundedWritesSelect_reassign, Parametricity.withStable_reassign]
  all_goals rfl
end
end Verification.TolerantFrames
