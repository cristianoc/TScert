import Verification.Programs.TolerantFramesNodeAsserts

/-! # A boundary of the start's written-contract projection -/
namespace Verification.TolerantFrames
open Verification ProgramTyping PositiveGraphs

/-- An entry check can accept a written separation whose slot-bound obligation
normalization removes. This is a counterexample to projecting the written
assertion from `startWritten` alone, not to the run's safety theorem. -/
theorem startWritten_projection_counterexample {ι : Type} [DecidableEq ι]
    (G : NormalGraph ι) (ρ : Env) (h : Heap) :
    ∃ written : HeapKnowledge.Knowledge,
      ControlFlow.entryKnows G [] written.separation [] written = true ∧
      HeapKnowledge.Holds (SinglePass.startWritten (some written) [] written.separation) ρ h ∧
      ¬HeapKnowledge.Holds written ρ h := by
  let written : HeapKnowledge.Knowledge :=
    { separation := { depth := 0, facts := [{ slot := 0, partners := [] }] } }
  refine ⟨written, ?_, ?_, ?_⟩
  · simp [ControlFlow.entryKnows, KnowledgeExpand.checkIn, KnowledgeExpand.cellsCheck,
      KnowledgeExpand.valuesCheck, HeapLinks.checkWith, HeapSeparation.checkWithTable,
      HeapSeparation.checkBy, written]
    decide
  · have he : SinglePass.startWritten (some written) [] written.separation = {} := by decide
    rw [he]
    exact HeapKnowledge.empty ρ h
  · intro hw
    have hs := hw.2.2.2.1 { slot := 0, partners := [] } (by simp [written])
    exact Nat.not_lt_zero _ hs.1

end Verification.TolerantFrames
