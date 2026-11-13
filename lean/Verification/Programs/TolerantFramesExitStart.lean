import Verification.Programs.TolerantFramesNodeAsserts

/-! # Projection of the checked start contract -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification ProgramTyping PositiveGraphs

/-- Projection for arbitrary proposals can fail: normalization removes a
partnerless fact's slot bound. `startSeparationKept` excludes this case. -/
theorem startWritten_projection_counterexample {ι : Type} [DecidableEq ι]
    (G : NormalGraph ι) (ρ : Env) (h : Heap) :
    ∃ written : HeapKnowledge.Knowledge,
      ControlFlow.entryKnows G [] written.separation [] written = true ∧
      HeapKnowledge.Holds (SinglePass.startWritten (some written) [] written.separation) ε ρ h ∧
      ¬HeapKnowledge.Holds written ε ρ h := by
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

/-- Union preserves the left separation when all its facts have partners
and nonempty operands have the same depth. -/
theorem union_keeps_left {S T : HeapSeparation.Separation} {ρ : Env}
    (hp : S.facts.all (!·.partners.isEmpty) = true)
    (hd : (S.facts.isEmpty || T.facts.isEmpty || S.depth == T.depth) = true)
    (h : HeapSeparation.Holds (HeapSeparation.union S T) ρ) : HeapSeparation.Holds S ρ := by
  intro a ha
  have hne : S.facts.isEmpty = false := List.isEmpty_eq_false_iff.mpr (fun he => by rw [he] at ha; cases ha)
  have hap := List.all_eq_true.mp hp a ha
  unfold HeapSeparation.union at h
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · exact h a ha
  · rename_i ht
    have heq : (S.depth == T.depth) = true := by simpa [hne, ht] using hd
    rw [if_pos heq] at h
    have ham : a ∈ (S.facts ++ T.facts.filter (!S.facts.contains ·)).filter
        (fun a => !a.partners.isEmpty) := List.mem_filter.mpr ⟨List.mem_append_left _ ha, hap⟩
    unfold HeapSeparation.norm at h
    dsimp only at h
    split at h
    · rename_i hem
      have := List.isEmpty_iff.mp hem
      rw [this] at ham
      cases ham
    · exact h a ham

/-- The checked start contract entails every component of its written assertion. -/
theorem startWrittenImpliesStated {w : Option HeapKnowledge.Knowledge}
    {idx : List HeapKnowledge.IndexAtom} {sep : HeapSeparation.Separation}
    (kept : SinglePass.startSeparationKept w sep = true) {ρ : Env} {h : Heap}
    (hw : HeapKnowledge.Holds (SinglePass.startWritten w idx sep) ε ρ h) :
    HeapKnowledge.Holds (w.getD {}) ε ρ h := by
  simp only [SinglePass.startSeparationKept, Bool.and_eq_true] at kept
  obtain ⟨hp, hd⟩ := kept
  exact ⟨hw.1, hw.2.1, hw.2.2.1, union_keeps_left hp hd hw.2.2.2.1,
    hw.2.2.2.2.1, fun a ha => hw.2.2.2.2.2 a (List.mem_append_left _ ha)⟩

end Verification.TolerantFrames
