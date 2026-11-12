import Verification.Programs.TolerantFramesRegionalRuns

/-! # The knowledge carried by regional evidence -/
namespace Verification.TolerantFrames
open Verification SinglePass HeapKnowledge PositiveRules

/-- Joining separations preserves their meaning when both inputs hold. -/
theorem separation_union_holds {S T : HeapSeparation.Separation} {ρ : Env}
    (hs : HeapSeparation.Holds S ρ) (ht : HeapSeparation.Holds T ρ) :
    HeapSeparation.Holds (HeapSeparation.union S T) ρ := by
  unfold HeapSeparation.union
  split
  · exact ht
  · split
    · exact hs
    · split
      · rename_i hd
        have hd : S.depth = T.depth := by simpa using hd
        apply HeapSeparation.norm_holds
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hs a ha
        · rw [hd]; exact ht a (List.mem_filter.mp ha).1
      · exact ht

/-- Regional knowledge holds whenever its two sources hold. -/
theorem regionalFacts_holds {a b : Knowledge} {ρ : Env} {h : Heap}
    (ha : Holds a ρ h) (hb : Holds b ρ h) : Holds (regionalFacts a b) ρ h := by
  have join {α : Type} [BEq α] {xs ys : List α} {P : α → Prop}
      (hx : ∀ x ∈ xs, P x) (hy : ∀ x ∈ ys, P x) :
      ∀ x ∈ xs ++ ys.filter (!xs.contains ·), P x := by
    intro x hx'
    rcases List.mem_append.mp hx' with hx' | hx'
    · exact hx x hx'
    · exact hy x (List.mem_filter.mp hx').1
  refine ⟨join ha.1 hb.1, join ha.2.1 hb.2.1, join ha.2.2.1 hb.2.2.1, ?_,
    join ha.2.2.2.2.1 hb.2.2.2.2.1, join ha.2.2.2.2.2 hb.2.2.2.2.2⟩
  dsimp only [regionalFacts]
  split
  · exact separation_union_holds ha.2.2.2.1 hb.2.2.2.1
  · exact ha.2.2.2.1

end Verification.TolerantFrames
