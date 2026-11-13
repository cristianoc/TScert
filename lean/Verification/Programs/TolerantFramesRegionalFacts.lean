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
  exact separation_union_holds ha.2.2.2.1 hb.2.2.2.1

/-- Expansion retains the meaning of every original link. -/
theorem expandedLinks_recover {k : Knowledge} {ρ : Env} {h : Heap}
    (hh : HeapLinks.Holds (KnowledgeExpand.links k (LinkClasses.closure k.links)) ρ h) :
    HeapLinks.Holds k.links ρ h := by
  have hrep : ∀ x, ρ (LinkClasses.rep k.links x) = ρ x := by
    intro x
    by_cases e : LinkClasses.rep k.links x = x
    · rw [e]
    · have hx : x ∈ LinkClasses.slots k.links := Classical.byContradiction fun hx => by
        have := Partitions.cls_not_mem (LinkClasses.closure_props (ls := k.links)).1 hx
        simp [LinkClasses.rep, this, LinkClasses.least] at e
      have := hh ⟨LinkClasses.rep k.links x, x, true, valueField, false⟩ (by
        apply List.mem_append_left
        apply List.mem_filterMap.mpr
        refine ⟨x, hx, ?_⟩
        change (if LinkClasses.rep k.links x = x then none else some _) = some _
        rw [if_neg e]
        rfl)
      simpa using this
  intro g hg
  cases ha : g.alias
  · have hm : g ∈ KnowledgeExpand.links k (LinkClasses.closure k.links) := by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨g, hg, ?_⟩
      simp only [ha, Bool.false_eq_true, ↓reduceIte]
      apply List.mem_flatMap.mpr
      refine ⟨g.cell, Partitions.mem_cls_self _, ?_⟩
      exact List.mem_map.mpr ⟨g.value, Partitions.mem_cls_self _, by cases g; simp_all⟩
    simpa only [ha] using hh g hm
  · have e := LinkClasses.rep_eq_of_gen k.links (.alias hg ha)
    simp only [↓reduceIte]
    rw [← hrep g.cell, ← hrep g.value, e]

/-- A member of either input remains in the duplicate-free concatenation. -/
theorem regionalJoin_right {α : Type} [BEq α] [LawfulBEq α] (xs ys : List α) {x : α} (hx : x ∈ ys) :
    x ∈ xs ++ ys.filter (!xs.contains ·) := by
  by_cases hm : x ∈ xs
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hx, by simpa using hm⟩)

/-- The expanded regional entry supplies all step links. -/
theorem regionalLinks_recover {ctx : KnowledgeNormal.Ctx} {a b : Knowledge} {ρ : Env} {h : Heap}
    (hh : Holds (KnowledgeExpand.expandLinks ctx (regionalFacts a b)) ρ h) :
    HeapLinks.Holds b.links ρ h := by
  have hl := expandedLinks_recover hh.2.2.1
  exact fun g hg => hl g (regionalJoin_right a.links b.links hg)

/-- A union supplies its right separation when its facts have partners. -/
theorem separation_union_right {S T : HeapSeparation.Separation} {ρ : Env}
    (hn : ∀ f ∈ T.facts, f.partners ≠ [])
    (hh : HeapSeparation.Holds (HeapSeparation.union S T) ρ) : HeapSeparation.Holds T ρ := by
  unfold HeapSeparation.union at hh
  split at hh
  · exact hh
  · split at hh
    · rename_i he
      intro f hf
      rw [List.isEmpty_iff.mp he] at hf
      cases hf
    · split at hh
      · rename_i hd
        have hd : S.depth = T.depth := by simpa using hd
        intro f hf
        have hm := regionalJoin_right S.facts T.facts hf
        have hm' : f ∈ (S.facts ++ T.facts.filter (!S.facts.contains ·)).filter
            (fun a => !a.partners.isEmpty) := List.mem_filter.mpr ⟨hm, by simpa using hn f hf⟩
        unfold HeapSeparation.norm at hh
        dsimp only at hh
        split at hh
        · rename_i he
          rw [List.isEmpty_iff.mp he] at hm'
          cases hm'
        · rw [← hd]
          exact hh f hm'
      · exact hh

/-- Regional knowledge supplies the step separation when its facts have partners. -/
theorem regionalSeparation_recover {a b : Knowledge} {ρ : Env}
    (hn : ∀ f ∈ b.separation.facts, f.partners ≠ [])
    (hh : HeapSeparation.Holds (regionalFacts a b).separation ρ) :
    HeapSeparation.Holds b.separation ρ :=
  separation_union_right hn hh

end Verification.TolerantFrames
