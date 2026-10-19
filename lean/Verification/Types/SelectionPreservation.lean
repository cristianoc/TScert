import Verification.Types.PositiveCertificates

/-! Selection preserves a completed certificate (docs/UNION-SHAPES.md §2.2).
A valid closed family's premise relation is sound, so each covering it
chooses is by a candidate (`ClauseSelection.covers_candidate`): the same
table, read with candidates only, is a valid certificate. What this does not
yet give is that the selected search discovers that table. -/
namespace Verification.SelectionPreservation
open PositiveNormalization PositiveGraphs PositiveRules PositiveCertificates

/-- The premise relation of a valid closed entry is sound: each premise is an
inclusion at every level, by the family's soundness and the inner induction on
premises (`prem_values`). -/
theorem prem_sound_closed [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    (hvalid : FamilyValid G sub known gen look F) (hvars : VariablesOk sub F)
    (hlook : ∀ k e, look k = some e → e ∈ F ∨ (EntrySound G e ∧ HypParams G e))
    (hk : ∀ η : MixedAssignment ι,
      ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    {f : Entry ι} (hf : f ∈ F) (hclosed : f.hypotheses = []) (η : MixedAssignment ι) :
    ClauseSelection.SoundRel G η (Prem G sub look gen f) := by
  have hfam := family_sound hvalid hvars hlook hk
  have hpar : ∀ k e, look k = some e → sub.isSome = true → HypParams G e := by
    intro k e hl _
    rcases hlook k e hl with he | he
    · exact hvars.params he
    · exact he.2
  intro A B hp n W v hv
  refine (prem_values (n := n) (η := η) (fun _ _ h hh => (by rw [hclosed] at hh; cases hh)) (hvars.params hf) hpar
    (fun j _ η' hh p hp => (hfam f hf).1 j η' hh p (List.mem_cons_of_mem _ hp))
    (fun η' hh p hp => (hfam f hf).2 n η' hh p (List.mem_cons_of_mem _ hp))
    ⟨fun h hh => (by rw [hclosed] at hh; cases hh), fun h hh => (by rw [hclosed] at hh; cases hh)⟩
    (fun j _ k e η' hl hh => ?_) (fun k e η' hl hh => ?_)).1 hp W v hv
  · rcases hlook k e hl with he | he
    · exact (hfam e he).1 j η' hh _ List.mem_cons_self
    · exact he.1.1 j η' hh
  · rcases hlook k e hl with he | he
    · exact (hfam e he).2 n η' hh _ List.mem_cons_self
    · exact he.1.2 n η' hh

/-- **Selection preserves a completed certificate.** In a valid family, every
covering a closed entry chooses is by a candidate: the entry's table, read
with candidates only, still covers every source clause of every pair. -/
theorem valid_selected [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    (hvalid : FamilyValid G sub known gen look F) (hvars : VariablesOk sub F)
    (hlook : ∀ k e, look k = some e → e ∈ F ∨ (EntrySound G e ∧ HypParams G e))
    (hk : ∀ η : MixedAssignment ι,
      ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    {f : Entry ι} (hf : f ∈ F) (hclosed : f.hypotheses = []) :
    ∀ p ∈ f.pairs, ∀ a ∈ sourceClauses G p.1 ++ meetSources G p.1 p.2 f.hypotheses,
      (∃ b ∈ ClauseSelection.candidates G a p.2, Covers G sub (Prem G sub look gen f) known p.1 a b) ∨
      ∀ e ∈ a.elements, ∃ b ∈ ClauseSelection.candidates G e p.2,
        Covers G sub (Prem G sub look gen f) known p.1 e b := by
  intro p hp a ha
  have hR := prem_sound_closed hvalid hvars hlook hk hf hclosed (ParameterAssignment.empty .mixed)
  rcases (hvalid f hf p hp).2.2 a ha with ⟨b, hb, hcov⟩ | he
  · refine .inl ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hcov⟩
    simp [ClauseSelection.covers_candidate G hR hcov]
  · refine .inr fun e he' => ?_
    obtain ⟨b, hb, hcov⟩ := he e he'
    refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hcov⟩
    simp [ClauseSelection.covers_candidate G hR hcov]

end Verification.SelectionPreservation
