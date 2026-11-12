import Verification.Source.Claims.PassUnitSafe

/-! # The single pass's unit theorem: the headline

`member_safe`: a member `passGroup` accepts is safe. `passUnit_safe`: from
mode 8's exact acceptance condition of a unit, every member of its group is
safe, under the graph-level hypotheses `RunSound` and `RunKeepsSummaries`,
the wrapper hypothesis `PassGroupChecks` and the entry-context hypothesis
`FragmentStartContexts` (docs/drafts/pass-unit-theorem.md). -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open PositiveCertificates (InstanceImageCheck)
open HeapExpressionRules (Checker)
open CertificateProducer (Answered)

/-- A file's checked summaries are sound at its frozen store's graph and
image check, for a request over that store (proved). -/
theorem summaries_of_checked {f : FilePlans} {r : Req f} (ht : r.types = f.F.store)
    {sums : List (ProgramCertificates.ReadSummary (EquationStore.CheckedLabel f.F.equations f.F.primitive))}
    (h : summariesChecked r sums = true) :
    ProgramCertificates.SummariesSound (StoreView.graph f.F.store) (StoreView.images f.F.store) sums := by
  simp only [summariesChecked, Bool.and_eq_true] at h
  have hs := ProgramCertificates.checkReadSummaries_sound h.2
  have key : ∀ t : EquationStore.Checked f.F.equations f.F.primitive, t = f.F.store →
      ProgramCertificates.SummariesSound (StoreView.graph t) (StoreView.images t) sums →
      ProgramCertificates.SummariesSound (StoreView.graph f.F.store) (StoreView.images f.F.store) sums := by
    rintro t rfl h; exact h
  exact key r.types ht hs

/-- **An unqualified member is safe** (proved, under `RunSound` and
`RunKeepsSummaries`): its codes accepted in order make a sound table
(`codesAccepted_sound`), each code's guarantee gives its assertions
(`codesAccepted_guarantees`), and its main graph accepted gives safety, the
footprint (by its bound, its purity or the regional fallback), the
postcondition, the stated regions and the assertions. -/
theorem ordinary_requestSafe {f : FilePlans} {r : Req f}
    {a₀ a₁ : Answered (StoreView.graph f.F.store)}
    (hrun : RunSound (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (hkeep : RunKeepsSummaries (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (htypes : r.types = f.F.store) (hctx : StartContext r.claims r.start r.inputs)
    (hcctx : ∀ q ∈ r.codes, StartContext q.claims q.entry.start
      (codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.store))
    (hq : r.qualification = none)
    (hregs : ∀ Φ regions, r.regional = some (Φ, regions) → r.async = false ∧ r.fresh = false ∧
      GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions = true)
    (hcodes : CodesAccepted (StoreView.graph f.F.store) (StoreView.images f.F.store) r [] r.codes.zipIdx a₀ a₁)
    (hmain : MainAccepted (StoreView.graph f.F.store) (StoreView.images f.F.store) r
      (GraphCode.admits (r.codes.map (·.entry))) a₁) :
    RequestSafe r := by
  have hadm : ∀ η, r.Admits η := fun η => by simp [SourceRequest.Admits, hq]
  have hstarts : ∀ p ∈ r.codes.zipIdx, StartContext p.1.claims p.1.entry.start
      (codeFrame p.1.entry.arity p.1.entry.row p.1.entry.captures p.1.entry.store) := by
    intro p hp
    exact hcctx p.1 (by
      have := List.mem_map_of_mem (f := (·.1)) hp
      rwa [List.zipIdx_map_fst] at this)
  have hnone : ProgramCertificates.CodesSound (StoreView.graph f.F.store) (GraphCode.admits []) := by
    intro c hc; simp [GraphCode.admits] at hc
  have hentries : r.codes.zipIdx.map (·.1.entry) = r.codes.map (·.entry) := by
    calc r.codes.zipIdx.map (·.1.entry) = (r.codes.zipIdx.map (·.1)).map (·.entry) := by
          rw [List.map_map]; rfl
      _ = r.codes.map (·.entry) := by rw [List.zipIdx_map_fst]
  -- The primary run: direct, or the regional fallback; its summaries checked.
  have primary : ∃ (c : RunCall (StoreView.graph f.F.store) (StoreView.images f.F.store))
      (after : Answered (StoreView.graph f.F.store)),
      MainCall r c (GraphCode.admits (r.codes.map (·.entry)))
        (Checker.ordinary (StoreView.graph f.F.store) (StoreView.images f.F.store)) a₁ ∧
      c.Accepts after ∧ summariesChecked r after.summaries.toList = true := by
    cases hmain with
    | direct c after hm _ _ hacc hs => exact ⟨c, after, hm, hacc, hs⟩
    | fallback c₁ a₂ _ hm _ _ hacc hs _ => exact ⟨c₁, a₂, hm, hacc, hs⟩
  obtain ⟨c, after, hm, hacc, hs⟩ := primary
  have hsums := summaries_of_checked htypes hs
  have hsub : ∀ s ∈ a₁.summaries.toList, s ∈ after.summaries.toList := by
    intro s hs'
    obtain ⟨-, -, -, -, -, -, -, -, hans, -, -⟩ := hm
    obtain ⟨counts, trace, hres⟩ := hacc
    have := hkeep _ _ c s (hans ▸ hs')
    rwa [hres] at this
  have htable : ProgramCertificates.CodesSound (StoreView.graph f.F.store)
      (GraphCode.admits (r.codes.map (·.entry))) := by
    have := codesAccepted_sound hrun hkeep hsums hcodes hstarts hsub hnone
    rwa [List.nil_append, hentries] at this
  have hcodeG := codesAccepted_guarantees hrun hkeep hsums hcodes hstarts hsub hnone
  -- Any accepted main call, with the table, is guaranteed.
  have guarantee : ∀ (c' : RunCall (StoreView.graph f.F.store) (StoreView.images f.F.store))
      (after' : Answered (StoreView.graph f.F.store)),
      MainCall r c' (GraphCode.admits (r.codes.map (·.entry)))
        (Checker.ordinary (StoreView.graph f.F.store) (StoreView.images f.F.store)) a₁ →
      c'.Accepts after' → summariesChecked r after'.summaries.toList = true →
      (∀ Φ regions exc, regionOf c'.regional = some (Φ, regions, exc) →
        GraphCode.ArgumentPathTracking.checkEntryFields (StoreView.graph f.F.store) r.inputs regions = true) →
      GraphGuarantee (StoreView.graph f.F.store) (fun _ => True) r.program r.start r.goal r.inputs
        r.entrySeparation r.entryIndices r.assertions c'.bound r.ensures (regionOf c'.regional) :=
    fun c' after' hm' hacc' hs' hreg' =>
      main_guarantee hrun hm' .ordinary hctx htable hacc' (summaries_of_checked htypes hs') hreg'
  have stated : ∀ (c' : RunCall (StoreView.graph f.F.store) (StoreView.images f.F.store)),
      regionOf c'.regional = regionalSpec r → ∀ Φ regions exc, regionOf c'.regional = some (Φ, regions, exc) →
        GraphCode.ArgumentPathTracking.checkEntryFields (StoreView.graph f.F.store) r.inputs regions = true := by
    intro c' hc' Φ regions exc h
    rw [hc'] at h
    simp only [regionalSpec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨Φ', regions'⟩, hr, rfl, rfl, -⟩ := h
    exact (hregs _ _ hr).2.2
  have fallbackRegions : ∀ (c' : RunCall (StoreView.graph f.F.store) (StoreView.images f.F.store)),
      regionOf c'.regional = some (r.footprint, [], r.onThrow) → ∀ Φ regions exc,
        regionOf c'.regional = some (Φ, regions, exc) →
        GraphCode.ArgumentPathTracking.checkEntryFields (StoreView.graph f.F.store) r.inputs regions = true := by
    intro c' hc' Φ regions exc h
    rw [hc'] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact checkEntryFields_nil _ _
  have hprimary : ∃ (bound : Option (Footprints.Closed × Bool × Bool))
      (regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)), GraphGuarantee (StoreView.graph f.F.store) (fun _ => True) r.program
      r.start r.goal r.inputs r.entrySeparation r.entryIndices r.assertions bound r.ensures regional := by
    cases hmain with
    | direct c after hm _ hreg hacc hs => exact ⟨_, _, guarantee c after hm hacc hs (stated c hreg)⟩
    | fallback c₁ a₂ _ hm _ hreg hacc hs _ => exact ⟨_, _, guarantee c₁ a₂ hm hacc hs (fallbackRegions c₁ hreg)⟩
  obtain ⟨bound, regional, g⟩ := hprimary
  refine ⟨fun η _ n W h ρ he => g.safe η trivial n W h ρ he, ?_, ?_, ?_,
    fun η _ n W h ρ he => g.asserted η trivial n W h ρ he, ?_⟩
  · -- The footprint: by the bound, the purity, or the regional fallback.
    intro heffect η n W h L d he hvalues hd
    cases hmain with
    | direct c after hm hb hreg hacc hs =>
      have g' := guarantee c after hm hacc hs (stated c hreg)
      rw [hb] at g'
      exact footprint_of_bound g' heffect η n W h L d he hvalues hd
    | fallback c₁ a₂ hfr hm _ hreg hacc hs _ =>
      have g' := guarantee c₁ a₂ hm hacc hs (fallbackRegions c₁ hreg)
      rw [hreg] at g'
      exact footprint_of_fallback g' hfr η n W h L d he
  · intro hne η n W h L d he
    exact g.ensured hne _ _ (program_nodes r.program) η trivial n W h L d he
  · -- The stated regions: the direct run's, or the regional run after the fallback.
    intro Φ regions hr η n W h L d he
    have hspec : regionalSpec r = some (Φ, regions, r.stated.any (·.onThrow)) := by
      simp [regionalSpec, hr]
    cases hmain with
    | direct c after hm _ hreg hacc hs =>
      have g' := guarantee c after hm hacc hs (stated c hreg)
      exact g'.regionally Φ regions _ (hreg.trans hspec) _ _ (program_nodes r.program) η trivial n W h L d he
    | fallback _ _ _ _ _ _ _ _ hrest =>
      rcases hrest with hnone' | ⟨c₂, a₂, hm, _, hreg, hacc, hs⟩
      · rw [hnone'] at hr; cases hr
      · have g' := guarantee c₂ a₂ hm hacc hs (stated c₂ hreg)
        exact g'.regionally Φ regions _ (hreg.trans hspec) _ _ (program_nodes r.program) η trivial n W h L d he
  · -- Each code's assertions, from its run's guarantee.
    intro ci q hci η n W h ρ he l k hk j h' ρ' hj hreach
    have hmem : (q, ci) ∈ r.codes.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hci
    exact (hcodeG (q, ci) hmem).asserted η trivial n W h ρ he l k hk j h' ρ' hj hreach

/-- **A qualified member is safe** (proved, under `RunSound`): its one call
at its checker gives safety and assertions at its admitted instances; its
footprint, postcondition, regions and codes are absent. -/
theorem qualified_requestSafe {f : FilePlans} {r : Req f}
    {q : QualifiedBody (RequestJson.graph r.toRequest) (StoreView.images r.types)}
    {c : RunCall (RequestJson.graph r.toRequest) (StoreView.images r.types)}
    {a₀ after : Answered (RequestJson.graph r.toRequest)}
    (hrun : RunSound (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (hctx : StartContext r.claims r.start r.inputs)
    (hq : r.qualification = some q) (hfp : r.footprint = .top) (hot : r.onThrow = false) (hfr : r.fresh = false)
    (hens : r.ensures = []) (hreg : r.regional = none) (hcodes : r.codes = [])
    (hm : MainCall r c (GraphCode.admits []) q.checker a₀) (hregc : c.regional = none)
    (hacc : c.Accepts after) (hs : summariesChecked r after.summaries.toList = true) :
    RequestSafe r := by
  have hnone : ProgramCertificates.CodesSound (RequestJson.graph r.toRequest) (GraphCode.admits []) := by
    intro c hc; simp [GraphCode.admits] at hc
  simp only [summariesChecked, Bool.and_eq_true] at hs
  have g := main_guarantee hrun hm (.qualified q) hctx hnone hacc
    (ProgramCertificates.checkReadSummaries_sound hs.2) (fun _ _ _ h => by rw [hregc] at h; cases h)
  have hadm : ∀ η, r.Admits η → q.Admits η := fun η h => by simpa [SourceRequest.Admits, hq] using h
  refine ⟨fun η ha n W h ρ he => g.safe η (hadm η ha) n W h ρ he, ?_, ?_, ?_,
    fun η ha n W h ρ he => g.asserted η (hadm η ha) n W h ρ he, ?_⟩
  · intro heffect
    rcases heffect with h | h | h
    · exact absurd hfp h
    · rw [hot] at h; cases h
    · rw [hfr] at h; cases h
  · intro hne; exact absurd hens hne
  · intro Φ regions h; rw [hreg] at h; cases h
  · intro ci q' hci; rw [hcodes] at hci; cases hci

/-- **A member `passGroup` accepts is safe** (proved, under `RunSound` and
`RunKeepsSummaries`, its plans over the file's store and stating their start
contexts): its plan crosses the exhaustive certification boundary and its
request is safe. -/
theorem member_safe {f : FilePlans} {j : Nat}
    (hrun : RunSound (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (hkeep : RunKeepsSummaries (EquationStore.CheckedLabel f.F.equations f.F.primitive))
    (hover : OverStore f) (hstart : StartContexts f) (h : MemberAccepted f j) : MemberSafe f j := by
  cases h with
  | ordinary name pos r a₀ a₁ hplan hq _ hregs hcodes hmain =>
    obtain ⟨hctx, hcctx⟩ := hstart j name pos r hplan
    exact ⟨_, _, hplan, rfl, ordinary_requestSafe hrun hkeep (hover j name pos r hplan) hctx hcctx hq hregs
      hcodes hmain⟩
  | qualified name pos r q c a₀ after hplan hq _ hfp hot hfr hens hreg hcodes hm _ hregc hacc hs =>
    obtain ⟨hctx, -⟩ := hstart j name pos r hplan
    exact ⟨_, _, hplan, rfl, qualified_requestSafe hrun hctx hq hfp hot hfr hens hreg hcodes hm hregc hacc hs⟩

/-- **The headline** (proved, under the graph-level hypotheses `RunSound`
and `RunKeepsSummaries`, the wrapper hypothesis `PassGroupChecks` and the
entry-context hypothesis `FragmentStartContexts`): when mode 8 prints a unit
accepted, its plans are those `fragmentPlans` gives with the given head
facts, the unit is selected and `passGroup` accepts its group, then every
member of its group is safe (`PassUnitSafe`). -/
theorem passUnit_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    (hgroup : PassGroupChecks) (hstarts : FragmentStartContexts)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f : FilePlans} {i : Nat}
    {givenLines : Std.HashMap String Json} {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting : Bool} {deps : List String}
    (hplans : fragmentPlans ast fileKey budget selection standIns force = .ok f)
    (_hselected : i ∈ f.fr.selected selection)
    (haccepted : ((f.withHeadFacts givenLines false).passGroup fuel (f.fr.group i) compare debugNode repeats
      given observe counting).2 = .ok deps) :
    PassUnitSafe (f.withHeadFacts givenLines false) i := by
  intro j hj
  exact member_safe (hrun _) (hkeep _) (withHeadFacts_overStore (fragmentPlans_overStore hplans))
    (withHeadFacts_startContexts (hstarts _ _ _ _ _ _ _ hplans))
    (hgroup _ _ _ _ _ _ _ _ _ _ haccepted j hj)

end Verification.SourceClaimJson.PassUnit
