import Verification.Programs.TolerantFramesRegionalHeld
import Verification.Programs.TolerantFramesDriverVisitRest

/-! # Regional typing from the derivation's checked requirements -/
namespace Verification.TolerantFrames
open Verification SinglePass ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open ProgramTyping PositiveRules HeapObservations LabelStore GraphCode GraphCode.ArgumentRegionGraph
variable {ι : Type} [Labels ι]

/-- The regional evidence supplies the facts read by the step's requirements check. -/
def RegionalStepFacts (G : NormalGraph ι) (ev : NodeEvidence ι) (stepK : HeapKnowledge.Knowledge) : Prop :=
  ∀ ρ h, HeapKnowledge.Holds (entryFacts G ev) ρ h → HeapKnowledge.Holds stepK ρ h

omit [Labels ι] in
/-- The combined entry supplies every nonrelational step fact. Only links
and separation need a recovery premise after expansion and normalization. -/
theorem regionalStepFacts_of_relations {G : NormalGraph ι} {ev : NodeEvidence ι}
    {a b : HeapKnowledge.Knowledge} (hknowledge : ev.knowledge = regionalFacts a b)
    (hrel : ∀ ρ h, HeapKnowledge.Holds (entryFacts G ev) ρ h →
      HeapLinks.Holds b.links ρ h ∧ HeapSeparation.Holds b.separation ρ) : RegionalStepFacts G ev b := by
  have right_mem {α : Type} [BEq α] [LawfulBEq α] (xs ys : List α) {x : α} (hx : x ∈ ys) :
      x ∈ xs ++ ys.filter (!xs.contains ·) := by
    by_cases hm : x ∈ xs
    · exact List.mem_append_left _ hm
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hx, by simpa using hm⟩)
  intro ρ h hs
  have hr := hrel ρ h hs
  unfold entryFacts at hs
  rw [hknowledge] at hs
  refine ⟨?_, ?_, hr.1, hr.2, ?_, ?_⟩
  · intro f hf
    exact hs.1 f (List.mem_append_left _ (right_mem a.cells b.cells hf))
  · intro f hf
    have hv := hs.2.1 _ (List.mem_append_left _
      (List.mem_map.mpr ⟨f, right_mem a.values b.values hf, rfl⟩))
    dsimp only at hv
    unfold KnowledgeExpand.restrict at hv
    split at hv
    · exact hv
    · rw [ValueSets.ValueSet.mem_meet, Bool.and_eq_true] at hv
      exact hv.1
  · intro f hf
    exact hs.2.2.2.2.1 f (right_mem a.elems b.elems hf)
  · intro f hf
    exact hs.2.2.2.2.2 f (right_mem a.indices b.indices hf)

/-- The requirements branch gives regional typing when the regional entry supplies the step facts. -/
theorem regionalTyped_of_requires {G : NormalGraph ι} {I : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {c : PointClaim ι} {node : Node} {d : ProgramCertificates.Evidence ι}
    {se : Option (HeapExpressionRules.StepEvidence ι)} {kHere stepK : HeapKnowledge.Knowledge}
    (hd : regionalDerivChecked G I codes sums c node stepK (some d) = true)
    (hr : PromiseCalls.requiresTree G I stepK codes sums d = true)
    (hk : RegionalStepFacts G (passRegionalEvidence c node (some d) se kHere) stepK)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G I sums) :
    ControlFlow.entry (passRegionalEvidence c node (some d) se kHere) = c.context ∧
      RegionalTyped G (passRegionalEvidence c node (some d) se kHere) node := by
  simp only [regionalDerivChecked, derivChecked, Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨hterm, hctx⟩, -⟩ := hd
  refine ⟨by simpa [ControlFlow.entry, passRegionalEvidence, NodeEvidence.expression] using hctx, ?_⟩
  intro n W h ρ he _ hf hw hh
  obtain ⟨_, _, hs⟩ := PromiseCalls.requiresTree_sound hcodes hsums d hr
  have hs := erase (hs (by simpa [ControlFlow.entry, passRegionalEvidence, NodeEvidence.expression] using he)
    (hk ρ h hf) hw hh)
  rw [hterm] at hs
  have hs' : Safe (excOf G) (fun k U u => meaning G (result (passRegionalEvidence c node (some d) se kHere)) k U u ∧
      PromiseCalls.YieldsOk G (passRegionalEvidence c node (some d) se kHere).yields ρ k U u) n W h
      (instantiate 0 ρ node.expression) :=
    Safe_mono n (fun _ _ _ v hv => ⟨by simpa [result, passRegionalEvidence, NodeEvidence.expression] using hv,
      fun y hy => by simp [passRegionalEvidence] at hy⟩) W h _ hs
  exact of_value_property (fun _ _ _ v _ => outFacts_holds he (HeapKnowledge.empty _ _)) hs'

/-- Both branches of the regional derivation check give typing under the step-facts bridge. -/
theorem regionalTyped_of_derivation {G : NormalGraph ι} {I : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {c : PointClaim ι} {node : Node} {d : ProgramCertificates.Evidence ι}
    {se : Option (HeapExpressionRules.StepEvidence ι)} {kHere stepK : HeapKnowledge.Knowledge}
    (hd : regionalDerivChecked G I codes sums c node stepK (some d) = true)
    (hk : RegionalStepFacts G (passRegionalEvidence c node (some d) se kHere) stepK)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G I sums) :
    ControlFlow.entry (passRegionalEvidence c node (some d) se kHere) = c.context ∧
      RegionalTyped G (passRegionalEvidence c node (some d) se kHere) node := by
  have hc := hd
  simp only [regionalDerivChecked, derivChecked, Bool.and_eq_true, Bool.or_eq_true] at hc
  rcases hc.2 with ht | hr
  · exact regionalTyped_of_tree hd ht hcodes hsums
  · exact regionalTyped_of_requires hd hr hk hcodes hsums

/-- A checked step runs safely whenever its checked knowledge holds. -/
theorem stepChecked_safe {G : NormalGraph ι} {I : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G I} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {l : Nat} (r : NodeChecked G I codes pc P w startNames ctx l)
    (hc : CodesSound G codes) {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G r.c.context ρ n W) (hk : HeapKnowledge.Holds r.st.stepK ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (excOf G) (meaning G r.c.type) n W h (instantiate 0 ρ r.node.expression) := by
  rcases r.hstep with ⟨x, hcopy, _⟩ | ⟨_, effect, a0, ha, hsum⟩
  · obtain ⟨i, hi, hty, _⟩ := copiedOf_some hcopy
    rw [hi]
    simpa [instantiate] using value_safe (meaning G r.c.type) n W h (ρ i) (meaning_value (he.2 i _ hty)).1 (he.2 i _ hty)
  · obtain ⟨out, pre, hsel, htree, _, _, _, _, hp, hn⟩ := ha
    have hs := (hsum r.sums).2
    by_cases hpres : passPreserving G I (jOf r.c r.node)
        (kOf G r.c r.entry r.ms (wholeOf r.node.expression)) effect codes a0.summaries.toList = true
    · have hK := (hp hpres).2.1
      rw [hK] at hk
      exact erase (pass_select_sound (fun h => passTreeCheck_ok htree h) hsel hc hs he hk hw hh)
    · have hfalse : passPreserving G I (jOf r.c r.node)
          (kOf G r.c r.entry r.ms (wholeOf r.node.expression)) effect codes a0.summaries.toList = false :=
        Bool.eq_false_iff.mpr hpres
      obtain ⟨out', hwhole, hsel', _, hK, _⟩ := hn hfalse
      rw [hK] at hk
      exact erase ((passRunChecker pc).sound (pass_select_whole htree hwhole hsel') hc hs he hk hw hh)

/-- Evidence without an ordinary derivation has the checked step's type. -/
theorem regionalTyped_of_step {G : NormalGraph ι} {I : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G I} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {l : Nat} (r : NodeChecked G I codes pc P w startNames ctx l)
    (hshape : ControlFlow.entry (passRegionalEvidenceOf r) = r.c.context ∧
      result (passRegionalEvidenceOf r) = r.c.type) (hc : CodesSound G codes)
    (hk : RegionalStepFacts G (passRegionalEvidenceOf r) r.st.stepK) :
    ControlFlow.entry (passRegionalEvidenceOf r) = r.c.context ∧
      RegionalTyped G (passRegionalEvidenceOf r) r.node := by
  obtain ⟨hent, hres⟩ := hshape
  refine ⟨hent, ?_⟩
  intro n W h ρ he _ hf hw hh
  have hs := stepChecked_safe r hc (hent ▸ he) (hk ρ h hf) hw hh
  apply of_value_property (fun _ _ _ v _ => outFacts_holds he (HeapKnowledge.empty _ _))
  apply Safe_mono n (fun _ _ _ v hv => ?_) W h _ hs
  exact ⟨hres.symm ▸ hv, fun y hy => by simp [passRegionalEvidenceOf, passRegionalEvidence] at hy⟩

/-- A successful visit supplies its step facts through regional entry
knowledge at every reassignment. Where its ordinary derivation is absent,
the regional evidence reads the node's claimed context and result type. -/
@[nospecialize] def RegionalStepBridge (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : WalkEnv ι G I) (σ : WalkState ι G)
    (l : Nat) (en : Entered ι) (sd : StepDone ι G),
    visitStep G I env σ l en = .ok sd → ∀ η,
    let ev := passRegionalEvidence env.claimed[l]! env.nodes[l]! sd.st.stepDeriv sd.st.stepEffect
      (regionalFacts (materialize en.entry (env.claimed[l]!).context.length
        (List.range (env.claimed[l]!).context.length) true).1 sd.st.stepK)
    (∀ ρ h, HeapKnowledge.Holds (entryFacts (reassign G η) ev) ρ h →
      HeapLinks.Holds sd.st.stepK.links ρ h ∧ HeapSeparation.Holds sd.st.stepK.separation ρ) ∧
      (sd.st.stepDeriv = none → ControlFlow.entry ev = (env.claimed[l]!).context ∧
        result ev = (env.claimed[l]!).type)

/-- Every retained normalized separation fact has partners. -/
theorem separation_norm_partners (d : Nat) (fs : List HeapSeparation.Fact) :
    ∀ f ∈ (HeapSeparation.norm d fs).facts, f.partners ≠ [] := by
  unfold HeapSeparation.norm
  dsimp only
  split
  · simp
  · intro f hf
    simpa using (List.mem_filter.mp hf).2

/-- The separation facts constructed by materialization have partners. -/
theorem materialize_separation_partners (st : SinglePass.State) (d : Nat) (slots : List Nat) (whole : Bool) :
    ∀ f ∈ (materialize st d slots whole).1.separation.facts, f.partners ≠ [] :=
  separation_norm_partners d _

/-- Every successful step's separation facts have partners. -/
theorem visitStep_separation_partners {G : NormalGraph ι} {I : InstanceImageCheck G}
    {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    (h : visitStep G I env σ l en = .ok sd) :
    ∀ f ∈ sd.st.stepK.separation.facts, f.partners ≠ [] := by
  obtain ⟨⟨ms, stats, hr⟩, -, -⟩ := visitStep_ok h
  rcases checkedStep_ok (stepRun_ok hr) with ⟨_, _, _, _, _, _, hk, _⟩ |
    ⟨_, effect, a0, a1, _, _, ha, _⟩
  · rw [hk]; simp
  · obtain ⟨out, pre, _, _, _, _, _, _, hp, hn⟩ := ha
    by_cases hpres : passPreserving G I (jOf env.claimed[l]! env.nodes[l]!)
        (kOf G env.claimed[l]! en.entry ms (wholeOf (env.nodes[l]!).expression)) effect env.codes
        a0.summaries.toList = true
    · rw [(hp hpres).2.1]
      exact materialize_separation_partners _ _ _ _
    · obtain ⟨out', _, _, _, hk, _⟩ := hn (Bool.eq_false_iff.mpr hpres)
      rw [hk]
      exact materialize_separation_partners _ _ _ _

/-- The selected effect's proof has the claimed header when no ordinary
step derivation is present. -/
@[nospecialize] def RegionalStepHeader (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : WalkEnv ι G I) (σ : WalkState ι G)
    (l : Nat) (en : Entered ι) (sd : StepDone ι G),
    visitStep G I env σ l en = .ok sd → sd.st.stepDeriv = none →
    ∀ p, sd.st.stepEffect.bind HeapExpressionRules.StepEvidence.proof? = some p →
      (claim p).context = (env.claimed[l]!).context ∧ (claim p).type = (env.claimed[l]!).type

/-- Regional entry facts supply the successful step's links and separation. -/
theorem visitStep_regional_relations {G : NormalGraph ι} {I : InstanceImageCheck G}
    {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    (hv : visitStep G I env σ l en = .ok sd) (η : MixedAssignment ι) :
    ∀ ρ h, HeapKnowledge.Holds (entryFacts (reassign G η)
      (passRegionalEvidence env.claimed[l]! env.nodes[l]! sd.st.stepDeriv sd.st.stepEffect
        (regionalFacts (materialize en.entry (env.claimed[l]!).context.length
          (List.range (env.claimed[l]!).context.length) true).1 sd.st.stepK))) ρ h →
      HeapLinks.Holds sd.st.stepK.links ρ h ∧ HeapSeparation.Holds sd.st.stepK.separation ρ := by
  intro ρ h hh
  exact ⟨regionalLinks_recover hh,
    regionalSeparation_recover (visitStep_separation_partners hv) hh.2.2.2.1⟩

/-- Composition of the visit's relational and header obligations. -/
theorem regionalStepBridge (hheader : RegionalStepHeader ι) : RegionalStepBridge ι := by
  intro G I env σ l en sd hv η
  have relations := visitStep_regional_relations hv η
  have header : sd.st.stepDeriv = none →
      ControlFlow.entry (passRegionalEvidence env.claimed[l]! env.nodes[l]! sd.st.stepDeriv sd.st.stepEffect
        (regionalFacts (materialize en.entry (env.claimed[l]!).context.length
          (List.range (env.claimed[l]!).context.length) true).1 sd.st.stepK)) = (env.claimed[l]!).context ∧
      result (passRegionalEvidence env.claimed[l]! env.nodes[l]! sd.st.stepDeriv sd.st.stepEffect
        (regionalFacts (materialize en.entry (env.claimed[l]!).context.length
          (List.range (env.claimed[l]!).context.length) true).1 sd.st.stepK)) = (env.claimed[l]!).type := by
    intro hd
    have hp := hheader G I env σ l en sd hv hd
    simp only [passRegionalEvidence, hd, ControlFlow.entry, result, NodeEvidence.expression, NodeEvidence.header]
    cases he : sd.st.stepEffect with
    | none => exact ⟨rfl, rfl⟩
    | some e =>
      cases hep : e.proof? with
      | none => simp only [Option.bind_some, hep]; exact ⟨rfl, rfl⟩
      | some p =>
        have hh := hp p (by simp [he, hep])
        simpa [hep] using hh
  exact ⟨relations, header⟩

end Verification.TolerantFrames
