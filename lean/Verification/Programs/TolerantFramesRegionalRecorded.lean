import Verification.Programs.TolerantFramesRegionalHeld
import Verification.Programs.TolerantFramesDriverVisit

/-! # The regional checks returned by a visit -/
namespace Verification.TolerantFrames
open Verification SinglePass ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open ProgramTyping LabelStore GraphCode GraphCode.ArgumentRegionGraph
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- A returned regional state has an accepted derivation check and an accepted regional check
at the entry materialization joined with the step's facts. -/
theorem regionalAt_checks {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming outgoing : Array (List RegionState)} {here : RegionState}
    (h : regionalAt G I env l en sd rg a incoming = .ok (outgoing, here)) :
    regionalDerivChecked G I env.codes a.summaries.toList env.claimed[l]! env.nodes[l]!
      sd.st.stepK sd.st.stepDeriv = true ∧
    ∃ (table : List (List ArgumentPathTracking.Fact)) (ft : ArgumentRegionFresh.FreshTables),
      checkNode G I a.summaries.toList rg.Φ rg.regions table ft rg.exc l env.nodes[l]!
        (passRegionalEvidence env.claimed[l]! env.nodes[l]! sd.st.stepDeriv sd.st.stepEffect
          (regionalFacts (materialize en.entry (env.claimed[l]!).context.length
            (List.range (env.claimed[l]!).context.length) true).1 sd.st.stepK)) = true := by
  unfold regionalAt at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals
    have bool_true : ∀ b : Bool, (¬ (!b) = true) → b = true := by
      intro b hb; cases b <;> simp_all
    refine ⟨bool_true _ (by assumption), ?_⟩
    refine ⟨‹List (List ArgumentPathTracking.Fact)›, ‹ArgumentRegionFresh.FreshTables›, ?_⟩
    apply bool_true
    assumption

/-- The graph's regional facts, from each label's own recorded check. -/
def recordedRegionFacts (w : SinglePass.Walk ι) : List (List ArgumentPathTracking.Fact) :=
  w.labels.toList.map fun r => (r.region.getD {}).facts

/-- The graph's freshness tables, from each label's own recorded check. -/
def recordedRegionFresh (w : SinglePass.Walk ι) (names : List String) : ArgumentRegionFresh.FreshTables :=
  ⟨w.labels.toList.map (fun r => (r.region.getD {}).values),
    w.labels.toList.map (fun r => (r.region.getD {}).cells),
    w.labels.toList.map (fun r => (r.region.getD {}).fields), names⟩

/-- A successful visit's record carries precisely the regional state returned by its exits. -/
theorem visitResult_region (σ : WalkState ι G) (l : Nat) (en : Entered ι) (sd : StepDone ι G)
    (ex : ExitsDone ι G) (hl : l < σ.walk.labels.size) :
    ((visitResult σ l en sd ex).walk.labels[l]?).bind (·.region) = ex.region := by
  simp only [visitResult, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hl]
  rfl

end Verification.TolerantFrames
