import Verification.Programs.TolerantFramesDriverVisit
import Verification.Programs.SinglePassClose
import Verification.Programs.TolerantFramesVisitSummaries

namespace Verification.SourceClaimJson.CallbackEffectInference
open SinglePass TolerantFrames ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs

variable {ι : Type} [LabelStore.Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- The final label and the effect record came from the same visit, even if
the driver later processed the label again. -/
def LabelRecordOrigin (env : WalkEnv ι G I) (w : SinglePass.Walk ι) (answers : Answered G) : Prop :=
  ∀ l lab, w.labels[l]? = some lab → lab.visited = true →
    ∃ (before : WalkState ι G) (en : Entered ι) (sd : StepDone ι G) (region : Option RegionState),
      visitStep G I env before l en = .ok sd ∧ lab = LabelWalk.ofVisit before.fresh en sd region ∧
      SumsPrefix sd.steppedAnswers answers ∧ ∃ r, sd.record = some r ∧ r ∈ w.visits

theorem drive_labelRecordOrigin (env : WalkEnv ι G I) (grading : env.grading = true) :
    ∀ fuel (σ σf : WalkState ι G), drive (visit G I env) fuel σ = .ok σf →
      LabelRecordOrigin env σ.walk σ.answers → LabelRecordOrigin env σf.walk σf.answers := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ σf done inv
    unfold drive at done
    split at done <;> cases done
    exact inv
  | succ fuel ih =>
    intro σ σf done inv
    unfold drive at done
    split at done
    · cases done; exact inv
    · rename_i l rest hq
      cases hv : visit G I env { σ with queue := rest } l with
      | error err => rw [hv] at done; cases done
      | ok next =>
        rw [hv] at done
        apply ih _ _ done
        obtain ⟨en,sd,ex,he,hs,hx,rfl⟩ := visit_ok hv
        obtain ⟨_,hrec⟩ := visitStep_record G I env _ _ _ _ hs
        have existsRecord : ∃ r, sd.record = some r := by
          rw [hrec]
          simp [stepCheck,grading]
        obtain ⟨r,hr⟩ := existsRecord
        have preSum := visitStepPrefix_of_exitStep exitStepPrefix G I env _ _ _ _ _ hs hx
        intro t lab hl visited
        by_cases same : t = l
        · subst t
          have inside := (Array.getElem?_eq_some_iff.mp hl).1
          rw [visitResult_size] at inside
          simp only [visitResult, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside] at hl
          cases hl
          refine ⟨_,en,sd,_,hs,rfl,preSum,r,hr,?_⟩
          simp [visitResult,pushRecord,hr]
        · rw [visitResult_labels _ _ _ _ _ same] at hl
          obtain ⟨old,e,d,reg,checked,eq,oldPrefix,rec,oldRec,member⟩ := inv t lab hl visited
          refine ⟨old,e,d,reg,checked,eq,oldPrefix.trans (keep_prefix _ _),rec,oldRec,?_⟩
          simp only [visitResult,hr,pushRecord,Array.mem_push]
          exact Or.inl member

end Verification.SourceClaimJson.CallbackEffectInference

namespace Verification.SourceClaimJson.CallbackEffectInference
open SinglePass TolerantFrames ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs
variable {ι : Type} [LabelStore.Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- Instantiation of the invariant for the driver's actual initial state. -/
theorem drive_from_setup_labelRecordOrigin (env : WalkEnv ι G I) (grading : env.grading = true)
    {n ans counts trace deg queue fresh fuel σf}
    (done : drive (visit G I env) fuel (setupState n ans counts trace deg queue fresh) = .ok σf) :
    LabelRecordOrigin env σf.walk σf.answers := by
  apply drive_labelRecordOrigin env grading _ _ _ done
  intro l lab hl visited
  simp only [setupState, Array.getElem?_replicate] at hl
  split at hl <;> cases hl
  contradiction

end Verification.SourceClaimJson.CallbackEffectInference
