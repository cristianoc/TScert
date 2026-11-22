import Verification.Source.Claims.CallbackProducerAccepted
import Verification.Source.Claims.CallbackCodeRowsSound
namespace Verification.SourceClaimJson.CallbackInferencePlan
open ProgramCertificates CallbackEffectInference ControlFlow ProgramTyping TolerantFrames LabelStore CertificateProducer

theorem AcceptedProducer.framedGuarantee {f i fuel params out}
    (a : AcceptedProducer f i fuel params out) (over : PassUnit.OverStore f) :
    let r := a.request
    let G := StoreView.graph f.F.store
    let bound := producerRunBound r
    let frames := framesOf a.rows
    r.program.all (fun node => ObjectCoherence.sourceTerm node.expression) = true ∧
      GraphGuaranteeR G (fun _ => True) r.program r.start r.goal r.inputs r.entrySeparation
        r.entryIndices r.assertions bound r.ensures none (framedFOf frames) (framedRet (framedSOf frames))
        (fun _ _ _ _ => True) := by
  have store := over.graph a.plan
  have codes := inferCodes_table_sound a.checkedCodes
  have sums := checkReadSummaries_sound (Bool.and_eq_true_iff.mp a.summaries).2
  change ProgramCertificates.CodesSound (StoreView.graph a.request.types) _ at codes
  rw [store] at codes
  have accepted := acceptsFramed_of_acceptedWalk (admits := fun _ => True) a.replayed
  apply run_sound_framed _ _ _ _ _ _ _ _ accepted .ordinary codes
  · change SummariesSound (StoreView.graph a.request.types) (StoreView.images a.request.types) _ at sums
    rwa [store] at sums
  · intro _ _ _ no
    cases no
end Verification.SourceClaimJson.CallbackInferencePlan
