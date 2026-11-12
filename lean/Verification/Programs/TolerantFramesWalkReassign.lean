import Verification.Programs.TolerantFramesGuarantee

/-! # Tolerant frames: the pass's inputs at a reassignment

`run_guarantee` asks for the walk predicates at `reassign G η` for every
admitted `η`, while the pass runs at `G`. The proved checker gets this from
one check: its acceptance at `G` is its acceptance at every reassignment
(`Parametricity.accept_reassign`), and each rule's soundness is stated for
every graph. The same route for the pass needs the pass's arguments at the
reassigned graph: the code table's soundness (`codesSound_reassign`), the
read summaries' (`Parametricity.summariesSound_reassign`), the cached
answers (`Answered.reassign`, whose proved inclusions hold at every
assignment) and the ordinary checker (`PassChecker.ordinary` at any graph). -/
namespace Verification.TolerantFrames
open Verification PositiveGraphs PositiveRules ProgramTyping ProgramCertificates

variable {ι : Type}

/-- **A sound code table is sound at every reassignment**: its soundness is
stated at every assignment. -/
theorem codesSound_reassign {G : NormalGraph ι} {codes : CodeEntry ι → Bool} (h : CodesSound G codes)
    (η : MixedAssignment ι) : CodesSound (reassign G η) codes :=
  fun c hc η' => h c hc η'

/-- **The cached answers at a reassigned graph**: the same tables; each
proved inclusion holds at every assignment of the reassigned graph, as of
the graph. -/
def Answered.reassign [BEq ι] [Hashable ι] {G : NormalGraph ι} (a : CertificateProducer.Answered G) (η : MixedAssignment ι) :
    CertificateProducer.Answered (reassign G η) where
  subtypes := a.subtypes
  summaries := a.summaries
  summaryAnswers := a.summaryAnswers
  fieldSlices := a.fieldSlices
  candidatePasses := a.candidatePasses
  candidatePassesMax := a.candidatePassesMax
  candidatesLeftOut := a.candidatesLeftOut
  proved := a.proved
  proved_sound := fun S T h η' => a.proved_sound S T h η'

end Verification.TolerantFrames
