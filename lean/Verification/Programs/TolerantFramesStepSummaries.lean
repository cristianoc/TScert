import Verification.Programs.TolerantFramesDriverSummaries
import Verification.Programs.TolerantFramesStepLinkSound

/-! # Summary tables of accepted steps -/
namespace Verification.TolerantFrames
open ProgramTyping
open Verification SinglePass ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates LabelStore
variable {ι : Type} [Labels ι]

/-- Restoring a table preserves its prefix. -/
theorem sumsPrefix_keep {G : NormalGraph ι} (a b : Answered G) : SumsPrefix a (keepSummaries a b) :=
  keep_prefix a b

/-- An accepted step uses only summaries from its returned table. -/
theorem stepChecked_of_final {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool}
    {aliases : List (ι × ι)} {pc : PassChecker G images} {undefTy : Option (Ty ι)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {ms : List Nat} {fresh : Nat}
    {answers : Answered G} {st : Stepped ι} {stats : StepStats} {ans : Answered G}
    (h : checkedStep G images pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh
      answers = (Except.ok st, stats, ans))
    (hs : SummariesSound G images ans.summaries.toList) :
    StepChecked G images pc codes c node entry ms fresh answers ans st := by
  rcases checkedStep_ok h with hcopy | ⟨hc, effect, a0, a1, _, ha1, hacc, hans⟩
  · exact .inl hcopy
  · subst hans
    have hp : SumsPrefix a0 ans := by
      rcases ha1 with rfl | ⟨k, own, adm, rfl⟩
      · exact .refl _
      · exact sumsPrefix_keep _ _
    exact .inr ⟨hc, effect, a0, hacc, fun _ => ⟨fun s hm => hs s (hp.mem s hm), hs⟩⟩

/-- The checked step's table survives the remainder of its successful visit. -/
def VisitStepPrefix (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : WalkEnv ι G I)
    (σ : WalkState ι G) (l : Nat) (en : Entered ι) (sd : StepDone ι G) (ex : ExitsDone ι G),
    visitStep G I env σ l en = .ok sd → visitExits G I env σ l en sd = .ok ex →
    SumsPrefix sd.steppedAnswers (keepSummaries σ.answers ex.answers)

end Verification.TolerantFrames
