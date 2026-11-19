import Verification.Source.Claims.FramedSpec
import Verification.Paper.TolerantFrames.ReadOnlyIncoming

/-! # The history of a framed plan's frame

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The history of a program"). The
frame a framed plan defines (`FramedSpec.frame`) crosses at each step its
entering step's arguments into `C`, then every value reaching outside code
out of `C` (`FramedSpec.chk`): its crossings are `ActualCrossingsIn` at the
entering step's crossings (`FramedSpec.actualCrossingsIn`), each of which
crosses into `C` (`FramedSpec.entryXs_into`), so the restated `ChkSound`
lemmas (`ClientFrame.chkSound_of_flowIn`) read it. -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly

namespace FramedSpec
variable {σ ι : Type} [Labels ι] [StoreView σ ι] (spec : FramedSpec ι)

/-- **The frame's crossings are the entering step's, then the actual ones**
(proved, by definition). -/
theorem actualCrossingsIn (r : SourceRequest σ ι) :
    (spec.frame r).ActualCrossingsIn spec.outType (fun _ t _ t' => spec.entryXs r t t') :=
  fun _ _ _ _ => rfl

/-- **Every crossing of an entering step crosses into `C`** (proved). -/
theorem entryXs_into (r : SourceRequest σ ι) {t t' : Tm} {c : Crossing spec.view.view}
    (hc : c ∈ spec.entryXs r t t') : c.dir = .into := by
  unfold entryXs at hc
  split at hc
  · split at hc
    · simp only [List.mem_map] at hc
      obtain ⟨_, -, rfl⟩ := hc
      rfl
    · cases hc
  · cases hc

end FramedSpec
end Verification.SourceClaimJson
