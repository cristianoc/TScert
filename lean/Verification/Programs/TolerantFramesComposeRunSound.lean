import Verification.Programs.TolerantFramesRunSound
import Verification.Programs.TolerantFramesNodeCallFresh
import Verification.Programs.TolerantFramesNodeReturns
import Verification.Programs.TolerantFramesComposeShape
import Verification.Programs.TolerantFramesNodeLabels

/-! # Tolerant frames: the driver's checks at the nodes it visits

`BoundsChecked` (each visited node's bound check, `BoundChecked`, with
`outFresh` as `run` computes it) and `ReturnsChecked` (each visited return's
`returnCheck` refusing nothing) are checks the driver makes at each node it
visits, read off its walk as `RunWalkA`'s other records are; the graph
theorem (`TolerantFramesComposeYields`) consumes them. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules LabelStore

section Checked
variable {ι : Type} [Labels ι]

variable (ι) in
/-- **(Named hypothesis) The driver checks every visited node's bound**
(`run`, "The footprint bound at this node"): under the call's bound
`(Φ, fr, ex)`, with its no-return region `dead`, `BoundChecked` at every
visited node of the walk, at `G`. -/
def BoundsChecked : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c,
      ∀ Φ fr ex, c.bound = some (Φ, fr, ex) → ∃ dead : List Bool,
        ∀ l (hl : r.w.visited l), BoundChecked (r.node l hl) Φ dead fr ex

variable (ι) in
/-- **(Named hypothesis) The driver checks every visited return** (`run`,
a return's checks): where the call states a postcondition, `returnCheck`
refuses nothing at every visited node whose continuation is a return, at
`G`. -/
def ReturnsChecked : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, c.ensures ≠ [] →
      ∀ l (hl : r.w.visited l), ReturnChecked (r.node l hl) c.goal c.ensures

end Checked

end Verification.TolerantFrames
