import Verification.Programs.TolerantFramesRunSound
import Verification.Programs.TolerantFramesNodeCallFresh
import Verification.Programs.TolerantFramesNodeReturns
import Verification.Programs.TolerantFramesComposeShape
import Verification.Programs.TolerantFramesNodeLabels
import Verification.Programs.TolerantFramesNodeYieldChecks

/-! # Tolerant frames: the driver's checks at the nodes it visits

The driver checks each node it visits: under a footprint bound, the bound
(`BoundChecked`, with `outFresh` as `run` computes it, in the call's
no-return region `dead`), and where the call states a postcondition, the
return (`ReturnChecked`), and the yields it keeps (`NodeYieldChecks`)
(`NodePassChecked`). A walk is checked
(`WalkChecked`) where every visited node is, in one no-return region. The
graph theorem's per-node premises are stated at a checked walk, the
record's: `RegionsHeld` here, `NodesYield` in `TolerantFramesComposeYields`. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules LabelStore

section Checked
variable {ι : Type} [Labels ι]

/-- **What the driver checks at a node it visits** (`run`, "The footprint
bound at this node" and a return's checks), at the node's checked step
`r`: under the call's bound `(Φ, fr, ex)`, `BoundChecked` in the no-return
region `dead`; where the call states a postcondition, `ReturnChecked`; the
yields it kept (`r.ys`) checked (`NodeYieldChecks`) over a sound summary
table. -/
structure NodePassChecked {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I)
    (dead : List Bool) {w : Walk ι} {ctx : Nat → List (Ty ι)} {l : Nat}
    (r : NodeChecked G I c.codes c.passChecker c.P w (List.range c.inputs.length) ctx l) : Prop where
  bound : ∀ Φ fr ex, c.bound = some (Φ, fr, ex) → BoundChecked r Φ dead fr ex
  ret : c.ensures ≠ [] → ReturnChecked r c.goal c.ensures
  yields : ∃ sums : List (ReadSummary ι), SummariesSound G I sums ∧
    NodeYieldChecks G I c.codes sums w (List.range c.inputs.length) c.goal c.ensures l r.node r.c r.entry r.st r.ys

/-- **A checked walk**: every visited node's step `NodePassChecked`, in one
no-return region. -/
def WalkChecked {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I) (r : RunWalkA G I c) :
    Prop :=
  ∃ dead, ∀ l (hl : r.w.visited l), NodePassChecked c dead (r.node l hl)

variable (ι) in
/-- **(Named hypothesis) An accepted call records a checked walk**: an
accepted call whose final summaries are sound records a walk
(`RunWalkA`) whose visited nodes the driver checked (`WalkChecked`). -/
def RunTraversedC : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) (after : Answered G),
    c.Accepts after → SummariesSound G I after.summaries.toList → ∃ r : RunWalkA G I c, WalkChecked c r

variable (ι) in
/-- **(Named hypothesis) The regional check keeps its facts** at every
admitted reassigned graph, over a checked walk, at the node assertion with
the traversed fields fixed (`RegionsKeptS`), its facts holding at the
start. -/
def RegionsHeld : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r → ∀ η, admits η →
      ∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
        ∃ X : Env → Heap → Nat → Env → Heap → Prop, ∀ ρ0 h₀, X ρ0 h₀ c.start ρ0 h₀ ∧
          RegionsKeptS c.P (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx (X ρ0 h₀) Φ regions h₀ exc

end Checked

end Verification.TolerantFrames
