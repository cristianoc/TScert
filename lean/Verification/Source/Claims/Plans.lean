import Verification.Source.SourceRequests
import Verification.Source.Equations.Store
import Verification.Paper.TolerantFrames.ReadOnlyClaim
import Verification.Source.Claims.FramedSpec

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)
/-- A unit's plan: its graph request, a generic unit and a generic closure
included, their binders parameter rows the graph checks at every
assignment; or its request with the proposals of the read-only frame
(`FramedSpec`), accepted under the client obligation of the frame they
define. -/
inductive FunctionPlan (σ ι : Type) [Labels ι] [StoreView σ ι] where
  | graph (name : String) (namePos : Span) (request : SourceRequest σ ι)
  | framed (name : String) (namePos : Span) (request : SourceRequest σ ι) (spec : FramedSpec ι)

/-- A plan's name, the position of its name and its request. -/
def FunctionPlan.parts {σ ι : Type} [Labels ι] [StoreView σ ι] : FunctionPlan σ ι → String × Span × SourceRequest σ ι
  | .graph name pos r | .framed name pos r _ => (name, pos, r)

/-- **A plan with its request changed**: the same kind, name, position and
proposals, its request `g`'s image. -/
def FunctionPlan.mapRequest {σ ι : Type} [Labels ι] [StoreView σ ι] (g : SourceRequest σ ι → SourceRequest σ ι) :
    FunctionPlan σ ι → FunctionPlan σ ι
  | .graph name pos r => .graph name pos (g r)
  | .framed name pos r spec => .framed name pos (g r) spec

theorem FunctionPlan.parts_mapRequest {σ ι : Type} [Labels ι] [StoreView σ ι] (g : SourceRequest σ ι → SourceRequest σ ι)
    (p : FunctionPlan σ ι) : (p.mapRequest g).parts = (p.parts.1, p.parts.2.1, g p.parts.2.2) := by
  cases p <;> rfl

/-- A plan admitted by the top-level verified outcome. Graph evidence is
consumed separately. Adding a source-plan variant cannot silently enter this
exhaustive boundary through a projection. A graph plan is accepted for every
execution (`PassUnit.RequestSafe`); a framed plan for the executions in
which code outside its frame's component keeps the frame's client
obligation (`PassUnit.FramedRequestSafe`), at the frame its proposals
define (`FramedSpec.frame`). -/
inductive CertifiedPlan (σ ι : Type) [Labels ι] [StoreView σ ι] where
  | graph (name : String) (namePos : Span) (request : SourceRequest σ ι)
  | framed (name : String) (namePos : Span) (request : SourceRequest σ ι) (spec : FramedSpec ι)

/-- **The trust a certified plan is accepted under**: none for a graph plan;
the client obligation of its frame for a framed plan. -/
def CertifiedPlan.clientTrust {σ ι : Type} [Labels ι] [StoreView σ ι] : CertifiedPlan σ ι → Bool
  | .graph .. => false
  | .framed .. => true

/-- The conversion into the verified-plan type used by the acceptance path.
Exhaustive matching makes
a new `FunctionPlan` constructor a compile error here. -/
def FunctionPlan.certify {σ ι : Type} [Labels ι] [StoreView σ ι] : FunctionPlan σ ι → Except String (CertifiedPlan σ ι)
  | .graph name pos request => pure (.graph name pos request)
  | .framed name pos request spec => pure (.framed name pos request spec)

open EquationGraphs EquationStore in
/-- A unit's plan over the frozen equations (`EquationStore.freeze`). -/
def FunctionPlan.over (F : Frozen) :
    FunctionPlan EquationStore.State Tree → Except String (FunctionPlan (Checked F.equations F.primitive)
      (CheckedLabel F.equations F.primitive))
  | .graph name pos r => do return .graph name pos (← SourceRequest.over F r)
  | .framed name pos r spec => do return .framed name pos (← SourceRequest.over F r) (← spec.over F)

end Verification.SourceClaimJson
