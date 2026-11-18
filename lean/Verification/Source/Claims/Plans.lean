import Verification.Source.SourceRequests
import Verification.Source.Equations.Store
import Verification.Paper.TolerantFrames.ReadOnlyClaim

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)
/-- A unit's plan: its graph request. Every unit is one, a generic unit and a
generic closure included, their binders parameter rows the graph checks at
every assignment. -/
inductive FunctionPlan (σ ι : Type) [Labels ι] [StoreView σ ι] where
  | graph (name : String) (namePos : Span) (request : SourceRequest σ ι)

/-- A plan admitted by the top-level verified outcome. Graph evidence is
consumed separately. Adding a source-plan variant cannot silently enter this
exhaustive boundary through a projection. A graph plan is accepted for every
execution (`PassUnit.RequestSafe`); a framed plan for the executions in
which code outside its frame's component keeps the frame's client
obligation (`PassUnit.FramedRequestSafe`). No plan certifies to a framed
plan: `FunctionPlan.certify` has no branch producing one. -/
inductive CertifiedPlan (σ ι : Type) [Labels ι] [StoreView σ ι] where
  | graph (name : String) (namePos : Span) (request : SourceRequest σ ι)
  | framed (name : String) (namePos : Span) (request : SourceRequest σ ι)
      (frame : Verification.TolerantFrames.ReadOnly.ClientFrame (Ty ι))

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

open EquationGraphs EquationStore in
/-- A unit's plan over the frozen equations (`EquationStore.freeze`). -/
def FunctionPlan.over (F : Frozen) :
    FunctionPlan EquationStore.State Tree → Except String (FunctionPlan (Checked F.equations F.primitive)
      (CheckedLabel F.equations F.primitive))
  | .graph name pos r => do return .graph name pos (← SourceRequest.over F r)

end Verification.SourceClaimJson
