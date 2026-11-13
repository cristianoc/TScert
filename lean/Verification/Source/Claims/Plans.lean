import Verification.Source.SourceRequests
import Verification.Source.Equations.Store

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
exhaustive boundary through a projection. -/
inductive CertifiedPlan (σ ι : Type) [Labels ι] [StoreView σ ι] where
  | graph (name : String) (namePos : Span) (request : SourceRequest σ ι)

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
