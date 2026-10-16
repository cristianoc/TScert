import Verification.Source.SourceRequests
import Verification.Source.EquationStore

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

def CertifiedPlan.requests {σ ι : Type} [Labels ι] [StoreView σ ι] : List (CertifiedPlan σ ι) → List (SourceRequest σ ι)
  | [] => []
  | .graph _ _ request :: rest => request :: CertifiedPlan.requests rest

/-- Graph projection for search and inspection. This is intentionally not the
acceptance boundary. -/
def FunctionPlan.requests {σ ι : Type} [Labels ι] [StoreView σ ι] : List (FunctionPlan σ ι) → List (SourceRequest σ ι)
  | [] => []
  | .graph _ _ request :: rest => request :: FunctionPlan.requests rest

/-- The conversion into the verified-plan type used by the acceptance path.
Exhaustive matching makes
a new `FunctionPlan` constructor a compile error here. -/
def FunctionPlan.certify {σ ι : Type} [Labels ι] [StoreView σ ι] : FunctionPlan σ ι → Except String (CertifiedPlan σ ι)
  | .graph name pos request => pure (.graph name pos request)

def certifyPlans {σ ι : Type} [Labels ι] [StoreView σ ι] (plans : List (FunctionPlan σ ι)) : Except String (List (CertifiedPlan σ ι)) :=
  plans.mapM FunctionPlan.certify

open EquationGraphs EquationStore in
/-- A unit's plan over the frozen equations (`EquationStore.freeze`). -/
def FunctionPlan.over (F : Frozen) :
    FunctionPlan EquationStore.State Tree → Except String (FunctionPlan (Checked F.equations F.primitive)
      (CheckedLabel F.equations F.primitive))
  | .graph name pos r => do return .graph name pos (← SourceRequest.over F r)

open EquationGraphs EquationStore in
/-- The extracted plans over the equations their store presents, validated
once extraction is done. -/
def freezePlans (T : EquationStore.State) (plans : List (FunctionPlan EquationStore.State Tree)) :
    Except String ((F : Frozen) ×
      List (FunctionPlan (Checked F.equations F.primitive) (CheckedLabel F.equations F.primitive))) := do
  let F ← freeze T
  return ⟨F, ← plans.mapM (FunctionPlan.over F)⟩


end Verification.SourceClaimJson
