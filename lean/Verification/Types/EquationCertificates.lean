import Verification.Types.EquationSubstitution
import Verification.Types.PositiveCertificates

/-! Recursive equation instances use the ordinary subtyping proof checker.
The image-table validator proves structural substitution. Admissibility,
bound, signature, receiver, effect and argument-pack checks remain shared. -/
namespace Verification.EquationGraphs
open PositiveGraphs PositiveRules PositiveCertificates

/-- Each recorded image equals structural substitution of its equation label. -/
def Equations.instanceImageCheck (equations : Equations) : InstanceImageCheck equations.graph :=
  { finiteInstanceImages equations.graph with
    compare := fun _ c => ComparisonResult.fromBool (substitutionTableOk c.table)
    sound := fun bs c hlen hkinds checked η =>
      equations.substitutionTable_instanceImages η bs c.instances c.table hlen hkinds
        (by simpa only [ComparisonResult.accepted_fromBool] using checked) }

end Verification.EquationGraphs
