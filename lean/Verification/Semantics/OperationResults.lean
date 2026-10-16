import Verification.Semantics.Safety

namespace Verification.OperationResults

/-- A concrete configuration of the existing calculus and its world. -/
structure Config where
  level : Nat
  world : WorldT level
  heap : Heap
  term : Tm

end Verification.OperationResults
