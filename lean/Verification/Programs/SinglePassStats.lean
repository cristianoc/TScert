import Verification.Programs.CertificateProducer

namespace Verification.SinglePassStats
open ProgramTyping ControlFlow CertificateProducer

def termKind : Tm → String
  | .var _ => "var" | .invoke .. => "invoke" | .construct .. => "construct" | .letE .. => "letE"
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => "lit"
  | .objAt .. => "objAt" | .makeAt .. => "makeAt" | .readAt .. => "readAt" | .indexAt .. => "indexAt"
  | .writeAt .. => "writeAt" | .test .. => "test" | .ite .. => "ite" | .arith .. => "arith"
  | .arr _ => "arr" | .arrLit _ => "arrLit" | .elemAt .. => "elemAt" | .setElem .. => "setElem"
  | .lenOf _ => "lenOf" | .spread _ => "spread" | .throw _ => "throw" | .merge .. => "merge"
  | .makeKey .. => "makeKey" | .goto .. => "goto" | .frame .. => "frame"

/-- Shape statistics of a graph: what a single forward pass must handle. -/
instance : Inhabited Node := ⟨⟨.nul, .ret, none⟩⟩

end Verification.SinglePassStats
