import Verification.Programs.ArgumentRegionCertificates

namespace Verification.SourceClaimJson.CallbackEffectInference
open ControlFlow GraphCode ArgumentPathTracking Footprints CertificateProducer HeapObservations

/-- A closure infers regions rooted at its arguments and captures. Only a
variable copy can introduce another name for such a root. -/
def checkRootTable (P : Program) (start width : Nat) (table : List (List Fact)) : Bool :=
  checkEntry (atLabel table start) && (List.range P.length).all fun l =>
    (P[l]?).any fun node =>
      let facts := atLabel table l
      facts.all (fun f => f.region.path.isEmpty && f.region.position < width) &&
      checkEdges table facts (ArgumentRegionGraph.copyOrigins facts node.expression) node.continuation &&
      checkHandler table facts node.handler

def certifiedRootTable (P : Program) (start width : Nat) (table : List (List Fact)) : List (List Fact) :=
  if checkRootTable P start width table then table else []

end Verification.SourceClaimJson.CallbackEffectInference
