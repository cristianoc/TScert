import Verification.Programs.SinglePass
import Verification.Types.EquationFamilies

namespace Verification.SourceClaimJson.CallbackOrigins
open ControlFlow CertificateProducer

/-- Component numbers decrease at entries whose allocation can be named
once throughout the invocation. Their validity is checked on every edge. -/
structure SiteRanks where
  rank : Array Nat
  once : Array Bool

def checkSiteRanks (nodes : Array Node) (r : SiteRanks) : Bool :=
  (List.range nodes.size).all fun p => (SinglePass.nodeSucc nodes p).all fun t =>
    r.rank.getD t 0 ≤ r.rank.getD p 0 && (!r.once.getD t false || r.rank.getD t 0 < r.rank.getD p 0)

def siteRanks (nodes : Array Node) : SiteRanks := Id.run do
  let n := nodes.size
  let initial : EquationGraphs.Tarjan := {
    index := Array.replicate n none, low := Array.replicate n 0, onStack := Array.replicate n false }
  let compute : StateM EquationGraphs.Tarjan Unit := (List.range n).forM fun p => do
    if (← get).index[p]!.isNone then EquationGraphs.Tarjan.visit (SinglePass.nodeSucc nodes) p
  let components := (compute.run initial).2.components
  let mut ranks : SiteRanks := ⟨Array.replicate n 0, Array.replicate n false⟩
  for (component,rank) in components.toList.zipIdx do
    for p in component do
      let once := component.length == 1 && !(SinglePass.nodeSucc nodes p).contains p
      ranks := ⟨ranks.rank.setIfInBounds p rank,ranks.once.setIfInBounds p once⟩
  return ranks

def namedSites (nodes : Array Node) : Array Bool :=
  let ranks := siteRanks nodes
  if checkSiteRanks nodes ranks then ranks.once else #[]

end Verification.SourceClaimJson.CallbackOrigins
