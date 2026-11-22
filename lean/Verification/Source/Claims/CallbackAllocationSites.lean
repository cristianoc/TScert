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

private def SiteInv (P : Program) (r : SiteRanks) (site : Nat) : State → Prop
  | .at l _ => l ≠ site ∧ r.rank.getD l 0 ≤ r.rank.getD site 0
  | .eval _ _ k handler => ∃ (p : Nat) (node : Node), P[p]? = some node ∧ node.continuation = k ∧
      node.handler = handler ∧ r.rank.getD p 0 ≤ r.rank.getD site 0
  | .done _ | .raised _ => True

private theorem nextSite {P : Program} {r : SiteRanks} {site p : Nat} {node : Node}
    (checked : checkSiteRanks P.toArray r = true) (safe : r.once.getD site false = true)
    (atNode : P[p]? = some node) (seen : r.rank.getD p 0 ≤ r.rank.getD site 0)
    {t : Target} (edge : t ∈ successors node.continuation ++ node.handler.toList) (ρ : Env) :
    SiteInv P r site (.at t.label ρ) := by
  have inside := (List.getElem?_eq_some_iff.mp atNode).1
  have get : (P.toArray[p]!) = node := by
    rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,List.getElem?_toArray,atNode]
    rfl
  have succ : t.label ∈ SinglePass.nodeSucc P.toArray p := by
    unfold SinglePass.nodeSucc
    rw [get]
    exact List.mem_map.mpr ⟨t,edge,rfl⟩
  have ok := List.all_eq_true.mp (List.all_eq_true.mp checked p (List.mem_range.mpr (by simpa using inside))) _ succ
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true,Bool.not_eq_true'] at ok
  refine ⟨?_,Nat.le_trans ok.1 seen⟩
  rintro rfl
  rcases ok.2 with no | lt
  · simp [safe] at no
  · omega

private theorem siteStep {P site h st h' st'} (checked : checkSiteRanks P.toArray r = true) (safe : r.once.getD site false = true)
    (inv : SiteInv P r site st) (tr : Transition P h st h' st') : SiteInv P r site st' := by
  cases tr with
  | enter get =>
    exact ⟨_,_,get,rfl,rfl,inv.2⟩
  | expr => exact inv
  | raise | ret => trivial
  | bind | effect | yes | no | yesBind | noBind | tagBind | handle =>
    all_goals
      obtain ⟨p,node,get,hk,hh,seen⟩ := inv
      apply nextSite checked safe get seen
      simp [hk,hh,successors]
    all_goals grind

/-- Every positive-length execution from an allocation label ends at a
different label whenever the executable single-visit test accepts. -/
theorem namedSite_no_return {P site h ρ k h' ρ'} (safe : (namedSites P.toArray).getD site false = true)
    (run : Execution P (k + 1) h (.at site ρ) h' (.at site ρ')) : False := by
  unfold namedSites at safe
  dsimp only at safe
  split at safe
  case isFalse => simp at safe
  rename_i checked
  let r := siteRanks P.toArray
  have keep {j h s h' s'} (path : Execution P j h s h' s') : SiteInv P r site s → SiteInv P r site s' := by
    induction path with
    | refl => exact id
    | next tr _ ih => exact fun inv => ih (siteStep checked safe inv tr)
  cases run with
  | next tr tail =>
    cases tr with
    | enter get =>
      have inside := (List.getElem?_eq_some_iff.mp get).1
      exact (keep tail ⟨_,_,get,rfl,rfl,Nat.le_refl _⟩).1 rfl

end Verification.SourceClaimJson.CallbackOrigins
