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

private def rootInv (table : List (List Fact)) (entry : Env) (initial : Heap) : State → Prop
  | .at l ρ => Holds (atLabel table l) ρ entry initial
  | .eval t ρ cont handler =>
    ∃ facts origins, Holds facts ρ entry initial ∧
      (∀ r ∈ origins, HeapKnowledge.readPath initial (entry r.position) r.path = some t ∧ isVal t = true) ∧
      checkEdges table facts origins cont = true ∧ checkHandler table facts handler = true
  | .done _ | .raised _ => True

private theorem rootInv_step {P start width table entry initial h st h' st'}
    (check : checkRootTable P start width table = true) (vals : ∀ i < width, isVal (entry i) = true)
    (inv : rootInv table entry initial st) (tr : Transition P h st h' st') :
    rootInv table entry initial st' := by
  cases tr with
  | enter hn =>
    have localOK := List.all_eq_true.mp (Bool.and_eq_true_iff.mp check).2 _
      (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hn).1)
    simp only [hn,Option.any_some,Bool.and_eq_true] at localOK
    obtain ⟨⟨paths,edges⟩,handler⟩ := localOK
    refine ⟨_,_,inv,?_,edges,handler⟩
    intro r hr
    unfold ArgumentRegionGraph.copyOrigins at hr
    split at hr
    · rename_i i hi
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hr
      obtain ⟨member,slot⟩ := List.mem_filter.mp hf
      have path := List.all_eq_true.mp paths f member
      obtain ⟨empty,bound⟩ := Bool.and_eq_true_iff.mp path
      have he := inv f member
      have nil := List.isEmpty_iff.mp empty
      have same := he
      rw [nil] at same
      have val := vals f.region.position (of_decide_eq_true bound)
      simp only [HeapKnowledge.readPath,Option.some.injEq] at same
      rw [same] at val
      simp only [beq_iff_eq] at slot
      simpa [hi,instantiate,slot] using And.intro he val
    · contradiction
  | expr st =>
    obtain ⟨facts,origins,hf,hv,edges,handler⟩ := inv
    exact ⟨facts,origins,hf,fun r hr => False.elim (value_no_step (hv r hr).2 st),edges,handler⟩
  | handle =>
    obtain ⟨_,_,hf,_,_,hh⟩ := inv
    exact checkHandler_sound hh hf _ rfl _
  | ret | raise => trivial
  | bind | effect | yes | no | yesBind | noBind | tagBind =>
    all_goals
      obtain ⟨_,_,hf,hv,edges,_⟩ := inv
      apply checkEdges_sound edges hf (fun r hr => (hv r hr).1)
      simp [successors]
    all_goals grind

theorem certifiedRootTable_reached {P start width table entry initial k l h ρ}
    (vals : ∀ i < width, isVal (entry i) = true)
    (run : Execution P k initial (.at start entry) h (.at l ρ)) :
    Holds (atLabel (certifiedRootTable P start width table) l) ρ entry initial := by
  unfold certifiedRootTable
  split
  · rename_i check
    have preserve {k h st h' st'} (steps : Execution P k h st h' st') :
        rootInv table entry initial st → rootInv table entry initial st' := by
      induction steps with
      | refl => exact id
      | next tr _ ih => exact fun hi => ih (rootInv_step check vals hi tr)
    exact preserve run (checkEntry_sound (Bool.and_eq_true_iff.mp check).1 entry initial)
  · simp [atLabel,Holds]

end Verification.SourceClaimJson.CallbackEffectInference
