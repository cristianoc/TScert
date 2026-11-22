import Verification.Source.Claims.CallbackProducerOrigins

namespace Verification.SourceClaimJson.CallbackInferencePlan
open CallbackOrigins CallbackPreservation ControlFlow TolerantFrames TolerantFrames.ReadOnly Footprints

private theorem private_member {slots privateRoots ρ h l} {r : Region} (privateRegion : ownPrivate slots privateRoots r = true)
    (member : r.mem ρ h l = true) :
    ∃ slot site key, slots[slot]? = some [.allocated site] ∧ site ∈ privateRoots ∧
      (fieldsOf (ρ slot)).lookup key = some l := by
  induction r with
  | inCls r c ih =>
    exact ih privateRegion (Bool.and_eq_true_iff.mp member).1
  | path i p key =>
    cases p with
    | cons => contradiction
    | nil =>
      unfold ownPrivate at privateRegion
      split at privateRegion
      next site hit => exact ⟨i,site,key,hit,List.contains_iff_mem.mp privateRegion,
        by simpa only [Region.mem,HeapKnowledge.readPath,beq_iff_eq] using member⟩
      next => contradiction
  | field i key =>
    unfold ownPrivate at privateRegion
    split at privateRegion
    next site hit => exact ⟨i,site,key,hit,List.contains_iff_mem.mp privateRegion,by simpa [Region.mem] using member⟩
    next => contradiction
  | fields | cells | cls | all | pathFields | pathCells | spine => contradiction

/-- Every private region discarded from a published demand has its
concrete change bound at this invocation. -/
theorem producerPrivate_supported {P : Program} {allowed table entry inputs start before h label ρ n proposed}
    (checked : checkNames P.toArray allowed start inputs table = true)
    (source : P.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (run : Execution P n before (.at start entry) h (.at label ρ))
    (moments : ∀ j hj st, j < n → Execution P j before (.at start entry) hj st → GraphMoment table hj st)
    {node fn recv args} (atNode : P[label]? = some node) (invoke : node.expression = .invoke fn recv args)
    {after t} (evaluation : ValRun h (instantiate 0 ρ node.expression) after t)
    (e : Region × Change)
    (claimed : ownPrivate (table.at label) (certifiedPrivate P.toArray table proposed) e.1 = true) :
    Supported [e] ρ h after := by
  intro item member l v inRegion old
  obtain rfl := List.mem_singleton.mp member
  obtain ⟨slot,site,key,origin,isPrivate,field⟩ := private_member claimed inRegion
  have ok := (List.mem_filter.mp isPrivate).2
  exact ⟨v,producerPrivate_kept checked source values run moments atNode invoke ok origin field old evaluation,
    Change.Holds.refl _ _ _⟩

/-- The exact immutable supports used by a replayed producer call follow
from its checked origins and the published obligations at this call. -/
theorem producerFrames_supported {P : Program} {allowed table entry inputs start before h label ρ n proposed params}
    (rows : List (Row P.toArray table (certifiedPrivate P.toArray table proposed) params))
    (checked : checkNames P.toArray allowed start inputs table = true)
    (source : P.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (run : Execution P n before (.at start entry) h (.at label ρ))
    (moments : ∀ j hj st, j < n → Execution P j before (.at start entry) hj st → GraphMoment table hj st)
    {node fn recv args} (atNode : P[label]? = some node) (invoke : node.expression = .invoke (.var fn) recv args)
    {after t} (evaluation : ValRun h (instantiate 0 ρ node.expression) after t)
    {supports} (selected : SinglePass.framedAt (framesOf rows) label = some supports)
    (callbacks : ∀ d ∈ (publication rows).demands, d.parameter ∈ params → entry d.parameter = ρ fn →
      Supported d.support.normal entry h after) : ∀ S ∈ supports, Supported S ρ h after := by
  unfold SinglePass.framedAt at selected
  obtain ⟨pair,found,rfl⟩ := Option.map_eq_some_iff.mp selected
  have atLabel := List.find?_some found
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
  simp only [beq_iff_eq] at atLabel
  subst label
  obtain ⟨param,state,marked,hc⟩ := row.source
  have getNode : P.toArray[row.label]! = node := by simp [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,atNode]
  have names := (producerOrigins_reached checked source values run moments).2
  have eqInput {slot p} (hit : (table.at row.label)[slot]? = some [.input p]) : entry p = ρ slot :=
    (names slot (.input p) (by simp [namedAt,hit])).1.2
  have roots : RealizesRoots (entryRoot (table.at row.label)) ρ entry h := by
    intro i p path hi
    unfold entryRoot at hi
    split at hi
    next j lookup => cases hi; simp [HeapKnowledge.readPath,eqInput lookup]
    next => contradiction
  have member : row.candidate.demand ∈ (publication rows).demands :=
    List.mem_eraseDups.mpr (List.mem_map.mpr ⟨row,hr,rfl⟩)
  rw [hc,getNode] at member ⊢
  apply atCall_supported roots (producerPrivate_supported checked source values run moments atNode invoke evaluation)
  apply callbacks _ member
  all_goals
    simp only [getNode,invoke,invocation] at marked
    split at marked
    next i lookup =>
      split at marked
      next inParams => cases marked; first | exact List.contains_iff_mem.mp inParams | exact eqInput lookup
      next => contradiction
    next => contradiction

end Verification.SourceClaimJson.CallbackInferencePlan
