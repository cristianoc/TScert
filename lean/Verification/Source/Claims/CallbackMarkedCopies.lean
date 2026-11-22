import Verification.Source.Claims.CallbackInterfaceCheck
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins ControlFlow CertificateProducer GraphCode

theorem knownSiblings_member {inputs siblings interfaces slot row}
    (member : (slot,row) ∈ knownSiblings inputs siblings interfaces) :
    ∃ j, siblings[j]? = some row.name ∧ slot = inputs - siblings.length + j ∧ row ∈ interfaces := by
  obtain ⟨⟨name,j⟩,pos,hit⟩ := List.mem_filterMap.mp member
  obtain ⟨iface,found,eq⟩ := Option.map_eq_some_iff.mp hit
  cases eq
  have named := List.find?_some found
  simp only [beq_iff_eq] at named
  exact ⟨j,named ▸ (List.mem_zipIdx_iff_getElem?.mp pos),rfl,List.mem_of_find?_eq_some found⟩

/-- Direct copies from the declaration input along a chosen graph path.
A branch pushes its result where the graph continuation does; a caught
exception replaces that result with an ordinary thrown value. -/
inductive Copies (P : Program) (start : Nat) (marked : List Nat) : Nat → (Nat → Bool) → Prop where
  | entry : Copies P start marked start marked.contains
  | normal {l slots node target} : Copies P start marked l slots → P[l]? = some node →
      target ∈ successors node.continuation → Copies P start marked target.label
        (fun i => afterSlot slots (pushes node.continuation) (markedResult slots node.expression)
          (PointClaims.slot target.mapping i))
  | caught {l slots node target} : Copies P start marked l slots → P[l]? = some node →
      node.handler = some target → Copies P start marked target.label
        (fun i => afterSlot slots true false (PointClaims.slot target.mapping i))

private theorem inputsAt {P : Program} {marked table start inputs l node}
    (ok : checkMayInputs P.toArray table start inputs marked = true) (hn : P[l]? = some node)
    (ready : privateReady P.toArray table l = true) :
    let slots := table.at l
    let valid := fun j => decide (j < slots.size)
    let seen := mayInput marked slots
    (SinglePass.mentioned 0 node.expression).any (fun ids => ids.all (· < slots.size)) = true ∧
      (successors node.continuation).all (markedEdge P.toArray table marked (afterSlot valid (pushes node.continuation) true)
        (afterSlot seen (pushes node.continuation) (markedResult seen node.expression))) = true ∧
      node.handler.toList.all (markedEdge P.toArray table marked (afterSlot valid true true) (afterSlot seen true false)) = true := by
  have inside := (List.getElem?_eq_some_iff.mp hn).1
  have found := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 l (List.mem_range.mpr (by simpa using inside))
  simp only [privateReady,List.size_toArray,Nat.not_le_of_gt inside,decide_false,Bool.false_or] at ready
  obtain ⟨row,hr⟩ := Option.isSome_iff_exists.mp ready
  have actual : table.at l = row := by
    unfold Table.at
    cases hl : table[l]? with
    | none => simp [hl] at hr
    | some v => simp only [hl,Option.join_some] at hr; simp [Array.getD_eq_getD_getElem?,hl,hr]
  simp only [hr,Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,List.getElem?_toArray,hn,Option.getD_some,Bool.and_eq_true] at found
  rw [actual]
  exact ⟨found.1.1,found.1.2,found.2⟩

private theorem afterTracked {size : Nat} {seen live : Nat → Bool} {pushed a b : Bool}
    (covered : ∀ i < size, live i = true → seen i = true) (fresh : a = true → b = true) {i}
    (valid : afterSlot (fun j => decide (j < size)) pushed true i = true)
    (hit : afterSlot live pushed a i = true) : afterSlot seen pushed b i = true := by
  cases pushed <;> cases i <;> first | exact fresh hit | exact covered _ (of_decide_eq_true valid) hit

private theorem checkedEdge {P : Program} {table marked target size pushed a b} {live seen : Nat → Bool}
    (covered : ∀ i < size, live i = true → seen i = true) (fresh : a = true → b = true)
    (ok : markedEdge P.toArray table marked (afterSlot (fun j => decide (j < size)) pushed true) (afterSlot seen pushed b) target = true) :
    privateReady P.toArray table target.label = true ∧ ∀ i < (table.at target.label).size,
      afterSlot live pushed a (PointClaims.slot target.mapping i) = true → mayInput marked (table.at target.label) i = true := by
  obtain ⟨ready,all⟩ := Bool.and_eq_true_iff.mp ok
  refine ⟨ready, fun i bounded hit => ?_⟩
  obtain ⟨valid,keep⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp all i (List.mem_range.mpr bounded))
  simpa only [afterTracked covered fresh valid hit,Bool.not_true,Bool.false_or] using keep

theorem checkedCopies {P : Program} {table marked start inputs l live}
    (ok : checkMayInputs P.toArray table start inputs marked = true) (path : Copies P start marked l live) :
    privateReady P.toArray table l = true ∧ ∀ i < (table.at l).size, live i = true → mayInput marked (table.at l) i = true := by
  induction path with
  | entry =>
    obtain ⟨⟨⟨ready,_⟩,starts⟩,_⟩ := (show ((_ ∧ _) ∧ _) ∧ _ from by simpa only [checkMayInputs,Bool.and_eq_true] using ok)
    exact ⟨ready,fun i _ hit => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp starts i (List.contains_iff_mem.mp hit))).2⟩
  | normal prev hn edge ih =>
    obtain ⟨reads,normal,_⟩ := inputsAt ok hn ih.1
    apply checkedEdge ih.2 _ (List.all_eq_true.mp normal _ edge)
    intro hit
    unfold markedResult at hit ⊢
    split at hit
    next j e =>
      simp only [e] at reads ⊢
      apply ih.2 _ _ hit
      simpa [SinglePass.mentioned] using reads
    next => contradiction
  | caught prev hn edge ih =>
    obtain ⟨_,_,handler⟩ := inputsAt ok hn ih.1
    exact checkedEdge ih.2 id (List.all_eq_true.mp handler _ (by simp [edge]))

end Verification.SourceClaimJson.CallbackInterfaceCheck
