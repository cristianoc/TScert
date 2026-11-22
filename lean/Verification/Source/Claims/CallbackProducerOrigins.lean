import Verification.Source.Claims.CallbackPrivateBirth

namespace Verification.SourceClaimJson.CallbackInferencePlan
open PointClaims CallbackOrigins ControlFlow CertificateProducer GraphCode TolerantFrames TolerantFrames.Reach Footprints HeapObservations

/-- The structural world available at a reached state. Point contexts
contain values, and the evaluated expression has valid references. -/
def GraphMoment (table : Table) (h : Heap) (st : State) :=
  ∃ s : IndexedHeap, s.h = h ∧ match st with
    | .at label ρ => RootsOk s.W ρ ∧ ∀ i < (table.at label).size, isVal (ρ i) = true
    | .eval t .. => RefsOk s.W t
    | _ => True

def producerOrigin (P : Program) (table : Table) (entry : Env) (inputs : Nat) (h : Heap) (st : State) :
    Origin → Val → Prop
  | .input i,v => i < inputs ∧ entry i = v
  | .allocated site,v => checkPrivateSite P.toArray table site = true → ∀ key field,
      (fieldsOf v).lookup key = some field → PrivateInv P table site field h st
  | _,_ => False

def producerSlots (P : Program) (table : Table) (entry : Env) (inputs : Nat) (h : Heap) (st : State)
    (slots : Slots) (ρ : Env) : Prop := ∀ i o, namedAt slots i = some o →
    producerOrigin P table entry inputs h st o (ρ i) ∧ isVal (ρ i) = true

private theorem originStep {P table entry inputs h st h' st' o v}
    (source : P.all (fun n => ObjectCoherence.sourceTerm n.expression) = true)
    (heap : ∀ (i : Nat) v, h[i]? = some v → isVal v = true)
    (tr : Transition P h st h' st') (origin : producerOrigin P table entry inputs h st o v) :
    producerOrigin P table entry inputs h' st' o v := by
  cases o with
  | allocated site => exact fun checked key field lookup => privateStep checked source heap (origin checked key field lookup) tr
  | input | read | other => exact origin

private theorem slotsStep {P table entry inputs h st h' st' slots ρ}
    (source : P.all (fun n => ObjectCoherence.sourceTerm n.expression) = true)
    (heap : ∀ (i : Nat) v, h[i]? = some v → isVal v = true)
    (tr : Transition P h st h' st') (names : producerSlots P table entry inputs h st slots ρ) :
    producerSlots P table entry inputs h' st' slots ρ :=
  fun i o hi => ⟨originStep source heap tr (names i o hi).1,(names i o hi).2⟩

private def ProducerInv (P : Program) (table : Table) (entry : Env) (inputs : Nat) (h : Heap) : State → Prop
  | .at label ρ => privateReady P.toArray table label = true ∧ producerSlots P table entry inputs h (.at label ρ) (table.at label) ρ
  | .eval t ρ k x => ∃ (label : Nat) (node : Node) (start : IndexedHeap) (n : Nat),
      P[label]? = some node ∧ node.continuation = k ∧ node.handler = x ∧
      privateReady P.toArray table label = true ∧ RootsOk start.W ρ ∧
      (∀ i < (table.at label).size, isVal (ρ i) = true) ∧
      Steps n start.h (instantiate 0 ρ node.expression) h t ∧ (allocates node.expression = true → BirthStage h t) ∧
      producerSlots P table entry inputs h (.eval t ρ k x) (table.at label) ρ
  | .done _ | .raised _ => True

private theorem nameEdgeAt {P : Program} {allowed table start inputs label node}
    (ok : checkNames P.toArray allowed start inputs table = true)
    (hn : P[label]? = some node) (active : privateReady P.toArray table label = true) :
    let slots := table.at label
    let normal := sourceName slots (pushes node.continuation) (namedResult allowed slots label node.expression)
    let edge := fun src (t : Target) => privateReady P.toArray table t.label && checkNameEdge table src t
    (successors node.continuation).all (edge normal) = true ∧ node.handler.toList.all (edge (sourceName slots true none)) = true := by
  have inside := (List.getElem?_eq_some_iff.mp hn).1
  have step := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 label (List.mem_range.mpr (by simpa using inside))
  simp only [privateReady,List.size_toArray,Nat.not_le_of_gt inside,decide_false,Bool.false_or] at active
  obtain ⟨row,hr⟩ := Option.isSome_iff_exists.mp active
  have actual : table.at label = row := by
    unfold Table.at
    cases hl : table[label]? with
    | none => simp [hl] at hr
    | some v => simp only [hl,Option.join_some] at hr; simp [Array.getD_eq_getD_getElem?,hl,hr]
  simp only [hr,Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,List.getElem?_toArray,
    hn,Option.getD_some,Bool.and_eq_true] at step
  simpa only [actual,privateReady,Bool.or_comm] using step

private theorem named_bound {slots : Slots} {i o} (hit : namedAt slots i = some o) : i < slots.size := by
  cases h : slots[i]? with
  | none => simp [namedAt,h] at hit
  | some v => exact (Array.getElem?_eq_some_iff.mp h).1

private theorem mappedProducer {P table entry inputs h st slots ρ edge pushed fresh v}
    (names : producerSlots P table entry inputs h st slots ρ)
    (value : ∀ o, fresh = some o → producerOrigin P table entry inputs h st o v ∧ isVal v = true)
    (checked : checkNameEdge table (sourceName slots pushed fresh) edge = true) :
    producerSlots P table entry inputs h st (table.at edge.label) (mapEnv edge.mapping (if pushed then push v ρ else ρ)) := by
  intro i o hi
  have valid := List.all_eq_true.mp checked i (List.mem_range.mpr (named_bound hi))
  rw [hi] at valid
  simp only [Option.all_some,beq_iff_eq] at valid
  unfold mapEnv
  cases pushed
  · exact names _ _ valid
  · cases hj : slot edge.mapping i with
    | zero => exact value _ (by simpa [sourceName,hj] using valid)
    | succ j => exact names _ _ (by simpa [sourceName,hj] using valid)

private theorem producerNormal {P : Program} {allowed table entry inputs start h t ρ k x edge}
    (checked : checkNames P.toArray allowed start inputs table = true)
    (source : P.all (fun n => ObjectCoherence.sourceTerm n.expression) = true)
    (heap : ∀ (i : Nat) v, h[i]? = some v → isVal v = true)
    (inv : ProducerInv P table entry inputs h (.eval t ρ k x)) (val : isVal t = true)
    (chosen : edge ∈ successors k)
    (tr : Transition P h (.eval t ρ k x) h (.at edge.label (mapEnv edge.mapping (if pushes k then push t ρ else ρ)))) :
    ProducerInv P table entry inputs h (.at edge.label (mapEnv edge.mapping (if pushes k then push t ρ else ρ))) := by
  obtain ⟨label,node,first,n,hn,rfl,rfl,ready,refs,values,run,birth,names⟩ := inv
  have checks := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (nameEdgeAt checked hn ready).1 edge chosen)
  have later := slotsStep source heap tr names
  refine ⟨checks.1,mappedProducer later (fun o hit => ⟨?_,val⟩) checks.2⟩
  by_cases copied : ∃ i, node.expression = .var i
  · obtain ⟨i,eq⟩ := copied
    rw [eq] at run hit
    have valid := later i o (by simpa only [namedResult] using hit)
    have same := PromiseCalls.steps_value valid.2 (by simpa [instantiate] using run)
    simpa [same] using valid.1
  · have result : namedResult allowed (table.at label) label node.expression =
        (if allowed.getD label false && allocates node.expression then some (.allocated label) else none) := by
      cases hx : node.expression <;> first | rfl | exact (copied ⟨_,hx⟩).elim
    rw [result] at hit
    split at hit <;> try contradiction
    rename_i condition
    cases hit
    have alloc := (Bool.and_eq_true_iff.mp condition).2
    intro privateCheck key field lookup
    apply birth_privateAt_of_hidden privateCheck hn ready alloc run val lookup first rfl refs values _ chosen
    rcases birth alloc with slow | ⟨_,finished⟩ | ⟨_,raised⟩
    · cases t <;> simp_all [allocates,isVal]
    · exact finished key field lookup
    · exact Bool.noConfusion (val.symm.trans (raises_not_val raised))

private theorem typedStepSnoc {n h t h' t' h'' t''} (r : Steps n h t h' t') (step : Step h' t' h'' t'') :
    Steps (n+1) h t h'' t'' := by
  induction r with
  | refl => exact .next step .refl
  | next tr _ ih => exact .next tr (ih step)

private theorem producerStep {P : Program} {allowed table entry inputs start h st h' st'}
    (checked : checkNames P.toArray allowed start inputs table = true)
    (source : P.all (fun n => ObjectCoherence.sourceTerm n.expression) = true)
    (moment : GraphMoment table h st)
    (inv : ProducerInv P table entry inputs h st) (tr : Transition P h st h' st') :
    ProducerInv P table entry inputs h' st' := by
  obtain ⟨world,href,current⟩ := moment
  have heap (i : Nat) (v : Val) (get : h[i]? = some v) : isVal v = true :=
    heap_isVal (s := world) (by simpa [href] using get)
  cases tr with
  | enter hn =>
    obtain ⟨ready,names⟩ := inv
    refine ⟨_,_,world,0,hn,rfl,rfl,ready,current.1,current.2,?_,?_,slotsStep source heap (.enter hn) names⟩
    · rw [href]; exact .refl
    · intro ha; exact .inl (instantiateAlloc ha _ _)
  | expr hs =>
    obtain ⟨l,n,b,j,hn,hk,hx,ready,refs,values,run,birth,names⟩ := inv
    exact ⟨l,n,b,j+1,hn,hk,hx,ready,refs,values,typedStepSnoc run hs,
      fun ha => birthStep (birth ha) ⟨world,href,current⟩ hs,slotsStep source heap (.expr hs) names⟩
  | handle raised =>
    obtain ⟨l,n,b,j,hn,hk,hx,ready,_,_,_,_,names⟩ := inv
    have edges := (nameEdgeAt checked hn ready).2
    rw [hx] at edges
    obtain ⟨active,edge⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp edges _ (List.mem_singleton_self _))
    exact ⟨active,mappedProducer (slotsStep source heap (.handle raised) names) (by simp) edge⟩
  | ret | raise => trivial
  | bind hv => exact producerNormal checked source heap inv hv (by simp [successors]) (.bind hv)
  | effect hv => exact producerNormal checked source heap inv hv (by simp [successors]) (.effect hv)
  | yes | no | yesBind | noBind =>
    all_goals apply producerNormal checked source heap inv rfl (by simp [successors])
    all_goals constructor
  | tagBind hv =>
    apply producerNormal checked source heap inv hv _ (.tagBind hv)
    simp only [successors,List.mem_cons]
    split <;> simp

/-- Producer slots carry their own dynamic object's privacy through each
actual transition. Distinct objects from repeated executions of a site
can coexist; this theorem never equates them. -/
theorem producerOrigins_reached {P : Program} {allowed table entry inputs start before h label ρ n}
    (checked : checkNames P.toArray allowed start inputs table = true)
    (source : P.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (run : Execution P n before (.at start entry) h (.at label ρ))
    (moments : ∀ j hj st, j < n → Execution P j before (.at start entry) hj st → GraphMoment table hj st) :
    privateReady P.toArray table label = true ∧ producerSlots P table entry inputs h (.at label ρ) (table.at label) ρ := by
  have keep {k h st h' st'} (r : Execution P k h st h' st') (inv : ProducerInv P table entry inputs h st)
      (typed : ∀ j hj s, j < k → Execution P j h st hj s → GraphMoment table hj s) :
      ProducerInv P table entry inputs h' st' := by
    induction r with
    | refl => exact inv
    | next tr _ ih =>
      exact ih (producerStep checked source (typed 0 _ _ (by omega) .refl) inv tr)
        (fun j hj s bound pre => typed (j+1) hj s (by omega) (.next tr pre))
  apply keep run _ moments
  have init := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1
  refine ⟨by simpa only [privateReady,Bool.or_comm] using init.1,?_⟩
  intro i o ho
  have ok := List.all_eq_true.mp init.2 i (List.mem_range.mpr (named_bound ho))
  rw [ho] at ok
  simp only [Option.all_some,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at ok
  obtain ⟨bound,rfl⟩ := ok
  exact ⟨⟨bound,rfl⟩,values i bound⟩

/-- A captured private field is preserved by a completed invocation at a
reached producer node, at either exit. Its origin may be a repeated site. -/
theorem producerPrivate_kept {P : Program} {allowed table entry inputs start before h label ρ n}
    (checked : checkNames P.toArray allowed start inputs table = true)
    (source : P.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (run : Execution P n before (.at start entry) h (.at label ρ))
    (moments : ∀ j hj st, j < n → Execution P j before (.at start entry) hj st → GraphMoment table hj st)
    {node fn recv args} (atNode : P[label]? = some node) (invoke : node.expression = .invoke fn recv args)
    {slot site key field cell} (privateCheck : checkPrivateSite P.toArray table site = true)
    (name : (table.at label)[slot]? = some [.allocated site]) (member : (fieldsOf (ρ slot)).lookup key = some field)
    (atEntry : h[field]? = some cell) {after t} (evaluation : ValRun h (instantiate 0 ρ node.expression) after t) :
    after[field]? = some cell := by
  have reached := producerOrigins_reached checked source values run moments
  have named := (reached.2 slot (.allocated site) (by simp [namedAt,name])).1
  obtain ⟨active,old,heap,vars⟩ := named privateCheck key field member
  have uses := (checkSiteAt privateCheck atNode active).1
  rw [invoke] at uses
  exact call_keeps_unreachable evaluation atEntry (cleanAtTerm (by simpa only [invoke,privateUse] using uses) vars
    (List.all_eq_true.mp source _ (List.mem_of_getElem? atNode)) old heap)

end Verification.SourceClaimJson.CallbackInferencePlan
