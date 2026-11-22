import Verification.Source.Claims.CallbackPrefixGraph
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallArguments ControlFlow GraphCode ProgramTyping PositiveGraphs PositiveRules ProgramCertificates HeapObservations
open CallbackInferencePlan CallbackOrigins CallbackEffectInference TolerantFrames PassUnit LabelStore

/-- The actual written two-formal ABI at the unique direct source call.
Only the two ordinary value comparisons are used. Sibling captures reside
after the formals, and the caller's marked walker slot needs no promise. -/
structure FixedInputs {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (I : PositiveCertificates.InstanceImageCheck G)
    (Γ : List (Option (Ty ι))) (x cb : Nat) (inputs : List (Ty ι)) (hosts : List (Ty ι)) where
  xsType : Ty ι
  cbType : Ty ι
  xsFormal : Ty ι
  cbFormal : Ty ι
  xsSlot : Γ[x]?.join = some xsType
  cbSlot : Γ[cb]?.join = some cbType
  formals : inputs = xsFormal :: cbFormal :: hosts
  xsEvidence : PositiveCertificates.SubtypeChoices ι
  cbEvidence : PositiveCertificates.SubtypeChoices ι
  xsOK : PositiveCertificates.checkUsing G I xsType xsFormal xsEvidence = true
  cbOK : PositiveCertificates.checkUsing G I cbType cbFormal cbEvidence = true

theorem FixedInputs.entry {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {I Γ x cb inputs hosts}
    (fixed : FixedInputs G I Γ x cb inputs hosts) {ρ n W h captures self sep idx}
    (partialTypes : PartialEnv G Γ ρ n W) (hostTypes : EnvOk G hosts (envOf (captures ++ [self]) .undef) n W)
    (separation : sep.facts = []) (indices : idx = []) (world : WorldAdm W) (heap : HeapOk n W h) :
    TolerantFrames.Target.EntryHolds G inputs sep idx (envOf (ρ x :: ρ cb :: (captures ++ [self])) .undef) n W h := by
  have xt := PositiveCertificates.acceptedUsing fixed.xsOK n W _ (partialTypes.2 _ _ fixed.xsSlot)
  have ct := PositiveCertificates.acceptedUsing fixed.cbOK n W _ (partialTypes.2 _ _ fixed.cbSlot)
  rw [fixed.formals]
  refine ⟨?_,?_,?_,world,heap⟩
  · simpa [push_envOf] using (hostTypes.push ct).push xt
  · simp [HeapSeparation.Holds,separation]
  · simp [HeapKnowledge.IndexHolds,indices]

private theorem frameFacts {P start c captures fields oid ρ self x cb} {n} {W : WorldT n}
    (linked : self = nativeWalker P start c captures fields oid)
    (good : RefsOk W self) (held : RootsOk W ρ) (vals : ∀ i, isVal (ρ i) = true)
    (capVals : ∀ t ∈ captures, isVal t = true) :
    RootsOk W (envOf (ρ x :: ρ cb :: (captures ++ [self])) .undef) ∧
    ∀ i, isVal (envOf (ρ x :: ρ cb :: (captures ++ [self])) .undef i) = true := by
  have capRefs := (graph_code_refs (linked ▸ good)).2
  have selfVal : isVal self = true := by rw [linked]; rfl
  constructor
  · apply envOf_refs_of _ RefsOk_undef
    intro t member
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | hx | rfl <;> first | exact held _ | exact good | exact capRefs _ hx
  · intro i
    generalize eq : envOf (ρ x :: ρ cb :: (captures ++ [self])) .undef i = t
    rcases getD_mem_or (ρ x :: ρ cb :: (captures ++ [self])) i .undef with mem | deflt
    · change (envOf _ _ i) ∈ _ at mem
      rw [eq] at mem
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at mem
      rcases mem with rfl | rfl | hx | rfl <;> first | exact vals _ | exact selfVal | exact capVals _ hx
    · exact (eq.symm.trans deflt) ▸ rfl

def callerEntryTypes (inputs : List (Ty ι)) (opaqueSlot : Nat) : List (Option (Ty ι)) :=
  inputs.zipIdx.map fun (A,i) => if i = opaqueSlot then none else some A

theorem TypicalPair.collectorEntry {f caller producer fuel p forwarded}
    (pair : TypicalPair f caller producer fuel p forwarded) (over : PassUnit.OverStore f)
    {startL startD h₀ label x cb fn input} {node : Node}
    (loc : pair.callerRun.request.program[label]? = some node)
    (direct : node.expression = .invoke (.var fn) .undef [.var x,.var cb])
    (binding : originOf (pair.callerRun.origins.at label) (.var fn) = some (.input input))
    (selected : (knownSiblings pair.callerRun.request.inputs.length pair.callerRun.request.siblings [p]).find? (·.1 == input) = some (input,p))
    (abi : checkedCallFrame p .undef [.var x,.var cb] = [.var x,.var cb])
    (present : absentCallback pair.callerRun.request label [.var x,.var cb] 1 = false)
    (literal : CollectorLiteral pair.callerRun label cb)
    {captures fields oid} (linked : envOf startL startD input =
      nativeWalker pair.producerRun.request.program pair.producerRun.request.start pair.producerRun.request.comp captures fields oid)
    {slot mid ret mapping mapping₂ retTy}
    (cont : node.continuation = .bind ⟨mid,some ((slot+1)::mapping)⟩) (unhandled : node.handler = none)
    (middle : pair.callerRun.request.program[mid]? = some ⟨.nul,.effect ⟨ret,some (0::mapping₂)⟩,none⟩)
    (endNode : pair.callerRun.request.program[ret]? = some ⟨.var 0,.ret,none⟩)
    (savedSlot : literal.slotTypes[slot]?.join = some retTy)
    (source : pair.callerRun.request.program.all (fun nd => ObjectCoherence.sourceTerm nd.expression) = true)
    (pointShape : ∀ l nd, pair.producerRun.request.program[l]? = some nd →
      ∀ slot br ba, nd.expression = .invoke (.var slot) br ba →
      (pair.producerRun.origins.at l)[slot]? = some [.input 1] →
      numericInvoke (StoreView.graph f.F.store) (((pair.producerRun.request.claims[l]?).map (·.context)).getD []) nd.expression = true)
    {hosts n} {W : WorldT n}
    (prefixPlan : PrefixPlan (RequestJson.graph pair.callerRun.request.toRequest)
      (StoreView.images pair.callerRun.request.types) (admits (pair.callerRun.codes.toList.map (·.entry)))
      pair.callerRun.request.program label literal.slotTypes pair.callerRun.request.start (callerEntryTypes pair.callerRun.request.inputs input))
    (bindingTypes : FixedInputs (StoreView.graph f.F.store) (StoreView.images f.F.store)
      literal.slotTypes x cb pair.producerRun.request.inputs hosts)
    (noSep : pair.producerRun.request.entrySeparation.facts = []) (noIdx : pair.producerRun.request.entryIndices = [])
    (sourceGoal : pair.callerRun.request.goal = .plain retTy)
    (_hostWidth : hosts.length = captures.length)
    (hostTypes : EnvOk (StoreView.graph f.F.store) hosts (envOf (captures ++ [envOf startL startD input]) .undef) n W)
    (capVals : ∀ v ∈ captures, isVal v = true)
    (typed : PartialEnv (RequestJson.graph pair.callerRun.request.toRequest) (callerEntryTypes pair.callerRun.request.inputs input) (envOf startL startD) n W)
    (roots : RootsOk W (envOf startL startD)) (vals : ∀ i, isVal (envOf startL startD i) = true)
    (world : WorldAdm W) (heap : HeapOk n W h₀) (closed : ∀ v ∈ h₀, Scoped 0 v) :
    SafePostExc (excOf (StoreView.graph f.F.store)) (GoalHolds (StoreView.graph f.F.store) pair.callerRun.request.goal
      (pair.callerRun.request.goal.argument (envOf startL startD))) (fun _ _ => True) (fun _ => True) n W h₀
      (gotoOf pair.callerRun.request.program pair.callerRun.request.start startL startD pair.callerRun.request.comp) := by
  rw [sourceGoal]
  let a := pair.callerRun
  let b := pair.producerRun
  let entryEnv := envOf startL startD
  let G := StoreView.graph f.F.store
  have store := over.graph a.plan
  have sameG : RequestJson.graph a.request.toRequest = G := by
    change StoreView.graph a.request.types = StoreView.graph f.F.store
    rw [store]
  change SafePostExc (excOf G) (meaning G retTy) _ _ _ _ _ _
  rw [← sameG]
  let Keep := fun m (U : WorldT m) => EnvOk G hosts (envOf (captures ++ [entryEnv input]) .undef) m U
  apply prefixPlan.safe (Keep := Keep) (inferCodes_table_sound a.codeAnswers) source
    (by intro n W j le U ext old; exact EnvOk.transfer old _ le _ ext) _ (.refl : Execution a.request.program 0 h₀ (.at a.request.start entryEnv) _ _)
    typed roots vals hostTypes world heap
  intro k h L d m U path hostsNow point points valsNow worldNow heapNow
  rw [sameG]
  have startClosed : Scoped 0 (gotoOf a.request.program a.request.start startL startD a.request.comp) := by
    refine ⟨(scopedArgs_iff ..).mpr ?_,?_⟩
    · intro v hv
      obtain ⟨j,atJ⟩ := List.mem_iff_getElem?.mp hv
      simpa [envOf,List.getD_eq_getElem?_getD,atJ] using typed.1 j
    · simpa [envOf] using typed.1 startL.length
  have closedNow : ∀ v ∈ h, Scoped 0 v := by
    have originPath := path
    rw [← SourceElaboration.program_nodes a.request.program] at originPath
    exact reachedHeapClosed originPath .goto startClosed closed
  have original := checkedNames_reached a.names (fun i _ => vals i) path
  obtain ⟨_,valid,_,_,_,held⟩ := original
  obtain ⟨_,varEq,hit⟩ := namedOrigin_slot binding
  cases varEq
  have live : entryEnv input = envOf L d fn := (held fn (.input input) (by change CallbackOrigins.namedAt (pair.callerRun.origins.at label) fn = _; simp [CallbackOrigins.namedAt,hit])).1.2
  have selfRefs : RefsOk U (entryEnv input) := live ▸ points fn
  obtain ⟨allRefs,allVals⟩ := frameFacts (x := x) (cb := cb) linked selfRefs points valsNow capVals
  apply TypicalPair.collectorReturn pair over (fun i _ => vals i) roots heap path loc direct binding selected abi
    present literal linked cont unhandled middle endNode savedSlot source closedNow point pointShape points
    (bindingTypes.entry (by change PartialEnv G _ _ _ _; rw [← sameG]; exact point) hostsNow noSep noIdx worldNow heapNow) allRefs allVals

theorem TypicalPair.noopEntry {f caller producer fuel p forwarded}
    (pair : TypicalPair f caller producer fuel p forwarded) (over : PassUnit.OverStore f)
    {startL startD h₀ label x cb fn input} {node : Node}
    (loc : pair.callerRun.request.program[label]? = some node)
    (direct : node.expression = .invoke (.var fn) .undef [.var x,.var cb])
    (binding : originOf (pair.callerRun.origins.at label) (.var fn) = some (.input input))
    (empty : emptyArgumentAt pair.callerRun.request.program pair.callerRun.origins label cb = true)
    {captures fields oid} (linked : envOf startL startD input =
      nativeWalker pair.producerRun.request.program pair.producerRun.request.start pair.producerRun.request.comp captures fields oid)
    {ret mapping retTy finalSlots}
    (cont : node.continuation = .bind ⟨ret,some (0::mapping)⟩) (unhandled : node.handler = none)
    (endNode : pair.callerRun.request.program[ret]? = some ⟨.var 0,.ret,none⟩)
    (plain : pair.producerRun.request.goal = .plain retTy)
    (source : pair.callerRun.request.program.all (fun nd => ObjectCoherence.sourceTerm nd.expression) = true)
    {hosts n} {W : WorldT n}
    (prefixPlan : PrefixPlan (RequestJson.graph pair.callerRun.request.toRequest)
      (StoreView.images pair.callerRun.request.types) (admits (pair.callerRun.codes.toList.map (·.entry)))
      pair.callerRun.request.program label finalSlots pair.callerRun.request.start (callerEntryTypes pair.callerRun.request.inputs input))
    (bindingTypes : FixedInputs (StoreView.graph f.F.store) (StoreView.images f.F.store)
      finalSlots x cb pair.producerRun.request.inputs hosts)
    (noSep : pair.producerRun.request.entrySeparation.facts = []) (noIdx : pair.producerRun.request.entryIndices = [])
    (sourceGoal : pair.callerRun.request.goal = .plain retTy)
    (_hostWidth : hosts.length = captures.length)
    (hostTypes : EnvOk (StoreView.graph f.F.store) hosts (envOf (captures ++ [envOf startL startD input]) .undef) n W)
    (capVals : ∀ v ∈ captures, isVal v = true)
    (typed : PartialEnv (RequestJson.graph pair.callerRun.request.toRequest) (callerEntryTypes pair.callerRun.request.inputs input) (envOf startL startD) n W)
    (roots : RootsOk W (envOf startL startD)) (vals : ∀ i, isVal (envOf startL startD i) = true)
    (world : WorldAdm W) (heap : HeapOk n W h₀) :
    SafePostExc (excOf (StoreView.graph f.F.store)) (GoalHolds (StoreView.graph f.F.store) pair.callerRun.request.goal
      (pair.callerRun.request.goal.argument (envOf startL startD))) (fun _ _ => True) (fun _ => True) n W h₀
      (gotoOf pair.callerRun.request.program pair.callerRun.request.start startL startD pair.callerRun.request.comp) := by
  rw [sourceGoal]
  let a := pair.callerRun
  let b := pair.producerRun
  let entryEnv := envOf startL startD
  let G := StoreView.graph f.F.store
  have store := over.graph a.plan
  have sameG : RequestJson.graph a.request.toRequest = G := by
    change StoreView.graph a.request.types = StoreView.graph f.F.store
    rw [store]
  change SafePostExc (excOf G) (meaning G retTy) _ _ _ _ _ _
  rw [← sameG]
  let Keep := fun m (U : WorldT m) => EnvOk G hosts (envOf (captures ++ [entryEnv input]) .undef) m U
  apply prefixPlan.safe (Keep := Keep) (inferCodes_table_sound a.codeAnswers) source
    (by intro n W j le U ext old; exact EnvOk.transfer old _ le _ ext) _ (.refl : Execution a.request.program 0 h₀ (.at a.request.start entryEnv) _ _)
    typed roots vals hostTypes world heap
  intro k h L d m U path hostsNow point points valsNow worldNow heapNow
  rw [sameG]
  have original := checkedNames_reached a.names (fun i _ => vals i) path
  obtain ⟨_,valid,_,_,_,held⟩ := original
  obtain ⟨_,varEq,hit⟩ := namedOrigin_slot binding
  cases varEq
  have live : entryEnv input = envOf L d fn := (held fn (.input input) (by change CallbackOrigins.namedAt (pair.callerRun.origins.at label) fn = _; simp [CallbackOrigins.namedAt,hit])).1.2
  have selfRefs : RefsOk U (entryEnv input) := live ▸ points fn
  obtain ⟨allRefs,allVals⟩ := frameFacts (x := x) (cb := cb) linked selfRefs points valsNow capVals
  exact pair.safeReturn (η := G.env) over (fun i _ => vals i) path loc direct binding empty cont unhandled endNode
    linked plain source points (bindingTypes.entry (by change PartialEnv G _ _ _ _; rw [← sameG]; exact point)
    hostsNow noSep noIdx worldNow heapNow) allRefs allVals

end Verification.SourceClaimJson.CallbackInterfaceCheck
