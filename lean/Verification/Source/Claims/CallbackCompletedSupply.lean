import Verification.Source.Claims.CallbackLiteralInvocation
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins CallbackPreservation CallbackEffectInference ControlFlow Footprints CallEffects ProgramTyping
open CallbackInferencePlan
/-- A checked literal supply meets the producer demand on the entire
completed native call. The row's entry typing is for the actual reached
graph state and budget, including allocation of a rest spine. -/
theorem checkedLiteral_call_supported {τ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView τ ι]
    {request : SourceElaboration.SourceRequest τ ι} {fuel codes known final}
    {q : RequestJson.CodeRequest ι} {summary : Summary} {P : Program} {table : Table}
    {inputs start entry l ρ h₀ h k n₀} {W₀ : WorldT n₀}
    (checkNames : CallbackOrigins.checkNames P.toArray (namedSites P.toArray) start inputs table = true)
    (callerValues : ∀ i < inputs, isVal (entry i) = true) (callerRoots : RootsOk W₀ entry) (callerHeap : HeapOk n₀ W₀ h₀)
    (reached : Execution P k h₀ (.at start entry) h (.at l ρ))
    {frame : List Tm} {d : Demand} {argument : Tm} {site : Nat} {node : Node}
    {caps kind component fields vals} {actual : Env} {br : Tm} {ba : List Tm} {producer : Env} {fn : Nat}
    {before after : Heap} {callSteps : Nat} (v : Val)
    (accept : d.check (argumentRoots inputs P.length (table.at l) frame)
      (fun p => frame[p]?.bind (closure codes P.toArray table inputs (table.at l)
        (invocationArguments d (argumentRoots inputs P.length (table.at l) frame))))
      (separation inputs P.length (table.at l)) = true)
    (atArg : frame[d.parameter]? = some argument)
    (atSite : originOf (table.at l) argument = some (.allocated site)) (lookup : P[site]? = some node)
    (literal : node.expression = .makeAt (.graph q.entry.arity q.entry.exprs q.entry.conts q.entry.start caps kind
      q.entry.spine.isSome component) fields vals)
    (width : caps.length = q.entry.captures.length)
    (member : (⟨q.entry,summary⟩ : CheckedCode ι) ∈ codes)
    (inferred : inferCodes request fuel = .ok (codes,known,final))

    (passed : ∀ i t o j, frame[i]? = some t → originOf (table.at l) t = some o →
      identity inputs o = some j → actual i = instantiate 0 ρ t)
    {slots privateSites param proposal}
    (proposalAt : d = (atCall slots privateSites param proposal (.invoke (.var fn) br ba)).demand)
    (callback : actual d.parameter = producer fn)
    (ready : readCall (.invoke (.var fn) br ba) = true) (values : ∀ i, isVal (producer i) = true)
    (heapValues : ∀ (i : Nat) (x : Tm), before[i]? = some x → isVal x = true)
    (closed : Scoped 0 (instantiate 0 producer (.invoke (.var fn) br ba))) (heapClosed : ∀ t ∈ before, Scoped 0 t)
    (roots : RealizesRoots (entryRoot slots) producer actual before)
    (completed : HeapObservations.Steps callSteps before (instantiate 0 producer (.invoke (.var fn) br ba)) after v)
    (value : isVal v = true)
    (entryTyped : ∀ {bodyHeap steps allocation pre recv args fs oid},
      instantiate 0 ρ argument = .objAt fs (.graph q.entry.arity q.entry.exprs q.entry.conts q.entry.start
        (instantiateArgs 0 allocation caps) kind q.entry.spine.isSome component) oid →
      DispatchAt before ⟨instantiate 0 producer (.var fn),instantiate 0 producer br,instantiateArgs 0 producer ba⟩
        q.entry.arity q.entry.exprs q.entry.conts q.entry.start (instantiateArgs 0 allocation caps) q.entry.spine.isSome
        component recv args pre bodyHeap →
      let closureEnv := literalEntry pre recv q.entry.arity args caps allocation (instantiate 0 producer (.var fn))
      Execution (GraphCode.program q.entry.exprs q.entry.conts) steps bodyHeap (.at q.entry.start closureEnv) after (.done v) →
      before.IsPrefix bodyHeap → steps < callSteps →
      ∃ (n : Nat) (W : WorldT n), HeapOk n W bodyHeap ∧ RootsOk W actual ∧ WorldAdm W ∧ steps ≤ n ∧ 0 < n ∧
        EnvOk (RequestJson.graph request.toRequest) (codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine) closureEnv n W ∧
        RootsOk W closureEnv ∧ HeapKnowledge.IndexHolds ⟨closureEnv,bodyHeap⟩ (GraphCode.codeEntryIndices q.entry) closureEnv bodyHeap) :
    Supported d.support.normal actual before after := by
  obtain ⟨hist,valid,_,_,_,held⟩ := checkedNames_reached checkNames callerValues reached
  obtain ⟨i,rfl,slot⟩ := namedOrigin_slot atSite
  obtain ⟨⟨b,hb,same⟩,_⟩ := held i (.allocated site) (by simp [namedAt,slot])
  obtain ⟨siteEq,birth,_⟩ := valid site b hb
  have hnode := birth.1
  rw [siteEq,lookup] at hnode
  obtain ⟨fs,oid,obj⟩ := literalBirth birth ((Option.some.inj hnode).symm ▸ literal)
  have fromSlot := passed _ _ _ _ atArg atSite (by rfl : identity inputs (.allocated site) = some (inputs + site))
  have calleeEq : instantiate 0 producer (.var fn) = instantiate 0 ρ (.var i) := by
    simpa only [instantiate,Nat.not_lt_zero,ite_false,Nat.sub_zero] using callback.symm.trans fromSlot
  have selected := calleeEq.trans (show instantiate 0 ρ (.var i) = _ by simpa [instantiate] using same.symm.trans obj)
  obtain ⟨pre,bodyHeap,steps,recv,args,installed,layout,ext,room,_,inv,run⟩ := literal_invocation
    (allocation := b.allocation) (caps := caps) (privateSites := privateSites) (param := param) (state := proposal) ready values heapValues closed heapClosed roots (by simpa only [instantiateArgs_eq_map] using selected) completed value
  have sourceObject : instantiate 0 ρ (.var i) = .objAt fs (.graph q.entry.arity q.entry.exprs q.entry.conts q.entry.start
      (instantiateArgs 0 b.allocation caps) kind q.entry.spine.isSome component) oid := by
    simpa only [instantiateArgs_eq_map] using calleeEq.symm.trans selected
  have realized := entryTyped sourceObject installed run ext room
  obtain ⟨n,W,ok,argsOK,world,budget,pos,typed,entryRefs,indices⟩ := realized
  apply supported_after_prefix ext
  apply checkedCaller_literal_supported checkNames callerValues callerRoots callerHeap reached .normal v
    accept atArg atSite lookup literal width member inferred layout passed (proposalAt ▸ inv)
    ok argsOK world budget pos (self := instantiate 0 producer (.var fn)) _ rfl
  intro allocation other
  obtain ⟨fs',oid',other⟩ := other
  have objects := (calleeEq.trans other).symm.trans selected
  simp only [Tm.objAt.injEq,CallCode.graph.injEq] at objects
  have captures : instantiateArgs 0 b.allocation caps = instantiateArgs 0 allocation caps := by
    simpa only [instantiateArgs_eq_map] using objects.2.1.2.2.2.2.1.symm
  have envEq : literalEntry pre recv q.entry.arity args caps b.allocation (instantiate 0 producer (.var fn)) =
      literalEntry pre recv q.entry.arity args caps allocation (instantiate 0 producer (.var fn)) := by
    unfold literalEntry
    rw [← instantiateArgs_eq_map,← instantiateArgs_eq_map,captures]
  rw [← envEq]
  exact ⟨typed,entryRefs,indices,run⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck
