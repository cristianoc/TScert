import Verification.Source.Claims.CallbackTypicalNumeric
import Verification.Source.Claims.CallbackCompletedSupply
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins CallbackPreservation CallbackEffectInference ControlFlow Footprints CallEffects ProgramTyping
open TolerantFrames HeapObservations GraphCode CallbackInferencePlan
/-- A checked literal supply meets the producer demand on the entire
completed native call. The row's entry typing is for the actual reached
graph state and budget, including allocation of a rest spine. -/
theorem checkedNumericLiteral_supported {τ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView τ ι]
    {request : SourceElaboration.SourceRequest τ ι} {fuel codes known final}
    {q : RequestJson.CodeRequest ι} {summary : Summary} {P : Program} {table : Table}
    {inputs start entry l ρ h₀ h k n₀} {W₀ : WorldT n₀}
    (checkNames : CallbackOrigins.checkNames P.toArray (namedSites P.toArray) start inputs table = true)
    (callerValues : ∀ i < inputs, isVal (entry i) = true) (callerRoots : RootsOk W₀ entry) (callerHeap : HeapOk n₀ W₀ h₀)
    (reached : Execution P k h₀ (.at start entry) h (.at l ρ))
    {frame : List Tm} {d : Demand} {argument : Tm} {site : Nat} {node : Node}
    {caps kind component fields vals} {actual : Env} {producer : Env} {fn index : Nat}
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
    (proposalAt : d = (atCall slots privateSites param proposal (.invoke (.var fn) .undef [.var index])).demand)
    (callback : actual d.parameter = producer fn)
    (ready : readCall (.invoke (.var fn) .undef [.var index]) = true) (values : ∀ i, isVal (producer i) = true)
    (heapValues : ∀ (i : Nat) (x : Tm), before[i]? = some x → isVal x = true)
    (closed : Scoped 0 (instantiate 0 producer (.invoke (.var fn) .undef [.var index]))) (heapClosed : ∀ t ∈ before, Scoped 0 t)
    (roots : RealizesRoots (entryRoot slots) producer actual before)
    (completed : HeapObservations.Steps callSteps before (instantiate 0 producer (.invoke (.var fn) .undef [.var index])) after v)
    (value : isVal v = true)

    {s : IndexedHeap} (heap : before = s.h) (budget : callSteps < s.n)
    (actualRefs : RootsOk s.W actual) (producerRefs : RootsOk s.W producer)
    (numeric : ∃ b, producer index = .num b)
    {A} (shape : q.entry.row.arguments = [A])
    (argTy : Represents (RequestJson.graph request.toRequest) A .num)
    (recvTy : PromiseCalls.admitsUndef (RequestJson.graph request.toRequest) q.entry.row.receiver = true)
    (precond : q.entry.row.effect.pre = []) (fixed : q.entry.spine = none) (arity : q.entry.arity = 1)
    (captured : ∀ fs vs oid, producer fn = .objAt fs (.graph q.entry.arity q.entry.exprs q.entry.conts
        q.entry.start vs kind false component) oid →
      EnvOk (RequestJson.graph request.toRequest) q.entry.captures (envOf (vs ++ [producer fn]) .nul) s.n s.W) :
    Supported d.support.normal actual before after := by
  apply checkedLiteral_call_supported checkNames callerValues callerRoots callerHeap reached v accept atArg atSite
    lookup literal width member inferred passed proposalAt callback ready values heapValues closed heapClosed roots completed value
  intro bodyHeap steps allocation pre recv args fs oid source dispatch closureEnv exec extendsHeap room
  dsimp only [closureEnv] at *
  obtain ⟨bits,numeral⟩ := numeric
  have atFrame := passed _ _ _ _ atArg atSite (by rfl : identity inputs (.allocated site) = some (inputs + site))
  have obj : producer fn = .objAt fs (.graph q.entry.arity q.entry.exprs q.entry.conts q.entry.start
      (instantiateArgs 0 allocation caps) kind false component) oid := by
    simpa [fixed] using callback.symm.trans (atFrame.trans source)
  have dispatched : DispatchAt before ⟨producer fn,.undef,[.num bits]⟩ q.entry.arity q.entry.exprs q.entry.conts q.entry.start (instantiateArgs 0 allocation caps) q.entry.spine.isSome component recv args pre bodyHeap := by
    simpa [instantiate,instantiateArgs,numeral] using dispatch
  obtain ⟨rfl,rfl,packed⟩ := fixed_dispatch (values fn) dispatched
  simp only [fixed,Option.isSome_none,packedEntry,Bool.false_eq_true,ite_false] at packed
  obtain ⟨rfl,rfl⟩ := packed
  let vs := instantiateArgs 0 allocation caps
  have capRefs := (graph_code_refs (obj ▸ producerRefs fn)).2
  have refs : RootsOk s.W (envOf (.undef :: CallArguments.parameters q.entry.arity [.num bits] ++ (vs ++ [producer fn])) .nul) := by
    apply GraphCode.envOf_refs_of _ RefsOk_nul
    intro t mem
    simp [arity,CallArguments.parameters] at mem
    rcases mem with rfl | rfl | hcap | rfl
    · exact RefsOk_undef
    · simp [RefsOk,refs]
    · exact capRefs _ hcap
    · exact producerRefs fn
  have actualRow := numeric_rowActuals inferred member shape argTy recvTy precond fixed (captured _ _ _ obj) refs
  have pos : 0 < steps := by cases exec <;> omega
  have idpack : packedEntry q.entry.arity q.entry.spine.isSome s.h [.num bits] [] s.h := by simp [fixed,packedEntry]
  obtain ⟨k,U,le,ext,adm,ok,time,positive,typed,locals,idx⟩ := rowActuals_entry actualRow idpack (Nat.lt_trans room budget) pos
  refine ⟨k,U,heap ▸ ok,fun i => RefsOk_mono ext (RefsOk_trunc le (actualRefs i)),adm,time,positive,?_,?_,?_⟩
  · simpa [literalEntry,vs,instantiateArgs_eq_map,instantiate] using typed
  · simpa [literalEntry,vs,instantiateArgs_eq_map,instantiate] using locals
  · simpa [literalEntry,vs,instantiateArgs_eq_map,instantiate,heap] using idx

end Verification.SourceClaimJson.CallbackInterfaceCheck
