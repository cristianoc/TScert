import Verification.Source.Claims.CallbackRestPrefix
import Verification.Semantics.Reach.Scoped
namespace Verification.SourceClaimJson.CallbackInferencePlan
open CallArguments ControlFlow GraphCode HeapObservations CallbackInterfaceCheck
open CallbackPreservation CallbackOrigins

private theorem Prepared.scoped {h n f next} (trace : Prepared h n f next)
    (closed : Scoped 0 (.invoke f.callee f.recv f.args)) (heapClosed : ∀ t ∈ h, Scoped 0 t) :
    Scoped 0 (.invoke next.callee next.recv next.args) := by
  induction trace with
  | refl => exact closed
  | next step _ ih => exact ih (TolerantFrames.Reach.step_scoped step.step closed heapClosed).1

/-- The dispatch installed these exact receiver, arguments and rest cells. -/
def DispatchAt (h : Heap) (initial : Frame) (arity : Nat) (E : List Tm)
    (K : List (Continuation × Option Target)) (start : Nat) (caps : List Tm) (rest : Bool) (comp : ComponentTag)
    (recv : Tm) (args pre : List Tm) (bodyHeap : Heap) : Prop :=
  ∃ spent frame, Prepared h spent initial frame ∧ frame.recv = recv ∧ frame.args = args ∧
    CallArguments.Invoke frame (graphEntry arity E K start caps initial.callee rest comp recv args) ∧
    packedEntry arity rest h args pre bodyHeap

/-- A completed producer callback invoke runs the graph of the literal
supplied at the caller, in its actual allocation environment. -/
theorem literal_invocation {h f recv args ρ k after v slots privateSites param state entry}
    {arity E K start caps allocation kind rest comp fs oid}
    (ok : readCall (.invoke f recv args) = true) (values : ∀ i, isVal (ρ i) = true)
    (heapValues : ∀ (l : Nat) (x : Tm), h[l]? = some x → isVal x = true)
    (closed : Scoped 0 (instantiate 0 ρ (.invoke f recv args))) (heapClosed : ∀ t ∈ h, Scoped 0 t)
    (roots : RealizesRoots (entryRoot slots) ρ entry h)
    (callee : instantiate 0 ρ f = .objAt fs (.graph arity E K start (instantiateArgs 0 allocation caps) kind rest comp) oid)
    (run : Steps k h (instantiate 0 ρ (.invoke f recv args)) after v) (value : isVal v = true) :
    ∃ pre heap steps target passed, DispatchAt h ⟨instantiate 0 ρ f,instantiate 0 ρ recv,instantiateArgs 0 ρ args⟩
      arity E K start (instantiateArgs 0 allocation caps) rest comp target passed pre heap ∧ pre.length = (if rest then 1 else 0) ∧ h.IsPrefix heap ∧ steps < k ∧
      kind.binds target = true ∧
      (∀ p x, (atCall slots privateSites param state (.invoke f recv args)).demand.actualRoots[p]? = some (some (x,[])) →
        entry x = CallEffects.callEnv target passed p) ∧
      Execution (program E K) steps heap (.at start (literalEntry pre target arity passed caps allocation
        (instantiate 0 ρ f))) after (.done v) := by
  obtain ⟨p,q,frame,body,count,trace,dispatch,bodyRun⟩ := readCall_dispatch run value (readCall_instantiate ok values) heapValues
  obtain ⟨_,argsValues,mode,rfl⟩ := graph_dispatch trace callee dispatch
  have scope := trace.scoped closed heapClosed
  obtain ⟨fnScope,recvScope,argsScope⟩ := scope
  have selfScope : Scoped 0 (instantiate 0 ρ f) := by
    rw [trace.keepsCallee callee (by rfl)] at fnScope
    simpa only [callee] using fnScope
  have capScope : ∀ t ∈ instantiateArgs 0 allocation caps, Scoped 0 t := by
    rw [callee] at selfScope
    exact (scopedArgs_iff ..).mp selfScope
  have localsClosed : ∀ t ∈ frame.recv :: parameters arity frame.args ++ (instantiateArgs 0 allocation caps ++ [instantiate 0 ρ f]), Scoped 0 t := by
    intro t ht
    simp only [List.mem_cons,List.mem_append] at ht
    rcases ht with (rfl | hm) | hc | rfl | no
    · exact recvScope
    · exact (Kinds.parameters_mem hm).elim (fun h => (scopedArgs_iff ..).mp argsScope _ h) (fun h => h ▸ trivial)
    · exact capScope _ hc
    · exact selfScope
    · cases no
  obtain ⟨pre,heap,steps,packed,len,ext,spent,exec⟩ := graphEntry_execution bodyRun value argsValues localsClosed
  exact ⟨pre,heap,steps,frame.recv,frame.args,⟨p,frame,trace,rfl,rfl,dispatch,packed⟩,len,ext,by omega,mode,
    fun _ _ => atCall_actualRoots roots ok values heapValues trace,by simpa [literalEntry] using exec⟩

end Verification.SourceClaimJson.CallbackInferencePlan
