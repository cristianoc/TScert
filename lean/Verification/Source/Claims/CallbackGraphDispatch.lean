import Verification.Source.Claims.CallbackCallPositions
import Verification.Source.Claims.CallbackInterfaceCheck
namespace Verification.SourceClaimJson.CallbackInferencePlan
open ControlFlow CallArguments HeapObservations GraphCode

theorem execution_of_sim {E K h t after v k state} (sim : Sim E K t state)
    (run : Steps k h t after v) (value : isVal v = true) :
    Execution (program E K) k h state after (.done v) := by
  induction run generalizing state with
  | refl =>
    cases sim with
    | done => exact .refl
    | goto | frame | raised => contradiction
  | next step _ ih =>
    obtain ⟨_,st,next⟩ := sim_step_back sim step
    exact .next st (ih next value)

private theorem consume {k h t after v h' t'} (run : Steps k h t after v) (value : isVal v = true)
    (step : Step h t h' t') : ∃ j, k = j+1 ∧ Steps j h' t' after v := by
  cases run with
  | refl => exact (value_no_step value step).elim
  | next fst tail =>
    obtain ⟨rfl,rfl⟩ := Step_det fst step
    exact ⟨_,rfl,tail⟩

def packedEntry (arity : Nat) (rest : Bool) (h : Heap) (args pre : List Tm) (heap : Heap) : Prop :=
  if rest then
    let extra := args.drop arity
    pre = [.arr (elemSlots h.length extra.length)] ∧ heap = h ++ extra ∧ extra.length ≤ maxArrayLength
  else pre = [] ∧ heap = h

/-- The rest prologue appends the extra actuals and installs the resulting
spine before the receiver. Its two reductions consume two steps. -/
theorem graphEntry_execution {arity E K start caps self rest comp recv args k h after v}
    (run : Steps k h (graphEntry arity E K start caps self rest comp recv args) after v)
    (value : isVal v = true) (argsVal : Values args)
    (closed : ∀ t ∈ recv :: parameters arity args ++ (caps ++ [self]), Scoped 0 t) :
    ∃ pre entryHeap steps, packedEntry arity rest h args pre entryHeap ∧ pre.length = (if rest then 1 else 0) ∧ h.IsPrefix entryHeap ∧
      k = steps + (if rest then 2 else 0) ∧
      Execution (program E K) steps entryHeap
        (.at start (envOf (pre ++ (recv :: parameters arity args ++ (caps ++ [self]))) .nul)) after (.done v) := by
  cases rest with
  | false => exact ⟨[],h,k,⟨rfl,rfl⟩,rfl,List.prefix_refl _,by simp,execution_of_sim .goto run value⟩
  | true =>
    let extra := args.drop arity
    let spine := Tm.arr (elemSlots h.length extra.length)
    have vals : ∀ t ∈ extra, isVal t = true := fun t ht => argsVal t (List.mem_of_mem_drop ht)
    by_cases fits : extra.length ≤ maxArrayLength
    · obtain ⟨j,rfl,left⟩ := consume run value (.letC (.arrAlloc vals fits))
      obtain ⟨steps,rfl,body⟩ := consume left value (.letV (by rfl))
      refine ⟨[spine],h ++ extra,steps,⟨rfl,rfl,fits⟩,rfl,⟨extra,rfl⟩,by simp [Nat.add_assoc],?_⟩
      let locals := recv :: parameters arity args ++ (caps ++ [self])
      have idmap : (locals.map (subst 0 spine)) = locals := by
        simpa using List.map_congr_left (g := id) (fun t (ht : t ∈ locals) => subst_above (closed t ht) (Nat.zero_le _) spine)
      change Steps _ _ (subst 0 spine (.goto E K start (.var 0 :: locals) .nul comp)) _ _ at body
      simp only [subst,substArgs_eq_map,List.map_cons,idmap] at body
      exact execution_of_sim .goto body value
    · obtain ⟨j,_,tail⟩ := consume run value (.letC (.arrAllocThrow vals ((Nat.lt_of_not_ge fits))))
      cases tail with
      | refl => contradiction
      | next st _ => exact (raises_no_step (.letC (.throwV (by rfl) (by rfl))) st).elim

/-- A value callee survives preparation; its graph descriptor fixes
dispatch, argument normalization, receiver mode and rest collection. -/
theorem graph_dispatch {h p f next fs arity E K start caps kind rest comp oid body}
    (trace : Prepared h p f next)
    (callee : f.callee = .objAt fs (.graph arity E K start caps kind rest comp) oid)
    (dispatch : CallArguments.Invoke next body) :
    isVal next.recv = true ∧ Values next.args ∧ kind.binds next.recv = true ∧
    body = graphEntry arity E K start caps f.callee rest comp next.recv next.args := by
  have fixed := trace.keepsCallee callee (by rfl)
  cases dispatch with
  | bound => cases fixed
  | graph r a compatible =>
    simp only [Tm.objAt.injEq, CallCode.graph.injEq] at fixed
    obtain ⟨rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩ := fixed
    exact ⟨r,a,compatible,by rw [callee]⟩

end Verification.SourceClaimJson.CallbackInferencePlan
