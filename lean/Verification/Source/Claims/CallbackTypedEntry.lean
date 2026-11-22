import Verification.Source.Claims.CallbackLiteralInvocation
import Verification.Programs.VariadicTyping
namespace Verification.SourceClaimJson.CallbackInferencePlan
open CallArguments ControlFlow ProgramTyping GraphCode HeapObservations PositiveGraphs PositiveRules CallEffects
open CallbackInterfaceCheck Footprints TolerantFrames

/-- Receiver, normalized fixed arguments, captures and precondition of
the row used by the ordinary application derivation. An actual rest pack
also meets the row's ordinary rest-spine type. -/
structure RowActuals {ι : Type} (G : NormalGraph ι) (row : CodeEntry ι) (s : IndexedHeap)
    (recv : Tm) (args vs : List Tm) : Prop where
  signature : row.Spec G
  captures : EnvOk G row.captures (envOf vs .nul) s.n s.W
  receiver : meaning G row.row.receiver s.n s.W recv
  arguments : ∃ fixed, parameters row.arity fixed = parameters row.arity args ∧
    ArgsShort (row.row.arguments.map (meaning G)) s.n s.W fixed
  precondition : ∀ F ∈ row.row.effect.pre, F.HoldsAt ⟨callEnv recv args,s.h⟩ (callEnv recv args) s.h
  rest : ∀ S, row.spine = some S →
    ∃ P, RestSpine G S P ∧ argMeaning G P s.n s.W (args.drop row.arity)
  argumentsValue : Values args
  frameRefs : RootsOk s.W (envOf (recv :: parameters row.arity args ++ vs) .nul)
  restRefs : RefsOk s.W (.arrLit (args.drop row.arity))

private theorem safe_step_at {Ξ T k} {W : WorldT (k+1)} {h t h' t'} (safe : Safe Ξ T (k+1) W h t)
    (step : Step h t h' t') : ∃ U : WorldT k, WExt (trunc k (Nat.le_succ _) W) U ∧
      WorldAdm U ∧ HeapOk k U h' ∧ Safe Ξ T k U h' t' := by
  rcases safe.2 with (⟨hv,_⟩ | ⟨v,raised,_,_⟩) | ⟨U,_,_,ext,world,other,heap,rest⟩
  · exact (value_no_step hv step).elim
  · exact (raises_no_step raised step).elim
  · obtain ⟨rfl,rfl⟩ := Step_det other step
    exact ⟨U,ext,world,heap,rest⟩

/-- Ordinary signature checking types the graph frame actually installed
by dispatch. Rest allocation extends the same world and costs one level. -/
theorem rowActuals_entry {ι : Type} {G : NormalGraph ι} {row : CodeEntry ι} {s : IndexedHeap}
    {recv args vs pre heap steps} (actual : RowActuals G row s recv args vs)
    (packed : packedEntry row.arity row.spine.isSome s.h args pre heap)
    (time : steps < s.n) (positive : 0 < steps) :
    let L := pre ++ (recv :: parameters row.arity args ++ vs)
    ∃ (k : Nat) (U : WorldT k) (le : k ≤ s.n), WExt (trunc k le s.W) U ∧ WorldAdm U ∧ HeapOk k U heap ∧
      steps ≤ k ∧ 0 < k ∧ EnvOk G (codeFrame row.arity row.row row.captures row.spine) (envOf L .nul) k U ∧
      RootsOk U (envOf L .nul) ∧ HeapKnowledge.IndexHolds ⟨envOf L .nul,heap⟩ (codeEntryIndices row) (envOf L .nul) heap := by
  dsimp only
  obtain ⟨spec,captured,recvTyped,⟨fixed,fixedEq,argsTyped⟩,precond,rest,vals,refs,extraRefs⟩ := actual
  have eqWorld : WExt (trunc s.n (Nat.le_refl _) s.W) s.W := by rw [trunc_id]; exact WExt_refl _
  have frame := frame_envOk spec.1 captured (Nat.le_refl _) eqWorld recvTyped argsTyped
  rw [fixedEq] at frame
  cases spine : row.spine with
  | none =>
    rw [spine] at packed
    obtain ⟨rfl,rfl⟩ := packed
    refine ⟨s.n,s.W,Nat.le_refl _,eqWorld,s.adm,s.ok,Nat.le_of_lt time,s.pos,frame,refs,codeEntryIndices_holds ?_⟩
    exact fun _ F wherePre => (Effect.pre_frame (Effect.belowRow_entry spec.2.1) wherePre recv args vs .nul s.h).mp (precond F wherePre)
  | some S =>
    rw [spine] at packed
    obtain ⟨rfl,rfl,fits⟩ := packed
    obtain ⟨P,spineType,extra⟩ := rest S spine
    obtain ⟨n,W,h,pos,adm,heapOk⟩ := s
    cases n with
    | zero => contradiction
    | succ n =>
      have extraVals : Values (args.drop row.arity) := fun x hx => vals _ (List.mem_of_mem_drop hx)
      have checked := restSpine_safe spineType adm heapOk extra extraVals extraRefs
      obtain ⟨U,ext,world,heap',value⟩ := safe_step_at checked (.arrAlloc extraVals fits)
      cases n with
      | zero => simp at time; omega
      | succ n =>
        have stored := safe_value_mem (by rfl) value
        have fixedFrame := frame.transfer _ (Nat.le_succ _) U ext
        have newFrame := fixedFrame.push stored
        have envEq := push_envOf (.arr (elemSlots h.length (args.drop row.arity).length)) (recv :: parameters row.arity args ++ vs) .nul
        rw [envEq] at newFrame
        refine ⟨n+1,U,Nat.le_succ _,ext,world,heap',by simp at time; omega,by omega,?_,?_,codeEntryIndices_holds ?_⟩
        · simpa only [spine,codeFrame,List.singleton_append] using newFrame
        · rw [List.singleton_append,← envEq]
          exact push_refs value.refs (fun i => RefsOk_mono ext (RefsOk_trunc _ (refs i)))
        · exact fun no => by rw [spine] at no; contradiction

end Verification.SourceClaimJson.CallbackInferencePlan
