import Verification.Source.Claims.CallbackTypicalPoint
import Verification.Source.Claims.CallbackTypedEntry
namespace Verification.SourceClaimJson.CallbackInferencePlan
open PromiseCalls CallArguments ControlFlow GraphCode HeapObservations PositiveGraphs PositiveRules CallEffects
open CallbackInterfaceCheck Footprints TolerantFrames ProgramTyping CallbackEffectInference

theorem point_number {ι : Type} {G : NormalGraph ι} {Γ ρ i A h}
    (point : ∃ s : IndexedHeap, s.h = h ∧ EnvOk G Γ ρ s.n s.W)
    (slot : Γ[i]? = some A) (only : Represents G A .num) : ∃ b, ρ i = .num b := by
  obtain ⟨s,_,env⟩ := point
  exact represents_raw only _ _ _ (env.2 i _ slot)

private theorem fixed_prepared {h p next f b} (trace : Prepared h p ⟨f,.undef,[.num b]⟩ next) (val : isVal f = true) :
    next = ⟨f,.undef,[.num b]⟩ := by
  cases trace with
  | refl => rfl
  | next step _ =>
    cases step with
    | callee st => exact (value_no_step val st).elim
    | recv _ st => exact (value_no_step rfl st).elim
    | args _ _ st =>
      cases st with
      | head st => exact (value_no_step rfl st).elim
      | tail _ st => cases st
    | splice _ _ eq _ _ =>
      have no : ∀ arg ∈ ([Tm.num b] : List Tm), ∀ z, arg ≠ .spread z := by simp
      rw [eq] at no
      exact (no _ (List.mem_append_right _ (List.mem_cons_self ..)) _ rfl).elim

theorem fixed_dispatch {h f b arity E K start caps rest comp recv args pre heap}
    (val : isVal f = true) (dispatch : DispatchAt h ⟨f,.undef,[.num b]⟩ arity E K start caps rest comp recv args pre heap) :
    recv = .undef ∧ args = [.num b] ∧ packedEntry arity rest h args pre heap := by
  obtain ⟨_,frame,trace,recvEq,argsEq,_,packed⟩ := dispatch
  obtain rfl := fixed_prepared trace val
  exact ⟨recvEq.symm,argsEq.symm,packed⟩

/-- Form the literal's concrete fixed row from its inferred code row,
the reached numeric operand, and the capture types from ordinary allocation. -/
theorem numeric_rowActuals {τ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView τ ι]
    {request : SourceElaboration.SourceRequest τ ι} {fuel codes known final}
    {q : RequestJson.CodeRequest ι} {summary : Summary}
    (inferred : inferCodes request fuel = .ok (codes,known,final))
    (member : (⟨q.entry,summary⟩ : CheckedCode ι) ∈ codes)
    {A : Ty ι} (shape : q.entry.row.arguments = [A])
    (argTy : Represents (RequestJson.graph request.toRequest) A .num)
    (recvTy : admitsUndef (RequestJson.graph request.toRequest) q.entry.row.receiver = true)
    (pre : q.entry.row.effect.pre = []) (fixed : q.entry.spine = none)
    {s : IndexedHeap} {vs : List Tm} {b : UInt64}
    (captured : EnvOk (RequestJson.graph request.toRequest) q.entry.captures (envOf vs .nul) s.n s.W)
    (frameRefs : RootsOk s.W (envOf (.undef :: parameters q.entry.arity [.num b] ++ vs) .nul)) :
    RowActuals (RequestJson.graph request.toRequest) q.entry s .undef [.num b] vs := by
  have mem : q.entry ∈ codes.toList.map (·.entry) := List.mem_map.mpr ⟨⟨q.entry,summary⟩,by simpa using member,rfl⟩
  have sig := inferCodes_table_sound inferred _ (List.contains_iff_mem.mpr mem) (RequestJson.graph request.toRequest).env
  refine ⟨sig,captured,admitsUndef_sound recvTy _ _,⟨[.num b],rfl,?_⟩,?_,?_,?_,frameRefs,?_⟩
  · have typed := represents_back argTy s.n s.W (.num b) rfl ⟨b,rfl⟩
    simpa [shape,ArgsShort,ArgsT] using typed
  · simp [pre]
  · simp [fixed]
  · simp [Values,isVal]
  · cases a : q.entry.arity <;> simp [RefsOk,refs,refsArgs_eq]

end Verification.SourceClaimJson.CallbackInferencePlan
