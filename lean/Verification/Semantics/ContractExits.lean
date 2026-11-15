import Verification.Semantics.ExitSummaries

/-! # A signature's contract read per exit

The native-contract condition of a signature (`NativeContract`,
`NativeConstruct`) stated by its specification per completion
(`Exits.exitPostW`, the note's Call on both exits) is the contract its
postconditions state today: at the states a safe run from a well-formed
entry reaches, the two agree (`Effect.summary_normal_iff`,
`Effect.summary_exceptional_iff`, `Effect.schema_atArity`), and safety
needs a postcondition only there (`SafePostExcV.weaken_admissible`). -/
namespace Verification.CallEffects
open Verification Footprints Parity TolerantFrames HeapObservations

section
variable {effect : Effect} {r : Tm} {args : List Tm} {s s' : IndexedHeap} {v : Tm}

/-- At an admissible transition with value actuals, a signature's normal
postcondition is its schema's normal exit. -/
theorem Effect.postW_iff_exit (hadm : Admissible s s') (hvals : CallArguments.Values args) :
    effect.postW r args s.W s.h s'.n s'.W s'.h v ↔ effect.schema.exitPostW .normal r args s.W s.h s'.n s'.W s'.h v := by
  rw [Exits.exitPostW_iff]
  show _ ↔ ((effect.schema.atArity args.length).get .normal).Holds _ _
  rw [Effect.schema_atArity]
  exact (Effect.summary_normal_iff effect hadm hvals).symm

/-- At an admissible transition, a signature's throw postcondition is its
schema's exceptional exit, whatever the thrown value. -/
theorem Effect.excPostW_iff_exit (hadm : Admissible s s') :
    (effect.excPostW r args s.h).liftV s'.n s'.W s'.h v ↔
      effect.schema.exitPostW .exceptional r args s.W s.h s'.n s'.W s'.h v := by
  rw [Exits.exitPostW_iff]
  show _ ↔ ((effect.schema.atArity args.length).get .exceptional).Holds _ _
  rw [Effect.schema_atArity]
  exact (Effect.summary_exceptional_iff effect args.length hadm).symm

end

/-- Safety from an entry at a world and heap, its postconditions changed to
ones agreeing with them at every admissible state the run reaches. -/
private theorem transport {Ξ T : Fam} {Q Q' : WPost} {R R' : WExcV} {j : Nat} {U : WorldT j} {heap : Heap}
    {t : Tm} (hu : WorldAdm U) (hh : HeapOk j U heap)
    (hq : ∀ (s s' : IndexedHeap) (v : Tm), s.n = j → s.W ≍ U → s.h = heap → Admissible s s' →
      Q s'.n s'.W s'.h v → Q' s'.n s'.W s'.h v)
    (hr : ∀ (s s' : IndexedHeap) (v : Tm), s.n = j → s.W ≍ U → s.h = heap → Admissible s s' →
      R s'.n s'.W s'.h v → R' s'.n s'.W s'.h v)
    (hs : SafePostExcV Ξ T Q R j U heap t) : SafePostExcV Ξ T Q' R' j U heap t := by
  cases j with
  | zero => exact hs
  | succ p =>
    let s : IndexedHeap := ⟨p + 1, U, heap, Nat.succ_pos _, hu, hh⟩
    exact SafePostExcV.weaken_admissible s (fun s' v hadm h => hq s s' v rfl HEq.rfl rfl hadm h)
      (fun s' v hadm h => hr s s' v rfl HEq.rfl rfl hadm h) hs

/-- **A signature's callable contract is the contract of its exits**: the
native-contract condition at its postconditions is the one at its exits. -/
theorem NativeContract.iff_exits {Ξ : Fam} {effect : Effect} {Acc : ArgFam} {Rc : Fam}
    {Rf : Tm → List Tm → Fam} {k : Nat} {W : WorldT k} {v : Val} :
    NativeContract Ξ Acc Rc effect.Requires Rf (fun r args _ U heap => effect.postW r args U heap)
        (fun r args _ _ heap => (effect.excPostW r args heap).liftV) k W v ↔
      NativeContract Ξ Acc Rc effect.Requires Rf
        (fun r args _ U heap => effect.schema.exitPostW .normal r args U heap)
        (fun r args _ U heap => effect.schema.exitPostW .exceptional r args U heap) k W v := by
  constructor <;> intro h j hj U hx hu heap hh hvr r hrv hrc hrr args hvals har hacc hreq <;>
    obtain ⟨res, hi, hs⟩ := h j hj U hx hu heap hh hvr r hrv hrc hrr args hvals har hacc hreq <;>
    refine ⟨res, hi, transport hu hh ?_ ?_ hs⟩ <;>
    rintro s s' val rfl hW rfl hadm hp <;> cases eq_of_heq hW
  · exact (Effect.postW_iff_exit hadm hvals).mp hp
  · exact (Effect.excPostW_iff_exit hadm).mp hp
  · exact (Effect.postW_iff_exit hadm hvals).mpr hp
  · exact (Effect.excPostW_iff_exit hadm).mpr hp

/-- **A construct signature's contract is the contract of its exits**, the
receiver `undefined`. -/
theorem NativeConstruct.iff_exits {Ξ : Fam} {effect : Effect} {P : ArgFam} {Rf : List Tm → Fam} {k : Nat}
    {W : WorldT k} {v : Val} :
    NativeConstruct Ξ P (effect.Requires .undef) Rf (fun r args _ U heap => effect.postW r args U heap)
        (fun r args _ _ heap => (effect.excPostW r args heap).liftV) k W v ↔
      NativeConstruct Ξ P (effect.Requires .undef) Rf
        (fun r args _ U heap => effect.schema.exitPostW .normal r args U heap)
        (fun r args _ U heap => effect.schema.exitPostW .exceptional r args U heap) k W v := by
  constructor <;> intro h j hj U hx hu heap hh hvr args hvals har hacc hreq <;>
    obtain ⟨res, hi, hs⟩ := h j hj U hx hu heap hh hvr args hvals har hacc hreq <;>
    refine ⟨res, hi, transport hu hh ?_ ?_ hs⟩ <;>
    rintro s s' val rfl hW rfl hadm hp <;> cases eq_of_heq hW
  · exact (Effect.postW_iff_exit hadm hvals).mp hp
  · exact (Effect.excPostW_iff_exit hadm).mp hp
  · exact (Effect.postW_iff_exit hadm hvals).mpr hp
  · exact (Effect.excPostW_iff_exit hadm).mpr hp

end Verification.CallEffects
