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

/-- At an admissible transition, a signature's normal postcondition is its
schema's normal exit, at actuals that are values where it states an append
of them. -/
theorem Effect.postW_iff_exit (hadm : Admissible s s')
    (hvals : effect.receiverGrows = true → CallArguments.Values args) :
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

/-- **Safety from an entry at a world and heap, its postconditions changed
to ones agreeing with them at every admissible state the run reaches**
(`SafePostExcV.weaken_admissible` at the entry's indexed state). -/
theorem SafePostExcV.weaken_reached {Ξ T : Fam} {Q Q' : WPost} {R R' : WExcV} {j : Nat} {U : WorldT j} {heap : Heap}
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
    refine ⟨res, hi, SafePostExcV.weaken_reached hu hh ?_ ?_ hs⟩ <;>
    rintro s s' val rfl hW rfl hadm hp <;> cases eq_of_heq hW
  · exact (Effect.postW_iff_exit hadm fun _ => hvals).mp hp
  · exact (Effect.excPostW_iff_exit hadm).mp hp
  · exact (Effect.postW_iff_exit hadm fun _ => hvals).mpr hp
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
    refine ⟨res, hi, SafePostExcV.weaken_reached hu hh ?_ ?_ hs⟩ <;>
    rintro s s' val rfl hW rfl hadm hp <;> cases eq_of_heq hW
  · exact (Effect.postW_iff_exit hadm fun _ => hvals).mp hp
  · exact (Effect.excPostW_iff_exit hadm).mp hp
  · exact (Effect.postW_iff_exit hadm fun _ => hvals).mpr hp
  · exact (Effect.excPostW_iff_exit hadm).mpr hp

/-- **Invocation at a callable's exits** (the note's Call at the evaluated
actuals): a callee meeting the native-contract condition at an exit
specification, invoked at values meeting its input contract one step below,
is safe at the specification's exits from the entry world truncated by the
invocation's step (`NativeContract.safe`). -/
theorem invoke_exits {Ξ : Fam} {Acc : ArgFam} {Rc : Fam} {req : Tm → List Tm → Heap → Prop}
    {Rf : Tm → List Tm → Fam} {x : Exits ExitSchema} {n : Nat} {W : WorldT (n + 1)} {f : Val}
    (hc : NativeContract Ξ Acc Rc req Rf (fun r vs _ U h => x.exitPostW .normal r vs U h)
      (fun r vs _ U h => x.exitPostW .exceptional r vs U h) (n + 1) W f)
    (hw : WorldAdm W) {h : Heap} (hh : HeapOk (n + 1) W h) {r : Tm} (hrv : isVal r = true)
    (hr : Rc n (trunc n (Nat.le_succ n) W) r) {vs : List Tm} (hv : CallArguments.Values vs)
    (ha : Acc n (trunc n (Nat.le_succ n) W) vs) (hq : req r vs h) (href : RefsOk W (.invoke f r vs)) :
    SafePostExcV Ξ (Rf r vs) (x.exitPostW .normal r vs (trunc n (Nat.le_succ n) W) h)
      (x.exitPostW .exceptional r vs (trunc n (Nat.le_succ n) W) h) (n + 1) W h (.invoke f r vs) :=
  NativeContract.safe hc hw hh hrv hr hv ha hq href

/-- **Safety at a signature's heap postconditions is safety at its exits**,
where it states no element write and its actuals are values where it states
an append of them: from an entry at a world and heap, at every admissible
state a run reaches the heap postconditions are the exits
(`Effect.postW_iff_exit`, `Effect.excPostW_iff_exit`). -/
theorem Effect.safe_exits {Ξ T : Fam} {e : Effect} (hx : e.elementWrite = none) {r : Tm} {args : List Tm}
    (hvals : e.receiverGrows = true → CallArguments.Values args) {j : Nat} {U : WorldT j} {heap : Heap} {t : Tm}
    (hu : WorldAdm U) (hh : HeapOk j U heap)
    (hs : SafePostExc Ξ T (e.post r args heap) (e.excPost r args heap) j U heap t) :
    SafePostExcV Ξ T (e.schema.exitPostW .normal r args U heap) (e.schema.exitPostW .exceptional r args U heap)
      j U heap t := by
  refine SafePostExcV.weaken_reached hu hh ?_ ?_ (Effect.safe_postW (U := U) hx hs) <;>
    rintro s s' val rfl hW rfl hadm hp <;> cases eq_of_heq hW
  · exact (Effect.postW_iff_exit hadm hvals).mp hp
  · exact (Effect.excPostW_iff_exit hadm).mp hp

/-- **Safety at a signature's exits is safety at its heap postconditions**,
at actuals that are values where it states an append of them: the heap
postcondition is the part of the normal exit that reads no world
(`Effect.postW`). -/
theorem Effect.safe_fields {Ξ T : Fam} {e : Effect} {r : Tm} {args : List Tm}
    (hvals : e.receiverGrows = true → CallArguments.Values args) {j : Nat} {U : WorldT j} {heap : Heap} {t : Tm}
    (hu : WorldAdm U) (hh : HeapOk j U heap)
    (hs : SafePostExcV Ξ T (e.schema.exitPostW .normal r args U heap) (e.schema.exitPostW .exceptional r args U heap)
      j U heap t) :
    SafePostExc Ξ T (e.post r args heap) (e.excPost r args heap) j U heap t := by
  have hw : SafePostExcV Ξ T (e.postW r args U heap) (e.excPostW r args heap).liftV j U heap t := by
    refine SafePostExcV.weaken_reached hu hh ?_ ?_ hs <;>
      rintro s s' val rfl hW rfl hadm hp <;> cases eq_of_heq hW
    · exact (Effect.postW_iff_exit hadm hvals).mpr hp
    · exact (Effect.excPostW_iff_exit hadm).mpr hp
  exact SafePostExcW.weaken (fun _ _ _ _ hp => hp.1) (fun _ _ _ hp => hp) (SafePostExcV.iff_lift.mp hw)

/-- **Safety at one signature's exits gives safety at another's**, at
another call, where their heap postconditions imply each other's, the
second states no element write, and each call's actuals are values where
its signature states an append of them. -/
theorem Effect.safe_exits_weaken {Ξ T : Fam} {e e' : Effect} {r r' : Tm} {args args' : List Tm}
    (hv : e.receiverGrows = true → CallArguments.Values args) (hx' : e'.elementWrite = none)
    (hv' : e'.receiverGrows = true → CallArguments.Values args') {j : Nat} {U : WorldT j} {heap : Heap} {t : Tm}
    (hu : WorldAdm U) (hh : HeapOk j U heap)
    (hq : ∀ h' v, e.post r args heap h' v → e'.post r' args' heap h' v)
    (hr : ∀ h', e.excPost r args heap h' → e'.excPost r' args' heap h')
    (hs : SafePostExcV Ξ T (e.schema.exitPostW .normal r args U heap) (e.schema.exitPostW .exceptional r args U heap)
      j U heap t) :
    SafePostExcV Ξ T (e'.schema.exitPostW .normal r' args' U heap)
      (e'.schema.exitPostW .exceptional r' args' U heap) j U heap t :=
  Effect.safe_exits hx' hv' hu hh (SafePostExc.weaken hq hr (Effect.safe_fields hv hu hh hs))

end Verification.CallEffects
