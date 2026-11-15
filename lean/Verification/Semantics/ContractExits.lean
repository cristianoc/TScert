import Verification.Semantics.ExitSummaries
import Verification.Semantics.ExitWorlds

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
is safe at the specification's exits from the invocation's entry: its world
truncated by the invocation's step, and its heap (`NativeContract.safe`). -/
theorem invoke_exits_exact {Ξ : Fam} {Acc : ArgFam} {Rc : Fam} {req : Tm → List Tm → Heap → Prop}
    {Rf : Tm → List Tm → Fam} {x : Exits ExitSchema} {n : Nat} {W : WorldT (n + 1)} {f : Val}
    (hc : NativeContract Ξ Acc Rc req Rf (fun r vs _ U h => x.exitPostW .normal r vs U h)
      (fun r vs _ U h => x.exitPostW .exceptional r vs U h) (n + 1) W f)
    (hw : WorldAdm W) {h : Heap} (hh : HeapOk (n + 1) W h) {r : Tm} (hrv : isVal r = true)
    (hr : Rc n (trunc n (Nat.le_succ n) W) r) {vs : List Tm} (hv : CallArguments.Values vs)
    (ha : Acc n (trunc n (Nat.le_succ n) W) vs) (hq : req r vs h) (href : RefsOk W (.invoke f r vs)) :
    SafePostExcV Ξ (Rf r vs) (x.exitPostW .normal r vs (trunc n (Nat.le_succ n) W) h)
      (x.exitPostW .exceptional r vs (trunc n (Nat.le_succ n) W) h) (n + 1) W h (.invoke f r vs) := by
  obtain ⟨hfr, hrr, har⟩ := RefsOk_invoke.mp href
  obtain ⟨result, hi, hs⟩ := hc n (Nat.lt_succ_self n) _ (WExt_refl _) (WorldAdm_trunc _ hw) h
    (HeapOk_trunc n W h hh) (RefsOk_trunc _ hfr) r hrv hr (RefsOk_trunc _ hrr) vs hv
    (fun a hm => RefsOk_trunc _ (har a hm)) ha hq
  exact ⟨href, .inr ⟨_, h, result, WExt_refl _, WorldAdm_trunc _ hw, hi.step h, HeapOk_trunc n W h hh, hs⟩⟩

/-- **Invocation at a callable's exits from a held entry**: the exact
entry (`invoke_exits_exact`) is held from the invocation's (`HeldEntry`;
`SafePostExcV.fromEntry_of_exact`). -/
theorem invoke_exits {Ξ : Fam} {Acc : ArgFam} {Rc : Fam} {req : Tm → List Tm → Heap → Prop}
    {Rf : Tm → List Tm → Fam} {x : Exits ExitSchema} {n : Nat} {W : WorldT (n + 1)} {f : Val}
    (hc : NativeContract Ξ Acc Rc req Rf (fun r vs _ U h => x.exitPostW .normal r vs U h)
      (fun r vs _ U h => x.exitPostW .exceptional r vs U h) (n + 1) W f)
    (hw : WorldAdm W) {h : Heap} (hh : HeapOk (n + 1) W h) {r : Tm} (hrv : isVal r = true)
    (hr : Rc n (trunc n (Nat.le_succ n) W) r) {vs : List Tm} (hv : CallArguments.Values vs)
    (ha : Acc n (trunc n (Nat.le_succ n) W) vs) (hq : req r vs h) (href : RefsOk W (.invoke f r vs)) :
    SafePostExcV Ξ (Rf r vs) (x.fromEntry .normal r vs (HeldEntry W h))
      (x.fromEntry .exceptional r vs (HeldEntry W h)) (n + 1) W h (.invoke f r vs) := by
  obtain ⟨hfr, hrr, har⟩ := RefsOk_invoke.mp href
  obtain ⟨_, hi, -⟩ := hc n (Nat.lt_succ_self n) _ (WExt_refl _) (WorldAdm_trunc _ hw) h
    (HeapOk_trunc n W h hh) (RefsOk_trunc _ hfr) r hrv hr (RefsOk_trunc _ hrr) vs hv
    (fun a hm => RefsOk_trunc _ (har a hm)) ha hq
  obtain ⟨hnv, hnr⟩ := Step.inert (hi.step h)
  exact SafePostExcV.fromEntry_of_exact hw hh hnv hnr (invoke_exits_exact hc hw hh hrv hr hv ha hq href)

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

/-! ## The meet of two specifications -/

/-- **A signature's schema reads its exits only through their heaps**
(`ExitSchema.exitHeapOnly`): its postconditions are operational posts,
index facts, transitions and the written result's transport, which
certifies no rigid image. -/
theorem Effect.schema_exitHeapOnly (e : Effect) (c : Completion) : (e.schema.get c).exitHeapOnly = true := by
  have hw : ∀ w : ElementWrite, w.schemaPosts.all (·.exitHeapOnly TransportSchema.stable) = true := by
    intro w; cases w with
    | stores => rfl
    | assign => rfl
    | exact k =>
      simp only [ElementWrite.schemaPosts, List.all_cons, List.all_append, List.all_map]
      simp [FormulaF.exitHeapOnly, Function.comp_def, writtenResultSchema]
  cases c
  · simp only [Exits.get, Effect.schema, ExitSchema.exitHeapOnly, Effect.normalSchema, List.all_append,
      Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
    · simp [List.all_map, FormulaF.exitHeapOnly, Function.comp_def]
    · split <;> rfl
    · split
      · exact hw _
      · rfl
  · simp only [Exits.get, Effect.schema, ExitSchema.exitHeapOnly]
    split <;> rfl

/-- **A signature's guarantee at each completion is independent of the exit
world** (`Exits.independent`, `Effect.schema_exitHeapOnly`). -/
theorem Effect.schema_independent (e : Effect) (c : Completion) (r : Tm) (args : List Tm) (s : IndexedHeap) :
    IndependentFrom s (e.schema.exitPostW c r args s.W s.h) :=
  Exits.independent (e.schema_exitHeapOnly c) r args s

/-- A signature's guarantee at a completion is its summary's at the call's
arity (`Effect.schema_atArity`). -/
theorem Effect.exitPost_summary {e : Effect} {c : Completion} {r : Tm} {args : List Tm} {s s' : IndexedHeap}
    {v : Tm} :
    e.schema.exitPost c r args s s' v ↔
      ((e.summary args.length).get c).Holds AssertionArena.empty (callState r args v s.h.length s s') := by
  unfold Exits.exitPost
  rw [Effect.schema_atArity]

/-- Each postcondition of the meet's normal return is one of either
signature's. -/
theorem Effect.normalPosts_meet (a b : Effect) (n : Nat) {F : Formula} (hF : F ∈ (a.meet b).normalPosts n) :
    F ∈ a.normalPosts n ∨ F ∈ b.normalPosts n := by
  have hor : ∀ (p q : Bool) (x : Formula), (F ∈ if (p || q) = true then [x] else []) →
      (F ∈ if p = true then [x] else []) ∨ (F ∈ if q = true then [x] else []) := by
    intro p q x hx
    cases p <;> cases q <;> simp_all
  have horl : ∀ (p q : Bool) (l : List Formula), (F ∈ if (p || q) = true then l else []) →
      (F ∈ if p = true then l else []) ∨ (F ∈ if q = true then l else []) := by
    intro p q l hx
    cases p <;> cases q <;> simp_all
  simp only [Effect.normalPosts, List.mem_append] at hF ⊢
  rcases hF with ((((hf | ho) | he) | hen) | hg) | hw
  · rcases hor _ _ _ hf with h | h
    · exact .inl (.inl (.inl (.inl (.inl (.inl h)))))
    · exact .inr (.inl (.inl (.inl (.inl (.inl h)))))
  · rcases hor _ _ _ ho with h | h
    · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
    · exact .inr (.inl (.inl (.inl (.inl (.inr h)))))
  · exact .inl (.inl (.inl (.inl (.inr he))))
  · simp only [Effect.meet, List.map_append, List.mem_append] at hen
    rcases hen with h | h
    · exact .inl (.inl (.inl (.inr h)))
    · exact .inr (.inl (.inl (.inr h)))
  · rcases horl _ _ _ hg with h | h
    · exact .inl (.inl (.inr h))
    · exact .inr (.inl (.inr h))
  · exact .inl (.inr hw)

/-- **The meet of two signatures with the same result meaning is a
consequence of both guarantees at one exit**: on a normal return its frame
is both frames' meet (`Effect.within_meet`) and each of its postconditions
is one of either's; on a throw it states the meet's frame where both state
`onThrow`, and the note's `⊤` otherwise. -/
theorem Effect.schema_meet {a b : Effect} (hs : a.sameResult b = true) {c : Completion} {r : Tm}
    {args : List Tm} {s s' : IndexedHeap} {v : Tm} (ha : a.schema.exitPost c r args s s' v)
    (hb : b.schema.exitPost c r args s s' v) : (a.meet b).schema.exitPost c r args s s' v := by
  rw [Effect.exitPost_summary] at ha hb ⊢
  cases c with
  | normal =>
    refine ⟨⟨ha.1.1, (Effect.within_meet hs).mpr ⟨ha.1.2, hb.1.2⟩⟩, fun F hF => ?_⟩
    rcases Effect.normalPosts_meet a b _ hF with h | h
    · exact ha.2 F h
    · exact hb.2 F h
  | exceptional =>
    simp only [Exits.get, Effect.summary] at ha hb ⊢
    by_cases hab : (a.meet b).onThrow = true
    · have ho : a.onThrow = true ∧ b.onThrow = true := by simpa [Effect.meet] using hab
      rw [if_pos ho.1] at ha
      rw [if_pos ho.2] at hb
      rw [if_pos hab]
      exact ⟨⟨ha.1.1, (Effect.within_meet hs).mpr ⟨ha.1.2, hb.1.2⟩⟩, fun _ hF => by cases hF⟩
    · rw [if_neg hab]
      have hadm : Admissible s s' := by split at ha <;> exact ha.1.1
      exact ⟨EffectAction.top hadm, fun _ hF => by cases hF⟩


/-! ## A call read at heaps -/

/-- **A call's normal completion read at heaps** (the note's Call, at the
evaluated actuals): the normal exit of the signature's schema at the
receiver and the actuals followed by the `undefined` of the positions a
construction omits, the receiver then owning no store, at some indexed
states with these heaps (`Exits.heapPost`). Each consequence a pass decision
reads is derived from the exit's frame or one of its postconditions
(`Effect.callPost_within`, `Effect.callPost_fresh`,
`Effect.callPost_freshObject`, `Effect.callPost_elements`,
`Effect.callPost_ensures`, `Effect.callPost_grows`,
`Effect.callPost_elementWrite`). -/
def Effect.callPost (e : Effect) (r : Tm) (args : List Tm) (before : Heap) : Post :=
  fun after v => ∃ pad : List Tm, (∀ a ∈ pad, a = .undef) ∧ (pad = [] ∨ Footprints.storeOf r = none) ∧
    e.schema.heapPost .normal r (args ++ pad) before after v

/-- **A call's throw read at heaps**: the exceptional exit at the actuals
followed by the omitted positions' `undefined`, read at heaps, or a throw of
the call's evaluation, which leaves the heap. -/
def Effect.callExc (e : Effect) (r : Tm) (args : List Tm) (before : Heap) : Heap → Prop :=
  fun after => (∃ (pad : List Tm) (v : Tm), (∀ a ∈ pad, a = .undef) ∧
    e.schema.heapPost .exceptional r (args ++ pad) before after v) ∨ after = before

section CallPost
variable {e : Effect} {r : Tm} {args : List Tm} {before after : Heap} {v : Tm}

/-- The normal exit read at heaps, as its summary's postconditions. -/
private theorem callPost_summary (hp : e.callPost r args before after v) :
    ∃ pad : List Tm, (∀ a ∈ pad, a = .undef) ∧ (pad = [] ∨ Footprints.storeOf r = none) ∧
      ∃ s s' : IndexedHeap, s.h = before ∧ s'.h = after ∧ Admissible s s' ∧
        Post e.frame (callEnv r args) before after ∧
        ∀ F ∈ e.normalPosts (args ++ pad).length,
          Parity.Holds AssertionArena.empty (callState r (args ++ pad) v before.length s s') F := by
  obtain ⟨pad, hpad, hrecv, s, s', rfl, rfl, hx⟩ := hp
  rw [Effect.exitPost_summary] at hx
  refine ⟨pad, hpad, hrecv, s, s', rfl, rfl, hx.1.1, ?_, hx.2⟩
  have h2 := hx.1.2
  change Post e.frame (callEnv r (args ++ pad)) s.h s'.h at h2
  rwa [callEnv_pad r args hpad] at h2

/-- **The frame**: the call's heaps meet the signature's frame. -/
theorem Effect.callPost_within (hp : e.callPost r args before after v) : e.within r args before after := by
  obtain ⟨-, -, -, -, -, -, -, -, hw, -⟩ := callPost_summary hp
  exact hw

/-- **A fresh result store**, where the signature states one. -/
theorem Effect.callPost_fresh (hf : e.fresh = true) (hp : e.callPost r args before after v) :
    Footprints.FreshAt before.length v := by
  obtain ⟨pad, _, _, s, s', hs, _, _, _, hF⟩ := callPost_summary hp
  subst hs
  exact hF (.operation (.freshStore 0)) (by simp [Effect.normalPosts, hf])

/-- **A fresh result object**, where the signature states one. -/
theorem Effect.callPost_freshObject (hf : e.freshObject = true) (hp : e.callPost r args before after v) :
    Footprints.FreshObjectAt before.length v := by
  obtain ⟨pad, _, _, s, s', hs, _, _, _, hF⟩ := callPost_summary hp
  subst hs
  exact hF (.operation (.freshObject 0)) (by simp [Effect.normalPosts, hf])

/-- **The receiver's elements** where the result is `true`, where the
signature states an elements predicate. -/
theorem Effect.callPost_elements {R : ElemPred} (hR : e.elements = some R) (hv : v = .tru)
    (hp : e.callPost r args before after v) : ElemsAt R r after := by
  obtain ⟨pad, _, _, s, s', _, hs', _, _, hF⟩ := callPost_summary hp
  subst hs'
  exact hF (.operation (.elementsWhen 0 .tru 1 R)) (by simp [Effect.normalPosts, hR]) hv

/-- **Each index fact the signature ensures**, read at the call's
positions. -/
theorem Effect.callPost_ensures {F : HeapKnowledge.IndexFact} (hF : F ∈ e.ensures) (hp : e.callPost r args before after v) :
    F.HoldsAt ⟨callEnv r args, before⟩ (ensuresEnv v r args) after := by
  obtain ⟨pad, hpad, -, s, s', rfl, rfl, -, -, hH⟩ := callPost_summary hp
  have h := hH (.operation (.fact .after 0 F)) (by simp [Effect.normalPosts, hF])
  have he : ensuresEnv v r (args ++ pad) = ensuresEnv v r args := by
    funext i; simp only [ensuresEnv, callEnv_pad r args hpad]
  change F.HoldsAt ⟨callEnv r (args ++ pad), s.h⟩ (ensuresEnv v r (args ++ pad)) s'.h at h
  rwa [he, callEnv_pad r args hpad] at h

/-- **The receiver's growth and the append of the actuals**, where the
signature states them. -/
theorem Effect.callPost_grows (hg : e.receiverGrows = true) (hp : e.callPost r args before after v) :
    ReceiverGrows r before after ∧ ReceiverAppends r args before after := by
  obtain ⟨pad, hpad, hrecv, s, s', rfl, rfl, hadm, -, hH⟩ := callPost_summary hp
  have hmem : ∀ F ∈ [(FormulaF.transition [(.field 0 arrayStoreKey, .any)] : Formula), .operation (.storeExtends 0),
      .operation (.push 0 1 (actualWitnesses (args ++ pad).length))], F ∈ e.normalPosts (args ++ pad).length := by
    intro F hF
    simp only [Effect.normalPosts, hg, List.mem_append]
    exact .inl (.inr hF)
  refine ⟨(receiverGrows_iff hadm).mp ⟨hH _ (hmem _ (by simp)), hH _ (hmem _ (by simp))⟩, fun hv => ?_⟩
  rcases hrecv with rfl | hr
  · have happ := (receiverAppends_iff (by simpa using hv)).mp (hH _ (hmem _ (by simp)))
    simp only [List.append_nil] at happ
    exact happ hv
  · exact ReceiverAppends.of_no_store hr hv

/-- **The element write's change of the heap**, where the signature states
an element write. -/
theorem Effect.callPost_elementWrite {w : ElementWrite} (hw : e.elementWrite = some w)
    (hp : e.callPost r args before after v) : w.Holds args before after := by
  obtain ⟨pad, hpad, -, s, s', rfl, rfl, -, -, hH⟩ := callPost_summary hp
  have hall : ∀ F ∈ w.posts (args ++ pad).length,
      Parity.Holds AssertionArena.empty (callState r (args ++ pad) v s.h.length s s') F := by
    intro F hF
    apply hH
    simp only [Effect.normalPosts, hw, List.mem_append]
    exact .inr hF
  exact ElementWrite.holds_pad hpad ((elementWrite_iff w).mp hall).1

/-- **The frame of a throw**, where the signature states `onThrow`; a throw
of the evaluation leaves the heap. -/
theorem Effect.callExc_within (ho : e.onThrow = true) (hp : e.callExc r args before after) :
    e.within r args before after := by
  rcases hp with ⟨pad, v, hpad, s, s', rfl, rfl, hx⟩ | rfl
  · have hf := Exits.exitPost_frame hx
    simp only [Effect.schema, Exits.get, ho, if_true] at hf
    unfold Effect.within
    rwa [callEnv_pad r args hpad] at hf
  · exact Footprints.Post.refl _ _ _

/-- **The exceptional exit's frame holds of a throw's heaps** (the note's
Call at the exceptional exit): the signature's frame where it states
`onThrow`, `⊤` otherwise; a throw of the evaluation leaves the heap. -/
theorem Effect.callExc_frame (n : Nat) (hp : e.callExc r args before after) :
    Post (e.summary n).exceptional.frame (callEnv r args) before after := by
  have hfr : (e.schema.get .exceptional).frame = (e.summary n).exceptional.frame := by
    unfold Effect.schema Effect.summary; cases e.onThrow <;> rfl
  rcases hp with ⟨pad, v, hpad, s, s', rfl, rfl, hx⟩ | rfl
  · have hf := Exits.exitPost_frame hx
    rwa [hfr, callEnv_pad r args hpad] at hf
  · exact Footprints.Post.refl _ _ _

/-- A call read at heaps from exits held from its entry: its normal and
exceptional exits at heaps (`SafePostExcV.heldPosts`). -/
theorem Effect.heldPosts_call {Ξ T : Fam} {pad : List Tm} (hpad : ∀ a ∈ pad, a = .undef)
    (hrecv : pad = [] ∨ Footprints.storeOf r = none) {n : Nat} {W : WorldT n} {h : Heap} {t : Tm}
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : SafePostExcV Ξ T (e.schema.heldPost r (args ++ pad) W h) (e.schema.heldExc r (args ++ pad) W h) n W h t) :
    SafePostExc Ξ T (e.callPost r args h) (e.callExc r args h) n W h t :=
  SafePostExc.weaken (fun _ _ hp => ⟨pad, hpad, hrecv, hp⟩)
    (fun _ hp => hp.imp (fun ⟨v, hv⟩ => ⟨pad, v, hpad, hv⟩) id) (SafePostExcV.heldPosts hw hh hs)

end CallPost

end Verification.CallEffects
