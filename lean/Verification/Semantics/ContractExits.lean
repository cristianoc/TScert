import Verification.Semantics.ExitSummaries
import Verification.Semantics.ExitWorlds
import Verification.Semantics.FormulaScopes
import Verification.Semantics.ExitComposition
import Verification.Semantics.ExitConjunction

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

/-- **A module function's summary reads its own positions**: where its
effect is about the receiver and its first `n` parameters
(`Effect.belowRow`), its frames read call positions up to `n` and its
postconditions the entry positions up to `n` and the exit positions up to
`n + 1`. -/
theorem Effect.summary_scoped {e : Effect} {n : Nat} (h : e.belowRow n = true) (k : Nat)
    (arena : AssertionArena) :
    effectScoped (n + 1) (e.summary k).normal.frame = true ∧
      (e.summary k).normal.ensures.all (FormulaF.scoped arena ⟨n + 1, n + 2⟩) = true ∧
      effectScoped (n + 1) (e.summary k).exceptional.frame = true ∧ (e.summary k).exceptional.ensures = [] := by
  have hb := Effect.belowRow_below h
  have hreg : e.regions = [] := Effect.below_regions (e := { e with ensures := [] }) hb
  have hg : e.receiverGrows = false := Effect.below_grows (e := { e with ensures := [] }) hb
  have hx : e.elementWrite = none := Effect.below_write (e := { e with ensures := [] }) hb
  have hframe : effectScoped (n + 1) e.frame = true := by
    unfold effectScoped
    refine List.all_eq_true.mpr fun x hx' => ?_
    rcases Effect.mem_frame hx' with hc | hr | ⟨q, hq, -⟩
    · obtain ⟨S, hS⟩ := Closed.fp_entry_cls hc
      simp [hS, regionRoots]
    · unfold Effect.receiverEntries at hr
      split at hr
      · simp only [List.mem_singleton] at hr; subst hr; simp [regionRoots]
      · split at hr
        · simp only [List.mem_singleton] at hr; subst hr; simp [regionRoots]
        · cases hr
    · rw [hreg] at hq; cases hq
  have htop : effectScoped (n + 1) topEffect = true := rfl
  refine ⟨hframe, ?_, ?_, ?_⟩
  · simp only [Effect.summary, Effect.normalPosts, hg, hx, Bool.false_eq_true, if_false,
      List.append_nil, List.all_append, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · cases e.fresh <;> simp [FormulaF.scoped, OperationPostF.scoped]
    · cases e.freshObject <;> simp [FormulaF.scoped, OperationPostF.scoped]
    · cases e.elements <;> simp [FormulaF.scoped, OperationPostF.scoped]
    · refine List.all_eq_true.mpr fun F hF => ?_
      obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
      simp only [FormulaF.scoped, OperationPostF.scoped, Scope.count, Nat.add_zero, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq]
      exact ⟨fun i hi => decide_eq_true (by have := Effect.belowRow_ensures h G hG i hi; omega),
        fun i hi => by have := Effect.belowRow_ensures_entry h G hG i hi; omega⟩
  · simp only [Effect.summary]
    split
    · exact hframe
    · exact htop
  · simp only [Effect.summary]
    split <;> rfl

/-- **A signature about its receiver and its first `n` parameters has one
summary at every arity** (`Effect.belowRow`): it states no append of the
actuals and no element write, the postconditions that read the arity. -/
theorem Effect.summary_arity {e : Effect} {n : Nat} (hb : e.belowRow n = true) (k k' : Nat) :
    e.summary k = e.summary k' := by
  have hb0 := Effect.belowRow_below hb
  have hg : e.receiverGrows = false := Effect.below_grows (e := { e with ensures := [] }) hb0
  have hx : e.elementWrite = none := Effect.below_write (e := { e with ensures := [] }) hb0
  simp [Effect.summary, Effect.normalPosts, hg, hx]

/-- **A call and the call of its first `m ≥ n` actuals agree below the
scope of the receiver and the first `n` parameters**: the same entry
values at positions up to `n`, the same exit values at positions up to
`n + 1`. -/
theorem callState_agreeBelow_take {n m : Nat} (hm : n ≤ m) (r : Tm) (args : List Tm) (v : Tm) (k : Nat)
    (s s' : IndexedHeap) :
    (callState r args v k s s').AgreeBelow ⟨n + 1, n + 2⟩ (callState r (args.take m) v k s s') := by
  have hc : ∀ i < n + 1, callEnv r (args.take m) i = callEnv r args i := by
    intro i hi
    unfold callEnv
    split
    · rfl
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
      rw [if_pos (by omega)]
  refine ⟨hc, fun i hi => ?_, rfl, rfl, rfl⟩
  change i < n + 2 at hi
  show ensuresEnv v r (args.take m) i = ensuresEnv v r args i
  unfold ensuresEnv
  split
  · rfl
  · exact hc _ (by omega)

/-- **A guarantee about the receiver and the first `n` parameters holds at
every call extending the call of its first `m ≥ n` actuals**
(`Effect.belowRow`): its summary is the same at both arities
(`Effect.summary_arity`) and reads the receiver, the first `n` parameters
and the result alone (`Effect.summary_scoped`), at which the two calls
agree (`callState_agreeBelow_take`, `ExitSpec.holds_scoped_congr`). -/
theorem Effect.exitPost_take {e : Effect} {n m : Nat} (hb : e.belowRow n = true) (hm : n ≤ m) {c : Completion}
    {r : Tm} {args : List Tm} {s s' : IndexedHeap} {v : Tm} (hp : e.schema.exitPost c r (args.take m) s s' v) :
    e.schema.exitPost c r args s s' v := by
  rw [Effect.exitPost_summary] at hp ⊢
  rw [Effect.summary_arity hb (args.take m).length args.length] at hp
  have hs := callState_agreeBelow_take hm r args v s.h.length s s'
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Effect.summary_scoped hb args.length AssertionArena.empty
  cases c with
  | normal => exact (ExitSpec.holds_scoped_congr h₁ h₂ hs).mp hp
  | exceptional => exact (ExitSpec.holds_scoped_congr h₃ (by rw [show ((e.summary args.length).get .exceptional).ensures = [] from h₄]; rfl) hs).mp hp

/-- **A signature without store regions selects no new old location across
allocation**, on either exit: its frame's paths agree across it
(`Effect.frame_mem_prefix`), and `⊤` is of class regions, which read a
location's contents. -/
theorem Effect.schema_frame_mem_prefix {e : Effect} (hreg : e.regions = []) (c : Completion) {ρ : Env}
    {before middle : Heap} (hprefix : before.IsPrefix middle) :
    ∀ x ∈ (e.schema.get c).frame, ∀ l, l < before.length → x.1.mem ρ middle l = true →
      x.1.mem ρ before l = true := by
  have hf := Effect.frame_mem_prefix hprefix (Effect.prefixAgrees_of_regions hreg ρ before middle)
  intro x hx l hl hm
  cases c with
  | normal => exact hf x hx l hl hm
  | exceptional =>
    simp only [Exits.get, Effect.schema] at hx
    split at hx
    · exact hf x hx l hl hm
    · have hgl : middle[l]? = before[l]? := by
        obtain ⟨t, rfl⟩ := hprefix
        exact List.getElem?_append_left hl
      obtain ⟨S, hS⟩ := Footprints.Closed.fp_entry_cls hx
      rw [hS] at hm ⊢
      simpa only [Footprints.Region.mem, hgl] using hm

/-- **A signature's exits carried across an allocation before the call**
(`Exits.compose_entry`): a signature stating no store region, no ensured
fact, no append and no element write has from an entry the exits it has
from a later entry, at a world the first reaches, whose heap extends the
first's by allocation. Its frame rebases to itself (`Rebases.of_prefix`),
the allocation keeps every old location (`Post.of_prefix`), and its
postconditions read the entry only through the freshness mark, which the
allocation raises (`FreshAt.lower`, `FreshObjectAt.lower`). -/
theorem Effect.exitPost_prefix {e : Effect} (hreg : e.regions = []) (hens : e.ensures = [])
    (hg : e.receiverGrows = false) (hx : e.elementWrite = none) {c : Completion} {r : Tm} {args : List Tm}
    {s₀ s₁ s₂ : IndexedHeap} {v : Tm} (hadm : Admissible s₀ s₁) (hprefix : s₀.h.IsPrefix s₁.h)
    (h : e.schema.exitPost c r args s₁ s₂ v) : e.schema.exitPost c r args s₀ s₂ v := by
  refine Exits.compose_entry (Φ := []) (cl := fun _ _ => none) ⟨hadm, Post.of_prefix _ _ hprefix⟩
    (Rebases.of_prefix (Effect.schema_frame_mem_prefix hreg c hprefix)) (Footprint.le_refl _ _)
    (fun _ _ _ _ hc => by cases hc) ?_ h
  intro u z hF
  rw [Effect.schema_atArity] at hF ⊢
  intro F hFm
  have hH := hF F hFm
  cases c with
  | exceptional =>
    simp only [Exits.get, Effect.summary] at hFm
    split at hFm <;> cases hFm
  | normal =>
    simp only [Exits.get, Effect.summary, Effect.normalPosts, hg, hx, hens, Bool.false_eq_true, if_false,
      List.map_nil, List.append_nil, List.mem_append] at hFm
    rcases hFm with (hf | ho) | hel
    · cases hc : e.fresh <;> simp [hc] at hf; subst hf; exact FreshAt.lower hprefix.length_le hH
    · cases hc : e.freshObject <;> simp [hc] at ho; subst ho; exact FreshObjectAt.lower hprefix.length_le hH
    · cases hc : e.elements <;> simp [hc] at hel; subst hel; exact hH

/-- **An allocation alone meets every signature's exceptional exit**: it
keeps every old location (`Post.of_prefix`), and the exceptional exit
states no postcondition. -/
theorem Effect.exitPost_exceptional_prefix (e : Effect) {r : Tm} {args : List Tm} {s s' : IndexedHeap} {v : Tm}
    (hadm : Admissible s s') (hprefix : s.h.IsPrefix s'.h) : e.schema.exitPost .exceptional r args s s' v := by
  rw [Effect.exitPost_summary]
  refine ⟨⟨hadm, Post.of_prefix _ _ hprefix⟩, fun F hF => ?_⟩
  simp only [Exits.get, Effect.summary] at hF
  split at hF <;> cases hF

/-- **Safety at a signature's exits at the first `m` actuals is safety at
its exits at every call extending them**, the signature about its receiver
and its first `n ≤ m` parameters (`Effect.exitPost_take`). -/
theorem Effect.safe_exits_take {Ξ T : Fam} {e : Effect} {n m : Nat} (hb : e.belowRow n = true) (hm : n ≤ m)
    {r : Tm} {args : List Tm} {j : Nat} {U : WorldT j} {heap : Heap} {t : Tm} (hu : WorldAdm U)
    (hh : HeapOk j U heap)
    (hs : SafePostExcV Ξ T (e.schema.exitPostW .normal r (args.take m) U heap)
      (e.schema.exitPostW .exceptional r (args.take m) U heap) j U heap t) :
    SafePostExcV Ξ T (e.schema.exitPostW .normal r args U heap) (e.schema.exitPostW .exceptional r args U heap)
      j U heap t := by
  refine SafePostExcV.weaken_reached hu hh ?_ ?_ hs <;>
    rintro s s' val rfl hW rfl - hp <;> cases eq_of_heq hW <;>
    exact (Exits.exitPostW_iff _ _ _ _ s s' val).mpr
      (Effect.exitPost_take hb hm ((Exits.exitPostW_iff _ _ _ _ s s' val).mp hp))

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
`onThrow`, and the note's `⊤` otherwise. It is weaker than the conjunction
of the two schemas (`Effect.meet_of_conjunction`): where one signature
alone bounds its throw, the meet's exceptional exit is `⊤` while the
conjunction keeps that bound. -/
theorem Effect.meet_consequence {a b : Effect} (hs : a.sameResult b = true) {c : Completion} {r : Tm}
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


/-- **A signature's schema has canonical transports**: its one transport,
the written result, reads each other entry slot at the next exit slot. -/
theorem Effect.schema_canonical (e : Effect) : e.schema.canonicalTransports = true := by
  have hw : ∀ w : ElementWrite, w.schemaPosts.all (·.canonical) = true := by
    intro w; cases w with
    | stores => rfl
    | assign => rfl
    | exact k =>
      simp only [ElementWrite.schemaPosts, List.all_cons, List.all_append, List.all_map]
      simp [FormulaF.canonical, Function.comp_def, writtenResultSchema]
  simp only [Exits.canonicalTransports, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · simp only [Effect.schema, ExitSchema.canonicalTransports, Effect.normalSchema, List.all_append,
      Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
    · simp [List.all_map, FormulaF.canonical, Function.comp_def]
    · split <;> rfl
    · split
      · exact hw _
      · rfl
  · simp only [Effect.schema, ExitSchema.canonicalTransports]
    split <;> rfl

/-- **The meet of two signatures is a consequence of their schemas'
conjunction** (`Exits.exitPost_meet`, `Effect.meet_consequence`). -/
theorem Effect.meet_of_conjunction {a b : Effect} (hs : a.sameResult b = true) {c : Completion} {r : Tm}
    {args : List Tm} {s s' : IndexedHeap} {v : Tm} (h : (a.schema.meet b.schema).exitPost c r args s s' v) :
    (a.meet b).schema.exitPost c r args s s' v :=
  have h' := (Exits.exitPost_meet a.schema_canonical b.schema_canonical).mp h
  Effect.meet_consequence hs h'.1 h'.2

/-! ## A call read at heaps -/

/-- **A call's normal completion read at heaps** (the note's Call, at the
evaluated actuals): the normal exit of the signature's schema at the
receiver and the actuals followed by the `undefined` of the positions a
construction omits, the receiver then owning no store, at some indexed
states with these heaps (`Exits.heapPost`). Each consequence a pass decision
reads is derived from the exit's frame or one of its postconditions
(`Effect.callPost_within`, `Effect.callPost_fresh`,
`Effect.callPost_freshObject`, `Effect.callPost_elements`,
`Effect.callPost_ensures`, `Effect.callPost_storeGrows`,
`Effect.callPost_appends`, `Effect.callPost_viewGrowth`,
`Effect.callPost_exactWrite`). -/
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

/-- **Every postcondition of the normal exit holds**, instantiated at the
evaluated actuals followed by the omitted positions' `undefined`, at indexed
states with the call's heaps. -/
theorem Effect.callPost_holds (hp : e.callPost r args before after v) :
    ∃ pad : List Tm, (∀ a ∈ pad, a = .undef) ∧ (pad = [] ∨ Footprints.storeOf r = none) ∧
      ∃ s s' : IndexedHeap, s.h = before ∧ s'.h = after ∧ Admissible s s' ∧
        ∀ F ∈ e.schema.normal.ensures, Parity.Holds AssertionArena.empty
          (callState r (args ++ pad) v before.length s s')
          (instantiateFormula (e.schema.callInstantiation (args ++ pad).length) F) := by
  obtain ⟨pad, hpad, hrecv, s, s', rfl, rfl, hx⟩ := hp
  exact ⟨pad, hpad, hrecv, s, s', rfl, rfl, Exits.exitPost_admissible hx, Exits.exitPost_ensures hx⟩

/-- **The receiver's growth**, where the normal exit states the frame
`{receiver store: any}` and the store's extension (`receiverGrows_iff`). -/
theorem Effect.callPost_storeGrows
    (h1 : (.transition [(.field 0 arrayStoreKey, .any)] : FormulaSchema) ∈ e.schema.normal.ensures)
    (h2 : (.operation (.storeExtends 0) : FormulaSchema) ∈ e.schema.normal.ensures)
    (hp : e.callPost r args before after v) : ReceiverGrows r before after := by
  obtain ⟨pad, -, -, s, s', rfl, rfl, hadm, hH⟩ := Effect.callPost_holds hp
  exact (receiverGrows_iff (args := args ++ pad) hadm).mp ⟨hH _ h1, hH _ h2⟩

/-- **The append of the actuals**, where the normal exit states the append
of the actuals from position `1` on (`receiverAppends_iff`). -/
theorem Effect.callPost_appends
    (ha : (.operation (.push 0 1 (.restFrom 1)) : FormulaSchema) ∈ e.schema.normal.ensures)
    (hp : e.callPost r args before after v) : ReceiverAppends r args before after := by
  obtain ⟨pad, -, hrecv, s, s', rfl, rfl, -, hH⟩ := Effect.callPost_holds hp
  have hF := hH _ ha
  simp only [instantiateFormula, FormulaF.map, OperationPostF.map, Exits.callInstantiation, restFrom_one] at hF
  intro hv
  rcases hrecv with rfl | hr
  · simp only [List.append_nil] at hF
    exact (receiverAppends_iff (by simpa using hv)).mp hF hv
  · exact ReceiverAppends.of_no_store hr hv

/-- **An element write's coarse change**, where the normal exit states the
views' growth `{all-views: grow}` (`Kinds.ViewWrite.frame_iff`,
`Kinds.ViewWrite.changes`). -/
theorem Effect.callPost_viewGrowth
    (hg : (.transition [(.cls .views, .grow)] : FormulaSchema) ∈ e.schema.normal.ensures)
    (hp : e.callPost r args before after v) : ElementWrite.stores.changes.Holds before after := by
  obtain ⟨pad, -, -, s, s', rfl, rfl, -, hH⟩ := Effect.callPost_holds hp
  have hF := hH _ hg
  have hw : Kinds.ViewWrite s.W s.h s'.W s'.h :=
    (Kinds.ViewWrite.frame_iff s.ok (callEnv r (args ++ pad))).mpr ⟨hF.1, s'.ok, hF.2⟩
  exact hw.changes s.ok .stores

/-- **An exact element write**, where the normal exit states View-Write at
the element type's format and the facts of its precondition
(`exactPre_iff`). -/
theorem Effect.callPost_exactWrite {k : ElementKind}
    (hw : (.operation (.viewWrite 1 2 3 (some k.format)) : FormulaSchema) ∈ e.schema.normal.ensures)
    (hpre : ∀ F ∈ k.preFacts, (.operation (.fact .before 0 F) : FormulaSchema) ∈ e.schema.normal.ensures)
    (hp : e.callPost r args before after v) : ExactWrite k args before after ∧ ExactPre k args := by
  obtain ⟨pad, hpad, -, s, s', rfl, rfl, -, hH⟩ := Effect.callPost_holds hp
  have hx : ExactWrite k (args ++ pad) s.h s'.h := hH _ hw _ rfl
  have hq : ExactPre k (args ++ pad) := (exactPre_iff (r := r) k s.h).mp fun F hF => hH _ (hpre F hF)
  have hg : ∀ i, (args ++ pad).getD i .undef = args.getD i .undef := fun i => by
    simpa [callEnv] using congrFun (callEnv_pad .undef args hpad) (i + 1)
  simp only [ExactWrite, WriteAt, ExactPre, hg] at hx hq ⊢
  exact ⟨hx, hq⟩

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
