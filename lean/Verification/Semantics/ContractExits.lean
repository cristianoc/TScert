import Verification.Semantics.ExitSummaries
import Verification.Semantics.ExitWorlds
import Verification.Semantics.FormulaScopes
import Verification.Semantics.ExitComposition
import Verification.Semantics.ExitConjunction
import Verification.Semantics.ExitRenaming
import Verification.Semantics.ExitScopes

/-! # A signature's contract read per exit

The native-contract condition of a signature (`NativeContract`,
`NativeConstruct`) stated by its specification per completion
(`Exits.exitPostW`, the note's Call on both exits), and the operations on
signatures and readings of a call that the pass draws from it. -/
namespace Verification.CallEffects
open Verification Footprints Parity TolerantFrames HeapObservations

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

/-- **The scope of a signature at code of arity `n`**: what it states of
the call's values at entry (`Effect.entryBelow`) and its schema
(`Exits.belowRow`) are about the receiver and the first `n` parameters, the
ones code of arity `n` binds. Whether a body establishes what the schema
states is body certification's decision (`ProgramTyping.codeObligations`). -/
def Effect.belowRow (n : Nat) (e : Effect) : Bool := e.entryBelow n && e.schema.belowRow n

theorem Effect.belowRow_entry {e : Effect} {n : Nat} (h : e.belowRow n = true) : e.entryBelow n = true := by
  simp only [Effect.belowRow, Bool.and_eq_true] at h; exact h.1

/-- **A signature scoped at arity `n` has a schema scoped there**. -/
theorem Effect.schema_belowRow {e : Effect} {n : Nat} (h : e.belowRow n = true) : e.schema.belowRow n = true := by
  simp only [Effect.belowRow, Bool.and_eq_true] at h; exact h.2

/-- **A signature's summary at its code's arity reads its own positions**
(`Exits.belowRow`): at arity `n` the summary is the schema at the code's
instantiation, its frames reading call positions up to `n`, its
postconditions entry positions up to `n` and exit positions up to `n + 1`. -/
theorem Effect.summary_scoped {e : Effect} {n : Nat} (h : e.belowRow n = true) (c : Completion) :
    effectScoped (n + 1) ((e.summary n).get c).frame = true ∧
      ((e.summary n).get c).ensures.all (FormulaF.scoped AssertionArena.empty ⟨n + 1, n + 2⟩) = true := by
  have hb := Effect.schema_belowRow h
  simp only [Exits.belowRow, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨-, hslots⟩, hn⟩, hx⟩ := hb
  have hι : e.schema.callInstantiation n = arityInstantiation n := by
    simp only [Exits.callInstantiation, arityInstantiation, Nat.max_eq_left hslots]
  have hq : (e.schema.get c).belowRow n = true := by cases c <;> assumption
  simp only [ExitSchema.belowRow, Bool.and_eq_true] at hq
  rw [Effect.summary, Exits.atArity, Exits.get_map, hι]
  exact ⟨hq.1.1, by simpa only [ExitSchema.instantiate, List.all_map, Function.comp_def] using hq.2⟩

/-- **A postcondition fact of a signature scoped at arity `n`** reads the
result, the receiver and the first `n` parameters at exit and the receiver
and the first `n` parameters at entry (`Effect.summary_scoped`, the fact as
the normal exit's postcondition). -/
theorem Effect.belowRow_ensures {e : Effect} {n : Nat} (h : e.belowRow n = true) {F : HeapKnowledge.IndexFact}
    (hF : F ∈ e.schema.normal.facts) : (∀ s ∈ F.slots, s ≤ n + 1) ∧ ∀ s ∈ F.entrySlots, s ≤ n := by
  have hs := (Effect.summary_scoped h .normal).2
  have hm : (FormulaF.operation (.fact .after 0 F) : Formula) ∈ ((e.summary n).get .normal).ensures := by
    exact List.mem_map_of_mem (f := instantiateFormula (e.schema.callInstantiation n)) (ExitSchema.mem_facts.mp hF)
  have := List.all_eq_true.mp hs _ hm
  simp only [FormulaF.scoped, OperationPostF.scoped, Scope.count, Nat.add_zero, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at this
  exact ⟨fun s hs' => by have := of_decide_eq_true (this.1 s hs'); omega,
    fun s hs' => by have := this.2 s hs'; omega⟩

/-- **A guarantee about the receiver and the first `n` parameters holds at
every call extending the call of its first `m ≥ n` actuals**
(`Effect.belowRow`): its schema is scoped there (`Effect.schema_belowRow`,
`Exits.exitPost_take`). -/
theorem Effect.exitPost_take {e : Effect} {n m : Nat} (hb : e.belowRow n = true) (hm : n ≤ m) {c : Completion}
    {r : Tm} {args : List Tm} {s s' : IndexedHeap} {v : Tm} (hp : e.schema.exitPost c r (args.take m) s s' v) :
    e.schema.exitPost c r args s s' v :=
  (Exits.exitPost_take (Effect.schema_belowRow hb) hm).mp hp

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

/-- **Binding `n` actuals** (the note, rule Call at a bound function, then
consequence): the bound signature's exits are the signature's weakened at
the bound call (`Exits.dropWeak`), exact where the substitution of the saved
positions is defined (`Exits.dropWeak_of_drop`); its promise is about the
same actual, counted after the saved ones; its preconditions are kept. -/
def Effect.drop (n : Nat) (e : Effect) : Effect :=
  ⟨e.exits.dropWeak n, e.promise.map (TypePromise.drop n), e.requires, e.pre⟩

/-- **Binding is consequence on both exits** (`Exits.exitPost_dropWeak`): a
signature's exits at the longer call, the saved receiver and actuals in
front, give the bound signature's exits at the bound call. -/
theorem Effect.drop_exits {e : Effect} {pre args : List Tm} {c : Completion} {r r₀ : Tm}
    {s s' : IndexedHeap} {v : Tm} (h : e.schema.exitPost c r₀ (pre ++ args) s s' v) :
    (e.drop pre.length).schema.exitPost c r args s s' v :=
  Exits.exitPost_dropWeak rfl h

/-- **A bound signature's exits reference no arena node**: a substituted
postcondition never does (`renameFormula`). -/
theorem Effect.drop_arenaFree (n : Nat) (e : Effect) (c : Completion) : ((e.drop n).schema.get c).arenaFree = true :=
  Exits.dropWeak_arenaFree n e.exits c

theorem Effect.promised_drop {e : Effect} {pre args : List Tm} (h : e.keeps pre.length = true) :
    (e.drop pre.length).promised args = e.promised (pre ++ args) := by
  rcases e with ⟨x, _ | (p | p), rq, pr⟩ <;>
    simp only [Effect.keeps, Effect.drop, Effect.promised, TypePromise.drop, TypePromise.param,
      Option.map, Bool.and_eq_true] at h ⊢
  all_goals
    have h' : pre.length ≤ p := of_decide_eq_true h.2
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h']

theorem Effect.result_drop (e : Effect) (n : Nat) (R : Fam) (a : Tm) :
    (e.drop n).result R a = e.result R a := by
  rcases e with ⟨x, _ | (_ | _), rq, pr⟩ <;> rfl

/-! ## A call read at heaps -/

/-- **A call's normal completion read at heaps** (the note's Call, at the
evaluated actuals): the normal exit of the signature's schema at the
receiver and the actuals followed by the `undefined` of the positions a
construction omits, the receiver then owning no spine, at some indexed
states with these heaps (`Exits.heapPost`). Each consequence a pass decision
reads is derived from the exit's frame or one of its postconditions
(`Effect.callPost_within`, `Effect.callPost_fresh`,
`Effect.callPost_freshObject`, `Effect.callPost_elements`,
`Effect.callPost_ensures`, `Effect.callPost_spineGrows`,
`Effect.callPost_appends`, `Effect.callPost_viewGrowth`,
`Effect.callPost_exactWrite`). -/
def Effect.callPost (e : Effect) (r : Tm) (args : List Tm) (before : Heap) : Post :=
  fun after v => ∃ pad : List Tm, (∀ a ∈ pad, a = .undef) ∧ (pad = [] ∨ Footprints.spineOf r = none) ∧
    e.schema.heapPost .normal r (args ++ pad) before after v

/-- **The receiver's extension as a frame**: what a normal return of the
note's Push may change, `{x.spine: extend}`, within its `{x.spine: grow}`,
the receiver at position `0`, its spine the location of its `[]` slot
holding an array spine (`Effect.callPost_receiverExtendFrame`). -/
def receiverExtendFrame : Footprint := [((Region.field 0 arraySpineKey).inCls .arrays, .extend)]

/-- **A call's throw read at heaps**: the exceptional exit at the actuals
followed by the omitted positions' `undefined`, read at heaps, or a throw of
the call's evaluation, which leaves the heap. -/
def Effect.callExc (e : Effect) (r : Tm) (args : List Tm) (before : Heap) : Heap → Prop :=
  fun after => (∃ (pad : List Tm) (v : Tm), (∀ a ∈ pad, a = .undef) ∧
    e.schema.heapPost .exceptional r (args ++ pad) before after v) ∨ after = before

section CallPost
variable {e : Effect} {r : Tm} {args : List Tm} {before after : Heap} {v : Tm}

/-- **Every postcondition of the normal exit holds**, instantiated at the
evaluated actuals followed by the omitted positions' `undefined`, at indexed
states with the call's heaps. -/
theorem Effect.callPost_holds (hp : e.callPost r args before after v) :
    ∃ pad : List Tm, (∀ a ∈ pad, a = .undef) ∧ (pad = [] ∨ Footprints.spineOf r = none) ∧
      ∃ s s' : IndexedHeap, s.h = before ∧ s'.h = after ∧ Admissible s s' ∧
        ∀ F ∈ e.schema.normal.ensures, Parity.Holds AssertionArena.empty
          (callState r (args ++ pad) v before.length s s')
          (instantiateFormula (e.schema.callInstantiation (args ++ pad).length) F) := by
  obtain ⟨pad, hpad, hrecv, s, s', rfl, rfl, hx⟩ := hp
  exact ⟨pad, hpad, hrecv, s, s', rfl, rfl, Exits.exitPost_admissible hx, Exits.exitPost_ensures hx⟩

/-- **The frame**: the call's heaps meet the normal exit's frame. -/
theorem Effect.callPost_within (hp : e.callPost r args before after v) : e.within r args before after := by
  obtain ⟨pad, hpad, -, s, s', rfl, rfl, hx⟩ := hp
  have hf := Exits.exitPost_frame hx
  change Post e.schema.normal.frame (callEnv r (args ++ pad)) s.h s'.h at hf
  rwa [callEnv_pad r args hpad] at hf

/-- **A fresh result spine**, where the normal exit states one
(`ExitSchema.freshResult`). -/
theorem Effect.callPost_fresh (hf : e.schema.normal.freshResult = true) (hp : e.callPost r args before after v) :
    Footprints.FreshAt before.length v := by
  obtain ⟨pad, -, -, s, s', rfl, -, -, hH⟩ := Effect.callPost_holds hp
  exact hH (.operation (.freshSpine 0)) (by simpa [ExitSchema.freshResult] using hf)

/-- **A fresh result object**, where the normal exit states one
(`ExitSchema.freshObjectResult`). -/
theorem Effect.callPost_freshObject (hf : e.schema.normal.freshObjectResult = true)
    (hp : e.callPost r args before after v) : Footprints.FreshObjectAt before.length v := by
  obtain ⟨pad, -, -, s, s', rfl, -, -, hH⟩ := Effect.callPost_holds hp
  exact hH (.operation (.freshObject 0)) (by simpa [ExitSchema.freshObjectResult] using hf)

/-- **The receiver's elements** where the result is `true`, for each
element predicate the normal exit states (`ExitSchema.elementsWhenTrue`). -/
theorem Effect.callPost_elements {R : ElemPred} (hR : R ∈ e.schema.normal.elementsWhenTrue) (hv : v = .tru)
    (hp : e.callPost r args before after v) : ElemsAt R r after := by
  obtain ⟨pad, -, -, s, s', -, rfl, -, hH⟩ := Effect.callPost_holds hp
  exact hH (.operation (.elementsWhen 0 .tru 1 R)) (ExitSchema.mem_elementsWhenTrue.mp hR) hv

/-- **Each index fact the normal exit states** (`ExitSchema.facts`), read at
the call's positions. -/
theorem Effect.callPost_ensures {F : HeapKnowledge.IndexFact} (hF : F ∈ e.schema.normal.facts)
    (hp : e.callPost r args before after v) :
    F.HoldsAt ⟨callEnv r args, before⟩ (ensuresEnv v r args) after := by
  obtain ⟨pad, hpad, -, s, s', rfl, rfl, -, hH⟩ := Effect.callPost_holds hp
  have h := hH (.operation (.fact .after 0 F)) (ExitSchema.mem_facts.mp hF)
  have he : ensuresEnv v r (args ++ pad) = ensuresEnv v r args := by
    funext i; simp only [ensuresEnv, callEnv_pad r args hpad]
  change F.HoldsAt ⟨callEnv r (args ++ pad), s.h⟩ (ensuresEnv v r (args ++ pad)) s'.h at h
  rwa [he, callEnv_pad r args hpad] at h

/-- **The receiver's growth**, where the normal exit states the frame
`{receiver spine: any}` and the spine's extension (`receiverGrows_iff`). -/
theorem Effect.callPost_spineGrows
    (h1 : (.transition [(.field 0 arraySpineKey, .any)] : FormulaSchema) ∈ e.schema.normal.ensures)
    (h2 : (.operation (.spineExtends 0) : FormulaSchema) ∈ e.schema.normal.ensures)
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
  · exact ReceiverAppends.of_no_spine hr hv

/-- **A growth that appends is within the receiver's extension frame**
(`receiverExtendFrame`, the note's Push): the spine `ReceiverGrows` lets
change extends the old one at its end, and the cells it lists past the old
length are the appended ones, each fresh (`ReceiverAppends`). -/
theorem receiverExtendFrame_post {r : Tm} {args vs : List Tm} {before after : Heap}
    (hlen : before.length ≤ after.length) (hg : ReceiverGrows r before after)
    (hvs : ∀ a ∈ vs, isVal a = true) (ha : ReceiverAppends r vs before after) :
    Post receiverExtendFrame (callEnv r args) before after := by
  refine ⟨hlen, fun l u hu => ?_⟩
  rcases hg l u hu with hk | ⟨hs, ls, ls', rfl, hl', hpre, hmax⟩
  · exact ⟨u, hk, .inl rfl⟩
  · obtain ⟨ls'', hl'', hn, hnew⟩ := ha hvs l ls hs hu
    rw [hl'] at hl''
    cases hl''
    obtain ⟨t, rfl⟩ := hpre
    refine ⟨.arr (ls ++ t), hl', .inr ⟨_, List.mem_singleton_self _, ?_, .inr (.inr ⟨ls, t, rfl, rfl,
      ?_, ⟨by simp, fun _ => hmax⟩⟩)⟩⟩
    · simp only [Region.mem, hu, Bool.and_eq_true]
      exact ⟨by simpa [callEnv, spineOf] using hs, rfl⟩
    · intro l₀ hm
      obtain ⟨j, hj, hjt⟩ := List.getElem_of_mem hm
      have hjv : j < vs.length := by simp at hn; omega
      obtain ⟨l₁, hl₁, -, hfresh⟩ := hnew j vs[j] (List.getElem?_eq_getElem hjv)
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj,
        hjt] at hl₁
      cases hl₁
      exact hfresh

/-- **The receiver's extension frame follows from the growth's
postconditions**: where the normal exit states the frame `{receiver spine:
any}`, the spine's extension and the append of the actuals, a normal return
is within `receiverExtendFrame`. A contract stating this frame as its
normal frame states nothing its postconditions do not. -/
theorem Effect.callPost_receiverExtendFrame
    (h1 : (.transition [(.field 0 arraySpineKey, .any)] : FormulaSchema) ∈ e.schema.normal.ensures)
    (h2 : (.operation (.spineExtends 0) : FormulaSchema) ∈ e.schema.normal.ensures)
    (h3 : (.operation (.push 0 1 (.restFrom 1)) : FormulaSchema) ∈ e.schema.normal.ensures)
    (hp : e.callPost r args before after v) : Post receiverExtendFrame (callEnv r args) before after := by
  obtain ⟨pad, -, -, s, s', rfl, rfl, hadm, hH⟩ := Effect.callPost_holds hp
  have hg := (receiverGrows_iff (args := args ++ pad) hadm).mp ⟨hH _ h1, hH _ h2⟩
  have hF := hH _ h3
  simp only [instantiateFormula, FormulaF.map, OperationPostF.map, Exits.callInstantiation, restFrom_one,
    Parity.Holds, OperationPostF.Holds, callState] at hF
  obtain ⟨vs, -, hvs, ha, -⟩ := hF
  exact receiverExtendFrame_post hadm.length_le hg hvs ha

/-- **An element write's coarse change**, where the normal exit states the
views' growth `{all-views: grow}` (`Kinds.ViewWrite.frame_iff`,
`Kinds.ViewWrite.changes`). -/
theorem Effect.callPost_viewGrowth
    (hg : (.transition [(.cls .views, .grow)] : FormulaSchema) ∈ e.schema.normal.ensures)
    (hp : e.callPost r args before after v) : ElementWrite.spines.changes.Holds before after := by
  obtain ⟨pad, -, -, s, s', rfl, rfl, -, hH⟩ := Effect.callPost_holds hp
  have hF := hH _ hg
  have hw : Kinds.ViewWrite s.W s.h s'.W s'.h :=
    (Kinds.ViewWrite.frame_iff s.ok (callEnv r (args ++ pad))).mpr ⟨hF.1, s'.ok, hF.2⟩
  exact hw.changes s.ok .spines

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

/-- **The frame of a throw**: the exceptional exit's frame at the call's
positions; a throw of the evaluation leaves the heap. -/
theorem Effect.callExc_exitFrame (hp : e.callExc r args before after) :
    Post e.schema.exceptional.frame (callEnv r args) before after := by
  rcases hp with ⟨pad, v, hpad, s, s', rfl, rfl, hx⟩ | rfl
  · have hf := Exits.exitPost_frame hx
    rwa [callEnv_pad r args hpad] at hf
  · exact Footprints.Post.refl _ _ _

/-- **A throw meets the exceptional exit's frame of the summary**, at
every arity (`Effect.callExc_exitFrame`). -/
theorem Effect.callExc_frame (n : Nat) (hp : e.callExc r args before after) :
    Post (e.summary n).exceptional.frame (callEnv r args) before after :=
  Effect.callExc_exitFrame hp

/-- A call read at heaps from exits held from its entry: its normal and
exceptional exits at heaps (`SafePostExcV.heldPosts`). -/
theorem Effect.heldPosts_call {Ξ T : Fam} {pad : List Tm} (hpad : ∀ a ∈ pad, a = .undef)
    (hrecv : pad = [] ∨ Footprints.spineOf r = none) {n : Nat} {W : WorldT n} {h : Heap} {t : Tm}
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : SafePostExcV Ξ T (e.schema.heldPost r (args ++ pad) W h) (e.schema.heldExc r (args ++ pad) W h) n W h t) :
    SafePostExc Ξ T (e.callPost r args h) (e.callExc r args h) n W h t :=
  SafePostExc.weaken (fun _ _ hp => ⟨pad, hpad, hrecv, hp⟩)
    (fun _ hp => hp.imp (fun ⟨v, hv⟩ => ⟨pad, v, hpad, hv⟩) id) (SafePostExcV.heldPosts hw hh hs)

end CallPost

/-! ### An exact write's range among a contract's preconditions

View-Write at a format (`viewWrite … (some f)`) is exact for the values its
element type takes; for any other value the host converts it. A contract
stating an exact write therefore states its value's and index's range
(`ElementKind.preFacts`) among its preconditions, which its callers
establish (`ElementKind.exactPre_of_requires`). This is a condition of a
contract's admission, checked where a document's effect is read
(`EffectJson`): the front end that writes the contract is unproved, and a
document can be forged. -/

/-- The formats of the exact view writes a formula states, its
conjunctions opened. -/
def exactWriteFormats : FormulaSchema → List ViewFormat
  | .operation (.viewWrite _ _ _ (some f)) => [f]
  | .and a b => exactWriteFormats a ++ exactWriteFormats b
  | _ => []

/-- **Every exact view write a contract states, at either exit and at any
conjunction depth, has its element type's range facts among the contract's
preconditions.** -/
def Effect.exactWritesRequired (e : Effect) : Bool :=
  (e.exits.normal.ensures ++ e.exits.exceptional.ensures).all fun F =>
    (exactWriteFormats F).all fun f => (ElementKind.ofFormat f).preFacts.all e.pre.contains

/-- **An admitted contract's exact write has its range among the
preconditions** (proved): at a call meeting the precondition, the facts an
exact write needs hold (`ElementKind.exactPre_of_requires`). -/
theorem Effect.exactWrite_pre {e : Effect} (h : e.exactWritesRequired = true) {x i v : Nat} {f : ViewFormat}
    (hw : (.operation (.viewWrite x i v (some f)) : FormulaSchema) ∈ e.schema.normal.ensures) :
    ∀ F ∈ (ElementKind.ofFormat f).preFacts, F ∈ e.pre := by
  intro F hF
  have hall := List.all_eq_true.mp h _ (List.mem_append_left _ hw)
  simp only [exactWriteFormats, List.all_cons, List.all_nil, Bool.and_true] at hall
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hall F hF)

end Verification.CallEffects
