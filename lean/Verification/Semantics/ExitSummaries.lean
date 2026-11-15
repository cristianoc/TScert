import Verification.Semantics.ParityDerivations

/-! # Exit summaries

A callable's guarantee per completion (the note *Tolerant frames*, §6, the
judgment $c:\Phi\mid\Phi^{e}$): for each exit, a frame, a list of
region-and-change entries read at the call's entry, and a list of two-state
postconditions (`Parity.Formula`), all read at one two-state interpretation
(`ExitSpec.Holds`). The entry environment holds the call's positions
(`callEnv`: `0` the receiver, `i + 1` the `i`-th actual); the exit
environment holds the returned or thrown value at `0` and the call's
positions one higher (`ensuresEnv`).

A signature's effect (`Effect`) is elaborated into its summary at an arity
(`Effect.summary`):

- the normal frame is the signature's frame (`Effect.frame`): its closed
  bound's three class entries, its receiver's entries and its argument store
  regions;
- the normal postconditions are the result's fresh store and fresh object,
  the receiver's elements where the result is `true`, the index facts the
  signature states, the receiver's growth and the append, and the view write
  with its assignment and conversion;
- the exceptional frame is the normal one where the signature states
  `onThrow`, and the note's `⊤` otherwise; a throw states no postcondition.

A guarantee stated beside the frame, the growth's frame `{receiver store:
any}` and the view write's `{all-views: grow}`, is a postcondition
`.transition Φ`, conjoined with the frame: the two hold of one transition.

**On admissible transitions the summary states the signature's contract**
(`Effect.summary_normal_iff`, `Effect.summary_exceptional_iff`): its normal
exit is `Effect.postW`, its exceptional exit `Effect.excPost`. -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge TolerantFrames Parity

/-! ## Exit specifications -/

/-- **A completion's guarantee** (the note, §6): the frame bounding the old
locations it may change, read at the entry's environment, and the
postconditions it states. -/
structure ExitSpec where
  frame : Footprint
  ensures : List Formula
  deriving DecidableEq

/-- **The meaning of an exit specification**: the transition is an action of
the frame, and every postcondition holds, all in the same two-state
interpretation. -/
def ExitSpec.Holds (arena : AssertionArena) (q : ExitSpec) (s : TwoState) : Prop :=
  EffectAction q.frame s.beforeEnv s.before s.after ∧ ∀ F ∈ q.ensures, Parity.Holds arena s F

/-- The two-state interpretation of a call with receiver `r` and actuals
`args` completing with `v`, from the state `s` to the state `s'`, at the
mark `m`. -/
def callState (r : Tm) (args : List Tm) (v : Tm) (m : Nat) (s s' : IndexedHeap) : TwoState :=
  ⟨callEnv r args, ensuresEnv v r args, m, s, s'⟩

/-- The call positions of the first `n` actuals, as witnesses read at the
entry. -/
def actualWitnesses (n : Nat) : List Witness := (List.range n).map fun i => .path ⟨i + 1, []⟩

/-- The transport stating that the result is the value written, the third
actual (entry slot `3`): exit slot `0` reads entry slot `3`, and each other
entry slot `i` is exit slot `i + 1`. -/
def writtenResult (n : Nat) : Substitution :=
  ⟨((List.range (max (n + 1) 4)).map fun i => Witness.path ⟨if i = 3 then 0 else i + 1, []⟩).toArray, false, []⟩

/-! ## The elaboration -/

/-- **A typed array's element write as postconditions**: its frame
`{all-views: grow}` (`Kinds.ViewWrite.frame_iff`), and for an element
assignment View-Write at the typed array's format and the result the value
written, for the exact form View-Write at the element type's format, the
facts its precondition gives and the result. -/
def ElementWrite.posts (n : Nat) : ElementWrite → List Formula
  | .stores => [.transition [(.cls .views, .grow)]]
  | .assign => [.transition [(.cls .views, .grow)], .operation (.viewWrite 1 2 3 none), .transport (writtenResult n)]
  | .exact k => .transition [(.cls .views, .grow)] :: .operation (.viewWrite 1 2 3 (some k.format)) ::
      ((k.preFacts.map fun F => .operation (.fact .before 0 F)) ++ [.transport (writtenResult n)])

/-- **The postconditions of a signature's normal return**, at arity `n`. -/
def Effect.normalPosts (e : Effect) (n : Nat) : List Formula :=
  (if e.fresh then [.operation (.freshStore 0)] else []) ++
  (if e.freshObject then [.operation (.freshObject 0)] else []) ++
  (match e.elements with
    | some R => [.operation (.elementsWhen 0 .tru 1 R)]
    | none => []) ++
  e.ensures.map (fun F => .operation (.fact .after 0 F)) ++
  (if e.receiverGrows then
    [.transition [(.field 0 arrayStoreKey, .any)], .operation (.storeExtends 0),
      .operation (.push 0 1 (actualWitnesses n))] else []) ++
  (match e.elementWrite with
    | some w => w.posts n
    | none => [])

/-- **The exit summary of a signature** at arity `n`: the normal exit's frame
and postconditions, and the exceptional exit's, `⊤` without `onThrow`. -/
def Effect.summary (e : Effect) (n : Nat) : Exits ExitSpec :=
  ⟨⟨e.frame, e.normalPosts n⟩, if e.onThrow then ⟨e.frame, []⟩ else ⟨topEffect, []⟩⟩

/-! ## Each postcondition states its field -/

section Equivalence
variable {arena : AssertionArena} {r : Tm} {args : List Tm} {v : Tm} {m : Nat} {s s' : IndexedHeap}

private theorem forall_ite {P : Formula → Prop} {c : Bool} {l : List Formula} :
    (∀ F ∈ (if c then l else []), P F) ↔ (c = true → ∀ F ∈ l, P F) := by
  cases c <;> simp

private theorem frame_iff {Φ : Footprint} (hadm : Admissible s s') :
    EffectAction Φ (callEnv r args) s s' ↔ Post Φ (callEnv r args) s.h s'.h :=
  ⟨fun h => h.2, fun h => ⟨hadm, h⟩⟩

private theorem fact_after_iff (F : IndexFact) :
    Parity.Holds arena (callState r args v m s s') (.operation (.fact .after 0 F)) ↔
      F.HoldsAt ⟨callEnv r args, s.h⟩ (ensuresEnv v r args) s'.h := Iff.rfl

private theorem fact_before_iff (F : IndexFact) :
    Parity.Holds arena (callState r args v m s s') (.operation (.fact .before 0 F)) ↔
      F.HoldsAt ⟨callEnv r args, s.h⟩ (callEnv r args) s.h := Iff.rfl

/-- **The receiver's growth is its frame and the store's extension.** -/
theorem receiverGrows_iff (hadm : Admissible s s') :
    (Parity.Holds arena (callState r args v m s s') (.transition [(.field 0 arrayStoreKey, .any)]) ∧
      Parity.Holds arena (callState r args v m s s') (.operation (.storeExtends 0))) ↔
      ReceiverGrows r s.h s'.h := by
  simp only [Parity.Holds, OperationPost.Holds, callState, EffectAction, TolerantFrames.Action]
  have h0 : callEnv r args 0 = r := rfl
  rw [h0]
  constructor
  · rintro ⟨⟨-, -, hp⟩, hx⟩ l u hu
    obtain ⟨u', hu', ha⟩ := hp l u hu
    rcases ha with rfl | ⟨e, he, hm, -⟩
    · exact .inl hu'
    · simp only [List.mem_singleton] at he
      subst he
      have hst : storeOf r = some l := by
        simpa [Region.mem, h0, storeOf] using hm
      rcases hx l u hst hu with hk | ⟨ls, ls', rfl, hls', hpre, hlen⟩
      · exact .inl hk
      · exact .inr ⟨hst, ls, ls', rfl, hls', hpre, hlen⟩
  · intro hg
    refine ⟨⟨hadm, hadm.length_le, fun l u hu => ?_⟩, fun st u hst hu => ?_⟩
    · rcases hg l u hu with hk | ⟨hst, ls, ls', rfl, hls', -⟩
      · exact ⟨u, hk, .inl rfl⟩
      · refine ⟨_, hls', .inr ⟨_, List.mem_singleton_self _, ?_, trivial⟩⟩
        simpa [Region.mem, h0, storeOf] using hst
    · rcases hg st u hu with hk | ⟨-, ls, ls', rfl, hls', hpre, hlen⟩
      · exact .inl hk
      · exact .inr ⟨ls, ls', rfl, hls', hpre, hlen⟩

private theorem actualWitnesses_values (r : Tm) (args : List Tm) (h : Heap) :
    (actualWitnesses args.length).mapM (·.value (callEnv r args) h) = some args := by
  unfold actualWitnesses
  suffices H : ∀ (k : Nat) (rest : List Tm), args.drop k = rest →
      ((List.range' k rest.length).map fun i => Witness.path ⟨i + 1, []⟩).mapM
        (·.value (callEnv r args) h) = some rest by
    have := H 0 args (by simp)
    simpa [List.range_eq_range'] using this
  intro k rest
  induction rest generalizing k with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro hd
    have ha : args.getD k .undef = a := by
      have : args[k]? = some a := by
        rw [← List.head?_drop, hd]; rfl
      simp [List.getD_eq_getElem?_getD, this]
    have hrest : args.drop (k + 1) = rest := by
      rw [← List.drop_drop, hd]; rfl
    simp only [List.length_cons, List.range'_succ, List.map_cons, List.mapM_cons]
    rw [ih (k + 1) hrest]
    simp only [Witness.value, Path.read, HeapKnowledge.readPath, callEnv, Nat.add_one_ne_zero, if_false,
      Nat.add_sub_cancel, ha]
    rfl

/-- **The append is the operational post of an append of the actuals**, at
actuals that are values. -/
theorem receiverAppends_iff (hvals : ∀ a ∈ args, isVal a = true) :
    Parity.Holds arena (callState r args v m s s') (.operation (.push 0 1 (actualWitnesses args.length))) ↔
      ReceiverAppends r args s.h s'.h := by
  simp only [Parity.Holds, OperationPost.Holds, callState]
  rw [actualWitnesses_values r args s.h]
  constructor
  · rintro ⟨vs, hvs, -, ha, -⟩
    cases hvs
    exact ha
  · intro ha
    exact ⟨args, rfl, hvals, ha, rfl⟩

private theorem writeAt_args (g : ViewFormat) (before after : Heap) :
    WriteAt g [callEnv r args 1, callEnv r args 2, callEnv r args 3] before after ↔
      WriteAt g args before after := Iff.rfl

/-- The transport `writtenResult` states that the result is the third
actual. -/
theorem writtenResult_iff (n : Nat) :
    Parity.Holds arena (callState r args v m s s') (.transport (writtenResult n)) ↔ v = args.getD 2 .undef := by
  have himg : ∀ i w, (writtenResult n).image i = some w →
      w = Witness.path ⟨if i = 3 then 0 else i + 1, []⟩ ∧ i < max (n + 1) 4 := by
    intro i w hi
    rw [Substitution.image_of_unboxed rfl] at hi
    simp only [writtenResult, List.getElem?_toArray, List.getElem?_map] at hi
    by_cases hlt : i < max (n + 1) 4
    · rw [List.getElem?_range hlt] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      exact ⟨hi.symm, hlt⟩
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at hi
      cases hi
  have hholds : (writtenResult n).Holds (callEnv r args) (ensuresEnv v r args) s'.h ↔
      v = args.getD 2 .undef := by
    constructor
    · intro hθ
      have h3 : (writtenResult n).image 3 = some (.path ⟨0, []⟩) := by
        rw [Substitution.image_of_unboxed rfl]
        simp only [writtenResult, List.getElem?_toArray, List.getElem?_map]
        rw [List.getElem?_range (by omega)]
        rfl
      have := hθ 3 _ h3
      simp [Witness.value, Path.read, HeapKnowledge.readPath, ensuresEnv, callEnv] at this
      rw [List.getD_eq_getElem?_getD]; exact this
    · intro hv i w hi
      obtain ⟨rfl, -⟩ := himg i w hi
      by_cases h3 : i = 3
      · subst h3
        simp [Witness.value, Path.read, HeapKnowledge.readPath, ensuresEnv, callEnv, hv]
      · simp only [h3, if_false, Witness.value, Path.read, HeapKnowledge.readPath, ensuresEnv,
          Nat.add_one_ne_zero, Nat.add_sub_cancel]
  simp only [Parity.Holds, callState, Substitution.HoldsAt]
  constructor
  · exact fun h => hholds.mp h.1
  · intro hv
    have hθ := hholds.mpr hv
    exact ⟨hθ, fun s'' _ => hθ.box rfl s''.h⟩

/-- **An exact write's precondition facts are `ExactPre`.** -/
theorem exactPre_iff (k : ElementKind) (h : Heap) :
    (∀ F ∈ k.preFacts, F.HoldsAt ⟨callEnv r args, h⟩ (callEnv r args) h) ↔ ExactPre k args := by
  constructor
  · intro hf
    have hq : (({ Effect.ordinary with pre := k.preFacts } : Effect)).Requires r args h :=
      ⟨fun R hR => by simp [Effect.ordinary, Effect.ofFootprint] at hR, hf⟩
    exact ElementKind.exactPre_of_requires (e := { Effect.ordinary with pre := k.preFacts })
      (fun F hF => hF) hq
  · rintro ⟨⟨x, j, hx, hsx, hr⟩, b, i, N, hb, hsi, hN, hlt⟩ F hF
    have h1 : callEnv r args 1 = args.getD 0 .undef := rfl
    have h2 : callEnv r args 2 = args.getD 1 .undef := rfl
    have h3 : callEnv r args 3 = args.getD 2 .undef := rfl
    have hiv : intValue (callEnv r args 2) = some (i : Int) := by
      rw [h2, hb]; exact SafeIntegers.safeIntOfBits_complete hsi
    have hxv : intValue (callEnv r args 3) = some j := by
      rw [h3, hx]; exact SafeIntegers.safeIntOfBits_complete hsx
    have hNv : termValue ⟨callEnv r args, h⟩ (callEnv r args) h (.now .view 1 []) = some N := by
      rw [termValue_nil, h1]; simpa [kindValue] using hN
    simp only [ElementKind.preFacts, List.mem_cons] at hF
    rcases hF with rfl | rfl | rfl | rfl | hF
    · simp [IndexFact.HoldsAt, hiv]
    · refine ⟨fun t ht => ?_, ?_⟩
      · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_singleton] at ht
        subst ht; simp [hiv]
      · simp [Linear.Fact.Holds, Linear.Form.eval, termValuation, hiv]
    · refine ⟨fun t ht => ?_, ?_⟩
      · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · simp [hiv]
        · rw [hNv]; rfl
      · simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, hiv, hNv,
          Option.getD_some]
        omega
    · simp [IndexFact.HoldsAt, hxv]
    · cases hk : k.range with
      | none => rw [hk] at hF; cases hF
      | some p =>
        obtain ⟨lo, hi⟩ := p
        have hb' := hr lo hi hk
        rw [hk] at hF
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
        rcases hF with rfl | rfl
        · refine ⟨fun t ht => ?_, ?_⟩
          · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_singleton] at ht
            subst ht; simp [hxv]
          · simp [Linear.Fact.Holds, Linear.Form.eval, termValuation, hxv]; omega
        · refine ⟨fun t ht => ?_, ?_⟩
          · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_singleton] at ht
            subst ht; simp [hxv]
          · simp [Linear.Fact.Holds, Linear.Form.eval, termValuation, hxv]; omega

/-- **A typed array's element write is its postconditions**, on admissible
transitions: the frame of the view write (`Kinds.ViewWrite.frame_iff`) and,
by its form, View-Write, the precondition's facts and the result. -/
theorem elementWrite_iff (w : ElementWrite) :
    (∀ F ∈ w.posts args.length, Parity.Holds arena (callState r args v m s s') F) ↔
      w.Holds args s.h s'.h ∧ Kinds.ViewWriteOf w args s.W s.h s'.W s'.h ∧ (w ≠ .stores → v = args.getD 2 .undef) := by
  have hview : Parity.Holds arena (callState r args v m s s') (.transition [(.cls .views, .grow)]) ↔
      Kinds.ViewWrite s.W s.h s'.W s'.h := by
    rw [Kinds.ViewWrite.frame_iff s.ok (callEnv r args)]
    exact ⟨fun h => ⟨h.1, s'.ok, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hwrite : ∀ f, Parity.Holds arena (callState r args v m s s') (.operation (.viewWrite 1 2 3 f)) ↔
      ∀ g, writeFormats (args.getD 0 .undef) f g → WriteAt g args s.h s'.h := fun _ => Iff.rfl
  cases w with
  | stores =>
    simp only [ElementWrite.posts, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    rw [hview]
    constructor
    · intro hw
      refine ⟨⟨hw.changes s.ok _, ?_, ?_⟩, ⟨hw, ?_, ?_⟩, fun h => absurd rfl h⟩ <;> intros <;>
        contradiction
    · rintro ⟨-, ⟨hw, -⟩, -⟩
      exact hw
  | assign =>
    simp only [ElementWrite.posts, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    rw [hview, hwrite, writtenResult_iff]
    have hassign : (∀ g, writeFormats (args.getD 0 .undef) none g → WriteAt g args s.h s'.h) ↔
        ViewAssign args s.h s'.h := Iff.rfl
    rw [hassign]
    constructor
    · rintro ⟨hw, ha, hr⟩
      refine ⟨⟨hw.changes s.ok _, ?_, fun _ => ha⟩, ⟨hw, ?_, fun _ => ha⟩, fun _ => hr⟩ <;> intros <;>
        contradiction
    · rintro ⟨-, ⟨hw, -, ha⟩, hr⟩
      exact ⟨hw, ha rfl, hr (fun h => by cases h)⟩
  | exact k =>
    simp only [ElementWrite.posts, List.forall_mem_cons, List.forall_mem_append, List.forall_mem_map,
      List.not_mem_nil, false_implies, implies_true, and_true]
    rw [hview, hwrite, writtenResult_iff]
    simp only [fact_before_iff]
    rw [exactPre_iff]
    have hexact : (∀ g, writeFormats (args.getD 0 .undef) (some k.format) g → WriteAt g args s.h s'.h) ↔
        ExactWrite k args s.h s'.h :=
      ⟨fun h => h _ rfl, fun h g hg => by cases hg; exact h⟩
    rw [hexact]
    constructor
    · rintro ⟨hw, hx, hp, hr⟩
      have hk : ∀ k', ElementWrite.exact k = .exact k' → ExactWrite k' args s.h s'.h ∧ ExactPre k' args :=
        fun k' h => by cases h; exact ⟨hx, hp⟩
      refine ⟨⟨hw.changes s.ok _, hk, ?_⟩, ⟨hw, hk, ?_⟩, fun _ => hr⟩ <;> intros <;> contradiction
    · rintro ⟨-, ⟨hw, hk, -⟩, hr⟩
      exact ⟨hw, (hk k rfl).1, (hk k rfl).2, hr (fun h => by cases h)⟩

/-- **The normal exit of a signature's summary is its normal-return
postcondition** (`Effect.postW`), on admissible transitions at actuals that
are values. -/
theorem Effect.summary_normal_iff (e : Effect) (hadm : Admissible s s') (hvals : ∀ a ∈ args, isVal a = true) :
    (e.summary args.length).normal.Holds arena (callState r args v m s s') ↔
      e.postW r args s.W s.h s'.n s'.W s'.h v := by
  simp only [Effect.summary, ExitSpec.Holds, Effect.normalPosts, List.forall_mem_append]
  have hfr : EffectAction e.frame (callState r args v m s s').beforeEnv (callState r args v m s s').before
      (callState r args v m s s').after ↔ e.within r args s.h s'.h := frame_iff hadm
  rw [hfr]
  simp only [Effect.postW, Effect.post, Effect.viewPost]
  -- each field and its postconditions
  have hfresh : (∀ F ∈ (if e.fresh then [Formula.operation (.freshStore 0)] else []),
      Parity.Holds arena (callState r args v m s s') F) ↔ (e.fresh = true → FreshAt s.h.length v) := by
    rw [forall_ite]; simp only [List.mem_singleton, forall_eq]; rfl
  have hobj : (∀ F ∈ (if e.freshObject then [Formula.operation (.freshObject 0)] else []),
      Parity.Holds arena (callState r args v m s s') F) ↔ (e.freshObject = true → FreshObjectAt s.h.length v) := by
    rw [forall_ite]; simp only [List.mem_singleton, forall_eq]; rfl
  have hel : (∀ F ∈ (match e.elements with
      | some R => [Formula.operation (.elementsWhen 0 .tru 1 R)]
      | none => []), Parity.Holds arena (callState r args v m s s') F) ↔
      (∀ R, e.elements = some R → v = .tru → ElemsAt R r s'.h) := by
    cases e.elements with
    | none => simp
    | some R =>
      simp only [List.mem_singleton, forall_eq, Option.some.injEq, forall_eq']
      rfl
  have hens : (∀ F ∈ e.ensures.map (fun F => Formula.operation (.fact .after 0 F)),
      Parity.Holds arena (callState r args v m s s') F) ↔
      (∀ F ∈ e.ensures, F.HoldsAt ⟨callEnv r args, s.h⟩ (ensuresEnv v r args) s'.h) := by
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl
  have hgrow : (∀ F ∈ (if e.receiverGrows then [Formula.transition [(.field 0 arrayStoreKey, .any)],
      .operation (.storeExtends 0), .operation (.push 0 1 (actualWitnesses args.length))] else []),
      Parity.Holds arena (callState r args v m s s') F) ↔
      (e.receiverGrows = true → ReceiverGrows r s.h s'.h ∧ ReceiverAppends r args s.h s'.h) := by
    rw [forall_ite]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [← receiverGrows_iff (arena := arena) (args := args) (v := v) (m := m) hadm,
      ← receiverAppends_iff (arena := arena) (v := v) (m := m) hvals]
    simp only [and_assoc]
  have hwr : (∀ F ∈ (match e.elementWrite with
      | some w => w.posts args.length
      | none => []), Parity.Holds arena (callState r args v m s s') F) ↔
      ((∀ w, e.elementWrite = some w → w.Holds args s.h s'.h) ∧
        ∀ w, e.elementWrite = some w → Kinds.ViewWriteOf w args s.W s.h s'.W s'.h ∧
          (w ≠ .stores → v = args.getD 2 .undef)) := by
    cases e.elementWrite with
    | none => simp
    | some w =>
      simp only [Option.some.injEq, forall_eq']
      rw [elementWrite_iff w]
  rw [hfresh, hobj, hel, hens, hgrow, hwr]
  constructor
  · rintro ⟨hw, ⟨⟨⟨⟨⟨hf, ho⟩, hl⟩, he⟩, hg⟩, hx, hv⟩⟩
    exact ⟨⟨hw, hf, ho, hl, he, hg, hx⟩, hv⟩
  · rintro ⟨⟨hw, hf, ho, hl, he, hg, hx⟩, hv⟩
    exact ⟨hw, ⟨⟨⟨⟨⟨hf, ho⟩, hl⟩, he⟩, hg⟩, hx, hv⟩⟩

/-- **The exceptional exit of a signature's summary is its throw
postcondition** (`Effect.excPost`), on admissible transitions: the frame
where it states `onThrow`, and `⊤` otherwise, which every admissible
transition meets. -/
theorem Effect.summary_exceptional_iff (e : Effect) (n : Nat) (hadm : Admissible s s') :
    (e.summary n).exceptional.Holds arena (callState r args v m s s') ↔ e.excPost r args s.h s'.h := by
  simp only [Effect.summary, Effect.excPost]
  cases ho : e.onThrow
  · simp only [Bool.false_eq_true, if_false, ExitSpec.Holds, List.not_mem_nil, false_imp_iff,
      implies_true, and_true, iff_true]
    exact EffectAction.top hadm
  · simp only [if_true, ExitSpec.Holds, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      forall_const]
    exact frame_iff hadm

/-- **The normal exit implies the heap postcondition** (`Effect.post`). -/
theorem Effect.summary_normal_post (e : Effect) (hadm : Admissible s s') (hvals : ∀ a ∈ args, isVal a = true)
    (h : (e.summary args.length).normal.Holds arena (callState r args v m s s')) :
    e.post r args s.h s'.h v :=
  ((e.summary_normal_iff hadm hvals).mp h).1

/-- **Without an element write the normal exit is the heap postcondition.** -/
theorem Effect.summary_normal_iff_post (e : Effect) (hx : e.elementWrite = none) (hadm : Admissible s s')
    (hvals : ∀ a ∈ args, isVal a = true) :
    (e.summary args.length).normal.Holds arena (callState r args v m s s') ↔ e.post r args s.h s'.h v :=
  (e.summary_normal_iff hadm hvals).trans ⟨fun h => h.1, Effect.postW_of_post hx⟩

/-! ## The operations on signatures -/

/-- **The meet's normal exit is both signatures' normal exits**: conjoining
two guarantees of one call (`Effect.meet`) conjoins their elaborations. -/
theorem Effect.summary_meet_normal {a b : Effect} (hs : a.sameResult b = true) (hadm : Admissible s s')
    (hvals : ∀ a ∈ args, isVal a = true) :
    ((a.meet b).summary args.length).normal.Holds arena (callState r args v m s s') ↔
      (a.summary args.length).normal.Holds arena (callState r args v m s s') ∧
        (b.summary args.length).normal.Holds arena (callState r args v m s s') := by
  rw [Effect.summary_normal_iff _ hadm hvals, Effect.summary_normal_iff _ hadm hvals,
    Effect.summary_normal_iff _ hadm hvals, Effect.postW_meet hs]
  have hbw : b.elementWrite = a.elementWrite := by
    simp only [Effect.sameResult, Bool.and_eq_true, beq_iff_eq] at hs; exact hs.1.2.symm
  have hview : b.viewPost args s.W s.h s'.n s'.W s'.h v ↔ a.viewPost args s.W s.h s'.n s'.W s'.h v := by
    simp only [Effect.viewPost, hbw]
  simp only [Effect.postW, hview]
  exact ⟨fun ⟨⟨ha, hw⟩, hb⟩ => ⟨⟨ha, hw⟩, hb, hw⟩, fun ⟨⟨ha, hw⟩, hb, _⟩ => ⟨⟨ha, hw⟩, hb⟩⟩

/-- **Both signatures' exceptional exits give the meet's.** -/
theorem Effect.summary_meet_exceptional {a b : Effect} (hs : a.sameResult b = true) (n : Nat)
    (hadm : Admissible s s')
    (ha : (a.summary n).exceptional.Holds arena (callState r args v m s s'))
    (hb : (b.summary n).exceptional.Holds arena (callState r args v m s s')) :
    ((a.meet b).summary n).exceptional.Holds arena (callState r args v m s s') :=
  (Effect.summary_exceptional_iff _ n hadm).mpr (Effect.excPost_meet hs r args s.h s'.h
    ((Effect.summary_exceptional_iff _ n hadm).mp ha) ((Effect.summary_exceptional_iff _ n hadm).mp hb))

/-- **Binding substitutes the saved actuals** (`Effect.drop`): the target's
normal exit at the call it forwards to, with receiver `rv` and actuals
`argsv`, gives the bound signature's at its own call. -/
theorem Effect.summary_drop_normal {e : Effect} (k : Nat) {rv : Tm} {argsv : List Tm}
    (hadm : Admissible s s') (hvalsv : ∀ a ∈ argsv, isVal a = true) (hvals : ∀ a ∈ args, isVal a = true)
    (h : (e.summary argsv.length).normal.Holds arena (callState rv argsv v m s s')) :
    ((e.drop k).summary args.length).normal.Holds arena (callState r args v m s s') := by
  obtain ⟨hp, hw⟩ := (Effect.summary_normal_iff _ hadm hvalsv).mp h
  refine (Effect.summary_normal_iff _ hadm hvals).mpr ⟨Effect.post_drop k hp, fun w hw' => ?_⟩
  simp only [Effect.drop, Option.map_eq_some_iff] at hw'
  obtain ⟨w0, h0, rfl⟩ := hw'
  refine ⟨⟨(hw w0 h0).1.1, fun _ h => ?_, fun h => ?_⟩, fun h => absurd rfl h⟩ <;> cases h

/-- **Binding keeps the exceptional exit.** -/
theorem Effect.summary_drop_exceptional {e : Effect} (k n n' : Nat) {rv : Tm} {argsv : List Tm} {v' : Tm}
    (hadm : Admissible s s') (h : (e.summary n).exceptional.Holds arena (callState rv argsv v' m s s')) :
    ((e.drop k).summary n').exceptional.Holds arena (callState r args v m s s') :=
  (Effect.summary_exceptional_iff _ n' hadm).mpr
    (Effect.excPost_drop k ((Effect.summary_exceptional_iff _ n hadm).mp h))

end Equivalence

/-! ## Scope and the operations on signatures -/

/-- **A module function's summary reads its own positions**: where its
effect is about the receiver and its first `n` parameters
(`Effect.belowRow`), its frames read call positions up to `n` and its
postconditions the entry positions up to `n` and the exit positions up to
`n + 1`. -/
theorem Effect.summary_scoped {e : Effect} {n : Nat} (h : e.belowRow n = true) (k : Nat)
    (arena : AssertionArena) :
    effectScoped (n + 1) (e.summary k).normal.frame = true ∧
      (e.summary k).normal.ensures.all (Formula.scoped arena ⟨n + 1, n + 2⟩) = true ∧
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
    · cases e.fresh <;> simp [Formula.scoped, OperationPost.scoped]
    · cases e.freshObject <;> simp [Formula.scoped, OperationPost.scoped]
    · cases e.elements <;> simp [Formula.scoped, OperationPost.scoped]
    · refine List.all_eq_true.mpr fun F hF => ?_
      obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
      simp only [Formula.scoped, OperationPost.scoped, Scope.count, Nat.add_zero, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq]
      exact ⟨fun i hi => decide_eq_true (by have := Effect.belowRow_ensures h G hG i hi; omega),
        fun i hi => by have := Effect.belowRow_ensures_entry h G hG i hi; omega⟩
  · simp only [Effect.summary]
    split
    · exact hframe
    · exact htop
  · simp only [Effect.summary]
    split <;> rfl

end Verification.CallEffects
