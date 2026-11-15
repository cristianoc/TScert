import Verification.Semantics.EffectSignatures

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

/-! ## The elaboration as a schema

The same guarantee stated once for every arity (the note's Call): the
append names the actuals from position `1` on, and the written result is the
transport `writtenResultSchema`, entry slot `3` read at exit slot `0` and every
other entry slot `i` at exit slot `i + 1`. -/

/-- The written result, over every entry slot. -/
def writtenResultSchema : TransportSchema := ⟨1, [(3, .path ⟨0, []⟩)], false, []⟩

/-- A typed array's element write as schema postconditions. -/
def ElementWrite.schemaPosts : ElementWrite → List FormulaSchema
  | .stores => [.transition [(.cls .views, .grow)]]
  | .assign => [.transition [(.cls .views, .grow)], .operation (.viewWrite 1 2 3 none), .transport writtenResultSchema]
  | .exact k => .transition [(.cls .views, .grow)] :: .operation (.viewWrite 1 2 3 (some k.format)) ::
      ((k.preFacts.map fun F => .operation (.fact .before 0 F)) ++ [.transport writtenResultSchema])

/-- The postconditions of a signature's normal return, as a schema. -/
def Effect.normalSchema (e : Effect) : List FormulaSchema :=
  (if e.fresh then [.operation (.freshStore 0)] else []) ++
  (if e.freshObject then [.operation (.freshObject 0)] else []) ++
  (match e.elements with
    | some R => [.operation (.elementsWhen 0 .tru 1 R)]
    | none => []) ++
  e.ensures.map (fun F => .operation (.fact .after 0 F)) ++
  (if e.receiverGrows then
    [.transition [(.field 0 arrayStoreKey, .any)], .operation (.storeExtends 0),
      .operation (.push 0 1 (.restFrom 1))] else []) ++
  (match e.elementWrite with
    | some w => w.schemaPosts
    | none => [])

/-- **A signature's specification schema**: the normal exit's frame and
postconditions, and the exceptional exit's, `⊤` without `onThrow`. -/
def Effect.schema (e : Effect) : Exits ExitSchema :=
  ⟨⟨e.frame, e.normalSchema⟩, if e.onThrow then ⟨e.frame, []⟩ else ⟨topEffect, []⟩⟩

private theorem foldr_slots_append (a b : List FormulaSchema) :
    (a ++ b).foldr (fun (F : FormulaSchema) k => max F.slots k) 0 =
      max (a.foldr (fun (F : FormulaSchema) k => max F.slots k) 0) (b.foldr (fun (F : FormulaSchema) k => max F.slots k) 0) := by
  induction a with
  | nil => simp
  | cons F t ih => simp only [List.cons_append, List.foldr_cons, ih, Nat.max_assoc]

/-- The actuals from position `1` at a call of `n` actuals are its actual
positions. -/
theorem restFrom_one (n : Nat) : (WitnessSeq.restFrom 1).instantiate n = actualWitnesses n := by
  simp only [WitnessSeq.instantiate, actualWitnesses]
  rw [List.filter_eq_self.mpr ?_, List.map_map]
  · rfl
  · intro i hi
    simp only [List.mem_map] at hi
    obtain ⟨j, -, rfl⟩ := hi
    simp

/-- The written result over an entry scope of `max (n + 1) 4` slots is
`writtenResult n`. -/
theorem writtenResultSchema_instantiate (n : Nat) :
    writtenResultSchema.instantiate (max (n + 1) 4) = writtenResult n := by
  simp only [TransportSchema.instantiate, writtenResultSchema, writtenResult]
  congr 2
  refine List.map_congr_left fun i _ => ?_
  by_cases h : i = 3
  · subst h; rfl
  · have h' : (i == 3) = false := by simp [h]
    simp [List.lookup, h', h]

private theorem write_slots (w : ElementWrite) :
    w.schemaPosts.foldr (fun (F : FormulaSchema) k => max F.slots k) 0 = if w = .stores then 0 else 4 := by
  have hf : ∀ l : List IndexFact, (l.map fun F => (FormulaF.operation (.fact .before 0 F) : FormulaSchema)).foldr
      (fun (F : FormulaSchema) k => max F.slots k) 0 = 0 := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, List.foldr_cons, ih]; rfl
  cases w with
  | stores => rfl
  | assign => rfl
  | exact k =>
    simp only [ElementWrite.schemaPosts, List.foldr_cons, foldr_slots_append, hf]
    rfl

/-- The entry slots a signature's schema names: `4` for an element
assignment or exact write, whose transport names entry slot `3`, else `0`. -/
theorem Effect.schema_slots (e : Effect) :
    e.schema.slots = match e.elementWrite with
      | some .stores | none => 0
      | some _ => 4 := by
  have hex : e.schema.exceptional.slots = 0 := by
    simp only [Effect.schema]; split <;> rfl
  have hens : (e.ensures.map fun F => (FormulaF.operation (.fact .after 0 F) : FormulaSchema)).foldr
      (fun (F : FormulaSchema) k => max F.slots k) 0 = 0 := by
    induction e.ensures with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, List.foldr_cons, ih]; rfl
  simp only [Exits.slots, hex, Nat.max_zero]
  simp only [Effect.schema, ExitSchema.slots, Effect.normalSchema, foldr_slots_append, hens]
  have h1 : (if e.fresh = true then [(FormulaF.operation (.freshStore 0) : FormulaSchema)] else []).foldr
      (fun (F : FormulaSchema) k => max F.slots k) 0 = 0 := by split <;> rfl
  have h2 : (if e.freshObject = true then [(FormulaF.operation (.freshObject 0) : FormulaSchema)] else []).foldr
      (fun (F : FormulaSchema) k => max F.slots k) 0 = 0 := by split <;> rfl
  have h3 : (match e.elements with
      | some R => [(FormulaF.operation (.elementsWhen 0 .tru 1 R) : FormulaSchema)]
      | none => []).foldr (fun (F : FormulaSchema) k => max F.slots k) 0 = 0 := by split <;> rfl
  have h4 : (if e.receiverGrows = true then [(FormulaF.transition [(.field 0 arrayStoreKey, .any)] : FormulaSchema),
      .operation (.storeExtends 0), .operation (.push 0 1 (.restFrom 1))] else []).foldr
      (fun (F : FormulaSchema) k => max F.slots k) 0 = 0 := by split <;> rfl
  rw [h1, h2, h3, h4]
  cases hw : e.elementWrite with
  | none => rfl
  | some w =>
    simp only [write_slots]
    cases w <;> simp

/-- **The schema at a call of `n` actuals is the summary at arity `n`.** -/
theorem Effect.schema_atArity (e : Effect) (n : Nat) : e.schema.atArity n = e.summary n := by
  have hι : (e.schema.callInstantiation n).actualCount = n := rfl
  have hslot : ∀ w, e.elementWrite = some w → w ≠ .stores → (e.schema.callInstantiation n).entrySlots = max (n + 1) 4 := by
    intro w hw hs
    show max (n + 1) e.schema.slots = _
    rw [Effect.schema_slots, hw]
    cases w with
    | stores => exact absurd rfl hs
    | assign => rfl
    | exact _ => rfl
  show e.schema.map (ExitSchema.instantiate (e.schema.callInstantiation n)) = _
  generalize e.schema.callInstantiation n = ι at hι hslot
  subst hι
  have hw : ∀ w, e.elementWrite = some w → w.schemaPosts.map (instantiateFormula ι) = w.posts ι.actualCount := by
    intro w hw'
    cases w with
    | stores => rfl
    | assign =>
      simp only [ElementWrite.schemaPosts, ElementWrite.posts, List.map_cons, List.map_nil, instantiateFormula,
        FormulaF.map, OperationPostF.map, hslot _ hw' (by intro h; cases h), writtenResultSchema_instantiate]
    | exact k =>
      simp only [ElementWrite.schemaPosts, ElementWrite.posts, List.map_cons, List.map_append, List.map_map,
        List.map_nil, instantiateFormula, FormulaF.map, OperationPostF.map,
        hslot _ hw' (by intro h; cases h), writtenResultSchema_instantiate]
      rfl
  simp only [Exits.map, ExitSchema.instantiate, Effect.schema, Effect.summary]
  congr 1
  · have p1 : (if e.fresh = true then [(FormulaF.operation (.freshStore 0) : FormulaSchema)] else []).map
        (instantiateFormula ι) = if e.fresh = true then [.operation (.freshStore 0)] else [] := by split <;> rfl
    have p2 : (if e.freshObject = true then [(FormulaF.operation (.freshObject 0) : FormulaSchema)] else []).map
        (instantiateFormula ι) = if e.freshObject = true then [.operation (.freshObject 0)] else [] := by
      split <;> rfl
    have p3 : (match e.elements with
        | some R => [(FormulaF.operation (.elementsWhen 0 .tru 1 R) : FormulaSchema)]
        | none => []).map (instantiateFormula ι) = (match e.elements with
        | some R => [.operation (.elementsWhen 0 .tru 1 R)]
        | none => []) := by split <;> rfl
    have p4 : (e.ensures.map fun F => (FormulaF.operation (.fact .after 0 F) : FormulaSchema)).map
        (instantiateFormula ι) = e.ensures.map fun F => .operation (.fact .after 0 F) := by
      rw [List.map_map]; rfl
    have p5 : (if e.receiverGrows = true then [(FormulaF.transition [(.field 0 arrayStoreKey, .any)] : FormulaSchema),
        .operation (.storeExtends 0), .operation (.push 0 1 (.restFrom 1))] else []).map (instantiateFormula ι) =
        if e.receiverGrows = true then [.transition [(.field 0 arrayStoreKey, .any)], .operation (.storeExtends 0),
          .operation (.push 0 1 (actualWitnesses ι.actualCount))] else [] := by
      split
      · simp only [List.map_cons, List.map_nil, instantiateFormula, FormulaF.map, OperationPostF.map, restFrom_one]
      · rfl
    have p6 : (match e.elementWrite with
        | some w => w.schemaPosts
        | none => []).map (instantiateFormula ι) = (match e.elementWrite with
        | some w => w.posts ι.actualCount
        | none => []) := by
      split
      · rename_i w heq; exact hw w heq
      · rfl
    simp only [Effect.normalSchema, Effect.normalPosts, List.map_append, p1, p2, p3, p4, p5, p6]
  · split <;> rfl

/-- **A signature's schema references no arena node**: the elaboration
states operational posts, index facts, transitions and transports alone. -/
theorem Effect.schema_arenaFree (e : Effect) : e.schema.arenaFree = true := by
  have hw : ∀ w : ElementWrite, w.schemaPosts.all (·.arenaFree) = true := by
    intro w; cases w with
    | stores => rfl
    | assign => rfl
    | exact k =>
      simp only [ElementWrite.schemaPosts, List.all_cons, List.all_append, List.all_map]
      simp [FormulaF.arenaFree, Function.comp_def]
  have hn : e.normalSchema.all (·.arenaFree) = true := by
    simp only [Effect.normalSchema, List.all_append, Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
    · simp [List.all_map, FormulaF.arenaFree, Function.comp_def]
    · split <;> rfl
    · split
      · exact hw _
      · rfl
  simp only [Exits.arenaFree, ExitSchema.arenaFree, Effect.schema, Bool.and_eq_true]
  exact ⟨hn, by split <;> rfl⟩

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
  simp only [Parity.Holds, OperationPostF.Holds, callState, EffectAction, TolerantFrames.Action]
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
  simp only [Parity.Holds, OperationPostF.Holds, callState]
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
postcondition** (`Effect.postW`), on admissible transitions, at actuals that
are values where the signature states an append of them. -/
theorem Effect.summary_normal_iff (e : Effect) (hadm : Admissible s s')
    (hvals : e.receiverGrows = true → ∀ a ∈ args, isVal a = true) :
    (e.summary args.length).normal.Holds arena (callState r args v m s s') ↔
      e.postW r args s.W s.h s'.n s'.W s'.h v := by
  simp only [Effect.summary, ExitSpec.Holds, Effect.normalPosts, List.forall_mem_append]
  have hfr : EffectAction e.frame (callState r args v m s s').beforeEnv (callState r args v m s s').before
      (callState r args v m s s').after ↔ e.within r args s.h s'.h := frame_iff hadm
  rw [hfr]
  simp only [Effect.postW, Effect.post, Effect.viewPost]
  -- each field and its postconditions
  have hfresh : (∀ F ∈ (if e.fresh then [FormulaF.operation (.freshStore 0)] else []),
      Parity.Holds arena (callState r args v m s s') F) ↔ (e.fresh = true → FreshAt s.h.length v) := by
    rw [forall_ite]; simp only [List.mem_singleton, forall_eq]; rfl
  have hobj : (∀ F ∈ (if e.freshObject then [FormulaF.operation (.freshObject 0)] else []),
      Parity.Holds arena (callState r args v m s s') F) ↔ (e.freshObject = true → FreshObjectAt s.h.length v) := by
    rw [forall_ite]; simp only [List.mem_singleton, forall_eq]; rfl
  have hel : (∀ F ∈ (match e.elements with
      | some R => [FormulaF.operation (.elementsWhen 0 .tru 1 R)]
      | none => []), Parity.Holds arena (callState r args v m s s') F) ↔
      (∀ R, e.elements = some R → v = .tru → ElemsAt R r s'.h) := by
    cases e.elements with
    | none => simp
    | some R =>
      simp only [List.mem_singleton, forall_eq, Option.some.injEq, forall_eq']
      rfl
  have hens : (∀ F ∈ e.ensures.map (fun F => FormulaF.operation (.fact .after 0 F)),
      Parity.Holds arena (callState r args v m s s') F) ↔
      (∀ F ∈ e.ensures, F.HoldsAt ⟨callEnv r args, s.h⟩ (ensuresEnv v r args) s'.h) := by
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl
  have hgrow : (∀ F ∈ (if e.receiverGrows then [FormulaF.transition [(.field 0 arrayStoreKey, .any)],
      .operation (.storeExtends 0), .operation (.push 0 1 (actualWitnesses args.length))] else []),
      Parity.Holds arena (callState r args v m s s') F) ↔
      (e.receiverGrows = true → ReceiverGrows r s.h s'.h ∧ ReceiverAppends r args s.h s'.h) := by
    rw [forall_ite]
    refine imp_congr_right fun hg => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [← receiverGrows_iff (arena := arena) (args := args) (v := v) (m := m) hadm,
      ← receiverAppends_iff (arena := arena) (v := v) (m := m) (hvals hg)]
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
  ((e.summary_normal_iff hadm fun _ => hvals).mp h).1

/-- **Without an element write the normal exit is the heap postcondition.** -/
theorem Effect.summary_normal_iff_post (e : Effect) (hx : e.elementWrite = none) (hadm : Admissible s s')
    (hvals : ∀ a ∈ args, isVal a = true) :
    (e.summary args.length).normal.Holds arena (callState r args v m s s') ↔ e.post r args s.h s'.h v :=
  (e.summary_normal_iff hadm fun _ => hvals).trans ⟨fun h => h.1, Effect.postW_of_post hx⟩

/-! ## The operations on signatures -/

/-- **The meet's normal exit is both signatures' normal exits**: conjoining
two guarantees of one call (`Effect.meet`) conjoins their elaborations. -/
theorem Effect.summary_meet_normal {a b : Effect} (hs : a.sameResult b = true) (hadm : Admissible s s')
    (hvals : ∀ a ∈ args, isVal a = true) :
    ((a.meet b).summary args.length).normal.Holds arena (callState r args v m s s') ↔
      (a.summary args.length).normal.Holds arena (callState r args v m s s') ∧
        (b.summary args.length).normal.Holds arena (callState r args v m s s') := by
  rw [Effect.summary_normal_iff _ hadm fun _ => hvals, Effect.summary_normal_iff _ hadm fun _ => hvals,
    Effect.summary_normal_iff _ hadm fun _ => hvals, Effect.postW_meet hs]
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
  obtain ⟨hp, hw⟩ := (Effect.summary_normal_iff _ hadm fun _ => hvalsv).mp h
  refine (Effect.summary_normal_iff _ hadm fun _ => hvals).mpr ⟨Effect.post_drop k hp, fun w hw' => ?_⟩
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

end Verification.CallEffects
