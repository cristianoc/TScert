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

A signature's effect (`Effect`) states its exits as a schema
(`Effect.schema`), the same for every arity (the note's Call); at a call of
`n` actuals it is its summary (`Effect.summary`, `Exits.atArity`). A
guarantee stated beside the frame, such as the receiver's growth `{receiver
spine: any}` or a typed array's element write `{all-views: grow}`, is a
postcondition `.transition Φ`, conjoined with the frame: the two hold of one
transition. This module holds the readers of postconditions by their
formulas, the meaning of the formulas the library's contracts state
(`receiverGrows_iff`, `receiverAppends_iff`, `exactPre_iff`), and the
builders of the effects code states. -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge TolerantFrames Parity

/-- The call positions of the first `n` actuals, as witnesses read at the
entry. -/
def actualWitnesses (n : Nat) : List Witness := (List.range n).map fun i => .path ⟨i + 1, []⟩

/-- **The summary of a signature** at a call of `n` actuals: its schema
instantiated there (`Exits.atArity`). -/
def Effect.summary (e : Effect) (n : Nat) : Exits ExitSpec := e.schema.atArity n

/-! ## Schemas of the library's contracts

The append names the actuals from position `1` on, and the written result is
the transport `writtenResultSchema`, entry slot `3` read at exit slot `0` and
every other entry slot `i` at exit slot `i + 1`. -/

/-- The written result, over every entry slot. -/
def writtenResultSchema : TransportSchema := ⟨1, [(3, .path ⟨0, []⟩)], false, []⟩

/-- **A typed array's element write as schema postconditions**: its frame
`{all-views: grow}` (`Kinds.ViewWrite.frame_iff`), and for an element
assignment View-Write at the typed array's format and the result the value
written, for the exact form View-Write at the element type's format, the
facts its precondition gives and the result. -/
def ElementWrite.schemaPosts : ElementWrite → List FormulaSchema
  | .spines => [.transition [(.cls .views, .grow)]]
  | .assign => [.transition [(.cls .views, .grow)], .operation (.viewWrite 1 2 3 none), .transport writtenResultSchema]
  | .exact k => .transition [(.cls .views, .grow)] :: .operation (.viewWrite 1 2 3 (some k.format)) ::
      ((k.preFacts.map fun F => .operation (.fact .before 0 F)) ++ [.transport writtenResultSchema])

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

/-! ## The formulas of the library's contracts -/

section Equivalence
variable {arena : AssertionArena} {r : Tm} {args : List Tm} {v : Tm} {m : Nat} {s s' : IndexedHeap}

/-- **The receiver's growth is its frame and the spine's extension.** -/
theorem receiverGrows_iff (hadm : Admissible s s') :
    (Parity.Holds arena (callState r args v m s s') (.transition [(.field 0 arraySpineKey, .any)]) ∧
      Parity.Holds arena (callState r args v m s s') (.operation (.spineExtends 0))) ↔
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
      have hst : spineOf r = some l := by
        simpa [Region.mem, h0, spineOf] using hm
      rcases hx l u hst hu with hk | ⟨ls, ls', rfl, hls', hpre, hlen⟩
      · exact .inl hk
      · exact .inr ⟨hst, ls, ls', rfl, hls', hpre, hlen⟩
  · intro hg
    refine ⟨⟨hadm, hadm.length_le, fun l u hu => ?_⟩, fun st u hst hu => ?_⟩
    · rcases hg l u hu with hk | ⟨hst, ls, ls', rfl, hls', -⟩
      · exact ⟨u, hk, .inl rfl⟩
      · refine ⟨_, hls', .inr ⟨_, List.mem_singleton_self _, ?_, trivial⟩⟩
        simpa [Region.mem, h0, spineOf] using hst
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
    simp only [Witness.value, Path.read, HeapKnowledge.readPath, callEnv, Nat.add_one_ne_zero, ite_false,
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

end Equivalence

/-! ## Readings of a schema

Readers of an exit schema that the front's proposals and the pass use. -/

/-- **The fields a frame's path regions read through one field**: for each
entry whose region is reached from a call position through the one field
`f` (`.path _ [f] _`), the field `f`. -/
def _root_.Verification.Footprints.Footprint.regionFields (Φ : Footprint) : List String :=
  Φ.filterMap fun e => match e.1 with
    | .path _ [f] _ => some f
    | _ => none

/-- **Whether an exit states a fresh result**: its postcondition that the
result's spine is allocated during the call (`freshSpine 0`). -/
def ExitSchema.freshResult (q : ExitSchema) : Bool := decide (FormulaF.operation (.freshSpine 0) ∈ q.ensures)

/-- **Whether an exit states a fresh result object**: its postcondition that
every own location of the result was allocated during the call
(`freshObject 0`). -/
def ExitSchema.freshObjectResult (q : ExitSchema) : Bool := decide (FormulaF.operation (.freshObject 0) ∈ q.ensures)

/-- The element predicate of a postcondition `elementsWhen 0 true 1 R`. -/
def elementsWhenTrueOf : FormulaSchema → Option ElemPred
  | .operation (.elementsWhen 0 .tru 1 R) => some R
  | _ => none

/-- The index fact of a postcondition `fact after 0 F`. -/
def factAfterOf : FormulaSchema → Option IndexFact
  | .operation (.fact .after 0 F) => some F
  | _ => none

/-- **The element predicates an exit states of the receiver where the
result is `true`**: each postcondition `elementsWhen 0 true 1 R`. -/
def ExitSchema.elementsWhenTrue (q : ExitSchema) : List ElemPred := q.ensures.filterMap elementsWhenTrueOf

/-- **The index facts an exit states at its exit**: each postcondition
`fact after 0 F`, the fact `F` read at the result (position `0`) and the
call's positions one higher, in the heap the exit leaves. -/
def ExitSchema.facts (q : ExitSchema) : List IndexFact := q.ensures.filterMap factAfterOf

theorem ExitSchema.mem_elementsWhenTrue {q : ExitSchema} {R : ElemPred} :
    R ∈ q.elementsWhenTrue ↔ FormulaF.operation (.elementsWhen 0 .tru 1 R) ∈ q.ensures := by
  simp only [ExitSchema.elementsWhenTrue, List.mem_filterMap]
  constructor
  · rintro ⟨F, hF, hR⟩
    unfold elementsWhenTrueOf at hR
    split at hR
    · cases hR; exact hF
    · cases hR
  · exact fun h => ⟨_, h, rfl⟩

theorem ExitSchema.mem_facts {q : ExitSchema} {F : IndexFact} :
    F ∈ q.facts ↔ FormulaF.operation (.fact .after 0 F) ∈ q.ensures := by
  simp only [ExitSchema.facts, List.mem_filterMap]
  constructor
  · rintro ⟨G, hG, hF⟩
    unfold factAfterOf at hF
    split at hF
    · cases hF; exact hG
    · cases hF
  · exact fun h => ⟨_, h, rfl⟩

/-! ## Builders of effects by their exits

Each builder states an effect by what it states of its two exits. -/

/-- **The exits of a closed frame** `c`: the normal exit within `c` with no
postcondition, the exceptional exit within `c` where `bounded`, `⊤`
otherwise. -/
def Exits.ofClosed (c : Footprints.Closed) (bounded : Bool) : Exits ExitSchema :=
  ⟨⟨c.fp, []⟩, if bounded then ⟨c.fp, []⟩ else ⟨topEffect, []⟩⟩

/-- **An effect of a closed frame** (`Exits.ofClosed`), with no promise and
no precondition. -/
def Effect.ofClosed (c : Footprints.Closed) (bounded : Bool) : Effect := ⟨Exits.ofClosed c bounded, none, none, []⟩

theorem Effect.ofClosed_frame (c : Footprints.Closed) (bounded : Bool) : (Effect.ofClosed c bounded).frame = c.fp := rfl

theorem Effect.ofClosed_schema (c : Footprints.Closed) (bounded : Bool) :
    (Effect.ofClosed c bounded).schema = Exits.ofClosed c bounded := rfl

/-- **The exits a declaration states**: on a normal return the closed frame
`c` and the spine regions `regions` at `any`, a fresh result where `fresh`
and the index facts `ensures` of the result and the call's positions; on a
throw the same frame where `bounded`, `⊤` otherwise. -/
def Exits.ofStated (c : Footprints.Closed) (bounded fresh : Bool) («ensures» : List HeapKnowledge.IndexFact)
    (regions : List Footprints.ArgumentSpineRegion) : Exits ExitSchema :=
  let frame := c.fp ++ regions.map regionEntry
  ⟨⟨frame, (if fresh then [.operation (.freshSpine 0)] else []) ++
      ensures.map fun F => .operation (.fact .after 0 F)⟩,
    if bounded then ⟨frame, []⟩ else ⟨topEffect, []⟩⟩

/-- **An effect a declaration states** (`Exits.ofStated`), with its promise
and its precondition `pre`. -/
def Effect.ofStated (c : Footprints.Closed) (promise : Option TypePromise) (bounded fresh : Bool)
    (pre «ensures» : List HeapKnowledge.IndexFact) (regions : List Footprints.ArgumentSpineRegion) : Effect :=
  ⟨Exits.ofStated c bounded fresh ensures regions, promise, none, pre⟩

/-- **A frame with its class entries those of `c`**: `c`'s class entries,
and the frame's entries over other regions. -/
def replaceClasses (c : Footprints.Closed) (Φ : Footprints.Footprint) : Footprints.Footprint :=
  c.fp ++ Φ.nonClasses

/-- **The exits of a specification with its class entries those of `c` and
its throws bounded**: the normal exit's frame with `c`'s class entries
(`replaceClasses`) and its postconditions, and the exceptional exit within
that frame, with no postcondition. -/
def Exits.withClasses (c : Footprints.Closed) (x : Exits ExitSchema) : Exits ExitSchema :=
  ⟨⟨replaceClasses c x.normal.frame, x.normal.ensures⟩, ⟨replaceClasses c x.normal.frame, []⟩⟩

/-- **An effect with its class entries those of `c` and its throws bounded**
(`Exits.withClasses`), its promise and preconditions `e`'s. -/
def Effect.withClasses (c : Footprints.Closed) (e : Effect) : Effect := { e with exits := Exits.withClasses c e.exits }

/-- **An effect whose throws are unbounded**: `e`'s normal exit, `⊤` on a
throw. -/
def Effect.throwUnbounded (e : Effect) : Effect := { e with exits := ⟨e.exits.normal, ⟨topEffect, []⟩⟩ }

end Verification.CallEffects
