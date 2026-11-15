import Verification.Semantics.FormulaScopes

/-! # Forgetting what a specification states of the actuals

A call whose evaluated actuals are not known where its guarantee is
consumed (a spread of unknown length) concludes, by the rule of consequence
after the guarantee at the evaluated actuals (the note's Call), what the
specification states independently of them, on both exits
(`Exits.forgetActuals_sound`): each frame kept where it reads the receiver
alone and widened to `⊤` otherwise, and the postconditions that read no
actual, the receiver at the entry and the result and the receiver at the
exit (`FormulaF.readsNoActual`: no append of a rest sequence, no transport,
the instantiation scoped there); the others are dropped. -/
namespace Verification.Parity
open Verification Footprints CallEffects TolerantFrames

/-- Whether an operational post's appended sequence is a list of fixed
witnesses. -/
def OperationPostF.fixedSeq : OperationPostF WitnessSeq → Bool
  | .push _ _ (.fixed _) => true
  | .push _ _ _ => false
  | _ => true

/-- Whether a schema formula reads no rest sequence and no transport: its
instantiation is the same at every call. -/
def FormulaF.fixedSeqs : FormulaSchema → Bool
  | .operation q => q.fixedSeq
  | .transport _ => false
  | .and F G => F.fixedSeqs && G.fixedSeqs
  | _ => true

/-- The scope of the receiver: entry slot `0`, and exit slots `0` (the
result or the thrown value) and `1`. -/
def receiverScope : Scope := ⟨1, 2⟩

/-- **A postcondition reading no actual**: its instantiation the same at
every call (`FormulaF.fixedSeqs`) and scoped at the receiver
(`receiverScope`). -/
def FormulaF.readsNoActual (F : FormulaSchema) : Bool :=
  F.fixedSeqs && (instantiateFormula ⟨0, 1, Nat.le_refl _⟩ F).scoped AssertionArena.empty receiverScope

end Verification.Parity

namespace Verification.CallEffects
open Verification Footprints Parity TolerantFrames

theorem instantiateFormula_fixedSeqs {F : FormulaSchema} (hF : F.fixedSeqs = true) (ι ι' : CallInstantiation) :
    instantiateFormula ι F = instantiateFormula ι' F := by
  unfold instantiateFormula
  induction F with
  | operation q =>
    cases q with
    | push x x' args => cases args <;> first | rfl | cases hF
    | _ => rfl
  | transport _ => cases hF
  | and F G ihF ihG =>
    simp only [FormulaF.fixedSeqs, Bool.and_eq_true] at hF
    simp only [FormulaF.map, ihF hF.1, ihG hF.2]
  | _ => rfl

/-- **An exit with what it states of the actuals forgotten**: its frame where
it reads the receiver alone, `⊤` otherwise, and its postconditions reading no
actual. -/
def ExitSchema.forgetActuals (q : ExitSchema) : ExitSchema :=
  ⟨if effectScoped 1 q.frame then q.frame else topEffect, q.ensures.filter FormulaF.readsNoActual⟩

/-- **A specification with what it states of the actuals forgotten**, on
both exits. -/
def Exits.forgetActuals (x : Exits ExitSchema) : Exits ExitSchema := x.map ExitSchema.forgetActuals

/-- Two calls with one receiver agree on the receiver, the result and the
states. -/
theorem callState_agree (r : Tm) (args other : List Tm) (v : Tm) (m : Nat) (s s' : IndexedHeap) :
    (callState r args v m s s').AgreeBelow receiverScope (callState r other v m s s') where
  beforeEnv i hi := by
    have : i = 0 := by simp only [receiverScope] at hi; omega
    subst this; rfl
  afterEnv i hi := by
    simp only [receiverScope] at hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl
  mark := rfl
  before := rfl
  after := rfl

/-- **Forgetting the actuals of an exit is consequence**: the exit at one
call's actuals gives the forgotten exit at any other's, the receiver, the
result and the states the same. -/
theorem ExitSchema.forgetActuals_holds {q : ExitSchema} {ι ι' : CallInstantiation} {r : Tm}
    {args other : List Tm} {v : Tm} {m : Nat} {s s' : IndexedHeap}
    (h : (q.instantiate ι).Holds AssertionArena.empty (callState r args v m s s')) :
    (q.forgetActuals.instantiate ι').Holds AssertionArena.empty (callState r other v m s s') := by
  obtain ⟨hfr, hens⟩ := h
  refine ⟨?_, ?_⟩
  · show EffectAction (if effectScoped 1 q.frame then q.frame else topEffect) (callEnv r other) s s'
    by_cases hsc : effectScoped 1 q.frame = true
    · rw [if_pos hsc]
      refine (EffectAction.congr_roots fun x ⟨e, he, hx⟩ => ?_).mpr hfr
      have hx0 : x < 1 := by
        simp only [effectScoped, List.all_eq_true, decide_eq_true_eq] at hsc
        exact hsc e he x hx
      have : x = 0 := by omega
      subst this; rfl
    · rw [if_neg hsc]
      exact EffectAction.top hfr.1
  · intro F hF
    simp only [ExitSchema.instantiate, ExitSchema.forgetActuals, List.mem_map, List.mem_filter] at hF
    obtain ⟨G, ⟨hG, hno⟩, rfl⟩ := hF
    simp only [FormulaF.readsNoActual, Bool.and_eq_true] at hno
    have h1 := hens _ (List.mem_map_of_mem hG)
    rw [instantiateFormula_fixedSeqs hno.1 ι ⟨0, 1, Nat.le_refl _⟩] at h1
    rw [instantiateFormula_fixedSeqs hno.1 ι' ⟨0, 1, Nat.le_refl _⟩]
    exact (FormulaF.holds_scoped_congr (callState_agree r args other v m s s') hno.2).mpr h1

/-- **Forgetting the actuals is consequence on both exits** (the note's
Call, then consequence): a completion's guarantee at the evaluated actuals
gives the forgotten specification's at any actuals. -/
theorem Exits.forgetActuals_sound {x : Exits ExitSchema} {c : Completion} {r : Tm} {args other : List Tm}
    {s s' : IndexedHeap} {v : Tm} (hp : x.exitPost c r args s s' v) :
    x.forgetActuals.exitPost c r other s s' v := by
  unfold Exits.exitPost Exits.atArity at *
  cases c <;> exact ExitSchema.forgetActuals_holds hp

/-! ## The signature the forgotten specification entails

What the deciders read of a call whose specification is forgotten at its
actuals, as a signature: what the forgotten specification entails
(`Effect.withoutActuals_entails`). -/

/-- **A signature without what it states of the actuals**: its frame through
its coarse bound, without store regions (`Effect.footprint`), no index fact,
no growth of the receiver, a typed array's element write as the views'
growth. -/
def Effect.withoutActuals (e : Effect) : Effect :=
  { e with ensures := [], elementWrite := (e.elementWrite.map fun _ => .stores), closed := e.footprint, regions := [], receiverGrows := false }

/-- A frame without store regions reads the receiver alone. -/
theorem Effect.frame_scoped_of_regions {e : Effect} (h : e.regions = []) : effectScoped 1 e.frame = true := by
  simp only [Effect.frame, h, List.map_nil, List.append_nil, Effect.receiverEntries, effectScoped, List.all_append,
    Footprints.Closed.fp]
  split
  · simp [regionRoots]
  · split <;> simp [regionRoots]

/-- **The frame without the actuals is the forgotten frame's consequence.** -/
theorem Effect.withoutActuals_frame (e : Effect) {η : Env} {s s' : IndexedHeap}
    (h : EffectAction (if effectScoped 1 e.frame then e.frame else topEffect) η s s') :
    EffectAction e.withoutActuals.frame η s s' := by
  by_cases hreg : e.regions = []
  · rw [if_pos (Effect.frame_scoped_of_regions hreg)] at h
    have hfr : e.withoutActuals.frame = e.frame := by
      simp only [Effect.withoutActuals, Effect.frame, Effect.receiverEntries, Effect.footprint_of_regions hreg, hreg]
    rw [hfr]
    exact h
  · have hfp : e.footprint = .top := by simp [Effect.footprint, List.isEmpty_iff, hreg]
    refine EffectAction.mono_entries (Φ := topEffect) (fun x hx l hl => ⟨x, ?_, hl, ?_⟩) (EffectAction.top h.1)
    · simp only [Effect.withoutActuals, Effect.frame, hfp]
      exact List.mem_append_left _ (List.mem_append_left _ hx)
    · cases x.2 <;> rfl

/-- Each postcondition of the signature without the actuals is one of the
signature's, reading no actual. -/
theorem Effect.withoutActuals_normal (e : Effect) {G : FormulaSchema} (hG : G ∈ e.withoutActuals.normalSchema) :
    G ∈ e.normalSchema ∧ G.readsNoActual = true := by
  simp only [Effect.withoutActuals, Effect.normalSchema, List.map_nil, List.append_nil, Bool.false_eq_true,
    if_false, List.mem_append] at hG
  simp only [Effect.normalSchema, List.mem_append]
  rcases hG with ((hG | hG) | hG) | hG
  · refine ⟨.inl (.inl (.inl (.inl (.inl hG)))), ?_⟩
    cases hf : e.fresh <;> simp only [hf, if_true, Bool.false_eq_true, if_false, List.mem_singleton,
      List.not_mem_nil] at hG
    subst hG; rfl
  · refine ⟨.inl (.inl (.inl (.inl (.inr hG)))), ?_⟩
    cases hf : e.freshObject <;> simp only [hf, if_true, Bool.false_eq_true, if_false, List.mem_singleton,
      List.not_mem_nil] at hG
    subst hG; rfl
  · refine ⟨.inl (.inl (.inl (.inr hG))), ?_⟩
    cases hR : e.elements <;> simp only [hR, List.mem_singleton, List.not_mem_nil] at hG
    subst hG; rfl
  · cases hw : e.elementWrite with
    | none => simp [hw] at hG
    | some w =>
      simp only [hw, Option.map_some, ElementWrite.schemaPosts, List.mem_singleton] at hG
      subst hG
      refine ⟨.inr ?_, rfl⟩
      cases w <;> simp [ElementWrite.schemaPosts]

/-- **The signature without the actuals is a consequence of the forgotten
specification**, on both exits. -/
theorem Effect.withoutActuals_entails (e : Effect) {c : Completion} {r : Tm} {args : List Tm}
    {s s' : IndexedHeap} {v : Tm} (h : e.schema.forgetActuals.exitPost c r args s s' v) :
    e.withoutActuals.schema.exitPost c r args s s' v := by
  cases c
  · obtain ⟨hfr, hens⟩ := h
    refine ⟨Effect.withoutActuals_frame e hfr, ?_⟩
    intro F hF
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
    obtain ⟨hGe, hno⟩ := Effect.withoutActuals_normal e hG
    have hfix : G.fixedSeqs = true := by
      simp only [FormulaF.readsNoActual, Bool.and_eq_true] at hno
      exact hno.1
    have := hens _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hGe, hno⟩))
    rwa [instantiateFormula_fixedSeqs hfix _ (e.withoutActuals.schema.callInstantiation args.length)] at this
  · obtain ⟨hfr, -⟩ := h
    refine ⟨?_, fun F hF => ?_⟩
    · cases ho : e.onThrow
      · simp only [Exits.atArity, Exits.map, Exits.get, Exits.forgetActuals, ExitSchema.instantiate,
          ExitSchema.forgetActuals, Effect.schema, ho, Bool.false_eq_true, if_false] at hfr ⊢
        have ho' : e.withoutActuals.onThrow = false := ho
        simp only [ho', Bool.false_eq_true, if_false]
        split at hfr <;> exact hfr
      · simp only [Exits.atArity, Exits.map, Exits.get, Exits.forgetActuals, ExitSchema.instantiate,
          ExitSchema.forgetActuals, Effect.schema, ho, if_true] at hfr ⊢
        have ho' : e.withoutActuals.onThrow = true := ho
        rw [if_pos ho']
        exact Effect.withoutActuals_frame e hfr
    · simp only [Exits.atArity, Exits.map, Exits.get, ExitSchema.instantiate, Effect.schema] at hF
      split at hF <;> simp at hF

end Verification.CallEffects
