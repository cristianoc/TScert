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

end Verification.CallEffects
