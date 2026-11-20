import Verification.Semantics.FormulaScopes
import Verification.Semantics.ExitSummaries

/-! # Forgetting what a specification states of the actuals

A call whose evaluated actuals are not known where its guarantee is
consumed (a spread of unknown length) concludes, by the rule of consequence
after the guarantee at the evaluated actuals (the note's Call), what the
specification states independently of them, on both exits.

**Independence of the actuals** is semantic: a frame is independent where
its action at one call's entry environment is its action at any other
actuals, the receiver and the states the same (`FrameActualsIndependent`);
a postcondition is where its instantiation at one call holding gives its
instantiation at any other actuals, the receiver, the completion's value,
the mark and the states the same (`FormulaActualsIndependent`). **The rule
of consequence across actuals** (`ExitSchema.consequence`) gives one exit
schema at one call's actuals from another at another's, from the action
inclusion of the frames and the implication of the postconditions; a frame
is widened only by action inclusion (`ActionIncluded`).

`Exits.forgetActuals` is one instance (`Exits.forgetActuals_sound`), its
choices decided by sufficient checks: each frame kept where it reads the
receiver alone (`effectScoped`, sufficient by
`frameActualsIndependent_of_scoped`) and widened to `⊤` otherwise
(`actionIncluded_top`), and the postconditions whose instantiation is the
same at every arity and which read the receiver at the entry and the result
and the receiver at the exit alone (`FormulaF.readsNoActual`, sufficient by
`FormulaF.readsNoActual_independent`); the others are dropped. A sequence
is the same at every arity where each of its parts is fixed
(`WitnessSeq.arityFree`, through `append`); a transport's instantiation
ranges over the call's entry scope, every actual in it
(`CallInstantiation.containsActuals`), so the check keeps none. -/
namespace Verification.Parity
open Verification Footprints CallEffects TolerantFrames

/-- Whether a sequence of a call's values is the same at every arity: each
of its parts fixed witnesses. -/
def WitnessSeq.arityFree : WitnessSeq → Bool
  | .fixed _ => true
  | .restFrom _ => false
  | .append a b => a.arityFree && b.arityFree

theorem WitnessSeq.instantiate_arityFree {a : WitnessSeq} (ha : a.arityFree = true) (n n' : Nat) :
    a.instantiate n = a.instantiate n' := by
  induction a with
  | fixed _ => rfl
  | restFrom _ => cases ha
  | append a b iha ihb =>
    simp only [WitnessSeq.arityFree, Bool.and_eq_true] at ha
    simp only [WitnessSeq.instantiate, iha ha.1, ihb ha.2]

/-- Whether an operational post's appended sequence is the same at every
arity. -/
def OperationPostF.fixedSeq : OperationPostF WitnessSeq → Bool
  | .push _ _ a => a.arityFree
  | _ => true

/-- Whether a schema formula's instantiation is the same at every call: its
sequences the same at every arity, and no transport (a transport ranges
over the call's entry scope). -/
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

/-! ## Independence of the actuals and consequence -/

/-- **A frame independent of the actuals**: its action at a call's entry
environment is its action at any other actuals, the receiver and the states
the same. -/
def FrameActualsIndependent (Φ : Footprint) : Prop :=
  ∀ (r : Tm) (args other : List Tm) (s s' : IndexedHeap),
    EffectAction Φ (callEnv r args) s s' → EffectAction Φ (callEnv r other) s s'

/-- **Action inclusion**: every action of `Φ` is one of `Φ'`, at every
environment (the note's effect order, read by its actions). -/
def ActionIncluded (Φ Φ' : Footprint) : Prop :=
  ∀ (η : Env) (s s' : IndexedHeap), EffectAction Φ η s s' → EffectAction Φ' η s s'

/-- **A postcondition independent of the actuals**: its instantiation at a
call holding gives its instantiation at any other actuals, each at an
instantiation of its own number of actuals, the receiver, the completion's
value, the mark and the states the same. -/
def FormulaActualsIndependent (F : FormulaSchema) : Prop :=
  ∀ (ι ι' : CallInstantiation) (r : Tm) (args other : List Tm) (v : Tm) (m : Nat) (s s' : IndexedHeap),
    ι.actualCount = args.length → ι'.actualCount = other.length →
    Holds AssertionArena.empty (callState r args v m s s') (instantiateFormula ι F) →
      Holds AssertionArena.empty (callState r other v m s s') (instantiateFormula ι' F)

/-- **The rule of consequence across actuals** for an exit schema: the
action of one frame at a call's actuals an action of the other's at other
actuals, and each postcondition of the other implied by the first's at
those calls, the first schema at the first call gives the second at the
second. -/
theorem ExitSchema.consequence {q q' : ExitSchema} {ι ι' : CallInstantiation} {r : Tm} {args other : List Tm}
    {v : Tm} {m : Nat} {s s' : IndexedHeap}
    (hframe : EffectAction q.frame (callEnv r args) s s' → EffectAction q'.frame (callEnv r other) s s')
    (hens : ∀ G ∈ q'.ensures, (∀ F ∈ q.ensures, Holds AssertionArena.empty (callState r args v m s s')
      (instantiateFormula ι F)) → Holds AssertionArena.empty (callState r other v m s s') (instantiateFormula ι' G))
    (h : (q.instantiate ι).Holds AssertionArena.empty (callState r args v m s s')) :
    (q'.instantiate ι').Holds AssertionArena.empty (callState r other v m s s') := by
  refine ⟨hframe h.1, ?_⟩
  simp only [ExitSchema.instantiate, List.forall_mem_map]
  exact fun G hG => hens G hG fun F hF => h.2 _ (List.mem_map_of_mem hF)

/-- A frame widened by action inclusion to one independent of the actuals
is a frame premise of the rule of consequence. -/
theorem ActionIncluded.independent {Φ Φ' : Footprint} (hinc : ActionIncluded Φ Φ')
    (hΦ' : FrameActualsIndependent Φ') {r : Tm} {args other : List Tm} {s s' : IndexedHeap}
    (h : EffectAction Φ (callEnv r args) s s') : EffectAction Φ' (callEnv r other) s s' :=
  hΦ' r args other s s' (hinc _ _ _ h)

/-- Every action is one of `⊤`, at every environment. -/
theorem actionIncluded_top (Φ : Footprint) : ActionIncluded Φ topEffect :=
  fun _ _ _ h => EffectAction.top h.1

/-- An action of `⊤` reads no environment. -/
theorem frameActualsIndependent_top : FrameActualsIndependent topEffect :=
  fun _ _ _ _ _ h => EffectAction.top h.1

/-- **A frame reading the receiver alone is independent of the actuals.** -/
theorem frameActualsIndependent_of_scoped {Φ : Footprint} (hsc : effectScoped 1 Φ = true) :
    FrameActualsIndependent Φ := by
  intro r args other s s' h
  refine (EffectAction.congr_roots fun x ⟨e, he, hx⟩ => ?_).mpr h
  have hx0 : x < 1 := by
    simp only [effectScoped, List.all_eq_true, decide_eq_true_eq] at hsc
    exact hsc e he x hx
  have : x = 0 := by omega
  subst this; rfl

theorem instantiateFormula_fixedSeqs {F : FormulaSchema} (hF : F.fixedSeqs = true) (ι ι' : CallInstantiation) :
    instantiateFormula ι F = instantiateFormula ι' F := by
  unfold instantiateFormula
  induction F with
  | operation q =>
    cases q with
    | push x x' a =>
      simp only [FormulaF.map, OperationPostF.map, FormulaF.fixedSeqs, OperationPostF.fixedSeq] at hF ⊢
      rw [WitnessSeq.instantiate_arityFree hF ι.actualCount ι'.actualCount]
    | _ => rfl
  | transport _ => cases hF
  | and F G ihF ihG =>
    simp only [FormulaF.fixedSeqs, Bool.and_eq_true] at hF
    simp only [FormulaF.map, ihF hF.1, ihG hF.2]
  | _ => rfl

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

/-- **A postcondition reading no actual is independent of the actuals.** -/
theorem FormulaF.readsNoActual_independent {F : FormulaSchema} (hno : F.readsNoActual = true) :
    FormulaActualsIndependent F := by
  intro ι ι' r args other v m s s' _ _ h1
  simp only [FormulaF.readsNoActual, Bool.and_eq_true] at hno
  rw [instantiateFormula_fixedSeqs hno.1 ι ⟨0, 1, Nat.le_refl _⟩] at h1
  rw [instantiateFormula_fixedSeqs hno.1 ι' ⟨0, 1, Nat.le_refl _⟩]
  exact (FormulaF.holds_scoped_congr (callState_agree r args other v m s s') hno.2).mpr h1

/-! ## Forgetting, an instance of consequence -/

/-- **An exit with what it states of the actuals forgotten**: its frame where
it reads the receiver alone, `⊤` otherwise, and its postconditions reading no
actual. -/
def ExitSchema.forgetActuals (q : ExitSchema) : ExitSchema :=
  ⟨if effectScoped 1 q.frame then q.frame else topEffect, q.ensures.filter FormulaF.readsNoActual⟩

/-- **A specification with what it states of the actuals forgotten**, on
both exits. -/
def Exits.forgetActuals (x : Exits ExitSchema) : Exits ExitSchema := x.map ExitSchema.forgetActuals

/-- The forgotten frame is independent of the actuals and includes the
frame's actions. -/
theorem ExitSchema.forgetActuals_frame (q : ExitSchema) :
    FrameActualsIndependent q.forgetActuals.frame ∧ ActionIncluded q.frame q.forgetActuals.frame := by
  show FrameActualsIndependent (if effectScoped 1 q.frame then q.frame else topEffect) ∧
    ActionIncluded q.frame (if effectScoped 1 q.frame then q.frame else topEffect)
  by_cases hsc : effectScoped 1 q.frame = true
  · rw [ite_eq_left hsc]
    exact ⟨frameActualsIndependent_of_scoped hsc, fun _ _ _ h => h⟩
  · rw [ite_eq_right hsc]
    exact ⟨frameActualsIndependent_top, actionIncluded_top _⟩

/-- **Forgetting the actuals of an exit is consequence**
(`ExitSchema.consequence`): the exit at one call's actuals gives the
forgotten exit at any other's, the receiver, the result and the states the
same. -/
theorem ExitSchema.forgetActuals_holds {q : ExitSchema} {ι ι' : CallInstantiation} {r : Tm}
    {args other : List Tm} {v : Tm} {m : Nat} {s s' : IndexedHeap} (hι : ι.actualCount = args.length)
    (hι' : ι'.actualCount = other.length)
    (h : (q.instantiate ι).Holds AssertionArena.empty (callState r args v m s s')) :
    (q.forgetActuals.instantiate ι').Holds AssertionArena.empty (callState r other v m s s') := by
  obtain ⟨hind, hinc⟩ := q.forgetActuals_frame
  refine ExitSchema.consequence (hinc.independent hind) (fun G hG hall => ?_) h
  obtain ⟨hGq, hno⟩ := List.mem_filter.mp hG
  exact FormulaF.readsNoActual_independent hno ι ι' r args other v m s s' hι hι' (hall G hGq)

/-- **Forgetting the actuals is consequence on both exits** (the note's
Call, then consequence): a completion's guarantee at the evaluated actuals
gives the forgotten specification's at any actuals. -/
theorem Exits.forgetActuals_sound {x : Exits ExitSchema} {c : Completion} {r : Tm} {args other : List Tm}
    {s s' : IndexedHeap} {v : Tm} (hp : x.exitPost c r args s s' v) :
    x.forgetActuals.exitPost c r other s s' v := by
  unfold Exits.exitPost Exits.atArity at *
  cases c <;> exact ExitSchema.forgetActuals_holds rfl rfl hp

/-! ## The signature without what it states of the actuals -/

/-- **A signature without what it states of the actuals**: its exits with
the actuals forgotten (`Exits.forgetActuals`, consequence of its exits at
any actuals by `Exits.forgetActuals_sound`), its promise and preconditions
its own. -/
def Effect.withoutActuals (e : Effect) : Effect := { e with exits := e.exits.forgetActuals }

end Verification.CallEffects
