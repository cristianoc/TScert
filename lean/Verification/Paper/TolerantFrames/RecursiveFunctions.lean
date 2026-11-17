import Verification.Paper.TolerantFrames.CallableEntrySpecification

/-! # Recursive body-premise discharge by actual invocation length

The hypothesis for a body proof supplies the concrete callable's specification
only at strictly smaller shared reduction counts. The bounded body judgments
retain their original entry budget. This is a rule schema: each body must
construct the relative premise using proved command/primitive rules. It neither
assumes an unrestricted self triple nor establishes callable type membership.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints TolerantFrames HeapObservations

/-- Freeze symbolic function entry in the initial body assertion. This is a
ghost parameter, not an added restriction on calls satisfying P. -/
def FunctionEntryPre (P : Assertion) (ρ : Env) (s : IndexedHeap) : Assertion :=
  fun ρ' m t => ρ' = ρ ∧ m = s.h.length ∧ t = s ∧ P ρ' m t

namespace Compiler.Callable

def NormalInvocationPost (Q : TwoState.Post) (η : TwoState.LogicalEnv) (y : Nat) (Φ : Footprint)
    (ρ : Env) (s : IndexedHeap) (n : Nat) (h' : Heap) (v : Val) : Prop :=
  ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧
    ValidContext (bindName ρ y v) s.h.length t ∧ isSourceVal v = true ∧ RefsOk t.W v ∧
    ResultPost Q η y v ρ ρ s.h.length s t ∧ Footprints.Post Φ ρ s.h h'

def ExceptionalInvocationPost (Qe : TwoState.Post) (η : TwoState.LogicalEnv) (Φe : Footprint)
    (ρ : Env) (s : IndexedHeap) (n : Nat) (h' : Heap) (v : Val) : Prop :=
  ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧
    ValidContext ρ s.h.length t ∧ isSourceVal v = true ∧ RefsOk t.W v ∧
    Qe.meaning η ρ ρ s.h.length s t ∧ Footprints.Post Φe ρ s.h h'

/-- Partial correctness of this concrete invocation at exactly n shared
reductions, both value and raise exits. Entry validity is explicit. -/
def InvocationSpecAt {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) (P : Assertion) (Q Qe : TwoState.Post)
    (η : TwoState.LogicalEnv) (y : Nat) (Φ Φe : Footprint) (n : Nat) : Prop :=
  ∀ receiver args (s : IndexedHeap), isVal receiver = true → CallArguments.Values args →
    CallArguments.Values caps →
    ValidContext (layout.env receiver args (function c layout fields identity)) s.h.length s →
    P (layout.env receiver args (function c layout fields identity)) s.h.length s →
    (∀ h' v, Steps n s.h (invocation c layout fields identity receiver args) h' v →
      isVal v = true → n < s.n →
      NormalInvocationPost Q η y Φ (layout.env receiver args (function c layout fields identity)) s n h' v) ∧
    (∀ h' term v, Steps n s.h (invocation c layout fields identity receiver args) h' term →
      Raises term v → n < s.n →
      ExceptionalInvocationPost Qe η Φe (layout.env receiver args (function c layout fields identity)) s n h' v)

/-- The actual Fun recursion argument for represented fixed-arity code.
The relative body premise must be proved; it is not a supplied sound-callable
summary. Its only recursive hypotheses have smaller concrete invocation counts. -/
theorem recursive_invocation_specification {arity} {caps : List Tm} (c : Command)
    (layout : Layout arity caps.length) (fields : List (PropKey × Nat)) (identity : Nat)
    {Γ Δ y P Φ Φe} (Q Qe : TwoState.Post) (η : TwoState.LogicalEnv)
    (scope : c.WellScoped Γ Δ)
    (normalScope : Q.Scoped Γ (fun x => x = y ∨ Γ x) 0 0)
    (exceptionalScope : Qe.Scoped Γ Γ 0 0)
    (body : ∀ N,
      (∀ k, k < N → InvocationSpecAt c layout fields identity P Q Qe η y Φ Φe k) →
      ∀ receiver args (s : IndexedHeap),
      let ρ := layout.env receiver args (function c layout fields identity)
      TripleBelow N layout.host (FunctionEntryPre P ρ s) c
        (ResultPost Q η y .undef) (Qe.meaning η) (fun _ _ _ _ _ => False)
        (FunctionReturn ρ s (ResultPost Q η y)) ∧
      EffectsBelow N layout.host (FunctionEntryPre P ρ s) c Φ Φe) :
    ∀ n, InvocationSpecAt c layout fields identity P Q Qe η y Φ Φe n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro receiver args s hr ha hc valid pre
    obtain ⟨triple, effects⟩ := body n ih receiver args s
    have entryPre : FunctionEntryPre P (layout.env receiver args (function c layout fields identity)) s
        (layout.env receiver args (function c layout fields identity)) s.h.length s := ⟨rfl, rfl, rfl, pre⟩
    constructor
    · intro h' v run value budget
      exact invocation_value_specification_below c layout fields identity receiver args s Q Qe η scope
        normalScope exceptionalScope triple effects valid entryPre hr ha hc run value budget (Nat.le_refl n)
    · intro h' term v run raised budget
      exact invocation_raise_specification_below c layout fields identity receiver args s Q Qe η scope
        normalScope exceptionalScope triple effects valid entryPre hr ha hc run raised budget (Nat.le_refl n)

end Compiler.Callable
end Verification.Paper.TolerantFrames
