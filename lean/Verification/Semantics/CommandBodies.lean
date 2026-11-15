import Verification.Semantics.CommandSummaries
import Verification.Semantics.FormulaScopes

/-! # From a function body's summary to its signature

The function's inferred effect is its body's summary
(`docs/drafts/effects-of-commands.md`, "Command summaries and
composition": the body frame at the call positions, the exported
postconditions checked consequences in the interface scope). A body's runs
are presented at a call's positions (`Runs.AtCall`): its entry valuation is
the call's (`callEnv`: `0` the receiver, `i + 1` the `i`-th actual) and its
exit valuation the call's exit (`ensuresEnv`: `0` the returned or thrown
value, `i + 1` entry slot `i`), the two-state `callState` that a signature's
summary is read at (the note *Tolerant frames*, §6, Call).

A body summary within a signature's summary at each exit
(`ExitSpec.Weakens`, by checked frame inclusion and checked consequence)
states the signature's summary (`Effect.summary`) for every such run
(`CommandSummary.signature_holds`). A summary is a signature's at
arity `n` when its frames read the receiver and the first `n` parameters
and its postconditions the entry slots up to `n` and the exit slots up to
`n + 1` (`CommandSummary.Scoped`), as every module function's is at its
arity (`Effect.summary_scoped`).

A body's exit valuation may hold locals past the call's exit positions
(`Runs.AtCallBelow`: it agrees with `ensuresEnv` below `n + 2`). A scoped
signature summary holds alike at two two-states agreeing below its scope
(`CommandSummary.Scoped.holds_congr`, by `FormulaF.holds_scoped_congr`), so
the signature's summary of such a body is stated at `callState` too
(`CommandSummary.signature_holds_below`). -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge TolerantFrames Parity

/-! ## Scope and the operations on signatures -/

/-- **A body's runs at a call's positions**: the run from the call's entry
valuation completing by `c` with the value `v`, read at `callState`. -/
def Runs.AtCall (R : Runs) (r : Tm) (args : List Tm) (c : Completion) (v : Tm) (m : Nat) (s s' : IndexedHeap) :
    Prop :=
  R c (callState r args v m s s')

/-- **A summary in a signature's scope at arity `n`**: its frames read call
positions up to `n`, its postconditions entry slots up to `n` and exit
slots up to `n + 1`. -/
def CommandSummary.Scoped (arena : AssertionArena) (n : Nat) (S : CommandSummary) : Bool :=
  effectScoped (n + 1) S.normal.frame && S.normal.ensures.all (FormulaF.scoped arena ⟨n + 1, n + 2⟩) &&
    effectScoped (n + 1) S.exceptional.frame && S.exceptional.ensures.all (FormulaF.scoped arena ⟨n + 1, n + 2⟩)

/-- **A module function's signature summary at its arity is in its scope**
(`Effect.summary_scoped`). -/
theorem Effect.summary_scopedSummary {e : Effect} {n : Nat} (h : e.belowRow n = true) :
    CommandSummary.Scoped AssertionArena.empty n (e.summary n) = true := by
  obtain ⟨h₁, h₂⟩ := Effect.summary_scoped h .normal
  obtain ⟨h₃, h₄⟩ := Effect.summary_scoped h .exceptional
  simp only [CommandSummary.Scoped, Bool.and_eq_true]
  exact ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩

/-- **A scoped summary reads its scope alone**: at each exit it holds alike
at two two-states agreeing below its scope (`FormulaF.holds_scoped_congr`). -/
theorem CommandSummary.Scoped.holds_congr {arena : AssertionArena} {n : Nat} {S : CommandSummary}
    (hsc : S.Scoped arena n = true) (c : Completion) {s s' : TwoState} (hs : s.AgreeBelow ⟨n + 1, n + 2⟩ s') :
    (S.get c).Holds arena s' ↔ (S.get c).Holds arena s := by
  simp only [CommandSummary.Scoped, Bool.and_eq_true] at hsc
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := hsc
  cases c
  · exact ExitSpec.holds_scoped_congr h₁ h₂ hs
  · exact ExitSpec.holds_scoped_congr h₃ h₄ hs

/-- **A body's runs at a call's positions, its exit valuation holding
locals**: the run from the call's entry valuation completing by `c` at an
exit valuation agreeing with the call's exit (`ensuresEnv`) below `n + 2`,
the exit slots a signature at arity `n` reads. -/
def Runs.AtCallBelow (R : Runs) (n : Nat) (r : Tm) (args : List Tm) (c : Completion) (v : Tm) (m : Nat)
    (s s' : IndexedHeap) : Prop :=
  ∃ η', (∀ i < n + 2, η' i = ensuresEnv v r args i) ∧ R c ⟨callEnv r args, η', m, s, s'⟩

/-- A run at exactly the call's positions is one at every scope. -/
theorem Runs.AtCall.below {R : Runs} {r : Tm} {args : List Tm} {c : Completion} {v : Tm} {m : Nat}
    {s s' : IndexedHeap} (h : R.AtCall r args c v m s s') (n : Nat) : R.AtCallBelow n r args c v m s s' :=
  ⟨_, fun _ _ => rfl, h⟩

/-- **A body's summary gives its signature's at every call**: a body summary
sound from `P`, within the signature summary `Sig` at each exit, gives
`Sig` at every run presented at the call's positions from an entry meeting
`P`. -/
theorem CommandSummary.signature_holds {arena : AssertionArena} {P : Assertion} {R : Runs} {S Sig : CommandSummary}
    (hS : S.Sound arena P R) (hw : ∀ c, (S.get c).Weakens arena P (Sig.get c)) {r : Tm} {args : List Tm}
    {c : Completion} {v : Tm} {m : Nat} {s s' : IndexedHeap} (hP : P (callEnv r args) m s)
    (hr : R.AtCall r args c v m s s') : (Sig.get c).Holds arena (callState r args v m s s') :=
  hw c _ hP (hS c _ hP hr)

/-- **The inferred mutation effect is the body's frame**: at every return
and every throw from an entry meeting `P`, the transition is within the
body summary's frame at that exit, read at the call's positions. -/
theorem CommandSummary.frame_at_call {arena : AssertionArena} {P : Assertion} {R : Runs} {S : CommandSummary}
    (hS : S.Sound arena P R) {r : Tm} {args : List Tm} {c : Completion} {v : Tm} {m : Nat} {s s' : IndexedHeap}
    (hP : P (callEnv r args) m s) (hr : R.AtCall r args c v m s s') :
    EffectAction (S.get c).frame (callEnv r args) s s' :=
  (hS c (callState r args v m s s') hP hr).1

/-- **A body's summary gives its scoped signature's at every call whose
exit holds locals**: a body summary sound from `P`, within a signature
summary `Sig` scoped at `n` at each exit, gives `Sig` at `callState` for
every run from the call's entry whose exit valuation agrees with the call's
below `n + 2`. -/
theorem CommandSummary.signature_holds_below {arena : AssertionArena} {P : Assertion} {R : Runs}
    {S Sig : CommandSummary} {n : Nat} (hS : S.Sound arena P R) (hw : ∀ c, (S.get c).Weakens arena P (Sig.get c))
    (hsc : Sig.Scoped arena n = true) {r : Tm} {args : List Tm} {c : Completion} {v : Tm} {m : Nat}
    {s s' : IndexedHeap} (hP : P (callEnv r args) m s) (hr : R.AtCallBelow n r args c v m s s') :
    (Sig.get c).Holds arena (callState r args v m s s') := by
  obtain ⟨η', hη', hr⟩ := hr
  have h := hw c ⟨callEnv r args, η', m, s, s'⟩ hP (hS c _ hP hr)
  have hs : TwoState.AgreeBelow ⟨n + 1, n + 2⟩ ⟨callEnv r args, η', m, s, s'⟩ (callState r args v m s s') :=
    ⟨fun _ _ => rfl, fun i hi => (hη' i hi).symm, rfl, rfl, rfl⟩
  exact (CommandSummary.Scoped.holds_congr hsc c hs).mpr h

/-- **The inferred mutation effect is the body's frame at every call whose
exit holds locals**: the frame reads the entry valuation alone. -/
theorem CommandSummary.frame_at_call_below {arena : AssertionArena} {P : Assertion} {R : Runs}
    {S : CommandSummary} (hS : S.Sound arena P R) {n : Nat} {r : Tm} {args : List Tm} {c : Completion} {v : Tm}
    {m : Nat} {s s' : IndexedHeap} (hP : P (callEnv r args) m s) (hr : R.AtCallBelow n r args c v m s s') :
    EffectAction (S.get c).frame (callEnv r args) s s' := by
  obtain ⟨η', -, hr⟩ := hr
  exact (hS c ⟨callEnv r args, η', m, s, s'⟩ hP hr).1

end Verification.CallEffects
