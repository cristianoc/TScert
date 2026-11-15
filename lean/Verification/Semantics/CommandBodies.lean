import Verification.Semantics.CommandSummaries

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
states the signature's contract for every such run
(`CommandSummary.signature_holds`), and with `Effect.summary` the
signature's normal and throw postconditions themselves
(`CommandSummary.signature_contract`). A summary is a signature's at
arity `n` when its frames read the receiver and the first `n` parameters
and its postconditions the entry slots up to `n` and the exit slots up to
`n + 1` (`CommandSummary.Scoped`), as every module function's is
(`Effect.summary_scoped`). -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge TolerantFrames Parity

/-- **A body's runs at a call's positions**: the run from the call's entry
valuation completing by `c` with the value `v`, read at `callState`. -/
def Runs.AtCall (R : Runs) (r : Tm) (args : List Tm) (c : Completion) (v : Tm) (m : Nat) (s s' : IndexedHeap) :
    Prop :=
  R c (callState r args v m s s')

/-- **A summary in a signature's scope at arity `n`**: its frames read call
positions up to `n`, its postconditions entry slots up to `n` and exit
slots up to `n + 1`. -/
def CommandSummary.Scoped (arena : AssertionArena) (n : Nat) (S : CommandSummary) : Bool :=
  effectScoped (n + 1) S.normal.frame && S.normal.ensures.all (Formula.scoped arena ⟨n + 1, n + 2⟩) &&
    effectScoped (n + 1) S.exceptional.frame && S.exceptional.ensures.all (Formula.scoped arena ⟨n + 1, n + 2⟩)

/-- **A module function's signature summary is in its scope**
(`Effect.summary_scoped`). -/
theorem Effect.summary_scopedSummary {e : Effect} {n : Nat} (h : e.belowRow n = true) (k : Nat)
    (arena : AssertionArena) : CommandSummary.Scoped arena n (e.summary k) = true := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Effect.summary_scoped h k arena
  simp [CommandSummary.Scoped, h₁, h₂, h₃, h₄]

/-- **A body's summary gives its signature's at every call**: a body summary
sound from `P`, within the signature summary `Sig` at each exit, gives
`Sig` at every run presented at the call's positions from an entry meeting
`P`. -/
theorem CommandSummary.signature_holds {arena : AssertionArena} {P : Assertion} {R : Runs} {S Sig : CommandSummary}
    (hS : S.Sound arena P R) (hw : ∀ c, (S.get c).Weakens arena P (Sig.get c)) {r : Tm} {args : List Tm}
    {c : Completion} {v : Tm} {m : Nat} {s s' : IndexedHeap} (hP : P (callEnv r args) m s)
    (hr : R.AtCall r args c v m s s') : (Sig.get c).Holds arena (callState r args v m s s') :=
  hw c _ hP (hS c _ hP hr)

/-- **An inferred effect states the signature's contract** (the note, §6,
Call, on both exits): a body summary within a signature's summary
(`Effect.summary`) at each exit gives, at every return with value `v`, the
signature's normal-return postcondition (`Effect.postW`), and at every
throw its throw postcondition (`Effect.excPost`), at actuals that are
values. -/
theorem CommandSummary.signature_contract {arena : AssertionArena} {P : Assertion} {R : Runs} {S : CommandSummary}
    {e : Effect} {r : Tm} {args : List Tm} (hS : S.Sound arena P R)
    (hw : ∀ c, (S.get c).Weakens arena P ((e.summary args.length).get c)) (hvals : ∀ a ∈ args, isVal a = true)
    {v : Tm} {m : Nat} {s s' : IndexedHeap} (hP : P (callEnv r args) m s) :
    (R.AtCall r args .normal v m s s' → e.postW r args s.W s.h s'.n s'.W s'.h v) ∧
      (R.AtCall r args .exceptional v m s s' → e.excPost r args s.h s'.h) := by
  constructor
  · intro hr
    have h := CommandSummary.signature_holds hS hw hP hr
    exact (Effect.summary_normal_iff e h.1.1 hvals).mp h
  · intro hr
    have h := CommandSummary.signature_holds hS hw hP hr
    exact (Effect.summary_exceptional_iff e args.length h.1.1).mp h

/-- **The inferred mutation effect is the body's frame**: at every return
and every throw from an entry meeting `P`, the transition is within the
body summary's frame at that exit, read at the call's positions. -/
theorem CommandSummary.frame_at_call {arena : AssertionArena} {P : Assertion} {R : Runs} {S : CommandSummary}
    (hS : S.Sound arena P R) {r : Tm} {args : List Tm} {c : Completion} {v : Tm} {m : Nat} {s s' : IndexedHeap}
    (hP : P (callEnv r args) m s) (hr : R.AtCall r args c v m s s') :
    EffectAction (S.get c).frame (callEnv r args) s s' :=
  (hS c (callState r args v m s s') hP hr).1

end Verification.CallEffects
