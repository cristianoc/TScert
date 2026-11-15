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
states the signature's contract for every such run
(`CommandSummary.signature_holds`), and with `Effect.summary` the
signature's normal and throw postconditions themselves
(`CommandSummary.signature_contract`). A summary is a signature's at
arity `n` when its frames read the receiver and the first `n` parameters
and its postconditions the entry slots up to `n` and the exit slots up to
`n + 1` (`CommandSummary.Scoped`), as every module function's is
(`Effect.summary_scoped`), and every signature's under the conditions
`Effect.summary_scopedSummary_of` states, natives' included.

A body's exit valuation may hold locals past the call's exit positions
(`Runs.AtCallBelow`: it agrees with `ensuresEnv` below `n + 2`). A scoped
signature summary holds alike at two two-states agreeing below its scope
(`CommandSummary.Scoped.holds_congr`, by `FormulaF.holds_scoped_congr`), so
the contract of such a body is stated at `callState` too
(`CommandSummary.signature_holds_below`,
`CommandSummary.signature_contract_below`). -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge TolerantFrames Parity

/-! ## Scope and the operations on signatures -/

/-- **A module function's summary reads its own positions**: where its
effect is about the receiver and its first `n` parameters
(`Effect.belowRow`), its frames read call positions up to `n` and its
postconditions the entry positions up to `n` and the exit positions up to
`n + 1`. -/
theorem Effect.summary_scoped {e : Effect} {n : Nat} (h : e.belowRow n = true) (k : Nat)
    (arena : AssertionArena) :
    effectScoped (n + 1) (e.summary k).normal.frame = true ∧
      (e.summary k).normal.ensures.all (FormulaF.scoped arena ⟨n + 1, n + 2⟩) = true ∧
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
    · cases e.fresh <;> simp [FormulaF.scoped, OperationPostF.scoped]
    · cases e.freshObject <;> simp [FormulaF.scoped, OperationPostF.scoped]
    · cases e.elements <;> simp [FormulaF.scoped, OperationPostF.scoped]
    · refine List.all_eq_true.mpr fun F hF => ?_
      obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
      simp only [FormulaF.scoped, OperationPostF.scoped, Scope.count, Nat.add_zero, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq]
      exact ⟨fun i hi => decide_eq_true (by have := Effect.belowRow_ensures h G hG i hi; omega),
        fun i hi => by have := Effect.belowRow_ensures_entry h G hG i hi; omega⟩
  · simp only [Effect.summary]
    split
    · exact hframe
    · exact htop
  · simp only [Effect.summary]
    split <;> rfl


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

/-- **A module function's signature summary is in its scope**
(`Effect.summary_scoped`). -/
theorem Effect.summary_scopedSummary {e : Effect} {n : Nat} (h : e.belowRow n = true) (k : Nat)
    (arena : AssertionArena) : CommandSummary.Scoped arena n (e.summary k) = true := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Effect.summary_scoped h k arena
  simp [CommandSummary.Scoped, h₁, h₂, h₃, h₄]

/-- **A signature's summary at arity `k`, scoped at `n`**: where its frame
reads call positions up to `n`, its postcondition's facts exit positions up
to `n + 1` and entry positions up to `n`, an append reads the actuals up to
position `n` (`k ≤ n`), and an element assignment or exact write, which
reads entry slots `1` to `3` and states its result by the transport
`writtenResult k` of `max (k + 1) 4` images, is at `n + 1 = max (k + 1) 4`
entry slots. The last condition is exact: `FormulaF.scoped` requires a
transport's images to be the scope's entry slots, so such a summary is
scoped at `n = max k 3` alone. -/
theorem Effect.summary_scopedSummary_of {e : Effect} {n k : Nat} (arena : AssertionArena)
    (hf : effectScoped (n + 1) e.frame = true)
    (hens : ∀ F ∈ e.ensures, (∀ i ∈ F.slots, i ≤ n + 1) ∧ ∀ i ∈ F.entrySlots, i ≤ n)
    (hg : e.receiverGrows = true → k ≤ n)
    (hw : ∀ w, e.elementWrite = some w → w ≠ .stores → max (k + 1) 4 = n + 1) :
    CommandSummary.Scoped arena n (e.summary k) = true := by
  have htop : effectScoped (n + 1) topEffect = true := rfl
  have hwr : max (k + 1) 4 = n + 1 →
      FormulaF.scoped arena ⟨n + 1, n + 2⟩ (.transport (writtenResult k)) = true := by
    intro hm
    simp only [FormulaF.scoped, writtenResult, List.size_toArray, List.length_map, List.length_range, hm,
      decide_true, Bool.true_and, List.all_eq_true, List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Witness.scoped, Path.scoped, decide_eq_true_eq]
    intro i hi; split <;> omega
  have hpost : (e.normalPosts k).all (FormulaF.scoped arena ⟨n + 1, n + 2⟩) = true := by
    simp only [Effect.normalPosts, List.all_append, Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · cases e.fresh <;> simp [FormulaF.scoped, OperationPostF.scoped]
    · cases e.freshObject <;> simp [FormulaF.scoped, OperationPostF.scoped]
    · cases e.elements <;> simp [FormulaF.scoped, OperationPostF.scoped]
    · refine List.all_eq_true.mpr fun F hF => ?_
      obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
      simp only [FormulaF.scoped, OperationPostF.scoped, Scope.count, Nat.add_zero, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq]
      exact ⟨fun i hi => decide_eq_true (by have := (hens G hG).1 i hi; omega),
        fun i hi => by have := (hens G hG).2 i hi; omega⟩
    · cases hgr : e.receiverGrows
      · rfl
      · have hk := hg hgr
        simp only [if_true, List.all_cons, List.all_nil, FormulaF.scoped, effectScoped, OperationPostF.scoped,
          regionRoots, actualWitnesses, Bool.and_true, List.all_eq_true, List.mem_map, List.mem_range,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Witness.scoped, Path.scoped, Bool.and_eq_true,
          decide_eq_true_eq]
        exact ⟨by omega, by omega, ⟨by omega, by omega⟩, fun _ _ => by omega⟩
    · cases hew : e.elementWrite with
      | none => rfl
      | some w =>
        cases w with
        | stores => rfl
        | assign =>
          have hm := hw .assign hew (by intro h; cases h)
          simp only [ElementWrite.posts, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
          refine ⟨rfl, ?_, hwr hm⟩
          simp only [FormulaF.scoped, OperationPostF.scoped, Bool.and_eq_true, decide_eq_true_eq]; omega
        | exact kk =>
          have hm := hw (.exact kk) hew (by intro h; cases h)
          simp only [ElementWrite.posts, List.all_cons, List.all_append, List.all_nil, Bool.and_true,
            Bool.and_eq_true]
          refine ⟨rfl, ?_, ?_, hwr hm⟩
          · simp only [FormulaF.scoped, OperationPostF.scoped, Bool.and_eq_true, decide_eq_true_eq]; omega
          · refine List.all_eq_true.mpr fun F hF => ?_
            obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
            simp only [FormulaF.scoped, OperationPostF.scoped, Scope.count, Nat.add_zero, Bool.and_eq_true,
              List.all_eq_true, decide_eq_true_eq]
            have h3 : 3 ≤ n := by omega
            simp only [ElementKind.preFacts] at hG
            cases hr : kk.range <;> simp only [hr] at hG <;>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hG <;>
              rcases hG with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [HeapKnowledge.IndexFact.slots, HeapKnowledge.IndexFact.entrySlots, Linear.Fact.vars,
                HeapKnowledge.Term.slots, HeapKnowledge.Term.entrySlots,
                HeapKnowledge.Term.value, HeapKnowledge.Term.now, decide_eq_true_eq] <;>
              first | exact decide_eq_true (by omega) | exact ⟨decide_eq_true (by omega), by omega⟩
  have hexc : effectScoped (n + 1) (e.summary k).exceptional.frame = true := by
    simp only [Effect.summary]; split
    · exact hf
    · exact htop
  have hexe : (e.summary k).exceptional.ensures = [] := by simp only [Effect.summary]; split <;> rfl
  simp only [CommandSummary.Scoped, Bool.and_eq_true, hexc, hexe, List.all_nil, and_true]
  exact ⟨hf, hpost⟩

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
    exact (Effect.summary_normal_iff e h.1.1 fun _ => hvals).mp h
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

/-- **An inferred effect states the signature's contract at every call
whose exit holds locals** (`signature_contract` with
`signature_holds_below`), its summary at the call's arity scoped at `n`
(`Effect.summary_scopedSummary`, `Effect.summary_scopedSummary_of`). -/
theorem CommandSummary.signature_contract_below {arena : AssertionArena} {P : Assertion} {R : Runs}
    {S : CommandSummary} {e : Effect} {n : Nat} {r : Tm} {args : List Tm} (hS : S.Sound arena P R)
    (hw : ∀ c, (S.get c).Weakens arena P ((e.summary args.length).get c))
    (hsc : CommandSummary.Scoped arena n (e.summary args.length) = true) (hvals : ∀ a ∈ args, isVal a = true)
    {v : Tm} {m : Nat} {s s' : IndexedHeap} (hP : P (callEnv r args) m s) :
    (R.AtCallBelow n r args .normal v m s s' → e.postW r args s.W s.h s'.n s'.W s'.h v) ∧
      (R.AtCallBelow n r args .exceptional v m s s' → e.excPost r args s.h s'.h) := by
  constructor
  · intro hr
    have h := CommandSummary.signature_holds_below hS hw hsc hP hr
    exact (Effect.summary_normal_iff e h.1.1 fun _ => hvals).mp h
  · intro hr
    have h := CommandSummary.signature_holds_below hS hw hsc hP hr
    exact (Effect.summary_exceptional_iff e args.length h.1.1).mp h

/-- **The inferred mutation effect is the body's frame at every call whose
exit holds locals**: the frame reads the entry valuation alone. -/
theorem CommandSummary.frame_at_call_below {arena : AssertionArena} {P : Assertion} {R : Runs}
    {S : CommandSummary} (hS : S.Sound arena P R) {n : Nat} {r : Tm} {args : List Tm} {c : Completion} {v : Tm}
    {m : Nat} {s s' : IndexedHeap} (hP : P (callEnv r args) m s) (hr : R.AtCallBelow n r args c v m s s') :
    EffectAction (S.get c).frame (callEnv r args) s s' := by
  obtain ⟨η', -, hr⟩ := hr
  exact (hS c ⟨callEnv r args, η', m, s, s'⟩ hP hr).1

end Verification.CallEffects
