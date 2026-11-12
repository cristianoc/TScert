import Verification.Source.Claims.PassUnitHeadline

/-! # The single pass's unit theorem: the wrapper's lemmas

`FilePlans.passGroup` is the fold of `FilePlans.passMember` over a group's
members. This module proves that a group it accepts has every member's run
accepted (`passGroup_members`), and what a member's accepted run
establishes (`passMember_sound`: `MemberAccepted`), so that H3
(`PassGroupChecks`) holds of the code where the command's verdict is
computed: with no observation asked. docs/drafts/pass-unit-theorem.md,
section 3. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-- One step of `passGroup`'s fold. -/
private def groupStep (f : FilePlans) (fuel : Nat) (compare : Bool) (debugNode repeats : Nat)
    (given : Option (Std.HashMap String Json)) (observe : Option String) (counting : Bool)
    (acc : List String × Option String) (i : Nat) : List String × Option String :=
  match f.passMember fuel i compare debugNode repeats given observe counting with
  | .ok m =>
    let failure := match m.outcome with
      | .accepted => none
      | .refused w | .notHandled w => some s!"single pass: {m.outcome} ({w.length})"
      | o => some s!"single pass: {o} ({(toString o).length})"
    (acc.1 ++ [s!"{m.name}: {m.outcome}; {m.line}"], acc.2.orElse fun _ => failure)
  | .error reason => (acc.1 ++ [s!"refused before the pass: {reason.take 200}"], acc.2.orElse fun _ => some reason)

private theorem groupStep_none {f : FilePlans} {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting : Bool}
    {acc : List String × Option String} {i : Nat}
    (h : (groupStep f fuel compare debugNode repeats given observe counting acc i).2 = none) :
    acc.2 = none ∧ ∃ m, f.passMember fuel i compare debugNode repeats given observe counting = .ok m ∧
      m.accepted = true := by
  unfold groupStep at h
  split at h
  · rename_i m hm
    obtain ⟨l, a⟩ := acc
    cases a with
    | some _ => simp at h
    | none =>
      refine ⟨rfl, m, hm, ?_⟩
      simp only [Option.orElse] at h
      unfold MemberRun.accepted
      split at h <;> simp_all
  · obtain ⟨l, a⟩ := acc
    cases a <;> simp [Option.orElse] at h

private theorem groupFold_none {f : FilePlans} {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting : Bool} :
    ∀ (group : List Nat) (acc : List String × Option String),
      (group.foldl (groupStep f fuel compare debugNode repeats given observe counting) acc).2 = none →
      acc.2 = none ∧ ∀ j ∈ group, ∃ m, f.passMember fuel j compare debugNode repeats given observe counting = .ok m ∧
        m.accepted = true := by
  intro group
  induction group with
  | nil => intro acc h; exact ⟨h, fun _ hj => absurd hj List.not_mem_nil⟩
  | cons i rest ih =>
    intro acc h
    obtain ⟨h1, hrest⟩ := ih _ h
    obtain ⟨h0, m, hm, hacc⟩ := groupStep_none h1
    refine ⟨h0, fun j hj => ?_⟩
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ⟨m, hm, hacc⟩
    · exact hrest j hj

/-- **A group `passGroup` accepts has every member's run accepted**
(proved): its verdict is `.ok` only where every member's `passMember` is
`.ok` with an accepted outcome. -/
theorem passGroup_members {f : FilePlans} {fuel : Nat} {group : List Nat} {compare : Bool}
    {debugNode repeats : Nat} {given : Option (Std.HashMap String Json)} {observe : Option String}
    {counting : Bool} {deps : List String}
    (h : (f.passGroup fuel group compare debugNode repeats given observe counting).2 = .ok deps) :
    ∀ j ∈ group, ∃ m, f.passMember fuel j compare debugNode repeats given observe counting = .ok m ∧
      m.accepted = true := by
  unfold FilePlans.passGroup at h
  have key : (group.foldl (groupStep f fuel compare debugNode repeats given observe counting) ([], none)).2 = none := by
    revert h
    show (match group.foldl (groupStep f fuel compare debugNode repeats given observe counting) ([], none) with
      | (_, failed) => match failed with
        | some reason => (Except.error reason : Except String (List String))
        | none => .ok (f.dependencies group)) = .ok deps → _
    cases group.foldl (groupStep f fuel compare debugNode repeats given observe counting) ([], none) with
    | mk l failed => cases failed <;> simp
  exact (groupFold_none group _ key).2

/-- **What an accepted member run establishes** (named hypothesis, the
command's verdict path: no observation asked): where `passMember` returns
an accepted run, the member is `MemberAccepted`. Not proved: one `dsimp`
over `passMember`'s body exceeds 1,000,000 heartbeats (measured
2026-11-12, about 80 s), so the proof needs the body split into named
steps (docs/drafts/pass-unit-theorem.md, section 3). With an observation
asked, a refused outcome is replaced by an observation rerun's, which
nothing keeps from being accepted, so the statement is made at
`observe = none` only. -/
def PassMemberSound : Prop :=
  ∀ (f : FilePlans) (fuel : Nat) (compare : Bool) (debugNode repeats : Nat)
    (given : Option (Std.HashMap String Json)) (counting : Bool) (j : Nat) m,
    f.passMember fuel j compare debugNode repeats given none counting = .ok m → m.accepted = true →
    MemberAccepted f j

/-- **H3 at the command's verdict path** (proved, under `PassMemberSound`):
`passGroup` accepting a group with no observation asked makes every member
`MemberAccepted`. -/
theorem passGroupChecks_unobserved (hsound : PassMemberSound) {f : FilePlans} {fuel : Nat} {group : List Nat}
    {compare : Bool} {debugNode repeats : Nat} {given : Option (Std.HashMap String Json)} {counting : Bool}
    {deps : List String}
    (h : (f.passGroup fuel group compare debugNode repeats given none counting).2 = .ok deps) :
    ∀ j ∈ group, MemberAccepted f j := by
  intro j hj
  obtain ⟨m, hm, hacc⟩ := passGroup_members h j hj
  exact hsound f fuel compare debugNode repeats given counting j m hm hacc

end Verification.SourceClaimJson.PassUnit
