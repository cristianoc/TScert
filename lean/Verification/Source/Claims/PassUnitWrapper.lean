import Verification.Source.Claims.PassUnitMember

/-! # The single pass's unit theorem: the wrapper's lemmas

`FilePlans.passGroup` is the fold of `FilePlans.passMember` over a group's
members. This module proves that a group it accepts has every member's run
accepted (`passGroup_members`), and states what a member's accepted run
establishes (`PassMemberSound`: `MemberAccepted`, proved in
PassUnitMemberRun), so that H3 (`PassGroupChecks`) holds of the code
(`passGroupChecks_of_sound`). docs/SINGLE-PASS-THEOREM.md,
section 3. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-- One step of `passGroup`'s fold. -/
private def groupStep (f : FilePlans) (fuel : Nat) (compare : Bool) (debugNode repeats : Nat)
    (given : Option (Std.HashMap String Json)) (observe : Option String) (counting located : Bool)
    (acc : List String × Option String) (i : Nat) : List String × Option String :=
  let place := fun (i : Nat) (w raw : String) =>
    if !located then raw else match f.locatedRefusal i w with
      | some l => s!"{l}\n{raw}"
      | none => raw
  match f.passMember fuel i compare debugNode repeats given observe counting with
  | .ok m =>
    let failure := match m.outcome with
      | .accepted => none
      | .refused w => some (place i w s!"single pass: {m.outcome} ({w.length})")
      | .notHandled w => some s!"single pass: {m.outcome} ({w.length})"
      | o => some s!"single pass: {o} ({(toString o).length})"
    (acc.1 ++ [s!"{m.name}: {m.outcome}; {m.line}"], acc.2.orElse fun _ => failure)
  | .error reason =>
    let reason := if !located || (reason.splitOn " at [").length > 1 then reason else
      match f.fr.units[i]? with
      | some (fn, _, _) => s!"source refusal at [{fn.namePos.1},{fn.namePos.2}): {reason}"
      | none => reason
    (acc.1 ++ [s!"refused before the pass: {reason.take 200}"], acc.2.orElse fun _ => some reason)

private theorem groupStep_none {f : FilePlans} {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool}
    {acc : List String × Option String} {i : Nat}
    (h : (groupStep f fuel compare debugNode repeats given observe counting located acc i).2 = none) :
    acc.2 = none ∧ ∃ m, f.passMember fuel i compare debugNode repeats given observe counting = .ok m ∧
      m.accepted = true := by
  unfold groupStep at h
  dsimp only at h
  obtain ⟨l, a⟩ := acc
  cases hm : f.passMember fuel i compare debugNode repeats given observe counting with
  | ok m =>
    rw [hm] at h
    cases a with
    | some _ => simp at h
    | none =>
      refine ⟨rfl, m, rfl, ?_⟩
      simp only [Option.orElse] at h
      unfold MemberRun.accepted
      cases ho : m.outcome <;> simp_all
  | error r =>
    rw [hm] at h
    cases a <;> simp [Option.orElse] at h

private theorem groupFold_none {f : FilePlans} {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool} :
    ∀ (group : List Nat) (acc : List String × Option String),
      (group.foldl (groupStep f fuel compare debugNode repeats given observe counting located) acc).2 = none →
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
    {counting located : Bool} {deps : List String}
    (h : (f.passGroup fuel group compare debugNode repeats given observe counting located).2 = .ok deps) :
    ∀ j ∈ group, ∃ m, f.passMember fuel j compare debugNode repeats given observe counting = .ok m ∧
      m.accepted = true := by
  unfold FilePlans.passGroup at h
  have key : (group.foldl (groupStep f fuel compare debugNode repeats given observe counting located) ([], none)).2 = none := by
    revert h
    show (match group.foldl (groupStep f fuel compare debugNode repeats given observe counting located) ([], none) with
      | (_, failed) => match failed with
        | some reason => (Except.error reason : Except String (List String))
        | none => .ok (f.dependencies group)) = .ok deps → _
    cases group.foldl (groupStep f fuel compare debugNode repeats given observe counting located) ([], none) with
    | mk l failed => cases failed <;> simp
  exact (groupFold_none group _ key).2

/-- **What an accepted member run establishes**: where `passMember` returns
an accepted run, at every value of every argument (the observation asked
included), the member is `MemberAccepted`. Proved as `passMember_sound`
(PassUnitMemberRun). -/
def PassMemberSound : Prop :=
  ∀ (f : FilePlans) (fuel : Nat) (compare : Bool) (debugNode repeats : Nat)
    (given : Option (Std.HashMap String Json)) (observe : Option String) (counting : Bool) (j : Nat) m,
    f.passMember fuel j compare debugNode repeats given observe counting = .ok m → m.accepted = true →
    MemberAccepted f j

/-- **H3** (proved, under `PassMemberSound`): `passGroup` accepting a group
makes every member `MemberAccepted`, at every value of every argument. -/
theorem passGroupChecks_of_sound (hsound : PassMemberSound) : PassGroupChecks := by
  intro f fuel group compare debugNode repeats given observe counting located deps h j hj
  obtain ⟨m, hm, hacc⟩ := passGroup_members h j hj
  exact hsound f fuel compare debugNode repeats given observe counting j m hm hacc

end Verification.SourceClaimJson.PassUnit
