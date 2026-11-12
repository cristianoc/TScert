import Verification.Source.Claims.PassUnitMemberRun
import Verification.Source.Claims.PassUnitInterfaces

/-! # The single pass's unit theorem: the command's verdict

`passUnitVerdict_safe`: where mode 8 (`verifyUnitsFile`) prints a unit's
line `"accepted": true` with no observation asked, every member of the
unit's group is safe, under the graph-level hypotheses `RunSound` and
`RunKeepsSummaries` alone. docs/drafts/pass-unit-theorem.md, section 1. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-- **A group accepted with no observation asked is safe** (proved, under
`RunSound` and `RunKeepsSummaries`): over plans on their frozen store,
`passGroup` accepting a unit's group makes every member safe. -/
theorem passGroupOver_safe_unobserved
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {f : FilePlans} (hover : OverStore f) {i fuel : Nat} {compare : Bool}
    {debugNode repeats : Nat} {given : Option (Std.HashMap String Json)} {counting : Bool} {deps : List String}
    (haccepted : (f.passGroup fuel (f.fr.group i) compare debugNode repeats given none counting).2 = .ok deps) :
    PassUnitSafe f i :=
  fun j hj => member_safe (hrun _) (hkeep _) hover (passGroupChecks_unobserved passMember_sound haccepted j hj)

/-- **The headline: mode 8's accepted verdict** (proved, under `RunSound`
and `RunKeepsSummaries`). Mode 8 plans the file from the interfaces it
reads (`fragmentPlansFromInterfaces`) or with its modules checked in the
invocation (`fragmentPlansWithModules`), prepares it (`preparedMode8`: the
given head facts, the false start fact where `TSCERT_FORCE` names
`start-facts`), and prints unit `i` accepted where `passGroup` accepts its
group; with `TSCERT_OBSERVE` unset (`observe = none`), every member of that
group is safe. Every other argument of the command is free: the comparison,
node, repetition, given lines and counting flags, the modules' checks and
the interface file's entries. -/
theorem passUnitVerdict_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f₀ : FilePlans}
    {prepare : String → FilePlans → FilePlans}
    {check : FilePlans → List Nat → List String × Except String (List String)}
    {givenLines : Std.HashMap String Json} {i fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {counting : Bool} {deps : List String}
    (hplanned : (∃ est, fragmentPlansFromInterfaces ast fileKey budget selection standIns force est = .ok f₀) ∨
      (∃ ms notes, fragmentPlansWithModules ast fileKey budget selection standIns force prepare check =
        .ok (f₀, ms, notes)))
    (haccepted : ((preparedMode8 force givenLines f₀).passGroup fuel ((preparedMode8 force givenLines f₀).fr.group i)
      compare debugNode repeats given none counting).2 = .ok deps) :
    PassUnitSafe (preparedMode8 force givenLines f₀) i := by
  have h0 : OverStore f₀ := by
    rcases hplanned with ⟨est, h⟩ | ⟨ms, notes, h⟩
    · exact fragmentPlansFromInterfaces_overStore h
    · exact fragmentPlansWithModules_overStore h
  have hover : OverStore (preparedMode8 force givenLines f₀) := by
    unfold preparedMode8
    split
    · exact withFalseStartFact_overStore (withHeadFacts_overStore h0)
    · exact withHeadFacts_overStore h0
  exact passGroupOver_safe_unobserved hrun hkeep hover haccepted

end Verification.SourceClaimJson.PassUnit
