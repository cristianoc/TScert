import Verification.Source.Claims.PassUnitMemberRun
import Verification.Source.Claims.PassUnitInterfaces

/-! # The single pass's unit theorem: the command's verdict

`passUnitVerdict_safe`: where mode 8 (`verifyUnitsFile`) prints a unit's
line `"accepted": true`, every member of the unit's group is safe, under the
graph-level hypotheses `RunSound` and `RunKeepsSummaries` alone. docs/SINGLE-PASS-THEOREM.md, section 1. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-- **The headline: mode 8's accepted verdict** (proved, under `RunSound`
and `RunKeepsSummaries`). Mode 8 plans the file from the interfaces it
reads (`fragmentPlansFromInterfaces`, its rows and unbound-import checks
included) or with its modules checked in the invocation
(`fragmentPlansWithModules`), prepares it (`preparedMode8`: the given head
facts, the false start fact where `TSCERT_FORCE` names `start-facts`), and
prints unit `i` accepted where `passGroup` accepts its group; every member
of that group is safe. Every other argument of the command is free: the
comparison, node, repetition, observation, given lines, counting and
location flags, the modules' checks and the interface file's entries and
rows. -/
theorem passUnitVerdict_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f₀ : FilePlans}
    {prepare : String → FilePlans → FilePlans}
    {check : FilePlans → List Nat → List String × Except String (List String)}
    {givenLines : Std.HashMap String Json} {infer : Bool}
    {keep : Nat → List (Nat × List HeapKnowledge.IndexAtom)} {i fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool}
    {deps : List String}
    (hplanned : (∃ est tables front known memo, fragmentPlansFromInterfaces ast fileKey budget selection standIns force est tables front known memo =
        .ok f₀) ∨
      (∃ ms notes, fragmentPlansWithModules ast fileKey budget selection standIns force prepare check =
        .ok (f₀, ms, notes)))
    (haccepted : ((preparedMode8 force givenLines infer f₀).passGroupMode8 infer force keep fuel
      ((preparedMode8 force givenLines infer f₀).fr.group i) compare debugNode repeats given observe counting
      located).2.1 = .ok deps) :
    PassUnitSafe (preparedMode8 force givenLines infer f₀) i :=
  passUnitCli_safe hrun hkeep hplanned haccepted

end Verification.SourceClaimJson.PassUnit
