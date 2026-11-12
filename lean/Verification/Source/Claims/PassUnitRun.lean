import Verification.Source.Claims.PassUnitVerdict
import Verification.Programs.TolerantFramesSinglePassSound

/-! # The single pass's unit theorem over the graph theorem

`passUnitVerdict_safe` takes the two run-level statements. The pass keeps
the read summaries it was given by proof (`runKeepsSummaries`), so mode 8's
accepted verdict gives the unit's safety from the graph theorem alone
(`passUnitVerdict_safe_run`), and the graph theorem is proved
(`run_sound_single_pass`): `passUnitVerdict_sound`. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-- **Mode 8's accepted verdict, from the graph theorem**: where `RunSound`
holds, every member of the group of a unit the command prints accepted is
safe. -/
theorem passUnitVerdict_safe_run
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f₀ : FilePlans}
    {prepare : String → FilePlans → FilePlans}
    {check : FilePlans → List Nat → List String × Except String (List String)}
    {givenLines : Std.HashMap String Json} {i fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool}
    {deps : List String}
    (hplanned : (∃ est tables, fragmentPlansFromInterfaces ast fileKey budget selection standIns force est tables =
        .ok f₀) ∨
      (∃ ms notes, fragmentPlansWithModules ast fileKey budget selection standIns force prepare check =
        .ok (f₀, ms, notes)))
    (haccepted : ((preparedMode8 force givenLines f₀).passGroup fuel ((preparedMode8 force givenLines f₀).fr.group i)
      compare debugNode repeats given observe counting located).2 = .ok deps) :
    PassUnitSafe (preparedMode8 force givenLines f₀) i :=
  passUnitVerdict_safe hrun (fun _ _ => Verification.TolerantFrames.runKeepsSummaries) hplanned haccepted

/-- **Mode 8's accepted verdict is sound**: every member of the group of a
unit the command prints accepted is safe. The statement has no premise
beyond the command's own: the file's plans and the accepted verdict. -/
theorem passUnitVerdict_sound
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f₀ : FilePlans}
    {prepare : String → FilePlans → FilePlans}
    {check : FilePlans → List Nat → List String × Except String (List String)}
    {givenLines : Std.HashMap String Json} {i fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool}
    {deps : List String}
    (hplanned : (∃ est tables, fragmentPlansFromInterfaces ast fileKey budget selection standIns force est tables =
        .ok f₀) ∨
      (∃ ms notes, fragmentPlansWithModules ast fileKey budget selection standIns force prepare check =
        .ok (f₀, ms, notes)))
    (haccepted : ((preparedMode8 force givenLines f₀).passGroup fuel ((preparedMode8 force givenLines f₀).fr.group i)
      compare debugNode repeats given observe counting located).2 = .ok deps) :
    PassUnitSafe (preparedMode8 force givenLines f₀) i :=
  passUnitVerdict_safe_run (fun _ _ => Verification.TolerantFrames.run_sound_single_pass) hplanned haccepted

end Verification.SourceClaimJson.PassUnit
