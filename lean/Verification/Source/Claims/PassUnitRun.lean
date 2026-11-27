import Verification.Source.Claims.PassUnitVerdict
import Verification.Programs.TolerantFramesSinglePassSound

/-! # The single pass's unit theorem over the graph theorem

`passUnitVerdict_safe` takes the two run-level statements. The pass keeps
the read summaries it was given by proof (`runKeepsSummaries`), so mode 8's
accepted verdict gives the unit's safety from the graph theorem alone
(`passUnitVerdict_safe_run`), and the graph theorem is proved
(`run_sound_single_pass`): `passUnitVerdict_sound`. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore

/-- **Mode 8's accepted verdict, from the graph theorem**: where `RunSound`
holds, every member of the group of a unit the command prints accepted is
safe. -/
theorem passUnitVerdict_safe_run
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f₀ : FilePlans}
    {prepare : String → FilePlans → FilePlans}
    {check : FilePlans → List Nat → List String × Except String (List String)}
    {givenLines : Std.HashMap String Json} {infer : Bool}
    {keep : Nat → List (Nat × List HeapKnowledge.Candidate)} {i fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {«given» : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool}
    {deps : List String}
    (hplanned : (∃ est tables front known, fragmentPlansFromInterfaces ast fileKey budget selection standIns force est tables front known =
        .ok f₀) ∨
      (∃ ms notes, fragmentPlansWithModules ast fileKey budget selection standIns force prepare check =
        .ok (f₀, ms, notes)))
    (haccepted : ((preparedMode8 force givenLines infer f₀).passGroupMode8 infer force keep fuel
      ((preparedMode8 force givenLines infer f₀).fr.group i) compare debugNode repeats given observe counting
      located).2.1 = .ok deps) :
    PassUnitSafe (preparedMode8 force givenLines infer f₀) i :=
  passUnitVerdict_safe hrun (fun _ _ => Verification.TolerantFrames.runKeepsSummaries) hplanned haccepted

/-- **Mode 8's accepted verdict is sound**: every member of the group of a
unit the command prints accepted is safe. The statement has no premise
beyond the command's own: the file's plans and the accepted verdict. -/
theorem passUnitVerdict_sound
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f₀ : FilePlans}
    {prepare : String → FilePlans → FilePlans}
    {check : FilePlans → List Nat → List String × Except String (List String)}
    {givenLines : Std.HashMap String Json} {infer : Bool}
    {keep : Nat → List (Nat × List HeapKnowledge.Candidate)} {i fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {«given» : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool}
    {deps : List String}
    (hplanned : (∃ est tables front known, fragmentPlansFromInterfaces ast fileKey budget selection standIns force est tables front known =
        .ok f₀) ∨
      (∃ ms notes, fragmentPlansWithModules ast fileKey budget selection standIns force prepare check =
        .ok (f₀, ms, notes)))
    (haccepted : ((preparedMode8 force givenLines infer f₀).passGroupMode8 infer force keep fuel
      ((preparedMode8 force givenLines infer f₀).fr.group i) compare debugNode repeats given observe counting
      located).2.1 = .ok deps) :
    PassUnitSafe (preparedMode8 force givenLines infer f₀) i :=
  passUnitVerdict_safe_run (fun _ _ => Verification.TolerantFrames.run_sound_single_pass) hplanned haccepted

/-- Acceptance with explicit import answers establishes safety for the
requests planned on the supplied front, including a group-local front. -/
theorem sliceVerdict_sound {imports : GroupImports} {ast : Json} {fileKey : String}
    {budget : PositiveCertificates.SearchBudget} {names : Option (List String)} {standIns : StandIns}
    {force : List String} {est : Established} {tables : List (String × RowTable)}
    {front updated : Option (PlanningFront force)} {known : List (String × Option StandIn)} {f₀ : FilePlans}
    {lines : Std.HashMap String Json} {keep : Nat → List (Nat × List HeapKnowledge.Candidate)}
    {i fuel : Nat} {counting : Bool} {deps : List String}
    (hp : imports.plan ast fileKey budget names standIns force est tables front known = .ok (f₀, updated))
    (ha : (let f := preparedMode8 force lines true f₀
      (f.passGroupMode8 true force keep fuel (f.fr.group i) (counting := counting) (located := true)).2.1) = .ok deps) :
    PassUnitSafe (preparedMode8 force lines true f₀) i := by
  apply passGroupMode8_safe (fun _ _ => Verification.TolerantFrames.run_sound_single_pass)
    (fun _ _ => Verification.TolerantFrames.runKeepsSummaries) _ ha
  have h := withHeadFacts_overStore (groupImportsPlan_overStore hp) (given := lines) (entries := false) (inferred := true)
  unfold preparedMode8
  split
  · exact withFalseStartFact_overStore h
  · exact h

/-- The plans checked at a fresh module's print site in `establishStep`.
The supplied lines are `moduleLines location` in `verifyUnitsFile`. -/
def preparedModuleMode8 (force : List String) (infer : Bool) (lines : Std.HashMap String Json)
    (location : String) (f₀ : FilePlans) (reads : List FragmentRead)
    (incoming : Established) (tables : List (String × RowTable)) : FilePlans :=
  stepPlans (fun location f => preparedMode8 force (RequestCli.forModule location lines) infer f)
    location f₀ reads incoming tables

/-- A fresh module's accepted group is safe. The premises are its core
planning result and the successful pass result printed by `establishStep`;
wire-prefixing the dependency identities preserves this success. -/
theorem freshModuleVerdict_sound
    {m : ModuleNeed} {budget : PositiveCertificates.SearchBudget} {force : List String}
    {forced : StandIns} {imported : List (String × QualifiedEffect)}
    {depends : List (String × List String)} {f₀ : FilePlans}
    {moduleLines : String → Std.HashMap String Json} {reads : List FragmentRead}
    {incoming : Established} {tables : List (String × RowTable)}
    {infer : Bool} {keep : Nat → List (Nat × List HeapKnowledge.Candidate)}
    {i fuel : Nat} {located : Bool} {deps : List String}
    (hplanned : fragmentPlansCore m.module.document m.module.location budget (some m.names)
      forced force imported depends true true none true = .ok f₀)
    (haccepted : (let f := preparedModuleMode8 force infer (moduleLines m.module.location) m.module.location f₀ reads incoming tables
      (f.passGroupMode8 infer force keep fuel (f.fr.group i)
        (given := some (RequestCli.moduleGiven f.fr.ast
          (moduleLines ((f.fr.ast.getObjValAs? String "file").toOption.getD "")))) (located := located)).2.1) = .ok deps) :
    PassUnitSafe (preparedModuleMode8 force infer (moduleLines m.module.location) m.module.location f₀ reads incoming tables) i := by
  have h₀ := fragmentPlansCore_overStore hplanned
  have hp : OverStore (preparedMode8 force (RequestCli.forModule m.module.location (moduleLines m.module.location)) infer
      f₀) := by
    unfold preparedMode8
    split
    · exact withFalseStartFact_overStore (withHeadFacts_overStore h₀)
    · exact withHeadFacts_overStore h₀
  exact passGroupMode8_safe (fun _ _ => Verification.TolerantFrames.run_sound_single_pass)
    (fun _ _ => Verification.TolerantFrames.runKeepsSummaries) (stepPlans_overStore hp) haccepted

/-- **A plan replaced by one over the same request's store keeps the plans
over the store** (proved). -/
theorem overStore_withPlan {f : FilePlans} (hover : OverStore f) {i : Nat}
    {x y : FunctionPlan (EquationStore.Checked f.F.equations f.F.primitive) (EquationStore.CheckedLabel f.F.equations f.F.primitive)}
    (hx : f.plans[i]? = some (.ok x)) (hy : y.parts.2.2.types = x.parts.2.2.types) : OverStore (f.withPlan i y) := by
  have key : ∀ (j : Nat) p, (f.plans.set i (.ok y))[j]? = some (.ok p) → p.parts.2.2.types = f.F.store := by
    intro j p hj
    rw [List.getElem?_set] at hj
    split at hj
    · rename_i hij
      subst hij
      split at hj
      · cases hj; exact hy.trans (hover _ _ hx)
      · cases hj
    · exact hover j p hj
  exact key

/-- Acceptance at either mode 8 print site for a group checked in this
process, indexed by its prepared plans and leader. The main-file branch
uses either planning route; the fresh-module branch uses the core planner,
module preparation and row refusal. Cached module projections have no
constructor. Planning inputs are universally quantified, as in
`passUnitVerdict_sound`. -/
inductive Mode8Accepted : FilePlans → Nat → Prop where
  | main
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f₀ : FilePlans}
    {prepare : String → FilePlans → FilePlans}
    {check : FilePlans → List Nat → List String × Except String (List String)}
    {givenLines : Std.HashMap String Json} {infer : Bool}
    {keep : Nat → List (Nat × List HeapKnowledge.Candidate)} {i fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {«given» : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool}
    {deps : List String}
    (hplanned : (∃ est tables front known, fragmentPlansFromInterfaces ast fileKey budget selection standIns force est tables front known =
        .ok f₀) ∨
      (∃ ms notes, fragmentPlansWithModules ast fileKey budget selection standIns force prepare check =
        .ok (f₀, ms, notes)))
    (hselected : i ∈ (preparedMode8 force givenLines infer f₀).fr.selected selection)
    (haccepted : ((preparedMode8 force givenLines infer f₀).passGroupMode8 infer force keep fuel
      ((preparedMode8 force givenLines infer f₀).fr.group i) compare debugNode repeats given observe counting
      located).2.1 = .ok deps) :
    Mode8Accepted (preparedMode8 force givenLines infer f₀) i
  | slice
    {imports : GroupImports} {ast : Json} {fileKey : String}
    {budget : PositiveCertificates.SearchBudget} {names : Option (List String)} {standIns : StandIns}
    {force : List String} {est : Established} {tables : List (String × RowTable)}
    {front updated : Option (PlanningFront force)} {known : List (String × Option StandIn)} {f₀ : FilePlans}
    {lines : Std.HashMap String Json} {keep : Nat → List (Nat × List HeapKnowledge.Candidate)}
    {i fuel : Nat} {counting : Bool} {deps : List String}
    (hp : imports.plan ast fileKey budget names standIns force est tables front known = .ok (f₀, updated))
    (hselected : i ∈ (preparedMode8 force lines true f₀).fr.selected names)
    (ha : (let f := preparedMode8 force lines true f₀
      (f.passGroupMode8 true force keep fuel (f.fr.group i) (counting := counting) (located := true)).2.1) = .ok deps) :
    Mode8Accepted (preparedMode8 force lines true f₀) i
  | freshModule
    {m : ModuleNeed} {budget : PositiveCertificates.SearchBudget} {force : List String}
    {forced : StandIns} {imported : List (String × QualifiedEffect)}
    {depends : List (String × List String)} {f₀ : FilePlans}
    {moduleLines : String → Std.HashMap String Json} {reads : List FragmentRead}
    {incoming : Established} {tables : List (String × RowTable)}
    {infer : Bool} {keep : Nat → List (Nat × List HeapKnowledge.Candidate)}
    {i fuel : Nat} {located : Bool} {deps : List String}
    (hplanned : fragmentPlansCore m.module.document m.module.location budget (some m.names)
      forced force imported depends true true none true = .ok f₀)
    (hselected : i ∈ establishChecked m
      (preparedModuleMode8 force infer (moduleLines m.module.location) m.module.location f₀ reads incoming tables))
    (haccepted : (let f := preparedModuleMode8 force infer (moduleLines m.module.location) m.module.location f₀ reads incoming tables
      (f.passGroupMode8 infer force keep fuel (f.fr.group i)
        (given := some (RequestCli.moduleGiven f.fr.ast
          (moduleLines ((f.fr.ast.getObjValAs? String "file").toOption.getD "")))) (located := located)).2.1) = .ok deps) :
    Mode8Accepted (preparedModuleMode8 force infer (moduleLines m.module.location) m.module.location f₀ reads incoming tables) i

/-- Every member of a group accepted at a mode 8 in-process check is safe. -/
theorem mode8Accepted_sound {f : FilePlans} {i : Nat}
    (h : Mode8Accepted f i) : PassUnitSafe f i := by
  cases h with
  | main hplanned _ haccepted => exact passUnitVerdict_sound hplanned haccepted
  | slice hp _ ha => exact sliceVerdict_sound hp ha
  | freshModule hplanned _ haccepted => exact freshModuleVerdict_sound hplanned haccepted

end Verification.SourceClaimJson.PassUnit
