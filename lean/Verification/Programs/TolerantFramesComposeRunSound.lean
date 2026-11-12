import Verification.Programs.TolerantFramesRunSound
import Verification.Programs.TolerantFramesNodeCallFresh
import Verification.Programs.TolerantFramesNodeReturns

/-! # Tolerant frames: the graph theorem with the per-node hypotheses the checks give

`run_sound` (`TolerantFramesRunSound`) takes `FootprintsKept` and
`ReturnsKept`, statements about every run of every node at every admitted
reassigned graph. Each follows from the check `run` makes at every visited
node of the driver's walk, at `G`, and the nodes' entry states
(`NodeMeaning.entered`, a field of `NodesMean`):

- `footprintsKept_of_checked`: `BoundsChecked` (each visited node's bound
  check, `BoundChecked`, with `outFresh` as `run` computes it) ∧ `NodesMean`
  ⟹ `FootprintsKept`, by `footprintKept_of` at each admitted assignment, the
  check carried by `BoundChecked.reassign`;
- `returnsKept_of_checked`: `ReturnsChecked` (each visited return's
  `returnCheck` refusing nothing) ∧ `NodesMean` ⟹ `ReturnsKept`, by
  `returnsEnsured_of` and `ReturnChecked.reassign`.

`run_sound_17a` is `run_sound` with these two premises in place of
`FootprintsKept` and `ReturnsKept`. `BoundsChecked` and `ReturnsChecked`
are checks the driver makes at each node it visits, read off its walk as
`RunWalkA`'s other records are. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules LabelStore

section Checked
variable {ι : Type} [Labels ι]

variable (ι) in
/-- **(Named hypothesis) The driver checks every visited node's bound**
(`run`, "The footprint bound at this node"): under the call's bound
`(Φ, fr, ex)`, with its no-return region `dead`, `BoundChecked` at every
visited node of the walk, at `G`. -/
def BoundsChecked : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c,
      ∀ Φ fr ex, c.bound = some (Φ, fr, ex) → ∃ dead : List Bool,
        ∀ l (hl : r.w.visited l), BoundChecked (r.node l hl) Φ dead fr ex

variable (ι) in
/-- **(Named hypothesis) The driver checks every visited return** (`run`,
a return's checks): where the call states a postcondition, `returnCheck`
refuses nothing at every visited node whose continuation is a return, at
`G`. -/
def ReturnsChecked : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, c.ensures ≠ [] →
      ∀ l (hl : r.w.visited l), ReturnChecked (r.node l hl) c.goal c.ensures

/-- **The footprint check keeps the bound at every admitted assignment**
(`FootprintsKept`): the bound checked at every visited node
(`BoundsChecked`), carried to `reassign G η` (`BoundChecked.reassign`), and
the entry states from `NodesMean`, by `footprintKept_of`. -/
theorem footprintsKept_of_checked (hmean : NodesMean ι) (hb : BoundsChecked ι) : FootprintsKept ι := by
  intro G I c after admits hp r η hη Φ fr ex hbd
  obtain ⟨dead, hd⟩ := hb G I c after admits hp r Φ fr ex hbd
  obtain ⟨pc', hpc⟩ := scope_reassign hp.2.1 hη
  exact ⟨dead, fun ρ0 h₀ => footprintKept_of
    (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl),
      (hmean G I c after admits hp r η hη ρ0 h₀.length l hl).entered, (hd l hl).reassign hpc⟩)
    (codesSound_reassign hp.2.2.1 η)⟩

/-- **The return check establishes `ensures` at every admitted assignment**
(`ReturnsKept`): the return check at every visited return
(`ReturnsChecked`), carried to `reassign G η` (`ReturnChecked.reassign`),
and the entry states from `NodesMean`, by `returnsEnsured_of`. -/
theorem returnsKept_of_checked (hmean : NodesMean ι) (hrc : ReturnsChecked ι) : ReturnsKept ι := by
  intro G I c after admits hp r η hη hne ρ0 m
  obtain ⟨pc', hpc⟩ := scope_reassign hp.2.1 hη
  exact returnsEnsured_of
    (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl),
      (hmean G I c after admits hp r η hη ρ0 m l hl).entered, (hrc G I c after admits hp r hne l hl).reassign hpc⟩)
    (codesSound_reassign hp.2.2.1 η)

/-- **THE GRAPH THEOREM, the footprint and return premises from the
checks** (`run_sound` with `BoundsChecked` for `FootprintsKept` and
`ReturnsChecked` for `ReturnsKept`). -/
theorem run_sound_17a (hrun : RunTraversedA ι) (hmean : NodesMean ι) (hnear : LinearNearFuelEq)
    (himp : MergeExitsJoined ι) (hb : BoundsChecked ι) (hrc : ReturnsChecked ι)
    (hreg : RegionsHeld ι) (hasr : AssertionsLabelled ι) : Target.RunSound ι :=
  run_sound hrun hmean hnear himp (footprintsKept_of_checked hmean hb) (returnsKept_of_checked hmean hrc) hreg hasr

end Checked

end Verification.TolerantFrames
