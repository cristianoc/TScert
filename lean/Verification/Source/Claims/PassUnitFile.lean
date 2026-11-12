import Verification.Source.Claims.PassUnitRealize

/-! # The single pass's unit theorem: the file-level theorem

Mode 8's verdicts of a file, closed (`closedUnits`), with the module's
layout (`ModuleLayout`: each closed unit's code, interface and slots, and
each signature of its interface realized by a member of its group) and the
contracts of the slots no unit of the file fills (`OutsideContracts`),
give every function of the file safe: each member of each closed unit's
group is safe (`PassUnitSafe`), and each closed unit's value in the module's
environment meets its interface at every budget (`approx_meets`), so its
captures meet their types (docs/drafts/pass-unit-theorem.md, section 6). -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-- The labels of a file's frozen store. -/
abbrev Lab (f : FilePlans) : Type := EquationStore.CheckedLabel f.F.equations f.F.primitive

/-- The graph of a file's frozen store. -/
abbrev graphOf (f : FilePlans) : NormalGraph (Lab f) := StoreView.graph f.F.store

/-- A member's request is safe where the member is (proved). -/
theorem requestSafe_of_member {f : FilePlans} {j : Nat} {name : String} {pos : Span} {r : Req f}
    (hm : MemberSafe f j) (hp : PlanAt f j name pos r) : RequestSafe r := by
  obtain ⟨p, c, hpl, hc, hs⟩ := hm
  unfold PlanAt at hp
  rw [hp] at hpl
  injection hpl with hpl
  injection hpl with hpl
  subst hpl
  simp only [FunctionPlan.certify, pure, Except.pure] at hc
  injection hc with hc
  subst hc
  exact hs

/-- **A signature realized by a member**: the member `j`'s plan is a graph
request that is a code's (`UnitIsCode`) meeting the code conditions, and the
code is the module function's code `c` at the signature `p`. -/
def RowRealized (f : FilePlans) (c : ModuleCode (Lab f) String) (j : Nat) (p : CallEffects.Arrow (Ty (Lab f))) :
    Prop :=
  ∃ (name : String) (pos : Span) (r : Req f) (e : CodeEntry (Lab f)), PlanAt f j name pos r ∧ UnitIsCode r e ∧
    codeConditions e = true ∧ e.arity = c.arity ∧ e.exprs = c.exprs ∧ e.conts = c.conts ∧ e.start = c.start ∧
    e.captures = c.captures ∧ e.store = none ∧ e.row = p

/-- **The module's layout** (H5a, the extraction's frame layout): the code of
each module function by unit identity and its interface, such that for each
unit `u` of `S`, its interface presents one clause of signatures its code's
kind offers, each signature realized by a member of the group of every
selected unit identified as `u`, one slot per capture, and each linked slot
read at its callee's interface, its callee in `S`; the outside values are
closed values. -/
structure ModuleLayout (f : FilePlans) (selection : Option (List String)) (S : List String) where
  code : String → ModuleCode (Lab f) String
  iface : String → Ty (Lab f)
  values : OutsideValues code
  shape : ∀ u ∈ S, ∃ (L : List (CallEffects.Arrow (Ty (Lab f)))) (Sg : List (CallEffects.RestArrow (Ty (Lab f)))),
    Represents (graphOf f) (iface u) (.arrs L Sg) ∧ KindOffers (graphOf f) (code u).kind L Sg ∧
    (code u).captures.length = (code u).slots.length ∧
    (∀ (k : Nat) d, (code u).slots[k]? = some (Slot.linked d) → (code u).captures[k]? = some (iface d) ∧ d ∈ S) ∧
    ∀ i ∈ f.fr.selected selection, f.fr.unitId i = u → ∀ p ∈ offerRows L Sg, ∃ j ∈ f.fr.group i,
      RowRealized f (code u) j p

/-- **The outside contracts** (H5b, the trusted boundary of the module's
slots): every value a closed unit's slot holds from outside the file's
functions, at each depth, meets the slot's type at every budget up to that
depth in every world. Such a slot
holds an import (its declaration's contract, or an import stand-in's
footprint), a host value (its host contract), or a module constant or cell
(the initialization's postcondition, `:init`). With no import, no host
value and no module constant, no slot is outside and this holds vacuously. -/
def OutsideContracts {f : FilePlans} {selection : Option (List String)} {S : List String}
    (m : ModuleLayout f selection S) : Prop :=
  ∀ u ∈ S, ∀ (k : Nat) v A, (m.code u).slots[k]? = some (Slot.outside v) → (m.code u).captures[k]? = some A →
    ∀ i, ∀ j ≤ i, ∀ V : WorldT j, meaning (graphOf f) A j V (v i)

/-- Every closed unit of mode 8's verdicts is a selected unit whose group
`passGroup` accepts (proved, under H1–H4, as `closedUnits_safe`), selection
included. -/
theorem closedUnits_selected_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    (hgroup : PassGroupChecks)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f : FilePlans}
    {givenLines : Std.HashMap String Json} {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting : Bool}
    (hplans : fragmentPlans ast fileKey budget selection standIns force = .ok f) {u : String}
    (hu : u ∈ closedUnits (fileVerdicts f selection givenLines fuel compare debugNode repeats given observe counting)) :
    ∃ i ∈ f.fr.selected selection, f.fr.unitId i = u ∧ PassUnitSafe (f.withHeadFacts givenLines false) i := by
  obtain ⟨ds, ha, -⟩ := closedUnits_closed _ u hu
  unfold Verdicts.accepted at ha
  cases hl : (fileVerdicts f selection givenLines fuel compare debugNode repeats given observe counting).lookup u with
  | none => rw [hl] at ha; cases ha
  | some v =>
    rw [hl] at ha
    simp only [Option.join_some] at ha
    subst ha
    have hm := lookup_mem hl
    simp only [fileVerdicts, List.mem_map, Prod.mk.injEq] at hm
    obtain ⟨i, hi, hid, hv⟩ := hm
    cases hp : ((f.withHeadFacts givenLines false).passGroup fuel (f.fr.group i) compare debugNode repeats given
        observe counting).2 with
    | error e => rw [hp] at hv; cases hv
    | ok d => exact ⟨i, hi, hid, passUnit_safe hrun hkeep hgroup hplans hi hp⟩

/-- **The file-level theorem** (proved, under the graph-level hypotheses
H1 `RunSound` and H2 `RunKeepsSummaries`, the wrapper hypothesis H3
`PassGroupChecks`,
the module's layout H5a and the outside contracts H5b): for every unit of
the closure of mode 8's verdicts of a file,

- every member of its group is safe (`PassUnitSafe`), and
- its value in the module's environment, unfolded `n` times, meets its
  interface at every budget up to `n` in every world, and the values the
  environment captures for it meet its capture types at `n`: its
  `RequestSafe` entry premise holds of the module's own values. -/
theorem passFile_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    (hgroup : PassGroupChecks)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f : FilePlans}
    {givenLines : Std.HashMap String Json} {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting : Bool}
    (hplans : fragmentPlans ast fileKey budget selection standIns force = .ok f)
    (layout : ModuleLayout (f.withHeadFacts givenLines false) selection
      (closedUnits (fileVerdicts f selection givenLines fuel compare debugNode repeats given observe counting)))
    (hout : OutsideContracts layout) :
    let S := closedUnits (fileVerdicts f selection givenLines fuel compare debugNode repeats given observe counting)
    (∀ u ∈ S, ∃ i ∈ f.fr.selected selection, f.fr.unitId i = u ∧ PassUnitSafe (f.withHeadFacts givenLines false) i) ∧
    (∀ u ∈ S, ∀ n, ∀ m ≤ n, ∀ W : WorldT m,
      meaning (graphOf (f.withHeadFacts givenLines false)) (layout.iface u) m W (approx layout.code n u)) ∧
    (∀ u ∈ S, ∀ n (W : WorldT n), EnvOk (graphOf (f.withHeadFacts givenLines false)) (layout.code u).captures
      (envOf ((layout.code u).captured (approx layout.code n) n) .nul) n W) := by
  intro S
  have hsafe := fun u (hu : u ∈ S) =>
    closedUnits_selected_safe hrun hkeep hgroup hplans hu
  have hover := withHeadFacts_overStore (given := givenLines) (entries := false) (fragmentPlans_overStore hplans)
  have hreal : ∀ u, u ∈ S → Realizes (graphOf (f.withHeadFacts givenLines false)) layout.code layout.iface
      (· ∈ S) u := by
    intro u hu
    obtain ⟨L, Sg, hrep, hk, hlen, hagree, hrows⟩ := layout.shape u hu
    obtain ⟨i, hi, hid, hunit⟩ := hsafe u hu
    refine ⟨L, Sg, hrep, hk, ?_, hlen, hagree, fun k v A hs hA i j hj V => hout u hu k v A hs hA i j hj V⟩
    intro p hp
    obtain ⟨j, hj, name, pos, r, e, hplan, hcode, hcond, ha, hex, hco, hst, hca, hsto, hrow⟩ :=
      hrows i hi hid p hp
    have hr := requestSafe_of_member (hunit j hj) hplan
    have hspec := unitSpec_of_requestSafe hr hcode hcond
    have htypes := hover j name pos r hplan
    have hG : RequestJson.graph r.toRequest = graphOf (f.withHeadFacts givenLines false) := by
      show StoreView.graph r.types = _
      rw [htypes]
    rw [hG] at hspec
    have he := hspec (graphOf (f.withHeadFacts givenLines false)).env
    rw [reassign_env] at he
    unfold CodeEntry.Spec at he
    rw [ha, hex, hco, hst, hca, hsto, hrow] at he
    exact he
  exact ⟨fun u hu => hsafe u hu,
    fun u hu n => approx_meets hreal layout.values n u hu,
    fun u hu n W => approx_captures_envOk hreal layout.values n hu W⟩

end Verification.SourceClaimJson.PassUnit
