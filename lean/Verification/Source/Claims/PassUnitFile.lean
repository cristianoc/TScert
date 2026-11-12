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

/-- **The code a member's request is**: its own code (`UnitIsCode`), or,
for a function declared without `this`, the code behind the receiver's
prologue (`UnitIsReceiverless`, `dropReceiver`). -/
def CodeOf (f : FilePlans) (r : Req f) (e e' : CodeEntry (Lab f)) : Prop :=
  (UnitIsCode r e ∧ e' = e) ∨ (UnitIsReceiverless r e ∧ e' = dropReceiver e)

/-- **A signature realized by a member**: the member `j`'s plan is a graph
request that is a code's (`CodeOf`) meeting the code conditions, and that
code is the module function's code `c` at the signature `p`. -/
def RowRealized (f : FilePlans) (c : ModuleCode (Lab f) String) (j : Nat) (p : CallEffects.Arrow (Ty (Lab f))) :
    Prop :=
  ∃ (name : String) (pos : Span) (r : Req f) (e e' : CodeEntry (Lab f)), PlanAt f j name pos r ∧ CodeOf f r e e' ∧
    codeConditions e = true ∧ e'.arity = c.arity ∧ e'.exprs = c.exprs ∧ e'.conts = c.conts ∧ e'.start = c.start ∧
    e'.captures = c.captures ∧ e'.store = none ∧ e'.row = p

/-- **A realized signature is met by the module function's code** (proved,
under `ReceiverDropSound` for a function declared without `this`): where
the realizing member is safe and its plan is over the file's store. -/
theorem rowRealized_spec (hdrop : ReceiverDropSound) {f : FilePlans} (hover : OverStore f)
    {c : ModuleCode (Lab f) String} {j : Nat} {p : CallEffects.Arrow (Ty (Lab f))}
    (hrow : RowRealized f c j p) (hj : MemberSafe f j) :
    GraphCodeSpec (graphOf f) c.arity c.exprs c.conts c.start c.captures p := by
  obtain ⟨name, pos, r, e, e', hplan, hcode, hcond, ha, hex, hco, hst, hca, hsto, hrow⟩ := hrow
  have hr := requestSafe_of_member hj hplan
  have hG : RequestJson.graph r.toRequest = graphOf f := by
    show StoreView.graph r.types = _
    rw [hover j name pos r hplan]
  have hspec : ∀ η, e'.Spec (reassign (RequestJson.graph r.toRequest) η) := by
    rcases hcode with ⟨hu, rfl⟩ | ⟨hu, rfl⟩
    · exact unitSpec_of_requestSafe hr hu hcond
    · exact hdrop _ _ r e hr hu hcond
  rw [hG] at hspec
  have he := hspec (graphOf f).env
  rw [reassign_env] at he
  unfold CodeEntry.Spec at he
  rw [ha, hex, hco, hst, hca, hsto, hrow] at he
  exact he

/-- **The module's layout** (H5a, the extraction's frame layout): the
functions `D` laid out (each closed unit's members, a mutually recursive
group's non-leaders included), the code of each by its identity and its
interface, such that each unit of `S` is laid out and each function `x` of
`D` has an interface presenting one clause of signatures its code's kind
offers, one slot per capture, each linked slot read at its callee's
interface with its callee in `D`, and each signature realized by a member
of the group of a closed unit (its own group, or another one for an
overload's signature); the outside values are closed values. -/
structure ModuleLayout (f : FilePlans) (selection : Option (List String)) (S : List String) where
  D : List String
  code : String → ModuleCode (Lab f) String
  iface : String → Ty (Lab f)
  values : OutsideValues code
  cover : ∀ u ∈ S, u ∈ D
  shape : ∀ x ∈ D, ∃ (L : List (CallEffects.Arrow (Ty (Lab f)))) (Sg : List (CallEffects.RestArrow (Ty (Lab f)))),
    Represents (graphOf f) (iface x) (.arrs L Sg) ∧ KindOffers (graphOf f) (code x).kind L Sg ∧
    (code x).captures.length = (code x).slots.length ∧
    (∀ (k : Nat) d, (code x).slots[k]? = some (Slot.linked d) → (code x).captures[k]? = some (iface d) ∧ d ∈ D) ∧
    ∀ p ∈ offerRows L Sg, ∃ u ∈ S, ∀ i ∈ f.fr.selected selection, f.fr.unitId i = u → ∃ j ∈ f.fr.group i,
      RowRealized f (code x) j p

/-- **The outside contracts** (H5b, the trusted boundary of the module's
slots): every value a laid-out function's slot holds from outside the file's
functions, at each depth, meets the slot's type at every budget up to that
depth in every world. Such a slot
holds an import (its declaration's contract, or an import stand-in's
footprint), a host value (its host contract), or a module constant or cell
(the initialization's postcondition, `:init`). With no import, no host
value and no module constant, no slot is outside and this holds vacuously. -/
def OutsideContracts {f : FilePlans} {selection : Option (List String)} {S : List String}
    (m : ModuleLayout f selection S) : Prop :=
  ∀ u ∈ m.D, ∀ (k : Nat) v A, (m.code u).slots[k]? = some (Slot.outside v) → (m.code u).captures[k]? = some A →
    ∀ i, ∀ j ≤ i, ∀ V : WorldT j, meaning (graphOf f) A j V (v i)

/-- **Every laid-out function is realized** (proved, under
`ReceiverDropSound`): where each unit of `S` is a selected unit whose group
is safe. -/
theorem layout_realizes (hdrop : ReceiverDropSound) {f : FilePlans} {selection : Option (List String)}
    {S : List String} (hover : OverStore f)
    (hsafe : ∀ u ∈ S, ∃ i ∈ f.fr.selected selection, f.fr.unitId i = u ∧ PassUnitSafe f i)
    (layout : ModuleLayout f selection S) (hout : OutsideContracts layout) :
    ∀ x, x ∈ layout.D → Realizes (graphOf f) layout.code layout.iface (· ∈ layout.D) x := by
  intro x hx
  obtain ⟨L, Sg, hrep, hk, hlen, hagree, hrows⟩ := layout.shape x hx
  refine ⟨L, Sg, hrep, hk, ?_, hlen, hagree, fun k v A hs hA i j hj V => hout x hx k v A hs hA i j hj V⟩
  intro p hp
  obtain ⟨u, hu, hall⟩ := hrows p hp
  obtain ⟨i, hi, hid, hunit⟩ := hsafe u hu
  obtain ⟨j, hj, hrow⟩ := hall i hi hid
  exact rowRealized_spec hdrop hover hrow (hunit j hj)

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
`PassGroupChecks`, `ReceiverDropSound`,
the module's layout H5a and the outside contracts H5b): for every unit of
the closure of mode 8's verdicts of a file, every member of its group is
safe (`PassUnitSafe`); and for every function the layout lays out (each
closed unit's members), its value in the module's environment, unfolded `n`
times, meets its interface at every budget up to `n` in every world, and
the values the environment captures for it meet its capture types at `n`:
its `RequestSafe` entry premise holds of the module's own values. -/
theorem passFile_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    (hgroup : PassGroupChecks) (hdrop : ReceiverDropSound)
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
    (∀ x ∈ layout.D, ∀ n, ∀ m ≤ n, ∀ W : WorldT m,
      meaning (graphOf (f.withHeadFacts givenLines false)) (layout.iface x) m W (approx layout.code n x)) ∧
    (∀ x ∈ layout.D, ∀ n (W : WorldT n), EnvOk (graphOf (f.withHeadFacts givenLines false)) (layout.code x).captures
      (envOf ((layout.code x).captured (approx layout.code n) n) .nul) n W) := by
  intro S
  have hsafe := fun u (hu : u ∈ S) =>
    closedUnits_selected_safe hrun hkeep hgroup hplans hu
  have hover := withHeadFacts_overStore (given := givenLines) (entries := false) (fragmentPlans_overStore hplans)
  have hreal := layout_realizes hdrop hover hsafe layout hout
  exact ⟨fun u hu => hsafe u hu,
    fun x hx n => approx_meets hreal layout.values n x hx,
    fun x hx n W => approx_captures_envOk hreal layout.values n hx W⟩

end Verification.SourceClaimJson.PassUnit
