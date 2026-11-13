import Verification.Source.Claims.PassUnitSignatures

/-! # The single pass's unit theorem: the cross-module theorem

An entry of a module's interface is realized (`EntryRealized`) where its
module's plans, safe units, layout and outside contracts are given. This
module builds that realization from one step of mode 8's interface
computation (`EstablishedStep` at mode 8's prepare and check) and the
module's layout at its established units (`StepLayout`, H5a at the module),
carries it along the publication order of the modules (`linkModules`), the
module's own established slots read at the realizations of the entries it
reads, and concludes the importer's file-level theorem from the entries its
interface file holds. docs/drafts/pass-unit-theorem.md, section 7. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-- A module's units on the wire are its units' identities (proved): the
wire identity is injective at one location. -/
theorem moduleUnitId_inj {loc a b : String} (h : moduleUnitId loc a = moduleUnitId loc b) : a = b := by
  unfold moduleUnitId at h
  simp only [toString] at h
  have := congrArg String.toList h
  simp [String.toList_append] at this
  exact String.ext this

/-- Mode 8's preparation of a module in the interface computation. -/
def mode8Prepare (given : Std.HashMap String Json) : String → FilePlans → FilePlans :=
  fun location f => f.withHeadFacts (RequestCli.forModule location given) false given.isEmpty

/-- Mode 8's check of a module's group in the interface computation. -/
def mode8Check (fuel : Nat) (force : List String) (given : Std.HashMap String Json) :
    FilePlans → List Nat → List String × Except String (List String) :=
  fun f group =>
    let r := f.passGroupMode8 given.isEmpty force (fun _ => []) fuel group
      (given := some (RequestCli.moduleGiven f.fr.ast given))
    (r.1, r.2.1)

/-- **A module's layout at its established units** (H5a at the module): a
set `Sm` of the module's units, each with its wire identity in the step's
set `ok`; a layout realized by their groups, the function of the entry `e` laid out, whose outside
contracts hold. -/
structure StepLayout (fm : FilePlans) (location : String) (ok : List String) (e : Entry) where
  Sm : List String
  layout : ModuleLayout fm none Sm
  hout : OutsideContracts layout
  unit : String
  hunit : unit ∈ layout.D
  hok : ∀ u ∈ Sm, moduleUnitId location u ∈ ok
  hentry : moduleUnitId location unit = e.2.2

/-- **An entry realized from its module's step** (proved, under H1 and H2 for
the module's check): the prepared plans of a step of mode 8's interface
computation, its accepted set `ok` and a layout of the module at units of
`ok` realize the entry. -/
def entryRealized_of_step
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {budget : PositiveCertificates.SearchBudget} {force : List String} {fuel : Nat}
    {given : Std.HashMap String Json} {m : ModuleNeed} {fm₀ : FilePlans} {forced : StandIns}
    {imported : List (String × Footprints.Closed × Bool × Footprints.Closed)} {depends : List (String × List String)}
    (hplan : fragmentPlansCore m.module.document m.module.location budget (some m.names) forced force imported
      depends true true none true = .ok fm₀)
    {ok : List String} {incoming : Established} {reads : List FragmentRead} {tables : List (String × RowTable)}
    (hok : ∀ u ∈ ok, ∃ l ∈ (stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables).fr.leaders,
        moduleUnitId m.module.location ((stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables).fr.unitId l) = u ∧
        ∃ lines deps, mode8Check fuel force given (stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables)
          ((stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables).fr.group l) = (lines, .ok deps) ∧
          ∀ d ∈ deps, d ∈ ok ∨ d ∈ incoming.map (·.2.2))
    {e : Entry} (L : StepLayout (stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables) m.module.location ok e) :
    EntryRealized e where
  fm := stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables
  selection := none
  Sm := L.Sm
  hover := stepPlans_overStore (withHeadFacts_overStore (fragmentPlansCore_overStore hplan))
  hsafe := by
    intro u hu
    obtain ⟨l, hl, hid, hsafe⟩ := step_units_safe hrun hkeep hplan hok _ (L.hok u hu)
    exact ⟨l, hl, moduleUnitId_inj hid, hsafe⟩
  layout := L.layout
  hout := L.hout
  unit := L.unit
  hunit := L.hunit

/-- **A step's layouts** (H5a at each module): for every step of mode 8's
interface computation publishing `e` (its module, plans and accepted set as
`EstablishedStep` states them), a layout of the module at units of the
step's accepted set whose realization `Chosen` names. -/
def StepLayouts (budget : PositiveCertificates.SearchBudget) (force : List String) (fuel : Nat)
    (given : Std.HashMap String Json) (Chosen : (e : Entry) → EntryRealized e → Prop) (e : Entry) : Prop :=
  ∀ (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    (m : ModuleNeed) (fm₀ : FilePlans) (forced : StandIns)
    (imported : List (String × Footprints.Closed × Bool × Footprints.Closed)) (depends : List (String × List String))
    (hplan : fragmentPlansCore m.module.document m.module.location budget (some m.names) forced force imported
      depends true true none true = .ok fm₀)
    (ok : List String) (incoming : Established) (reads : List FragmentRead) (tables : List (String × RowTable))
    (hok : ∀ u ∈ ok, ∃ l ∈ (stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables).fr.leaders,
        moduleUnitId m.module.location ((stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables).fr.unitId l) = u ∧
        ∃ lines deps, mode8Check fuel force given (stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables)
          ((stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables).fr.group l) = (lines, .ok deps) ∧
          ∀ d ∈ deps, d ∈ ok ∨ d ∈ incoming.map (·.2.2)),
    e.2.2 ∈ ok →
    ∃ L : StepLayout (stepPlans (mode8Prepare given) m.module.location fm₀ reads incoming tables) m.module.location ok e,
      Chosen e (entryRealized_of_step hrun hkeep hplan hok L)

/-- **An established entry is realized** (proved, under H1 and H2 and the
module's layout): an entry a step of mode 8's interface computation
publishes has a realization `Chosen` names. -/
theorem realized_of_established
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {budget : PositiveCertificates.SearchBudget} {force : List String} {fuel : Nat}
    {given : Std.HashMap String Json} {Chosen : (e : Entry) → EntryRealized e → Prop}
    {needs : List ModuleNeed} {incoming : Established} {e : Entry}
    (hstep : EstablishedStep budget force (mode8Prepare given) (mode8Check fuel force given) needs incoming e)
    (hlay : StepLayouts budget force fuel given Chosen e) : ∃ src : EntryRealized e, Chosen e src := by
  obtain ⟨m, -, -, -, fm₀, forced, imported, depends, reads, tables, hplan, ok, he, -, hok⟩ := hstep
  obtain ⟨L, hL⟩ := hlay hrun hkeep m fm₀ forced imported depends hplan ok incoming reads tables hok he
  exact ⟨_, hL⟩

/-- **Every published entry is realized** (proved, under H1 and H2, the modules'
layouts and the publication order): over an order in which each module
reads only entries published before it, where each module publishes its
entries by steps of mode 8's interface computation and lays them out once
the entries it reads are realized, every published entry has a realization
`Chosen` names. By `linkModules`. -/
theorem entries_realized
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {budget : PositiveCertificates.SearchBudget} {force : List String} {fuel : Nat}
    {given : Std.HashMap String Json} {Chosen : (e : Entry) → EntryRealized e → Prop}
    {M : Type} (order : List M) (est reads : M → List Entry) (hord : ReadsEarlier order est reads)
    (hstep : ∀ m ∈ order, (∀ e ∈ reads m, ∃ src : EntryRealized e, Chosen e src) → ∀ e ∈ est m,
      (∃ needs incoming, EstablishedStep budget force (mode8Prepare given) (mode8Check fuel force given) needs incoming e) ∧
      StepLayouts budget force fuel given Chosen e) :
    ∀ m ∈ order, ∀ e ∈ est m, ∃ src : EntryRealized e, Chosen e src :=
  linkModules order est reads (fun e => ∃ src : EntryRealized e, Chosen e src) hord fun m hm hreads e he => by
    obtain ⟨⟨needs, incoming, hs⟩, hl⟩ := hstep m hm hreads e he
    exact realized_of_established hrun hkeep hs hl

/-- **Every entry an importer reads was published by a step** (proved,
under `InterfaceProvenance` and `EstablishProvenance`): an entry of the
interface file was returned by mode 8's interface computation and was not
among its incoming entries, so one module's step published it. -/
theorem established_of_provenance {budget : PositiveCertificates.SearchBudget} {force : List String}
    {fuel : Nat} {given : Std.HashMap String Json} {est : Established}
    (hprov : InterfaceProvenance budget force fuel given est) (hest : EstablishProvenance) :
    ∀ e ∈ est, ∃ needs incoming,
      EstablishedStep budget force (mode8Prepare given) (mode8Check fuel force given) needs incoming e := by
  intro e he
  obtain ⟨needs, incoming, tables, vs, ns, ts, est', hrun, he', hnot⟩ := hprov e he
  rcases hest needs budget force incoming _ _ est' vs ns tables ts hrun e he' with hin | ⟨est₀, hstep⟩
  · exact absurd hin hnot
  · exact ⟨needs, est₀, hstep⟩

/-- **An importer's established slots, at the chosen realizations** (H5a's
import part): each slot of kind `established e` holds, at each depth, the
function's value in every realization of `e` that `Chosen` names, read at a
type the stores agree on. -/
def ChosenSlots {f : FilePlans} {selection : Option (List String)} {S : List String}
    (m : ModuleLayout f selection S) (kinds : String → Nat → OutsideKind)
    (Chosen : (e : Entry) → EntryRealized e → Prop) : Prop :=
  ∀ u ∈ m.D, ∀ (k : Nat) v A e, (m.code u).slots[k]? = some (Slot.outside v) → (m.code u).captures[k]? = some A →
    kinds u k = .established e → ∀ src : EntryRealized e, Chosen e src →
      HoldsModuleValue src v ∧ SignatureAgrees src (graphOf f) A

/-- The chosen slots with every read entry realized are the established
slots (proved). -/
theorem establishedSlots_of_chosen {f : FilePlans} {selection : Option (List String)} {S : List String}
    {m : ModuleLayout f selection S} {kinds : String → Nat → OutsideKind}
    {Chosen : (e : Entry) → EntryRealized e → Prop}
    (hreal : ∀ u ∈ m.D, ∀ k e, kinds u k = .established e → ∃ src : EntryRealized e, Chosen e src)
    (h : ChosenSlots m kinds Chosen) : EstablishedSlots m kinds := by
  intro u hu k v A e hs hA hk
  obtain ⟨src, hsrc⟩ := hreal u hu k e hk
  exact ⟨src, h u hu k v A e hs hA hk src hsrc⟩

/-- **The cross-module theorem** (proved, under H1 and H2, the layouts of the
importer and of each module, the publication order and the per-kind
contracts of the other outside slots): for plans over their store and a set
`S` of their units each a selected unit whose group is safe, whose laid-out
functions' established slots read entries published along the order, every
function the layout lays out (the members of `S`'s groups) meets its interface at every budget and its captures meet their
types. Its premises about the published entries are what
`InterfaceProvenance` (the replay) and `EstablishProvenance` (the wrapper
lane's lemma about `establishModules`) state. -/
theorem crossModule_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    (hdrop : ReceiverDropSound) {budget : PositiveCertificates.SearchBudget}
    {force : List String} {fuel : Nat}
    {given : Std.HashMap String Json} {Chosen : (e : Entry) → EntryRealized e → Prop}
    {M : Type} (order : List M) (est reads : M → List Entry) (hord : ReadsEarlier order est reads)
    (hstep : ∀ m ∈ order, (∀ e ∈ reads m, ∃ src : EntryRealized e, Chosen e src) → ∀ e ∈ est m,
      (∃ needs incoming, EstablishedStep budget force (mode8Prepare given) (mode8Check fuel force given) needs incoming e) ∧
      StepLayouts budget force fuel given Chosen e)
    {f : FilePlans} {selection : Option (List String)} {S : List String} (hover : OverStore f)
    (hsafe : ∀ u ∈ S, ∃ i ∈ f.fr.selected selection, f.fr.unitId i = u ∧ PassUnitSafe f i)
    (layout : ModuleLayout f selection S) (kinds : String → Nat → OutsideKind)
    (hread : ∀ u ∈ layout.D, ∀ k e, kinds u k = .established e → ∃ m ∈ order, e ∈ est m)
    (hslots : ChosenSlots layout kinds Chosen) (hdecl : KindMet layout kinds (· = .declared))
    (hstand : KindMet layout kinds (· = .standIn)) (hhost : KindMet layout kinds (· = .host))
    (hcell : KindMet layout kinds (· = .moduleCell)) :
    (∀ u ∈ layout.D, ∀ n, ∀ m ≤ n, ∀ W : WorldT m, meaning (graphOf f) (layout.iface u) m W (approx layout.code n u)) ∧
    (∀ u ∈ layout.D, ∀ n (W : WorldT n), EnvOk (graphOf f) (layout.code u).captures
      (envOf ((layout.code u).captured (approx layout.code n) n) .nul) n W) := by
  have hreal := entries_realized hrun hkeep order est reads hord hstep
  have hest : EstablishedSlots layout kinds := establishedSlots_of_chosen (fun u hu k e hk => by
    obtain ⟨m, hm, he⟩ := hread u hu k e hk
    exact hreal m hm e he) hslots
  exact passPlans_safe hdrop hover hsafe layout
    (outsideContracts_of_kinds (established_met hdrop hest) hdecl hstand hhost hcell)

end Verification.SourceClaimJson.PassUnit
