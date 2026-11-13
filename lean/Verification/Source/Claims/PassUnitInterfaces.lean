import Verification.Source.Claims.PassUnitModules
import Verification.Source.RequestCli

/-! # The single pass's unit theorem: module interfaces and outside slots

The file-level theorem (`passFile_safe`) rests on the outside contracts of
a file's slots (`OutsideContracts`). This module splits them by the kind of
value a slot holds (`OutsideKind`): an import read at an entry another
module's interface establishes, a declaration-only import read at its
declared contract, an import stand-in, a host value, a module constant or
cell. It proves the file-level conclusion for any plans over their store
and any set of units whose groups the pass accepts (`passPlans_safe`), so
that a module checked by the interface computation (`establishModules`) has
the same theorem as the selected file; and that an importer's slot reading
an established entry is met where the entry's module realizes it and the
two stores agree on its signature (`entry_met`). The statements and the
hypotheses' owners are in docs/SINGLE-PASS-THEOREM.md, section 7. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-! ## Kinds of outside slots -/

/-- An entry of a module's interface: the module's location and the
function's name, its footprint, throw flag and result footprint, and its
unit's identity on the wire (`Established`'s element). -/
abbrev Entry := (String × String) × (Footprints.Closed × Bool × Footprints.Closed) × String

/-- **What an outside slot holds**: an import read at an entry of its
module's interface (`established`); an import read at its declared
contract, which a declaration-only import always is (`declared`); an import
stand-in's footprint (`standIn`); a host value
(`host`); a module constant or cell, typed by the initialization's walk
(`moduleCell`). -/
inductive OutsideKind where
  | established (e : Entry)
  | declared
  | standIn
  | host
  | moduleCell

/-- **The outside slots of a given kind are met**: every value an outside
slot of a laid-out function holds, the slot's kind satisfying `κ`, meets at each
depth the slot's type at every budget up to that depth in every world. -/
def KindMet {f : FilePlans} {selection : Option (List String)} {S : List String}
    (m : ModuleLayout f selection S) (kinds : String → Nat → OutsideKind) (κ : OutsideKind → Prop) : Prop :=
  ∀ u ∈ m.D, ∀ (k : Nat) v A, (m.code u).slots[k]? = some (Slot.outside v) → (m.code u).captures[k]? = some A →
    κ (kinds u k) → ∀ i, ∀ j ≤ i, ∀ V : WorldT j, meaning (graphOf f) A j V (v i)

/-- The established-entry slots of the kinds' table. -/
def IsEstablished : OutsideKind → Prop
  | .established _ => True
  | _ => False

/-- **The outside contracts, kind by kind** (proved): the five kinds met
give `OutsideContracts`. -/
theorem outsideContracts_of_kinds {f : FilePlans} {selection : Option (List String)} {S : List String}
    {m : ModuleLayout f selection S} {kinds : String → Nat → OutsideKind}
    (hest : KindMet m kinds IsEstablished) (hdecl : KindMet m kinds (· = .declared))
    (hstand : KindMet m kinds (· = .standIn)) (hhost : KindMet m kinds (· = .host))
    (hcell : KindMet m kinds (· = .moduleCell)) : OutsideContracts m := by
  intro u hu k v A hs hA
  cases hk : kinds u k with
  | established e => exact hest u hu k v A hs hA (by rw [hk]; trivial)
  | declared => exact hdecl u hu k v A hs hA hk
  | standIn => exact hstand u hu k v A hs hA hk
  | host => exact hhost u hu k v A hs hA hk
  | moduleCell => exact hcell u hu k v A hs hA hk

/-- **No stand-in slot, no stand-in contract** (proved): where no outside
slot is a stand-in's, as with no stand-ins supplied, the stand-ins'
contracts hold vacuously. -/
theorem standIns_vacuous {f : FilePlans} {selection : Option (List String)} {S : List String}
    {m : ModuleLayout f selection S} {kinds : String → Nat → OutsideKind}
    (hnone : ∀ u k, kinds u k ≠ .standIn) : KindMet m kinds (· = .standIn) :=
  fun u _ k _ _ _ _ hk => absurd hk (hnone u k)

/-! ## The file-level conclusion for any accepted closed set -/

/-- **The file-level conclusion for any plans and accepted units** (proved):
for plans over their store, a set `S` of units each identified with a
selected unit whose group is safe, a layout of `S` and its outside
contracts, each unit's value in the module's environment meets its
interface and its captures meet their types. `passFile_safe` is this at
mode 8's closed units; a module's interface check is this at its own. -/
theorem passPlans_safe (hdrop : ReceiverDropSound) {f : FilePlans} {selection : Option (List String)}
    {S : List String} (hover : OverStore f)
    (hsafe : ∀ u ∈ S, ∃ i ∈ f.fr.selected selection, f.fr.unitId i = u ∧ PassUnitSafe f i)
    (layout : ModuleLayout f selection S) (hout : OutsideContracts layout) :
    (∀ u ∈ layout.D, ∀ n, ∀ m ≤ n, ∀ W : WorldT m,
      meaning (graphOf f) (layout.iface u) m W (approx layout.code n u)) ∧
    (∀ u ∈ layout.D, ∀ n (W : WorldT n), EnvOk (graphOf f) (layout.code u).captures
      (envOf ((layout.code u).captured (approx layout.code n) n) .nul) n W) := by
  have hreal := layout_realizes hdrop hover hsafe layout hout
  exact ⟨fun u hu n => approx_meets hreal layout.values n u hu,
    fun u hu n W => approx_captures_envOk hreal layout.values n hu W⟩

/-- **A group the pass accepts, over any plans over their store** (proved,
under H1 and H2): every member is safe. `passUnit_safe` is this at mode 8's
plans; the interface computation's `check` is `passGroup` at a module's. -/
theorem passGroupOver_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {f : FilePlans} (hover : OverStore f) {i fuel : Nat} {compare : Bool}
    {debugNode repeats : Nat} {given : Option (Std.HashMap String Json)} {observe : Option String}
    {counting : Bool} {deps : List String}
    (haccepted : (f.passGroup fuel (f.fr.group i) compare debugNode repeats given observe counting located).2 = .ok deps) :
    PassUnitSafe f i :=
  fun j hj => member_safe (hrun _) (hkeep _) hover (passGroupChecks _ _ _ _ _ _ _ _ _ _ _ haccepted j hj)

/-! ## An importer's slot read at an established entry -/

/-- **An entry realized by its module** (the module's side of an entry):
the module's plans `fm` over their store, a set `Sm` of its units each a
selected unit whose group is safe, a layout of `Sm` whose outside contracts
hold, and the entry's function `u` laid out. `interface_entry_meets` gives the
function's value in its module's environment meeting its interface. -/
structure EntryRealized (e : Entry) where
  fm : FilePlans
  selection : Option (List String)
  Sm : List String
  hover : OverStore fm
  hsafe : ∀ u ∈ Sm, ∃ i ∈ fm.fr.selected selection, fm.fr.unitId i = u ∧ PassUnitSafe fm i
  layout : ModuleLayout fm selection Sm
  hout : OutsideContracts layout
  unit : String
  hunit : unit ∈ layout.D

/-- **Signature agreement across two stores**: every value meeting the
function's interface in its module's graph meets, at the same budget and
world, the type an importer's slot reads it at in the importer's graph. -/
def SignatureAgrees {ι : Type} [Labels ι] (src : EntryRealized e) (G : NormalGraph ι) (A : Ty ι) : Prop :=
  ∀ j (V : WorldT j) w, meaning (graphOf src.fm) (src.layout.iface src.unit) j V w → meaning G A j V w

/-- **The module's function at each depth**: the importer's slot holds, at
depth `i`, the function's value in its module's environment unfolded `i`
times. -/
def HoldsModuleValue (src : EntryRealized e) (v : Nat → Tm) : Prop :=
  ∀ i, v i = approx src.layout.code i src.unit

/-- **An interface entry meets its interface in its module** (proved, under
H1 and H2 for the module's own check): the function's value in its module's
environment, unfolded `n` times, meets its interface at every budget up to
`n`. -/
theorem interface_entry_meets (hdrop : ReceiverDropSound) (src : EntryRealized e) :
    ∀ n, ∀ m ≤ n, ∀ W : WorldT m,
      meaning (graphOf src.fm) (src.layout.iface src.unit) m W (approx src.layout.code n src.unit) :=
  (passPlans_safe hdrop src.hover src.hsafe src.layout src.hout).1 src.unit src.hunit

/-- **An importer's slot read at an established entry is met** (proved):
where the entry's module realizes it, the slot holds the module's function
at each depth and the two stores agree on its signature, the slot's value
at each depth meets the slot's type at every budget up to that depth. -/
theorem entry_met (hdrop : ReceiverDropSound) {e : Entry} (src : EntryRealized e) {ι : Type} [Labels ι] {G : NormalGraph ι} {A : Ty ι}
    {v : Nat → Tm} (hv : HoldsModuleValue src v) (hagree : SignatureAgrees src G A) :
    ∀ i, ∀ j ≤ i, ∀ V : WorldT j, meaning G A j V (v i) := by
  intro i j hj V
  rw [hv i]
  exact hagree j V _ (interface_entry_meets hdrop src i j hj V)

/-- **What an importer's established-entry slots read** (the part of H5a
stating the import slots): each slot of kind `established e` holds, at each
depth, the value of the function `e` names in a module that realizes `e`,
read at a type the module's interface agrees with. -/
def EstablishedSlots {f : FilePlans} {selection : Option (List String)} {S : List String}
    (m : ModuleLayout f selection S) (kinds : String → Nat → OutsideKind) : Prop :=
  ∀ u ∈ m.D, ∀ (k : Nat) v A e, (m.code u).slots[k]? = some (Slot.outside v) → (m.code u).captures[k]? = some A →
    kinds u k = .established e →
    ∃ src : EntryRealized e, HoldsModuleValue src v ∧ SignatureAgrees src (graphOf f) A

/-- **An importer's established-entry slots are met** (proved): the
established kind of `OutsideContracts`, discharged by the entries' modules. -/
theorem established_met (hdrop : ReceiverDropSound) {f : FilePlans} {selection : Option (List String)} {S : List String}
    {m : ModuleLayout f selection S} {kinds : String → Nat → OutsideKind}
    (h : EstablishedSlots m kinds) : KindMet m kinds IsEstablished := by
  intro u hu k v A hs hA hκ
  cases hk : kinds u k with
  | established e =>
    obtain ⟨src, hv, hagree⟩ := h u hu k v A e hs hA hk
    exact entry_met hdrop src hv hagree
  | _ => rw [hk] at hκ; exact hκ.elim

/-! ## What the interface computation's step establishes -/

/-- The plans a module's step checks (`establishStep`): the module's plans
prepared (`prepare`), each read of an entry published before it checked by
rows (`FilePlans.refuseRows`). -/
def stepPlans (prepare : String → FilePlans → FilePlans) (location : String) (fm₀ : FilePlans)
    (reads : List FragmentRead) (est : Established) (tables : List (String × RowTable)) : FilePlans :=
  (prepare location fm₀).refuseRows reads est tables

/-- A step's checked plans are over their store where the prepared plans are
(proved). -/
theorem stepPlans_overStore {prepare : String → FilePlans → FilePlans} {location : String} {fm₀ : FilePlans}
    {reads : List FragmentRead} {est : Established} {tables : List (String × RowTable)}
    (h : OverStore (prepare location fm₀)) : OverStore (stepPlans prepare location fm₀ reads est tables) :=
  refuseRows_overStore h

/-- **An entry published by one module's step** of the interface
computation (`establishStep`), stated as the exact calls: the module `m`
planned by `fragmentPlansCore` over its document, at its names, with some
stand-ins and the reads of the entries `incoming` established before it,
its interface slots lowered; then prepared (`prepare`) and its reads of
entries checked by rows (`stepPlans`); the entry's unit in a set `ok` of
wire identities, each the identity of a leader of those plans whose group
`check` accepts with every dependency in `ok` or among the units `incoming`
established; and the entry's footprint the one the module's claim of that
function states (`d.functions`, the claims the walk proposed). -/
def EstablishedStep (budget : PositiveCertificates.SearchBudget) (force : List String)
    (prepare : String → FilePlans → FilePlans)
    (check : FilePlans → List Nat → List String × Except String (List String))
    (needs : List ModuleNeed) (incoming : Established) (e : Entry) : Prop :=
  ∃ m ∈ needs, e.1.1 = m.module.location ∧ e.1.2 ∈ m.names ∧
  ∃ (fm₀ : FilePlans) (forced : StandIns) (imported : List (String × Footprints.Closed × Bool × Footprints.Closed))
    (depends : List (String × List String)) (reads : List FragmentRead) (tables : List (String × RowTable)),
    fragmentPlansCore m.module.document m.module.location budget (some m.names) forced force imported depends
      true true none true = .ok fm₀ ∧
    ∃ ok : List String, e.2.2 ∈ ok ∧
      (∃ c ∈ (stepPlans prepare m.module.location fm₀ reads incoming tables).fr.d.functions, c.name = e.1.2 ∧
        (c.footprint, c.onThrow, c.resultFootprint) = e.2.1) ∧
      ∀ u ∈ ok, ∃ l ∈ (stepPlans prepare m.module.location fm₀ reads incoming tables).fr.leaders,
        moduleUnitId m.module.location ((stepPlans prepare m.module.location fm₀ reads incoming tables).fr.unitId l) = u ∧
        ∃ lines deps, check (stepPlans prepare m.module.location fm₀ reads incoming tables)
          ((stepPlans prepare m.module.location fm₀ reads incoming tables).fr.group l) =
          (lines, .ok deps) ∧ ∀ d ∈ deps, d ∈ ok ∨ d ∈ incoming.map (·.2.2)

/-- **The interface computation's step publishes only established
entries** (the wrapper lane's lemma about `establishModules`, as
`passGroup_members` is about `passGroup`): every entry it returns was given
to it or published by a step of one of its modules. -/
def EstablishProvenance : Prop :=
  ∀ needs budget force incoming prepare check (est : Established) vs ns,
    ∀ tables (ts : List (String × RowTable)),
    establishModules needs budget force incoming prepare check tables = .ok (est, vs, ns, ts) →
    ∀ e ∈ est, e ∈ incoming ∨ ∃ est₀, EstablishedStep budget force prepare check needs est₀ e

/-- **The interface replay boundary** (trusted, the stage store): every
entry the importer decodes (`decodeInterfaces`) from the interface file it
reads was published by the interface computation of mode 8
(`RequestCli.interfaceFile`): `establishModules` over a component of the
importer's modules, from entries of the components before it, with mode 8's
prepare (each module's plans with its given head facts) and check (the
pass over each group). The forged-interface control exercises it. -/
def InterfaceProvenance (budget : PositiveCertificates.SearchBudget) (force : List String) (fuel : Nat)
    (given : Std.HashMap String Json) (est : Established) : Prop :=
  ∀ e ∈ est, ∃ needs incoming tables vs ns ts est',
    establishModules needs budget force incoming
      (fun location f => f.withHeadFacts (RequestCli.forModule location given) false given.isEmpty)
      (fun f group =>
        let r := f.passGroupMode8 given.isEmpty force (fun _ => []) fuel group
          (given := some (RequestCli.moduleGiven f.fr.ast given))
        (r.1, r.2.1)) tables
      = .ok (est', vs, ns, ts) ∧ e ∈ est' ∧ e ∉ incoming

/-- **A step's units are safe** (proved, under H1 and H2): every unit of the
set `ok` a step of mode 8's interface computation establishes is a leader
of the module's prepared plans whose group is safe. -/
theorem step_units_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {budget : PositiveCertificates.SearchBudget} {force : List String} {fuel : Nat}
    {given : Std.HashMap String Json} {m : ModuleNeed} {fm₀ : FilePlans} {forced : StandIns}
    {imported : List (String × Footprints.Closed × Bool × Footprints.Closed)} {depends : List (String × List String)}
    (hplan : fragmentPlansCore m.module.document m.module.location budget (some m.names) forced force imported
      depends true true none true = .ok fm₀)
    {ok : List String} {incoming : Established} {reads : List FragmentRead} {tables : List (String × RowTable)}
    (hok : ∀ u ∈ ok, ∃ l ∈ (stepPlans (fun location f => f.withHeadFacts (RequestCli.forModule location given) false given.isEmpty) m.module.location fm₀
          reads incoming tables).fr.leaders,
        moduleUnitId m.module.location
          ((stepPlans (fun location f => f.withHeadFacts (RequestCli.forModule location given) false given.isEmpty) m.module.location fm₀
          reads incoming tables).fr.unitId l) = u ∧
        ∃ lines deps, (fun (f : FilePlans) group =>
            let r := f.passGroupMode8 given.isEmpty force (fun _ => []) fuel group
              (given := some (RequestCli.moduleGiven f.fr.ast given))
            (r.1, r.2.1))
          (stepPlans (fun location f => f.withHeadFacts (RequestCli.forModule location given) false given.isEmpty) m.module.location fm₀
          reads incoming tables)
          ((stepPlans (fun location f => f.withHeadFacts (RequestCli.forModule location given) false given.isEmpty) m.module.location fm₀
          reads incoming tables).fr.group l) =
            (lines, .ok deps) ∧ ∀ d ∈ deps, d ∈ ok ∨ d ∈ incoming.map (·.2.2)) :
    ∀ u ∈ ok, ∃ l ∈ (stepPlans (fun location f => f.withHeadFacts (RequestCli.forModule location given) false given.isEmpty) m.module.location fm₀
          reads incoming tables).fr.selected none,
      moduleUnitId m.module.location
        ((stepPlans (fun location f => f.withHeadFacts (RequestCli.forModule location given) false given.isEmpty) m.module.location fm₀
          reads incoming tables).fr.unitId l) = u ∧
      PassUnitSafe (stepPlans (fun location f => f.withHeadFacts (RequestCli.forModule location given) false given.isEmpty) m.module.location fm₀
          reads incoming tables) l := by
  intro u hu
  obtain ⟨l, hl, hid, lines, deps, hcheck, -⟩ := hok u hu
  have hover := stepPlans_overStore (reads := reads) (est := incoming) (tables := tables)
    (prepare := fun location f => f.withHeadFacts (RequestCli.forModule location given) false given.isEmpty)
    (withHeadFacts_overStore (given := RequestCli.forModule m.module.location given) (entries := false)
      (inferred := given.isEmpty)
      (fragmentPlansCore_overStore hplan))
  refine ⟨l, ?_, hid, ?_⟩
  · simp only [Front.selected, List.filter_eq_self.mpr (fun _ _ => rfl)]; exact hl
  · have h2 := congrArg Prod.snd hcheck
    dsimp only at h2
    exact passGroupMode8_safe hrun hkeep hover h2

/-- **The file-level theorem, its outside slots by kind** (proved, under
H1 and H2, the layout H5a and, per kind of outside slot, its contract): an
established entry's slots discharged by the entry's module
(`EstablishedSlots`); a declaration-only import's, a stand-in's, a host
value's and a module cell's contracts named. With no stand-in slot the
stand-ins' contracts hold (`standIns_vacuous`). -/
theorem passFile_safe_kinds
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    (hdrop : ReceiverDropSound)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f : FilePlans}
    {givenLines : Std.HashMap String Json} {infer : Bool}
    {keep : Nat → List (Nat × List HeapKnowledge.IndexAtom)} {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool}
    (hplans : fragmentPlans ast fileKey budget selection standIns force = .ok f)
    (layout : ModuleLayout (f.withHeadFacts givenLines false infer) selection
      (closedUnits (fileVerdicts f selection givenLines infer force keep fuel compare debugNode repeats given observe counting located)))
    (kinds : String → Nat → OutsideKind)
    (hest : EstablishedSlots layout kinds) (hdecl : KindMet layout kinds (· = .declared))
    (hstand : KindMet layout kinds (· = .standIn)) (hhost : KindMet layout kinds (· = .host))
    (hcell : KindMet layout kinds (· = .moduleCell)) :
    let S := closedUnits (fileVerdicts f selection givenLines infer force keep fuel compare debugNode repeats given observe counting located)
    (∀ u ∈ S, ∃ i ∈ f.fr.selected selection, f.fr.unitId i = u ∧ PassUnitSafe (f.withHeadFacts givenLines false infer) i) ∧
    (∀ u ∈ layout.D, ∀ n, ∀ m ≤ n, ∀ W : WorldT m,
      meaning (graphOf (f.withHeadFacts givenLines false infer)) (layout.iface u) m W (approx layout.code n u)) ∧
    (∀ u ∈ layout.D, ∀ n (W : WorldT n), EnvOk (graphOf (f.withHeadFacts givenLines false infer)) (layout.code u).captures
      (envOf ((layout.code u).captured (approx layout.code n) n) .nul) n W) :=
  passFile_safe hrun hkeep hdrop hplans layout
    (outsideContracts_of_kinds (established_met hdrop hest) hdecl hstand hhost hcell)

/-! ## Mode 8's plans as the command line computes them -/

/-- **Importer plans from interfaces are over their store** (proved): both
branches of `fragmentPlansOfInterfaces` return the core planner's plans, the
rows check (`refuseRows`) and the unbound-import check (`refuseUnbound`)
refusing plans and keeping the rest. -/
theorem fragmentPlansFromInterfaces_overStore {ast : Json} {fileKey : String}
    {budget : PositiveCertificates.SearchBudget} {names : Option (List String)} {standIns : StandIns}
    {force : List String} {est : Established} {tables : List (String × RowTable)}
    {front : Option (Json × Front)} {known : List (String × Option StandIn)} {f : FilePlans}
    (h : fragmentPlansFromInterfaces ast fileKey budget names standIns force est tables front known = .ok f) :
    OverStore f := by
  unfold fragmentPlansFromInterfaces at h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨f₁, h₁, h⟩ := except_bind_ok h
  cases h
  apply refuseUnbound_overStore
  unfold fragmentPlansOfInterfaces at h₁
  by_cases he : est.isEmpty = true
  · rw [if_pos he] at h₁
    exact fragmentPlansCore_overStore h₁
  · rw [if_neg he] at h₁
    obtain ⟨_, -, h₁⟩ := except_bind_ok h₁
    obtain ⟨_, -, h₁⟩ := except_bind_ok h₁
    obtain ⟨_, h₂, h₁⟩ := except_bind_ok h₁
    cases h₁
    exact refuseRows_overStore (fragmentPlansCore_overStore h₂)

/-- **Plans with modules checked in the invocation are over their store**
(proved): `fragmentPlansWithModules` returns importer plans from the
entries its components establish. -/
theorem fragmentPlansWithModules_overStore {ast : Json} {fileKey : String}
    {budget : PositiveCertificates.SearchBudget} {names : Option (List String)} {standIns : StandIns}
    {force : List String} {prepare : String → FilePlans → FilePlans}
    {check : FilePlans → List Nat → List String × Except String (List String)}
    {f : FilePlans} {ms : List ModuleVerdict} {notes : List String}
    (h : fragmentPlansWithModules ast fileKey budget names standIns force prepare check = .ok (f, ms, notes)) :
    OverStore f := by
  unfold fragmentPlansWithModules at h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok h
  obtain ⟨f', hf', h⟩ := except_bind_ok h
  cases h
  exact fragmentPlansFromInterfaces_overStore hf'

/-- The false start fact keeps the store every plan is over (proved). -/
theorem withFalseStartFact_overStore {f : FilePlans} (h : OverStore f) : OverStore f.withFalseStartFact := by
  intro i name pos r hi
  unfold PlanAt FilePlans.withFalseStartFact at hi
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨p, hp, he⟩ := hi
  cases p with
  | error _ => cases he
  | ok q =>
    cases q with
    | graph n ps r₀ =>
      simp only [Except.map, Except.ok.injEq] at he
      injection he with h1 h2 h3
      subst h1 h2 h3
      exact h i _ _ r₀ hp

/-- Mode 8's preparation of the planned file (`verifyUnitsFile`): its given
head facts, with `infer` beside the proposals inference recorded, then the
false start fact where `TSCERT_FORCE` names `start-facts`. -/
def preparedMode8 (force : List String) (givenLines : Std.HashMap String Json) (infer : Bool) (f : FilePlans) :
    FilePlans :=
  if force.contains "start-facts" then (f.withHeadFacts givenLines false infer).withFalseStartFact
  else f.withHeadFacts givenLines false infer

/-- **The headline at the command line's exact condition** (proved, under
H1 and H2): mode 8 plans the file from the interfaces it reads
(`fragmentPlansFromInterfaces`) or with its modules checked in the
invocation (`fragmentPlansWithModules`), prepares it, and prints a selected
unit accepted where its check (`passGroupMode8`) accepts its group; every
member of that group is safe. -/
theorem passUnitCli_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f₀ : FilePlans}
    {prepare : String → FilePlans → FilePlans}
    {check : FilePlans → List Nat → List String × Except String (List String)}
    {givenLines : Std.HashMap String Json} {infer : Bool}
    {keep : Nat → List (Nat × List HeapKnowledge.IndexAtom)} {i fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting located : Bool} {deps : List String}
    (hplanned : (∃ est tables front known, fragmentPlansFromInterfaces ast fileKey budget selection standIns force est tables front known = .ok f₀) ∨
      (∃ ms notes, fragmentPlansWithModules ast fileKey budget selection standIns force prepare check =
        .ok (f₀, ms, notes)))
    (haccepted : ((preparedMode8 force givenLines infer f₀).passGroupMode8 infer force keep fuel
      ((preparedMode8 force givenLines infer f₀).fr.group i) compare debugNode repeats given observe counting
      located).2.1 = .ok deps) :
    PassUnitSafe (preparedMode8 force givenLines infer f₀) i := by
  have h0 : OverStore f₀ := by
    rcases hplanned with ⟨est, tables, front, known, h⟩ | ⟨ms, notes, h⟩
    · exact fragmentPlansFromInterfaces_overStore h
    · exact fragmentPlansWithModules_overStore h
  have hover : OverStore (preparedMode8 force givenLines infer f₀) := by
    unfold preparedMode8
    split
    · exact withFalseStartFact_overStore (withHeadFacts_overStore h0)
    · exact withHeadFacts_overStore h0
  exact passGroupMode8_safe hrun hkeep hover haccepted

end Verification.SourceClaimJson.PassUnit
