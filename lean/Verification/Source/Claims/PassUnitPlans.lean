import Verification.Source.Claims.PassUnitCodes

/-! # The single pass's unit theorem: what mode 8's plans are built with

Construction facts of `fragmentPlans` and `FilePlans.withHeadFacts` the
unit theorem reads: every plan is over the file's frozen store
(`fragmentPlans_overStore`), so the pass's graph and image check are each
request's own; mode 8 plans no module run (`fragmentPlans_modules`), so a
unit's dependencies name units of its file alone. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore

/-- A request over a file's frozen store. -/
abbrev Req (f : FilePlans) : Type :=
  SourceRequest (EquationStore.Checked f.F.equations f.F.primitive) (EquationStore.CheckedLabel f.F.equations f.F.primitive)

/-- The plan of unit `i` of `f` is the graph request `r`. -/
def PlanAt (f : FilePlans) (i : Nat) (name : String) (pos : Span) (r : Req f) : Prop :=
  f.plans[i]? = some (Except.ok (FunctionPlan.graph name pos r))

/-- The plan of unit `i` of `f` is the framed plan of the request `r` with
the proposals `spec`. -/
def FramedPlanAt (f : FilePlans) (i : Nat) (name : String) (pos : Span) (r : Req f)
    (spec : FramedSpec (EquationStore.CheckedLabel f.F.equations f.F.primitive)) : Prop :=
  f.plans[i]? = some (Except.ok (FunctionPlan.framed name pos r spec))

/-- The plan of unit `i` of `f` is the callback-demand plan of the request `r`
with specification `spec`. -/
def CallbackDemandsPlanAt (f : FilePlans) (i : Nat) (name : String) (pos : Span) (r : Req f)
    (spec : CallbackDemands.CallbackDemandSpec) : Prop :=
  f.plans[i]? = some (Except.ok (FunctionPlan.callbackDemands name pos r spec))

/-- Every plan of `f`, a graph plan, framed plan or callback-demand plan, is
over `f`'s frozen store: its request's store is the file's. -/
def OverStore (f : FilePlans) : Prop :=
  ∀ (i : Nat) (p : FunctionPlan (EquationStore.Checked f.F.equations f.F.primitive)
      (EquationStore.CheckedLabel f.F.equations f.F.primitive)),
    f.plans[i]? = some (Except.ok p) → p.parts.2.2.types = f.F.store

/-- A graph plan of a file over its store has the file's store. -/
theorem OverStore.graph {f : FilePlans} (h : OverStore f) {i name pos} {r : Req f} (hp : PlanAt f i name pos r) :
    r.types = f.F.store :=
  h i _ hp

/-- A framed plan of a file over its store has the file's store. -/
theorem OverStore.framed {f : FilePlans} (h : OverStore f) {i name pos} {r : Req f} {spec}
    (hp : FramedPlanAt f i name pos r spec) : r.types = f.F.store :=
  h i _ hp

/-- A callback-demand plan of a file over its store has the file's store. -/
theorem OverStore.callbackDemands {f : FilePlans} (h : OverStore f) {i name pos} {r : Req f} {spec}
    (hp : CallbackDemandsPlanAt f i name pos r spec) : r.types = f.F.store :=
  h i _ hp

/-- A request over the frozen equations has their store. -/
theorem over_types {F : EquationStore.Frozen} {r : SourceRequest EquationStore.State EquationGraphs.Tree} {r'}
    (h : SourceRequest.over F r = .ok r') : r'.types = F.store := by
  unfold SourceRequest.over at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | (injection h with h; subst h; rfl)

/-- A plan over the frozen equations, a graph plan or a framed plan, has
their store. -/
theorem planOver_types {F : EquationStore.Frozen} {e : Except String (FunctionPlan EquationStore.State EquationGraphs.Tree)}
    {p} (h : e.bind (FunctionPlan.over F) = .ok p) : p.parts.2.2.types = F.store := by
  cases e with
  | error _ => cases h
  | ok p₀ =>
    cases p₀ with
    | graph n ps r₀ =>
      simp only [Except.bind, FunctionPlan.over, bind, pure, Except.pure] at h
      cases hr : SourceRequest.over F r₀ with
      | error _ => rw [hr] at h; cases h
      | ok r₁ =>
        rw [hr] at h
        injection h with h
        subst h
        exact over_types hr
    | framed n ps r₀ spec =>
      simp only [Except.bind, FunctionPlan.over, bind, pure, Except.pure] at h
      cases hr : SourceRequest.over F r₀ with
      | error _ => rw [hr] at h; cases h
      | ok r₁ =>
        rw [hr] at h
        cases hs : spec.over F with
        | error _ => rw [hs] at h; cases h
        | ok _ =>
          rw [hs] at h
          injection h with h
          subst h
          exact over_types hr
    | callbackDemands n ps r₀ spec =>
      simp only [Except.bind, FunctionPlan.over, bind, pure, Except.pure] at h
      cases hr : SourceRequest.over F r₀ with
      | error _ => rw [hr] at h; cases h
      | ok r₁ =>
        rw [hr] at h
        injection h with h
        subst h
        exact over_types hr

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {k : α → Except ε β} {b : β}
    (h : (x >>= k) = .ok b) : ∃ a, x = .ok a ∧ k a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **The core planner's result** (proved), at every value of its
arguments (the imported footprints, dependencies, closure, proposal flag and
front given and the interface slots included): its import plan has no module run, and its plans are
plans over its frozen store. -/
theorem fragmentPlansCore_shape {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {names : Option (List String)} {standIns : StandIns} {force : List String}
    {imported : List (String × Footprints.Closed × Bool × Footprints.Closed)} {depends : List (String × List String)}
    {closure proposed : Bool} {front : Option (Json × Front)} {interfaceSlots : Bool}
    {known : List (String × Option StandIn)} {memo : ProposalMemo} {f : FilePlans}
    (h : fragmentPlansCore ast fileKey budget names standIns force imported depends closure proposed front
      interfaceSlots known memo = .ok f) :
    f.p.modules = [] ∧ ∃ plans₀ : List (Except String (FunctionPlan EquationStore.State EquationGraphs.Tree)),
      f.plans = plans₀.map fun e => e.bind (FunctionPlan.over f.F) := by
  unfold fragmentPlansCore at h
  cases front with
  | none =>
    dsimp only at h
    repeat (obtain ⟨_, -, h⟩ := except_bind_ok h)
    cases h; exact ⟨rfl, _, rfl⟩
  | some p =>
    obtain ⟨claims, fr⟩ := p
    dsimp only at h
    by_cases hc : (standIns.functions.isEmpty && standIns.imports.isEmpty) = true
    · rw [ite_eq_left hc] at h
      repeat (obtain ⟨_, -, h⟩ := except_bind_ok h)
      cases h; exact ⟨rfl, _, rfl⟩
    · rw [ite_eq_right hc] at h
      repeat (obtain ⟨_, -, h⟩ := except_bind_ok h)
      cases h; exact ⟨rfl, _, rfl⟩

/-- **The core planner's plans are over its frozen store** (proved), at
every value of its arguments. -/
theorem fragmentPlansCore_overStore {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {names : Option (List String)} {standIns : StandIns} {force : List String}
    {imported : List (String × Footprints.Closed × Bool × Footprints.Closed)} {depends : List (String × List String)}
    {closure proposed : Bool} {front : Option (Json × Front)} {interfaceSlots : Bool}
    {known : List (String × Option StandIn)} {memo : ProposalMemo} {f : FilePlans}
    (h : fragmentPlansCore ast fileKey budget names standIns force imported depends closure proposed front
      interfaceSlots known memo = .ok f) :
    OverStore f := by
  obtain ⟨-, plans₀, hp⟩ := fragmentPlansCore_shape h
  intro i p hi
  simp only [hp, List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨e, -, he⟩ := hi
  exact planOver_types he

/-- **Mode 8's plans are over its frozen store** (proved). -/
theorem fragmentPlans_overStore {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {names : Option (List String)} {standIns : StandIns} {force : List String} {f : FilePlans}
    (h : fragmentPlans ast fileKey budget names standIns force = .ok f) : OverStore f :=
  fragmentPlansCore_overStore h

/-- **The core planner plans no module run** (proved), at every value of
its arguments. -/
theorem fragmentPlansCore_modules {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {names : Option (List String)} {standIns : StandIns} {force : List String}
    {imported : List (String × Footprints.Closed × Bool × Footprints.Closed)} {depends : List (String × List String)}
    {closure proposed : Bool} {front : Option (Json × Front)} {interfaceSlots : Bool}
    {known : List (String × Option StandIn)} {memo : ProposalMemo} {f : FilePlans}
    (h : fragmentPlansCore ast fileKey budget names standIns force imported depends closure proposed front
      interfaceSlots known memo = .ok f) :
    f.p.modules = [] :=
  (fragmentPlansCore_shape h).1

/-- **Mode 8 plans no module run** (proved): its import plan's module runs
are empty, so `FilePlans.dependencies` names the file's units alone. -/
theorem fragmentPlans_modules {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {names : Option (List String)} {standIns : StandIns} {force : List String} {f : FilePlans}
    (h : fragmentPlans ast fileKey budget names standIns force = .ok f) : f.p.modules = [] :=
  fragmentPlansCore_modules h

/-- **A plan transform changing requests alone keeps the store** (proved):
plans `P` of which each is a plan of `f` at the same index, its request
changed by a map keeping the store, are over `f`'s store where `f`'s are. -/
theorem overStore_of_mapRequest {f : FilePlans} {P : List (Except String (FunctionPlan
      (EquationStore.Checked f.F.equations f.F.primitive) (EquationStore.CheckedLabel f.F.equations f.F.primitive)))}
    (hP : ∀ (i : Nat) x, P[i]? = some (Except.ok x) → ∃ x₀ g, f.plans[i]? = some (Except.ok x₀) ∧
      x = x₀.mapRequest g ∧ (g x₀.parts.2.2).types = x₀.parts.2.2.types) (h : OverStore f) :
    OverStore { f with plans := P } := by
  intro i p hi
  obtain ⟨x₀, g, h₀, rfl, hg⟩ := hP i p hi
  rw [FunctionPlan.parts_mapRequest]
  exact hg.trans (h i x₀ h₀)

/-- Head facts keep the store every plan is over (proved): they change each
plan's request's candidates and code sources alone. -/
theorem withHeadFacts_overStore {f : FilePlans} {given : Std.HashMap String Json} {entries inferred : Bool}
    (h : OverStore f) : OverStore (f.withHeadFacts given entries inferred) := by
  refine overStore_of_mapRequest (fun i x hx => ?_) h
  simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_eq_some_iff] at hx
  obtain ⟨⟨p, j⟩, hp, he⟩ := hx
  simp only [Prod.mk.injEq] at hp
  obtain ⟨p', hp', rfl, rfl⟩ := hp
  cases p' with
  | error _ => cases he
  | ok q =>
    simp only [Except.map, Except.ok.injEq] at he
    exact ⟨q, _, hp', he.symm, rfl⟩

/-- Plans `P` keep the store of `f` where each request plan of `P` is one of
`f`'s at the same index (proved). -/
theorem overStore_of_plans {f : FilePlans} {P : List (Except String (FunctionPlan
      (EquationStore.Checked f.F.equations f.F.primitive) (EquationStore.CheckedLabel f.F.equations f.F.primitive)))}
    (hP : ∀ (i : Nat) x, P[i]? = some (Except.ok x) → f.plans[i]? = some (Except.ok x)) (h : OverStore f) :
    OverStore { f with plans := P } := by
  intro i p hi
  exact h i p (hP i _ hi)

/-- **The rows check refuses plans, nothing else** (proved): `refuseRows`
keeps every field but the plans, and each request plan it returns is the
one at its index. -/
theorem refuseRows_plans (f : FilePlans) (reads : List FragmentRead) (est : Established)
    (tables : List (String × RowTable)) :
    ∃ P, f.refuseRows reads est tables = { f with plans := P } ∧
      ∀ (i : Nat) x, P[i]? = some (Except.ok x) → f.plans[i]? = some (Except.ok x) := by
  unfold FilePlans.refuseRows
  dsimp only
  split
  · exact ⟨f.plans, rfl, fun _ _ h => h⟩
  · refine ⟨_, rfl, ?_⟩
    intro i x h
    simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, j⟩, hp, he⟩ := h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨p', hp', rfl, rfl⟩ := hp
    cases p' with
    | error _ => cases he
    | ok q =>
      simp only [Except.bind] at he
      split at he
      · cases he
      · cases he; exact hp'

/-- **The unbound-import check refuses plans, nothing else** (proved). -/
theorem refuseUnbound_plans (f : FilePlans) (unbound : List (String × List (String × String))) :
    ∃ P, f.refuseUnbound unbound = { f with plans := P } ∧
      ∀ (i : Nat) x, P[i]? = some (Except.ok x) → f.plans[i]? = some (Except.ok x) := by
  unfold FilePlans.refuseUnbound
  dsimp only
  split
  · exact ⟨f.plans, rfl, fun _ _ h => h⟩
  · refine ⟨_, rfl, ?_⟩
    intro i x h
    simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_eq_some_iff] at h
    obtain ⟨⟨p, j⟩, hp, he⟩ := h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨p', hp', rfl, rfl⟩ := hp
    dsimp only at he
    split at he
    · subst he; exact hp'
    · cases he

theorem refuseRows_overStore {f : FilePlans} {reads : List FragmentRead} {est : Established}
    {tables : List (String × RowTable)} (h : OverStore f) : OverStore (f.refuseRows reads est tables) := by
  obtain ⟨P, hP, hk⟩ := refuseRows_plans f reads est tables
  rw [hP]; exact overStore_of_plans hk h

theorem refuseUnbound_overStore {f : FilePlans} {unbound : List (String × List (String × String))}
    (h : OverStore f) : OverStore (f.refuseUnbound unbound) := by
  obtain ⟨P, hP, hk⟩ := refuseUnbound_plans f unbound
  rw [hP]; exact overStore_of_plans hk h

end Verification.SourceClaimJson.PassUnit
