import Verification.Source.Claims.PassUnitPlans
import Verification.Programs.TolerantFramesComposeYields

/-! # The single pass's unit theorem: a member and the headline

What `FilePlans.passGroup` establishes of a member it accepts, stated as
`MemberAccepted` (the wrapper's checks, each the exact call or condition
the wrapper makes), the theorem that such a member is safe
(`member_safe`, under `RunSound` and `RunKeepsSummaries`), and the
headline from mode 8's exact acceptance condition (`passUnit_safe`). -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore
open PositiveCertificates (InstanceImageCheck)
open HeapExpressionRules (Checker)
open CertificateProducer (Answered)

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- The bound the main graph's run is given, as `passGroup` computes it
(`bounded`): none for the footprint letting everything change on normal
return alone, none for a pure graph promising no fresh result, the claimed
footprint, fresh flag and throw flag otherwise (`RunBound.ofRequest`). -/
def mainBound (r : SourceRequest σ ι) : Option RunBound :=
  if (!(r.footprint == .top && !r.onThrow && !r.fresh) &&
      !(!r.fresh && r.program.all fun n => Purity.pureTerm n.expression)) = true then
    some (RunBound.ofRequest r.footprint r.onThrow r.fresh)
  else none

/-- The regional option the unit's stated regions give the run (`regionalOf
"regional"`): their bound and regions, a throw bounded where the stated
effect bounds one. -/
def regionalSpec (r : SourceRequest σ ι) :
    Option (Footprints.Closed × List Footprints.ArgumentSpineRegion × Bool) :=
  r.regional.map fun (Φ, regions) => (Φ, regions, r.stated.any (·.onThrow))

/-- The read summaries a run leaves, checked as `passGroup` checks them
(`validSummary`, `checkReadSummariesResult`) over the request's graph and
image check. -/
def summariesChecked (r : SourceRequest σ ι) (sums : List (ProgramCertificates.ReadSummary ι)) : Bool :=
  sums.all (RequestJson.validSummary (StoreView.valid r.types)) &&
    (ProgramCertificates.checkReadSummariesResult (RequestJson.graph r.toRequest) (StoreView.images r.types)
      sums).accepted

/-- The declared effect's conditions `passGroup` checks first. -/
def declaredEffect (r : SourceRequest σ ι) : Bool :=
  RequestJson.asyncEffects r.async r.footprint && (!r.async || !r.fresh) &&
    RequestJson.statedWithin r.async r.footprint r.onThrow r.fresh r.stated

/-- A call of the pass over a request's own graph, as `passGroup` makes it:
the request's program, claims, start, inputs, goal, assertions, entry
indices, postcondition and entry separation, the codes `codes` admits, the
pass checker `checker`, from the answers `a`. -/
def MainCall {G : NormalGraph ι} {I : InstanceImageCheck G} (r : SourceRequest σ ι) (c : RunCall G I)
    (codes : CodeEntry ι → Bool) (checker : SinglePass.PassChecker G I) (a : Answered G) : Prop :=
  c.P = r.program ∧ c.claims = r.claims ∧ c.start = r.start ∧ c.inputs = r.inputs ∧ c.goal = r.goal ∧
    c.assertions = r.assertions ∧
    c.entryIndices = r.entryIndices ∧ c.codes = codes ∧ c.passChecker = checker ∧ c.answers = a ∧
    c.ensures = r.ensures ∧ c.entrySeparation = r.entrySeparation

/-- **A run accepted at framed nodes `fr`**: its walk accepted, framing
those nodes. -/
def _root_.Verification.TolerantFrames.Target.RunCall.AcceptsAt {G : NormalGraph ι} {I : InstanceImageCheck G}
    (c : RunCall G I) (after : Answered G) (fr : List (Nat × List Footprints.Footprint)) : Prop :=
  c.AcceptsWalk after ∧ c.framed = fr

/-- **The main graph accepted** as `passGroup` accepts it, its walks framing
the nodes `fr`: directly, at its bound and stated regions; or, the bound
refused and the fallback allowed (`fb`), by the footprint's regional
fallback (no regions), followed by the stated regions' run where it states
any. Each accepted run's read summaries checked. -/
inductive MainAcceptedAt (G : NormalGraph ι) (I : InstanceImageCheck G) (r : SourceRequest σ ι)
    (codes : CodeEntry ι → Bool) (fr : List (Nat × List Footprints.Footprint)) (fb : Bool) (a : Answered G) : Prop where
  | direct (c : RunCall G I) (after : Answered G) :
      MainCall r c codes .ordinary a → c.bound = mainBound r → regionOf c.regional = regionalSpec r →
      c.AcceptsAt after fr → summariesChecked r after.summaries.toList = true → MainAcceptedAt G I r codes fr fb a
  | fallback (c₁ : RunCall G I) (a₁ : Answered G) : fb = true →
      r.fresh = false → MainCall r c₁ codes .ordinary a → c₁.bound = none →
      regionOf c₁.regional = some (r.footprint, [], r.onThrow) → c₁.AcceptsAt a₁ fr →
      summariesChecked r a₁.summaries.toList = true →
      (r.regional = none ∨ ∃ (c₂ : RunCall G I) (a₂ : Answered G), MainCall r c₂ codes .ordinary a ∧
        c₂.bound = none ∧ regionOf c₂.regional = regionalSpec r ∧ c₂.AcceptsAt a₂ fr ∧
        summariesChecked r a₂.summaries.toList = true) →
      MainAcceptedAt G I r codes fr fb a

/-- **The main graph accepted** as `passGroup` accepts it: framing no node,
directly or by the fallback (`MainAcceptedAt`). -/
abbrev MainAccepted (G : NormalGraph ι) (I : InstanceImageCheck G) (r : SourceRequest σ ι)
    (codes : CodeEntry ι → Bool) (a : Answered G) : Prop :=
  MainAcceptedAt G I r codes [] true a

end


/-- **A framed member as the pass accepts it** (the draft, "What the pass
checks"): the binding checks that read its component alone passing
(`componentBindingRefusal` at the plan's fields refusing nothing,
`componentBindingRefusal_none`); its code requests accepted in order by
the ordinary pass (`CodesAccepted`); each stated region meeting its entry
conditions; its main graph, over the codes' table, its walk accepted at
its bound and stated regions (`RunCall.AcceptsWalk`) at the plan's framed
nodes (`c.framed`), its read summaries checked; the binding checks that
read its request before its walk (`FramedSpec.bindingB`: `entryB`,
`codesCoverB` at the request's code, `entryFnB`, `clientsB`,
`protocolAtLeastB`, `roPositionsB` at the member `name`, `readOnlyB`, `arityB`, the framed nodes the
flow's); and the checks that read the request after its walk
(`FramedSpec.requestB`, each framed node's callee's stated effect read by
`callEffects`). -/
structure FramedAccepted (f : FilePlans) (name : String) (r : Req f)
    (spec : FramedSpec (EquationStore.CheckedLabel f.F.equations f.F.primitive)) : Prop where
  codes : ∃ a₀ a₁ : Answered (StoreView.graph f.F.store),
    CodesAccepted (StoreView.graph f.F.store) (StoreView.images f.F.store) r [] r.codes.zipIdx a₀ a₁ ∧
      ∃ (c : RunCall (StoreView.graph f.F.store) (StoreView.images f.F.store))
        (after : Answered (StoreView.graph f.F.store)),
        MainCall r c (GraphCode.admits (r.codes.map (·.entry))) .ordinary a₁ ∧ c.bound = mainBound r ∧
        regionOf c.regional = regionalSpec r ∧ c.AcceptsWalk after ∧
        summariesChecked r after.summaries.toList = true ∧ c.framed = spec.framed
  regions : ∀ Φ regions, r.regional = some (Φ, regions) →
    GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions = true
  component : componentBindingRefusal spec.checked spec.lay spec.codes spec.C = none
  binding : spec.bindingB name r = true
  request : spec.requestB r (callEffects (StoreView.graph f.F.store) r) = true

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]
open Verification.TolerantFrames.ReadOnly

/-- **The binding checks of a request are its checks, each passing**
(proved, by their definition). -/
theorem _root_.Verification.SourceClaimJson.FramedSpec.bindingB_iff {spec : FramedSpec ι} {name : String}
    {r : SourceRequest σ ι} :
    spec.bindingB name r = true ↔
      (spec.inner = true ∨ spec.checked.entryB (realizedCode r) ((realizedCode r).1.length - 1) = true) ∧
      codesCoverB spec.checked [requestCode r] = true ∧
      entryFnB spec.checked (realizedCode r) ((realizedCode r).1.length - 1)
        ((List.range (r.siblings.length + 1)).map (capSlot spec.arity false 0 + ·)) = true ∧
      clientsB spec.theta (componentRows spec.family spec.C) = true ∧
      protocolAtLeastB (flowSites spec.checked) (partsKeys spec.psiDef) (protocolOfParts id (partsIndex spec.psiDef))
        (protocolOfParts id (partsIndex spec.psi)) = true ∧
      spec.roPositionsB name r = true ∧ readOnlyB r.inputs spec.readOnly spec.roPositions spec.outType = true ∧
      spec.arityB r = true ∧ spec.framed.map (·.1) = framedCallNodes spec.checked spec.host (realizedCode r) ∧
      spec.inner = innerB spec.checked spec.entries name (realizedCode r) := by
  simp [FramedSpec.bindingB, FramedSpec.bindingChecks]

/-- **The frame's client obligation is the checked file's `@clients`
rows'** (proved, `clientsB_sound`): where the binding checks pass, the
frame's $`\Theta_C`$ is, at every part, the rows' of the exported types
of `C`'s module in the family the declaration document describes, which
state class keys only. -/
theorem _root_.Verification.SourceClaimJson.FramedSpec.theta_rows {spec : FramedSpec ι} {name : String}
    {r : SourceRequest σ ι} (h : spec.bindingB name r = true) :
    clientsByKindB (componentRows spec.family spec.C) = true ∧
      ∀ p, spec.Θ p = rowsTheta (componentRows spec.family spec.C) p :=
  let hc := clientsB_sound (FramedSpec.bindingB_iff.mp h).2.2.2.1
  ⟨hc.1, fun p => hc.2 p⟩

/-- **The read-only positions are those every function sharing the
realized code declares** (proved, by `roPositionsB`): position `j` is
read-only exactly when it is below the arity and the member and every
module function of `C` whose code is the realized code declare it
read-only throughout. -/
theorem _root_.Verification.SourceClaimJson.FramedSpec.roPositionsB_sound {spec : FramedSpec ι} {name : String}
    {r : SourceRequest σ ι} (h : spec.roPositionsB name r = true) (j : Nat) :
    spec.roPos j = true ↔ j < spec.arity ∧ declaredReadOnly spec.family spec.C name j = true ∧
      ∀ m n, (m, n) ∈ spec.codes.zip spec.names → m = realizedCode r →
        declaredReadOnly spec.family spec.C n.1 j = true := by
  simp only [FramedSpec.roPositionsB, beq_iff_eq] at h
  simp only [FramedSpec.roPos, h, readOnlyPositions, sharingReadOnlyB]
  by_cases hj : j < spec.arity
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
    refine ⟨fun ⟨h1, h2⟩ => ⟨hj, h1, fun m n hm he => (h2 (m, n) hm).resolve_left (by simpa using he)⟩,
      fun ⟨_, h1, h2⟩ => ⟨h1, fun ⟨m, n⟩ hm => ?_⟩⟩
    by_cases he : m = realizedCode r
    · exact .inr (h2 m n hm he)
    · exact .inl he
  · simp [List.getD_eq_getElem?_getD, hj]

/-- **A crossing recorded read-only is at a declared read-only position**
(proved, by `roPositionsB` and `readOnlyB`): every crossing an entering
step records at a type the frame's view reads read-only is the argument at
a position `j` below the arity, at its declared type, which the member and
every module function of `C` sharing the realized code declare read-only
throughout. -/
theorem _root_.Verification.SourceClaimJson.FramedSpec.readOnly_declared {spec : FramedSpec ι} {name : String}
    {r : SourceRequest σ ι} (h : spec.bindingB name r = true) {t t' : Tm} {c : Crossing spec.view.view}
    (hc : c ∈ spec.entryXs r t t') (hro : spec.view.RO c.ty) :
    ∃ j, c.ty = r.inputs.getD j spec.outType ∧ j < spec.arity ∧ declaredReadOnly spec.family spec.C name j = true ∧
      ∀ m n, (m, n) ∈ spec.codes.zip spec.names → m = realizedCode r →
        declaredReadOnly spec.family spec.C n.1 j = true := by
  obtain ⟨-, -, -, -, -, hpos, hro', -, -⟩ := FramedSpec.bindingB_iff.mp h
  have hout : ¬ spec.view.RO spec.outType := by
    intro hm
    have h3 : (!spec.readOnly.contains spec.outType) = true := by
      simp only [readOnlyB, Bool.and_eq_true] at hro'; exact hro'.2
    have h4 : spec.readOnly.contains spec.outType = true :=
      List.contains_iff_mem.mpr (show spec.outType ∈ spec.readOnly from hm)
    rw [h4] at h3; cases h3
  have hj : ∃ j, c.ty = spec.entryTy r j := by
    unfold FramedSpec.entryXs at hc
    split at hc
    · split at hc
      · obtain ⟨j, _, rfl⟩ := List.mem_mapIdx.mp hc; exact ⟨j, rfl⟩
      · obtain ⟨j, _, rfl⟩ := List.mem_mapIdx.mp hc; exact ⟨j, rfl⟩
      · cases hc
    · cases hc
  obtain ⟨j, hty⟩ := hj
  unfold FramedSpec.entryTy at hty
  split at hty
  · rename_i hr
    exact ⟨j, hty, (FramedSpec.roPositionsB_sound hpos j).mp hr⟩
  · rw [hty] at hro; exact (hout hro).elim

/-- **The frame's framed nodes are the flow's framed call nodes** (proved,
by the binding check): the nodes of the realized code whose call may
reach outside code at some context of the checked flow. -/
theorem _root_.Verification.SourceClaimJson.FramedSpec.framed_nodes {spec : FramedSpec ι} {name : String}
    {r : SourceRequest σ ι} (h : spec.bindingB name r = true) :
    spec.framed.map (·.1) = framedCallNodes spec.checked spec.host (realizedCode r) :=
  (FramedSpec.bindingB_iff.mp h).2.2.2.2.2.2.2.2.1

/-- **The entry of the realized code is an entry of the checked flow**,
at a function checked at its entry (proved, `FFlow.entryB_sound`,
`entryFnB_sound`, `codesCoverB_sound`):
its proposal at the entry context holds what outside code may supply at
every slot of its entry node and returns within `O`, names signatures
there only at the sibling slots and the closure's own, and the request's
code has a proposal at the entry context. -/
theorem _root_.Verification.SourceClaimJson.FramedSpec.entry_checked {spec : FramedSpec ι} {name : String}
    {r : SourceRequest σ ι} (h : spec.bindingB name r = true) (hi : spec.inner = false) :
    (∃ π, spec.checked.flow.code (realizedCode r) entryCx = some π ∧
      (∀ i, Supplied spec.checked.flow (π.env ((realizedCode r).1.length - 1) i)) ∧ Sub π.ret spec.checked.flow.O ∧
      ∀ i σ', π.fn ((realizedCode r).1.length - 1) i = some σ' →
        i ∈ (List.range (r.siblings.length + 1)).map (capSlot spec.arity false 0 + ·)) ∧
    ∃ π, spec.checked.flow.code (requestCode r) entryCx = some π := by
  obtain ⟨he, hc, hf, -⟩ := FramedSpec.bindingB_iff.mp h
  obtain ⟨π, hπ, hs, hr⟩ := FFlow.entryB_sound (he.resolve_left (by simp [hi]))
  exact ⟨⟨π, hπ, hs, hr, fun i σ' hi => entryFnB_sound hf hπ hi⟩,
    codesCoverB_sound hc (requestCode r) (List.mem_singleton_self _)⟩
end

/-- **A graph plan's run accepted** (`passMemberGraph`'s, its walks framing
the nodes `fr`, the footprint's fallback allowed where `fb`): unqualified,
its code requests accepted in order and its main graph over their table
(`MainAcceptedAt`); or a qualified body accepted by one call at its
checker, as `MemberAccepted` states them. -/
inductive GraphAccepted (f : FilePlans) (i : Nat) (fr : List (Nat × List Footprints.Footprint)) (fb : Bool) : Prop where
  | ordinary (name : String) (pos : Span) (r : Req f) (a₀ a₁ : Answered (StoreView.graph f.F.store)) :
      PlanAt f i name pos r → r.qualification = none → declaredEffect r = true →
      (∀ Φ regions, r.regional = some (Φ, regions) → r.async = false ∧ r.fresh = false ∧
        GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions = true) →
      CodesAccepted (StoreView.graph f.F.store) (StoreView.images f.F.store) r [] r.codes.zipIdx a₀ a₁ →
      MainAcceptedAt (StoreView.graph f.F.store) (StoreView.images f.F.store) r
        (GraphCode.admits (r.codes.map (·.entry))) fr fb a₁ →
      GraphAccepted f i fr fb
  | qualified (name : String) (pos : Span) (r : Req f)
      (q : QualifiedBody (RequestJson.graph r.toRequest) (StoreView.images r.types))
      (c : RunCall (RequestJson.graph r.toRequest) (StoreView.images r.types))
      (a₀ after : Answered (RequestJson.graph r.toRequest)) :
      PlanAt f i name pos r → r.qualification = some q → declaredEffect r = true →
      r.footprint = .top → r.onThrow = false → r.fresh = false → r.ensures = [] → r.regional = none →
      r.codes = [] → MainCall r c (GraphCode.admits []) (.qualified q.body q.ordinary) a₀ → c.bound = none → c.regional = none →
      c.Accepts after → summariesChecked r after.summaries.toList = true → GraphAccepted f i fr fb

/-- **A callback-demand plan accepted**: its codes accepted in order, its main
graph walked at its framed callback nodes (`spec.framed`), its read summaries
checked, and its regional entry conditions satisfied. -/
def CallbackDemandsAccepted (f : FilePlans) (r : Req f) (spec : CallbackDemands.CallbackDemandSpec) : Prop :=
  (∃ (a₀ a₁ : Answered (StoreView.graph f.F.store)),
      CodesAccepted (StoreView.graph f.F.store) (StoreView.images f.F.store) r [] r.codes.zipIdx a₀ a₁ ∧
      ∃ (c : RunCall (StoreView.graph f.F.store) (StoreView.images f.F.store))
        (after : Answered (StoreView.graph f.F.store)),
        MainCall r c (GraphCode.admits (r.codes.map (·.entry))) .ordinary a₁ ∧
        c.bound = mainBound r ∧ regionOf c.regional = regionalSpec r ∧ c.AcceptsWalk after ∧
        summariesChecked r after.summaries.toList = true ∧ c.framed = spec.framed) ∧
    (∀ Φ regions, r.regional = some (Φ, regions) →
      GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions = true)

/-- **A member as `passGroup` accepts it.** Its plan is a graph request;
its declared effect's conditions hold; then either it is unqualified, each
stated region meets its entry conditions, its code requests are accepted in
order (`CodesAccepted`) and its graph over their table (`MainAccepted`); or
it is a qualified body, at the footprint letting everything change on
normal return alone, with no postcondition, regions or codes, accepted by
one call at its checker, its read summaries checked; or its plan is a
framed plan accepted (`FramedAccepted`), its request at the candidates its
walk settled at; or its plan is a callback-demand plan accepted
(`CallbackDemandsAccepted`), its request at the settled candidates. -/
inductive MemberAccepted (f : FilePlans) (i : Nat) : Prop where
  | ordinary (name : String) (pos : Span) (r : Req f) (a₀ a₁ : Answered (StoreView.graph f.F.store)) :
      PlanAt f i name pos r → r.qualification = none → declaredEffect r = true →
      (∀ Φ regions, r.regional = some (Φ, regions) → r.async = false ∧ r.fresh = false ∧
        GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions = true) →
      CodesAccepted (StoreView.graph f.F.store) (StoreView.images f.F.store) r [] r.codes.zipIdx a₀ a₁ →
      MainAccepted (StoreView.graph f.F.store) (StoreView.images f.F.store) r
        (GraphCode.admits (r.codes.map (·.entry))) a₁ →
      MemberAccepted f i
  | qualified (name : String) (pos : Span) (r : Req f)
      (q : QualifiedBody (RequestJson.graph r.toRequest) (StoreView.images r.types))
      (c : RunCall (RequestJson.graph r.toRequest) (StoreView.images r.types))
      (a₀ after : Answered (RequestJson.graph r.toRequest)) :
      PlanAt f i name pos r → r.qualification = some q → declaredEffect r = true →
      r.footprint = .top → r.onThrow = false → r.fresh = false → r.ensures = [] → r.regional = none →
      r.codes = [] → MainCall r c (GraphCode.admits []) (.qualified q.body q.ordinary) a₀ → c.bound = none → c.regional = none →
      c.Accepts after → summariesChecked r after.summaries.toList = true → MemberAccepted f i
  | framed (name : String) (pos : Span) (r : Req f)
      (spec : FramedSpec (EquationStore.CheckedLabel f.F.equations f.F.primitive))
      (cands : List (Nat × List HeapKnowledge.IndexAtom)) :
      FramedPlanAt f i name pos r spec → FramedAccepted f name { r with candidates := cands } spec → MemberAccepted f i
  | callbackDemands (name : String) (pos : Span) (r : Req f)
      (spec : CallbackDemands.CallbackDemandSpec)
      (cands : List (Nat × List HeapKnowledge.IndexAtom)) :
      CallbackDemandsPlanAt f i name pos r spec →
      CallbackDemandsAccepted f { r with candidates := cands } spec → MemberAccepted f i

/-- **H3, the wrapper's statement**: `passGroup` accepting a group makes
every member `MemberAccepted`, at every value of every argument. Proved
(`passGroupChecks_of_sound passMember_sound`, PassUnitWrapper and
PassUnitMemberRun). -/
def PassGroupChecks : Prop :=
  ∀ (f : FilePlans) (fuel : Nat) (group : List Nat) (compare : Bool) (debugNode repeats : Nat)
    (given : Option (Std.HashMap String Json)) (observe : Option String) (counting located : Bool)
    (deps : List String),
    (f.passGroup fuel group compare debugNode repeats given observe counting located).2 = .ok deps →
    ∀ j ∈ group, MemberAccepted f j

end Verification.SourceClaimJson.PassUnit
