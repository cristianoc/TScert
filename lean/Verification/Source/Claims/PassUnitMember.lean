import Verification.Source.Claims.PassUnitPlans
import Verification.Programs.TolerantFramesComposeYields

/-! # The single pass's unit theorem: a member and the headline

What `FilePlans.passGroup` establishes of a member it accepts, stated as
`MemberAccepted` (the wrapper's checks, each the exact call or condition
the wrapper makes), the theorem that such a member is safe
(`member_safe`, under `RunSound` and `RunKeepsSummaries`), and the
headline from mode 8's exact acceptance condition (`passUnit_safe`). -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
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

/-- **The main graph accepted** as `passGroup` accepts it: directly, at its
bound and stated regions; or, the bound refused, by the footprint's
regional fallback (no regions), followed by the stated regions' run where
it states any. Each accepted run's read summaries checked. -/
inductive MainAccepted (G : NormalGraph ι) (I : InstanceImageCheck G) (r : SourceRequest σ ι)
    (codes : CodeEntry ι → Bool) (a : Answered G) : Prop where
  | direct (c : RunCall G I) (after : Answered G) :
      MainCall r c codes .ordinary a → c.bound = mainBound r → regionOf c.regional = regionalSpec r →
      c.Accepts after → summariesChecked r after.summaries.toList = true → MainAccepted G I r codes a
  | fallback (c₁ : RunCall G I) (a₁ : Answered G) :
      r.fresh = false → MainCall r c₁ codes .ordinary a → c₁.bound = none →
      regionOf c₁.regional = some (r.footprint, [], r.onThrow) → c₁.Accepts a₁ →
      summariesChecked r a₁.summaries.toList = true →
      (r.regional = none ∨ ∃ (c₂ : RunCall G I) (a₂ : Answered G), MainCall r c₂ codes .ordinary a ∧
        c₂.bound = none ∧ regionOf c₂.regional = regionalSpec r ∧ c₂.Accepts a₂ ∧
        summariesChecked r a₂.summaries.toList = true) →
      MainAccepted G I r codes a

end

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **The framed claim's obligations** (the draft "Accepting a unit through
the read-only frame", "The theorems"): what no lemma yet proves from the
pass's check of a framed plan, at the framed nodes `F` keeping the supports
`S` of its main graph's framed run: the returns `framedRet S` hold at the
executions the frame's claim is about (`FramedReturnsReached`, by
`ret_reached`), at some return premise of a throw. The main graph's five
clauses of `FramedRequestSafe` follow from them and from the framed run's
guarantee (`framedReturns_of_main`, `framedRun_of_returns`). A field leaves
this structure in the commit that proves it from the check. -/
structure FramedObligations (r : SourceRequest σ ι) (spec : FramedSpec ι) (F : Nat → Bool)
    (S : Nat → List Footprints.Footprint) : Prop where
  reached : ∃ RetE : Nat → Env → Heap → Heap → Prop,
    FramedReturnsReached r (spec.frame r) F (Verification.TolerantFrames.framedRet S) RetE
end

/-- **A framed member as the pass accepts it** (the draft, "What the pass
checks"): its code requests accepted in order by the ordinary pass
(`CodesAccepted`), the read summaries their runs leave checked; each
stated region meeting its entry conditions; its main graph, over the codes'
table, accepted by the pass's framed mode at its bound and stated regions
(`RunCall.AcceptsFramed` at the framed nodes `F` keeping the supports `S`),
its read summaries checked; and the framed claim's obligations not yet
proved from the checks. `FilePlans.passMember` refuses every framed plan,
so no member `passGroup` accepts is accepted by this constructor until
every obligation is proved from the checks the pass makes. -/
structure FramedAccepted (f : FilePlans) (r : Req f)
    (spec : FramedSpec (EquationStore.CheckedLabel f.F.equations f.F.primitive)) : Prop where
  codes : ∃ a₀ a₁ : Answered (StoreView.graph f.F.store),
    CodesAccepted (StoreView.graph f.F.store) (StoreView.images f.F.store) r [] r.codes.zipIdx a₀ a₁ ∧
      summariesChecked r a₁.summaries.toList = true ∧
      ∃ (c : RunCall (StoreView.graph f.F.store) (StoreView.images f.F.store))
        (after : Answered (StoreView.graph f.F.store)) (F : Nat → Bool) (S : Nat → List Footprints.Footprint),
        MainCall r c (GraphCode.admits (r.codes.map (·.entry))) .ordinary a₁ ∧ c.bound = mainBound r ∧
        regionOf c.regional = regionalSpec r ∧ c.AcceptsFramed after (fun _ => True) F S ∧
        summariesChecked r after.summaries.toList = true ∧ FramedObligations r spec F S
  regions : ∀ Φ regions, r.regional = some (Φ, regions) →
    GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions = true

/-- **A member as `passGroup` accepts it.** Its plan is a graph request;
its declared effect's conditions hold; then either it is unqualified, each
stated region meets its entry conditions, its code requests are accepted in
order (`CodesAccepted`) and its graph over their table (`MainAccepted`); or
it is a qualified body, at the footprint letting everything change on
normal return alone, with no postcondition, regions or codes, accepted by
one call at its checker, its read summaries checked; or its plan is a
framed plan accepted (`FramedAccepted`). -/
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
      (spec : FramedSpec (EquationStore.CheckedLabel f.F.equations f.F.primitive)) :
      FramedPlanAt f i name pos r spec → FramedAccepted f r spec → MemberAccepted f i

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
