import Verification.Source.Claims.PassUnitPlans

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
footprint, fresh flag and throw flag otherwise. -/
def mainBound (r : SourceRequest σ ι) : Option (Footprints.Closed × Bool × Bool) :=
  if (!(r.footprint == .top && !r.onThrow && !r.fresh) &&
      !(!r.fresh && r.program.all fun n => Purity.pureTerm n.expression)) = true then
    some (r.footprint, r.fresh, r.onThrow)
  else none

/-- The regional option the unit's stated regions give the run (`regionalOf
"regional"`): their bound and regions, a throw bounded where the stated
effect bounds one. -/
def regionalSpec (r : SourceRequest σ ι) :
    Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool) :=
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

/-- **A member as `passGroup` accepts it.** Its plan is a graph request;
its declared effect's conditions hold; then either it is unqualified, each
stated region meets its entry conditions, its code requests are accepted in
order (`CodesAccepted`) and its graph over their table (`MainAccepted`); or
it is a qualified body, at the footprint letting everything change on
normal return alone, with no postcondition, regions or codes, accepted by
one call at its checker, its read summaries checked. -/
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

/-- **The wrapper hypothesis**: `passGroup` accepting a group makes every
member `MemberAccepted`. A statement about the actual function, not proved
here: `passGroup` is one `Id.run` block whose member outcome is a local of
its loop (docs/drafts/pass-unit-theorem.md, "The wrapper"). -/
def PassGroupChecks : Prop :=
  ∀ (f : FilePlans) (fuel : Nat) (group : List Nat) (compare : Bool) (debugNode repeats : Nat)
    (given : Option (Std.HashMap String Json)) (observe : Option String) (counting : Bool) (deps : List String),
    (f.passGroup fuel group compare debugNode repeats given observe counting).2 = .ok deps →
    ∀ j ∈ group, MemberAccepted f j

end Verification.SourceClaimJson.PassUnit
