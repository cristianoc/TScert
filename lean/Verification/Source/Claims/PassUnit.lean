import Verification.Source.Claims.FragmentFront

/-! # The single pass's unit theorem: definitions

What an accepted unit of mode 8 (`FilePlans.passGroup`) means, stated
without certificates (`RequestSafe`, `PassUnitSafe`), and the interface the
graph-level proof of `SinglePass.run` supplies (`RunSound`). The statements
and the theorems built on them are presented in
docs/drafts/pass-unit-theorem.md. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open PositiveCertificates (InstanceImageCheck)
open HeapExpressionRules (Checker)
open CertificateProducer (Answered)

/-! ## Reachability of the graph machine -/

/-- `ReachesIn P k h s h' s'`: the graph machine of `P` goes from `s` on heap
`h` to `s'` on heap `h'` in exactly `k` transitions. -/
inductive ReachesIn (P : Program) : Nat → Heap → State → Heap → State → Prop where
  | refl : ReachesIn P 0 h s h s
  | step : Transition P h s h₁ s₁ → ReachesIn P k h₁ s₁ h' s' → ReachesIn P (k + 1) h s h' s'

section
variable {ι : Type} [Labels ι]

/-! ## Entry conditions and graph guarantees -/

/-- What a request assumes of its entry: an environment meeting its inputs'
types at budget `n` and world `W`, its entry separation and index facts, an
admissible world and a heap the world types. -/
def EntryHolds (G : NormalGraph ι) (inputs : List (Ty ι)) (sep : HeapSeparation.Separation)
    (idx : List HeapKnowledge.IndexAtom) (ρ : Env) (n : Nat) (W : WorldT n) (h : Heap) : Prop :=
  EnvOk G inputs ρ n W ∧ HeapSeparation.Holds sep ρ ∧ HeapKnowledge.IndexHolds idx ρ h ∧
    WorldAdm W ∧ HeapOk n W h

/-- The term that runs a program graph from `start`, frame `L`, receiver `d`. -/
def gotoOf (P : Program) (start : Nat) (L : List Tm) (d : Tm) : Tm :=
  .goto (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) start L d

/-- **What an accepted run of a graph guarantees**, at every assignment
`admits` lets through: safety from every entry meeting `inputs`; within a
footprint where `bound` names one; the stated postcondition where `ensures`
is not empty; within the regional bound where `regional` names one (each of
these three for the term running any node lists whose graph is `P`); and each
stated assertion true at every state reached at its label within the
budget. -/
structure GraphGuarantee (G : NormalGraph ι) (admits : MixedAssignment ι → Prop) (P : Program)
    (start : Nat) (goal : Goal ι) (inputs : List (Ty ι)) (sep : HeapSeparation.Separation)
    (idx : List HeapKnowledge.IndexAtom) (assertions : List (Nat × HeapKnowledge.Knowledge))
    (bound : Option (Footprints.Closed × Bool × Bool)) (ensures : List HeapKnowledge.IndexFact)
    (regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)) : Prop where
  safe : ∀ η, admits η → ∀ n W h ρ, EntryHolds (reassign G η) inputs sep idx ρ n W h →
    SafeGraph (excOf (reassign G η)) P (GoalHolds (reassign G η) goal (goal.argument ρ)) n W h (.at start ρ)
  bounded : ∀ Φ fresh onThrow, bound = some (Φ, fresh, onThrow) → ∀ E K, GraphCode.program E K = P →
    ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → (∀ v ∈ L, isVal v = true) → isVal d = true →
    HeapObservations.SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' v => Φ.Holds h h' ∧ (fresh = true → Footprints.FreshAt h.length v))
      (fun h' => onThrow = true → Φ.Holds h h') n W h (.goto E K start L d)
  ensured : ensures ≠ [] → ∀ E K, GraphCode.program E K = P → ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h →
    HeapObservations.SafePost (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' v => GraphCode.EnsuresAt ensures h' (push v (envOf L d))) n W h (.goto E K start L d)
  regionally : ∀ Φ regions exc, regional = some (Φ, regions, exc) → ∀ E K, GraphCode.program E K = P →
    ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h →
    HeapObservations.SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' _ => Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      (fun h' => exc = true → Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      n W h (.goto E K start L d)
  asserted : ∀ η, admits η → ∀ n W h ρ, EntryHolds (reassign G η) inputs sep idx ρ n W h →
    ∀ l k, (l, k) ∈ assertions → ∀ j h' ρ', j < n → ReachesIn P j h (.at start ρ) h' (.at l ρ') →
      HeapKnowledge.Holds k ρ' h'

/-- The assignments a pass checker's acceptance covers: every one for the
ordinary checker, a qualified body's admitted instances for its checker
(`SinglePass.PassChecker.qualified` at the body's subtyping). -/
inductive CheckerScope (G : NormalGraph ι) (I : InstanceImageCheck G) :
    SinglePass.PassChecker G I → (MixedAssignment ι → Prop) → Prop where
  | ordinary : CheckerScope G I .ordinary (fun _ => True)
  | qualified (q : QualifiedBody G I) : CheckerScope G I (.qualified q.body q.ordinary) q.Admits

/-! ## A call of the pass -/

/-- One call of `SinglePass.run`: every argument it takes, over the graph
`G` and image check `I`. -/
structure RunCall (G : NormalGraph ι) (I : InstanceImageCheck G) where
  pool : List (Ty ι)
  fuel : Nat
  P : Program
  claims : List (CertificateProducer.PointClaim ι)
  start : Nat
  inputs : List (Ty ι)
  goal : Goal ι
  assertions : List (Nat × HeapKnowledge.Knowledge)
  cuts : List Nat
  candidates : List (Nat × List HeapKnowledge.IndexAtom)
  entryIndices : List HeapKnowledge.IndexAtom
  suggestions : List (ProgramCertificates.Sequent ι)
  known : List (ProgramCertificates.Evidence ι)
  codes : CodeEntry ι → Bool
  aliases : List (ι × ι)
  passChecker : SinglePass.PassChecker G I
  answers : Answered G
  reference : Array HeapKnowledge.Knowledge
  debugNode : Nat
  bound : Option (Footprints.Closed × Bool × Bool)
  givenImplies : Array (List (PromiseCalls.Implication ι))
  givenArgs : Array (List Nat)
  ensures : List HeapKnowledge.IndexFact
  givenInputs : Array (List (Nat × Nat))
  entrySeparation : HeapSeparation.Separation
  observe : Option Nat
  tracing : Bool
  observeEntry : Bool
  regional : Option SinglePass.Regional

/-- The call's result. -/
def RunCall.result {G : NormalGraph ι} {I : InstanceImageCheck G} (c : RunCall G I) :
    SinglePass.Outcome ι × SinglePass.Counts × Answered G × SinglePass.Trace :=
  SinglePass.run G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions c.cuts c.candidates
    c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers c.reference c.debugNode
    c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation c.observe c.tracing
    c.observeEntry c.regional

/-- The call accepted, leaving the answers `after`. -/
def RunCall.Accepts {G : NormalGraph ι} {I : InstanceImageCheck G} (c : RunCall G I) (after : Answered G) : Prop :=
  ∃ counts trace, c.result = (.accepted, counts, after, trace)

/-- A regional option's bound, regions and throw flag. -/
def regionOf (rg : Option SinglePass.Regional) :
    Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool) :=
  rg.map fun g => (g.Φ, g.regions, g.exc)

/-- The start's point claim states the inputs as its context. -/
def StartContext (claims : List (CertificateProducer.PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) : Prop :=
  (claims[start]?).map (·.context) = some inputs

/-- **The graph-level hypothesis** (the tolerant-frames lane's target): an
accepted call of the pass, whose checker covers `admits`, run with sound
codes and with the read summaries it leaves sound, and with each region's
entry field condition, guarantees what its options ask (`GraphGuarantee`)
from every entry meeting the inputs it is given. The pass checks the start's
context against those inputs itself (`SinglePass.entryRefusal`). Every
other argument is a free proposal: the candidates, given implications,
arguments and inputs, known evidence, cached answers, reference and pool are
arbitrary. -/
def RunSound (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : RunCall G I) (after : Answered G)
    (admits : MixedAssignment ι → Prop),
    c.Accepts after → CheckerScope G I c.passChecker admits →
    ProgramCertificates.CodesSound G c.codes → ProgramCertificates.SummariesSound G I after.summaries.toList →
    (∀ Φ regions exc, regionOf c.regional = some (Φ, regions, exc) →
      GraphCode.ArgumentPathTracking.checkEntryFields G c.inputs regions = true) →
    GraphGuarantee G admits c.P c.start c.goal c.inputs c.entrySeparation c.entryIndices c.assertions c.bound
      c.ensures (regionOf c.regional)

/-- **The pass keeps the read summaries it was given**: every summary of
the answers a call starts from is among those it leaves. -/
def RunKeepsSummaries (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : RunCall G I),
    ∀ s ∈ c.answers.summaries.toList, s ∈ c.result.2.2.1.summaries.toList

end

/-! ## Certificate-independent safety of a request and of a unit -/

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- The request a code request of `r` is checked as. -/
abbrev codeRequest (r : SourceRequest σ ι) (q : CodeRequest ι) : Request σ ι := q.asRequest r.toRequest

/-- The hints of `r`'s code request at `ci`, as the pass reads them. -/
def codeHintsAt (r : SourceRequest σ ι) (ci : Nat) : RequestJson.CodeHints := (r.codeHints[ci]?).getD {}

/-- Safety at every admitted assignment, from every entry. -/
def SafeClause (r : SourceRequest σ ι) : Prop :=
  ∀ η, r.Admits η → ∀ n W h ρ,
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices ρ n W h →
    SafeGraph (excOf (reassign (RequestJson.graph r.toRequest) η)) r.program
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument ρ)) n W h (.at r.start ρ)

/-- Within the claimed footprint, and returning fresh where promised, when the
declaration claims either. -/
def FootprintClause (r : SourceRequest σ ι) : Prop :=
  r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true →
    ∀ η n W h (L : List Tm) (d : Tm),
      EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
        (envOf L d) n W h →
      (∀ v ∈ L, isVal v = true) → isVal d = true →
      HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
        (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
        (fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
        (fun h' => r.onThrow = true → r.footprint.Holds h h') n W h (gotoOf r.program r.start L d)

/-- Meeting the stated postcondition where the declaration states one. -/
def EnsuresClause (r : SourceRequest σ ι) : Prop :=
  r.ensures ≠ [] → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h →
    HeapObservations.SafePost (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' v => GraphCode.EnsuresAt r.ensures h' (push v (envOf L d))) n W h (gotoOf r.program r.start L d)

/-- Within the stated regional bound where the declaration states regions. -/
def RegionalClause (r : SourceRequest σ ι) : Prop :=
  ∀ Φ regions, r.regional = some (Φ, regions) → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h →
    HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' _ => Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      (fun h' => r.stated.any (·.onThrow) = true →
        Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      n W h (gotoOf r.program r.start L d)

/-- Each stated assertion of the graph true at every state reached at its
label within the budget, at every admitted assignment. -/
def AssertionsClause (r : SourceRequest σ ι) : Prop :=
  ∀ η, r.Admits η → ∀ n W h ρ,
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices ρ n W h →
    ∀ l k, (l, k) ∈ r.assertions → ∀ j h' ρ', j < n → ReachesIn r.program j h (.at r.start ρ) h' (.at l ρ') →
      HeapKnowledge.Holds k ρ' h'

/-- Each stated assertion of each code's graph true at every state reached
at its label within the budget, from every frame meeting its signature. -/
def CodeAssertionsClause (r : SourceRequest σ ι) : Prop :=
  ∀ ci q, r.codes[ci]? = some q → ∀ η n W h ρ,
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) (codeRequest r q).inputs {}
      (codeRequest r q).entryIndices ρ n W h →
    ∀ l k, (l, k) ∈ (codeHintsAt r ci).requirements → ∀ j h' ρ', j < n →
      ReachesIn (codeRequest r q).program j h (.at (codeRequest r q).start ρ) h' (.at l ρ') →
      HeapKnowledge.Holds k ρ' h'

/-- **A request is safe** (`RequestsSafe`'s semantic conjuncts, no
certificate): at every admitted assignment its graph is safe from every
entry meeting its inputs, separation and index facts; it meets its claimed
footprint, fresh result, postcondition and regional bound; each stated
assertion of its graph and of each of its codes holds at every state reached
at its label within the budget. -/
def RequestSafe (r : SourceRequest σ ι) : Prop :=
  SafeClause r ∧ FootprintClause r ∧ EnsuresClause r ∧ RegionalClause r ∧ AssertionsClause r ∧
    CodeAssertionsClause r
end

/-! ## A unit's members -/

/-- **A member is safe**: its plan crosses the exhaustive certification
boundary (`FunctionPlan.certify`), and the request of the certified plan,
whatever its constructor, is safe. -/
def MemberSafe (f : FilePlans) (i : Nat) : Prop :=
  ∃ p c, f.plans[i]? = some (.ok p) ∧ p.certify = .ok c ∧
    match c with
    | .graph _ _ r => RequestSafe r

/-- **A unit is safe**: every member of its group is. -/
def PassUnitSafe (f : FilePlans) (i : Nat) : Prop :=
  ∀ j ∈ f.fr.group i, MemberSafe f j

end Verification.SourceClaimJson.PassUnit
