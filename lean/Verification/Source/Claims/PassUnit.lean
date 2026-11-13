import Verification.Source.Claims.FragmentFront
import Verification.Programs.TolerantFramesGuaranteeTarget

/-! # The single pass's unit theorem: definitions

What an accepted unit of mode 8 (`FilePlans.passGroup`) means, stated
without certificates (`RequestSafe`, `PassUnitSafe`), and the interface the
graph-level proof of `SinglePass.run` supplies (`RunSound`). The statements
and the theorems built on them are presented in
docs/SINGLE-PASS-THEOREM.md. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open PositiveCertificates (InstanceImageCheck)
open HeapExpressionRules (Checker)
open CertificateProducer (Answered)

/-! ## The run-level statements

The graph machine's reachability, what an accepted call of the pass
guarantees and the two run-level statements (`RunSound`,
`RunKeepsSummaries`) are the graph proof's own definitions
(`Verification.TolerantFrames.Target`). -/

export Verification.TolerantFrames.Target (ReachesIn EntryHolds GraphGuarantee CheckerScope RunCall
  RunCall.result RunCall.Accepts regionOf RunSound RunKeepsSummaries)

section
variable {ι : Type} [Labels ι]

/-- The term that runs a program graph from `start`, frame `L`, receiver `d`. -/
def gotoOf (P : Program) (start : Nat) (L : List Tm) (d : Tm) : Tm :=
  .goto (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) start L d

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
