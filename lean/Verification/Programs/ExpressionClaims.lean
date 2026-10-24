import Verification.Source.RequestJson
import Verification.Programs.DirectProof

/-! Exact, independently checked expression sequents. These supplement the
whole-program certificate when source expressions occur inside lambda bodies.
The consumer uses existing declarative rules, never producer success alone. -/
namespace Verification.ExpressionClaims
open Lean ProgramTyping ProgramCertificates PositiveRules PositiveGraphs PositiveNormalization RequestJson
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

variable {ι : Type}

structure Required (ι : Type) where
  pos : Nat × Nat
  sequent : Sequent ι
  plan : Option (DirectProof.Plan ι) := none
  role : String := "expression-claim"
  /-- This obligation's source map: one descriptor per context binding. -/
  context : List Descriptor := []

section
variable [DecidableEq ι] [CertificateProducer.Instantiates ι]

/-- `valid` says which labels the graph's store holds. -/
@[nospecialize] def checkResult (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool)
    (j : Sequent ι) (e : Evidence ι) (codes : CodeEntry ι → Bool := fun _ => false)
    (sums : List (ReadSummary ι) := []) : CheckResult ι Unit :=
  (CheckResult.ofBool (validEvidence valid e && decide (claim e = j) &&
    checkScope j.context.length j.term)).bind fun _ => checkTreeResult G images e codes sums

@[nospecialize] def checkUsing (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool)
    (j : Sequent ι) (e : Evidence ι) (codes : CodeEntry ι → Bool := fun _ => false)
    (sums : List (ReadSummary ι) := []) : Bool :=
  (checkResult G images valid j e codes sums).accepted

omit [CertificateProducer.Instantiates ι] in

omit [CertificateProducer.Instantiates ι] in

@[nospecialize] def checkAllResult (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool)
    (rs : List (Required ι)) (es : List (Evidence ι)) (codes : CodeEntry ι → Bool := fun _ => false)
    (sums : List (ReadSummary ι) := []) : CheckResult ι Unit :=
  (CheckResult.ofBool (rs.length == es.length)).bind fun _ =>
  CheckResult.allLocated (rs.zip es) .obligation fun (r,e) => checkResult G images valid r.sequent e codes sums

@[nospecialize] def checkAllUsing (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool) (rs : List (Required ι)) (es : List (Evidence ι))
    (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) : Bool :=
  (checkAllResult G images valid rs es codes sums).accepted

omit [CertificateProducer.Instantiates ι] in

omit [CertificateProducer.Instantiates ι] in

/-- `valid` says which labels the graph's store holds, `project` what a
diagnostic mentioning some of them shows of it (`StoreView.project`). -/
@[nospecialize] def produceUsing [Hashable ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (labels : List ι)
    (valid : ι → Bool) (project : List ι → LabelStore.Projection ι) (fuel : Nat)
    (rs : List (Required ι)) (answers : CertificateProducer.Answered G := {}) :
    Except String (List (Evidence ι) × CertificateProducer.Answered G) := do
  let pool := CertificateProducer.vocabulary G labels []
    (rs.flatMap (fun r => r.sequent.type :: r.sequent.context))
  -- Nested obligations render the same coercions again: one search cache
  -- serves them all, the graph being fixed here; its answered requests are
  -- the caller's, for the same graph and image check.
  let mut cache : DirectProof.SubtypeCache G := { answers }
  let mut es := #[]
  for (r,index) in rs.zipIdx do
    let j := r.sequent
    let candidate : ProgramCertificates.CheckResult ι (Evidence ι) ← match r.plan with
      | some plan => do
        let (e, next) := DirectProof.renderWith G images pool j.context plan cache
        cache := next
        pure e
      | none => do
        let (e, answers) := CertificateProducer.expressionWithUsing G images pool (rs.map Required.sequent) []
          fuel j.context j.term j.type cache.answers
        cache := { cache with answers }
        pure e
    -- Attribute an invalid suggested proof to its own obligation, rather than
    -- losing the source location in the final aggregate check.
    -- The graph code a unit creates is checked after its obligations are
    -- rendered: here every code is admitted, and acceptance checks the
    -- obligation again against the table its certificate checked.
    let validated := candidate.bind fun e =>
      (checkResult G images valid j e (fun _ => true) cache.answers.summaries.toList).map fun _ => e
    let some e := validated.value
      | if let some stop := validated.exhaustion then
          let p := project (stop.source ++ stop.target ++ j.context.flatten).eraseDups
          throw (withDiagnostic s!"closure expression claim at [{r.pos.1},{r.pos.2}): subtype search exhausted"
            ([("kind",toJson "direct-obligation"),("phase",toJson "proof-search"),
              ("outcome",toJson (DiagnosticOutcome.exhausted stop.limit stop.rounds stop.visited)),
              ("id",toJson s!"expression:{index}"),
              ("sourceMap",toJson (SourceMapEntry.mk r.pos r.role none [])),
              ("judgment",Json.mkObj [("kind",toJson "subtyping"),("subject",toJson r.pos),
                ("actual",toJson (p.shown stop.source)),("expected",toJson (p.shown stop.target))]),
              ("fuel",toJson fuel)] ++ p.fields))
        let p := project (j.type ++ j.context.flatten).eraseDups
        -- This record's table shows each row's clauses alone: a parameter,
        -- scheme or meet row as no clauses.
        throw (withDiagnostic s!"closure expression claim at [{r.pos.1},{r.pos.2}): evidence search failed"
          ([("kind",toJson "expression-claim"),("phase",toJson "proof-search"),
           ("outcome",toJson RequestJson.DiagnosticOutcome.notEstablished),("id",toJson s!"expression:{index}"),
           ("sourceMap",toJson (SourceMapEntry.mk r.pos r.role none r.context)),
           ("sequent",toJson (Sequent.mk (j.context.map p.shown) j.term (p.shown j.type))),
           ("fuel",toJson fuel),("types",toJson (p.rows.map GraphRow.union))] ++
           (if p.names.isEmpty then [] else [("names",toJson p.names)])))
    es := es.push e
  -- Each item passed `check` against its own obligation above, so no final
  -- aggregate check is repeated here; acceptance (`checkRequests`) checks
  -- the evidence independently.
  return (es.toList, cache.answers)

/-- Node plans rendered where they can be: search hints, never obligations.
A plan that does not render is dropped; its node is searched as any other. -/
@[nospecialize] def renderKnownUsing [Hashable ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (labels : List ι) (valid : ι → Bool)
    (plans : List (DirectProof.Plan ι)) (answers : CertificateProducer.Answered G := {}) :
    List (Evidence ι) × CertificateProducer.Answered G := Id.run do
  let pool := CertificateProducer.vocabulary G labels [] (plans.flatMap fun p => p.goal.type :: p.goal.context)
  let mut cache : DirectProof.SubtypeCache G := { answers }
  let mut es := #[]
  for plan in plans do
    let (e, next) := DirectProof.renderWith G images pool plan.goal.context plan cache
    cache := next
    if let some e := e.value.filter (fun e =>
        checkUsing G images valid plan.goal e (fun _ => true) cache.answers.summaries.toList) then es := es.push e
  return (es.toList, cache.answers)

end

end Verification.ExpressionClaims
