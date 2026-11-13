import Verification.Source.Claims.Json
import Verification.Programs.SinglePassDiagnosis

/-! # A member's lacking loop-head proposals, in one walk

The proposals a member's main graph states at its loop heads that some
edge into their head lacks: the diagnosing walk (`SinglePass.lackingFacts`)
over the member's graph at the arguments `FilePlans.passMember` gives its
main run, each found left out of its head as the walk goes. Its result
only chooses the candidates of the member's next run; that run is the
pass's, and decides. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-- **Member `i`'s lacking proposals**, by head (facts, or one of the
head's implications, `SinglePass.LeftOut`): the main graph's diagnosing
walk (`SinglePass.lackingFacts`) at the arguments of `passMember`'s main
run, `droppable` the facts at a head that may be left out; none where the
member has no main run (a qualified body, a code request not accepted, a
request refused before its run). -/
def FilePlans.lackingAt (f : FilePlans) (fuel : Nat) (i : Nat) (given : Option (Std.HashMap String Json))
    (droppable : Nat → List HeapKnowledge.IndexAtom) : List (Nat × SinglePass.LeftOut) :=
  let G : NormalGraph (EquationStore.CheckedLabel f.F.equations f.F.primitive) := StoreView.graph f.F.store
  let I : PositiveCertificates.InstanceImageCheck G := StoreView.images f.F.store
  let answers : CertificateProducer.Answered G := {}
  match f.plans[i]? with
  | some (.ok (.graph _ _ r)) =>
    if r.qualification.isSome then [] else
    let bounded := !(r.footprint == .top && !r.onThrow && !r.fresh) &&
      !(!r.fresh && r.program.all fun n => Purity.pureTerm n.expression)
    let bound := if bounded then some (r.footprint, r.fresh, r.onThrow) else none
    let labels := r.searchLabels
    match ExpressionClaims.produceUsing G I labels (StoreView.valid r.types)
        (StoreView.projection r.types) fuel r.obligations { answers with summaries := #[], summaryAnswers := {} } with
    | .error _ => []
    | .ok (e, next) =>
    let (rendered, next) := ExpressionClaims.renderKnownUsing G I labels (StoreView.valid r.types) r.nodePlans next
    let pool := CertificateProducer.vocabulary G labels r.claims r.inputs
    let line := given.bind fun m => m.get? (f.fr.unitId i)
    let main : GivenHeads _ := match line with
      | some l => match (l.getObjVal? "graph").bind (GivenHeads.fromJson r.program.length) with
        | Except.ok g => g
        | Except.error _ => {}
      | none => {}
    -- The code requests in order, as `passMember` passes them; the main
    -- graph's walk over the table of those accepted.
    let codeStep := fun (table : List (CodeEntry _)) (sumsAnswers : CertificateProducer.Answered G)
        ((q, ci) : CodeRequest _ × Nat) =>
      let refuse := fun (o : SinglePass.Outcome _) => ({ index := ci, outcome := o, answers := sumsAnswers, line := "" } : CodeRun _ _)
      let hints := (r.codeHints[ci]?).getD {}
      let rq := q.asRequest r.toRequest
      let eff := q.entry.row.effect
      let conditions := decide (q.entry.arity ≤ q.entry.row.arguments.length) && eff.below q.entry.arity &&
        !eff.freshObject && eff.requires.isNone && eff.elements.isNone && !eff.receiverGrows && eff.elementWrite.isNone
      if !conditions then refuse (.refused "its signature")
      else if !RequestJson.asyncEffects q.async eff.footprint then refuse (.refused "an async footprint")
      else
      let codeBound := if eff.footprint == .top && !eff.fresh && !eff.onThrow then none
        else if !eff.fresh && q.entry.exprs.all Purity.pureTerm then none
        else some (eff.footprint, eff.fresh, eff.onThrow)
      let codePool := CertificateProducer.vocabulary G labels rq.claims rq.inputs
      let codeGiven : GivenHeads _ := match line with
        | some l => match (l.getObjVal? "codes").bind fun cs => do
            let arr ← cs.getArr?
            GivenHeads.fromJson rq.program.length ((arr[ci]?).getD (Json.arr #[])) with
          | Except.ok g => g
          | Except.error _ => {}
        | none => {}
      let (o, _, a, _) := SinglePass.runRecorded "code" "direct"
          (runDigests r line s!"code {ci}" (boundText codeBound none)) (fun x => x.2.1.visited) fun _ =>
        SinglePass.run G I codePool fuel rq.program rq.claims rq.start rq.inputs q.entry.goal hints.requirements
        hints.cuts hints.candidates rq.entryIndices [] (e ++ rendered) (GraphCode.admits table) r.aliases
        .ordinary sumsAnswers #[] 1000000000 codeBound codeGiven.implies codeGiven.args
      ({ index := ci, outcome := o.asRefusal, answers := a, line := "" } : CodeRun _ _)
    let (codeRuns, table, sumsAnswers) := codesInOrder (·.1.entry) codeStep [] next r.codes.zipIdx
    if codeRuns.any fun c => !(c.outcome matches .accepted) then [] else
    let regional := r.regional.map fun (Φ, regions) =>
      let (names, heads) := match line.bind fun l => (l.getObjVal? "regional").toOption with
        | some j => (regionalFromJson r.program.length j).toOption.getD ([], #[])
        | none => ([], #[])
      ({ Φ, regions, exc := r.stated.any (·.onThrow), names, heads } : SinglePass.Regional)
    SinglePass.runRecorded "diagnose" (if regional.isSome then "regions" else "direct")
      (runDigests r line "main" (boundText bound regional)) (fun _ => 0) fun _ =>
    SinglePass.lackingFacts G I droppable true pool fuel r.program r.claims r.start r.inputs r.goal r.assertions r.cuts
      r.candidates r.entryIndices [] (e ++ rendered) (GraphCode.admits table) r.aliases .ordinary sumsAnswers bound
      main.implies main.args r.ensures main.inputs r.entrySeparation regional
  | _ => []

end Verification.SourceClaimJson
