import Verification.Source.Claims.CallbackProducerReplay
import Verification.Source.Claims.PassUnitPlans
import Verification.Programs.SinglePassClose

namespace Verification.SourceClaimJson.CallbackInferencePlan
open CallbackOrigins CallbackEffectInference ControlFlow PassUnit LabelStore
open PositiveCertificates CertificateProducer

/-- The actual producer run, with the same code answers, validated origin
table and immutable frames that its published obligations were read from. -/
structure AcceptedProducer (f : FilePlans) (i fuel : Nat) (params : List Nat) (out : Interface) where
  name : String
  position : Span
  request : Req f
  plan : PlanAt f i name position request
  ordinary : request.qualification = none
  synchronous : request.async = false
  regions : request.regional = none
  codes : Array (CheckedCode (EquationStore.CheckedLabel f.F.equations f.F.primitive))
  known : List (ProgramCertificates.Evidence (EquationStore.CheckedLabel f.F.equations f.F.primitive))
  before : Answered (RequestJson.graph request.toRequest)
  checkedCodes : inferCodes request fuel = .ok (codes,known,before)
  origins : Table
  names : checkNames request.program.toArray (Array.replicate request.program.length true)
    request.start request.inputs.length origins = true
  nodes : Array Node
  nodeList : nodes = request.program.toArray
  rows : List (Row nodes origins (certifiedPrivate request.program.toArray origins
    (privateAllocations request.program origins)) params)
  published : out = publication rows
  after : Answered (StoreView.graph f.F.store)
  replayed : let G := StoreView.graph f.F.store
    let I := StoreView.images f.F.store
    let pool := vocabulary G request.searchLabels request.claims request.inputs
    let bound := if request.stated.isSome || request.fresh then
      some (ProgramTyping.RunBound.ofRequest request.footprint request.onThrow request.fresh) else none
    let call : TolerantFrames.Target.RunCall G I :=
      ⟨pool,fuel,request.program,request.claims,request.start,request.inputs,request.goal,request.assertions,request.cuts,[],
        request.entryIndices,[],known,GraphCode.admits (codes.toList.map (·.entry)),request.aliases,.ordinary,before,#[],
        1000000000,bound,#[],#[],request.ensures,#[],request.entrySeparation,none,true,false,none,framesOf rows⟩
    call.AcceptsWalk after
  summaries : SourceClaimJson.summariesChecked request after.summaries.toList = true

set_option pp.deepTerms false in
theorem infer_accepted_origins {f i fuel params out} (ok : infer f i fuel params = .ok out) :
    ∃ a : AcceptedProducer f i fuel params out,
      CallbackOrigins.infer a.request.program (a.request.claims.map (·.context.length)).toArray a.request.start a.request.inputs.length = some a.origins := by
  unfold infer at ok
  split at ok
  next plan hp =>
    obtain ⟨p,ep,ok⟩ := except_bind_ok ok
    obtain ⟨cp,ec,ok⟩ := except_bind_ok ok
    cases ep
    cases p with
    | framed => cases ec; contradiction
    | graph name pos r =>
      cases ec
      dsimp only at ok
      split at ok
      next => contradiction
      next qo =>
        split at ok
        next => contradiction
        next rg =>
          obtain ⟨_,_,ok⟩ := except_bind_ok ok
          obtain ⟨⟨codes,known,answers⟩,hc,ok⟩ := except_bind_ok ok
          dsimp only at ok
          split at ok
          next origins eq =>
            split at ok
            next => contradiction
            next checked =>
              split at ok
              next envState hs =>
                obtain ⟨env,initial⟩ := envState
                obtain ⟨pair,purePair,ok⟩ := except_bind_ok ok
                cases purePair
                obtain ⟨rows,_,replayed⟩ := except_bind_ok ok
                obtain ⟨pub,after,acc,sum⟩ := replay_accepted replayed
                have hn := (SinglePass.setup_env (h := hs)).2.2.1
                simp only [Bool.or_eq_true,not_or] at qo
                refine ⟨⟨name,pos,r,hp,(by simpa using qo.1),(by simpa using qo.2),?_,codes,known,answers,hc,origins,?_,env.nodes,hn,rows,pub,after,acc,sum⟩,by simpa using eq⟩
                · simpa using rg
                · simpa using checked
              next => contradiction
          next => contradiction
  next => contradiction
theorem infer_accepted {f i fuel params out} (ok : infer f i fuel params = .ok out) :
    Nonempty (AcceptedProducer f i fuel params out) := by
  obtain ⟨a,_⟩ := infer_accepted_origins ok
  exact ⟨a⟩

end Verification.SourceClaimJson.CallbackInferencePlan
