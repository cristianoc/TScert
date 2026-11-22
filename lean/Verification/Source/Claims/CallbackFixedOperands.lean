import Verification.Source.Claims.CallbackEvaluatedOperands
import Verification.Source.Claims.CallbackTypicalPoint
namespace Verification.SourceClaimJson.CallbackInferencePlan
open TolerantFrames CallbackOrigins CallbackPreservation Footprints CallArguments HeapObservations PositiveGraphs PositiveRules
open ControlFlow ProgramTyping ProgramCertificates LabelStore CertificateProducer PassUnit

/-- Type each operand in the point context by the ordinary expression checker. -/
@[nospecialize] def checkedOperand {ι : Type} [Labels ι] [Instantiates ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (pool : List (Ty ι)) (aliases : List (ι × ι))
    (fuel : Nat) (Γ : List (Ty ι)) (answers : Answered G) (t : Tm) (A : Ty ι) : Bool :=
  Purity.readTerm t && match (expressionWithUsing G images pool [] aliases (fun _ _ => true) fuel Γ t A answers).1.value with
    | none => false
    | some e => decide (claim e = ⟨Γ,t,A⟩) && checkTreeUsing G images e (fun _ => false) []

theorem checkedOperand_sound {ι : Type} [Labels ι] [Instantiates ι] {G : NormalGraph ι}
    {images pool aliases fuel Γ answers t A} (ok : checkedOperand G images pool aliases fuel Γ answers t A = true)
    {ρ η} (s : IndexedHeap) (typed : EnvOk (reassign G η) Γ ρ s.n s.W)
    (refs : RefsOk s.W (instantiate 0 ρ t)) :
    ∀ u : IndexedHeap, WorldReach s.W u.W → u.h = s.h →
      Safe (excOf (reassign G η)) (meaning (reassign G η) A) u.n u.W u.h (instantiate 0 ρ t) := by
  obtain ⟨ready,check⟩ := Bool.and_eq_true_iff.mp ok
  split at check
  · contradiction
  rename_i e _
  obtain ⟨same,tree⟩ := Bool.and_eq_true_iff.mp check
  have valid := (Parametricity.checkTree_reassign G η images e (fun _ => false) []).trans tree
  have deriv := checkTreeUsing_sound e valid (by intro _ no; contradiction)
  rw [of_decide_eq_true same] at deriv
  intro u ⟨le,ext⟩ _
  exact deriv.sound _ _ _ _ (typed.transfer _ le _ ext) u.adm u.ok (RefsOk_mono ext (RefsOk_trunc le refs))

private theorem preparedRefs {h p f final} (trace : Prepared h p f final) {n} {W : WorldT n} (heap : HeapOk n W h)
    (refs : RefsOk W (.invoke f.callee f.recv f.args)) : RefsOk W (.invoke final.callee final.recv final.args) := by
  induction trace with
  | refl => exact refs
  | next step _ ih => exact ih (Kinds.step_refs step.step (by simpa using heap.1.1) heap.2 refs)

private theorem fullRoot {slots privateSites param state fn br ba} {i x : Nat} {path : List String}
    (hit : (atCall slots privateSites param state (.invoke (.var fn) br ba)).demand.actualRoots[i]? = some (some (x,path))) :
    path = [] := by
  have nil_of_root {slot} (root : entryRoot slots slot = some (x,path)) : path = [] := by
    unfold entryRoot at root
    split at root
    · cases root; rfl
    · contradiction
  simp only [atCall,List.getElem?_map] at hit
  obtain ⟨t,_,eq⟩ := Option.map_eq_some_iff.mp hit
  cases t <;> first | exact nil_of_root eq | contradiction

/-- Check every fixed argument at its position, including the ordinary
undefined contract for a missing trailing argument. -/
@[nospecialize] def checkedArgs {ι : Type} [Labels ι] [Instantiates ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (pool : List (Ty ι)) (aliases : List (ι × ι))
    (fuel : Nat) (Γ : List (Ty ι)) (answers : Answered G) : List Tm → List (Ty ι) → Bool
  | [], rest => rest.all (PromiseCalls.admitsUndef G)
  | _::_, [] => false
  | t::ts, A::As => checkedOperand G images pool aliases fuel Γ answers t A && checkedArgs G images pool aliases fuel Γ answers ts As

theorem checkedArgs_sound {ι : Type} [Labels ι] [Instantiates ι] {G : NormalGraph ι}
    {images pool aliases fuel Γ answers ts As} (ok : checkedArgs G images pool aliases fuel Γ answers ts As = true)
    {ρ η} (s : IndexedHeap) (typed : EnvOk (reassign G η) Γ ρ s.n s.W)
    (refs : ∀ t ∈ ts, RefsOk s.W (instantiate 0 ρ t)) :
    ts.length ≤ As.length ∧ ts.all Purity.readTerm = true ∧
    (∀ A ∈ As.drop ts.length, PromiseCalls.admitsUndef G A = true) ∧
    OperandTypes (excOf (reassign G η)) s ((As.take ts.length).map (meaning (reassign G η))) (instantiateArgs 0 ρ ts) := by
  induction ts generalizing As with
  | nil => exact ⟨by simp,rfl,by simpa using List.all_eq_true.mp ok,.nil⟩
  | cons t ts ih =>
    cases As with
    | nil => contradiction
    | cons A As =>
      obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
      obtain ⟨le,reads,missing,more⟩ := ih tail (fun a ha => refs a (List.mem_cons_of_mem _ ha))
      exact ⟨by simpa using le,Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp head).1,reads⟩,
        by simpa using missing,.cons (checkedOperand_sound head s typed (refs _ (List.mem_cons_self ..))) more⟩

/-- The source operand is already a runtime value after substitution. -/
def readyOperand (t : Tm) : Bool := (t matches .var _) || isVal t

private theorem readyOperand_value {ρ : Env} {t : Tm} (ok : readyOperand t = true)
    (values : ∀ i, isVal (ρ i) = true) : isVal (instantiate 0 ρ t) = true := by
  cases t <;> simp_all [readyOperand,isVal,instantiate]
  case objAt fs code oid => cases code <;> rfl

private theorem preparedValues {h p frame next} (trace : Prepared h p frame next)
    (fn : isVal frame.callee = true) (rc : isVal frame.recv = true)
    (args : Values frame.args) : next = frame := by
  cases trace with
  | refl => rfl
  | next step _ =>
    cases step with
    | callee st => exact (value_no_step fn st).elim
    | recv _ st => exact (value_no_step rc st).elim
    | args _ _ st =>
      obtain ⟨_,_,_,atArg,_,head,_⟩ := focus_iff.mp st
      exact (value_no_step (args _ (List.mem_of_getElem? atArg)) head).elim
    | splice _ _ eq _ _ => exact (by have := args _ (eq ▸ List.mem_append_right _ (List.mem_cons_self ..)); contradiction)

/-- The ordinary index checker proves each declared callback precondition
on the invocation's fixed slots, using a checked assertion at this label
or the empty knowledge. These slots already hold their runtime values. -/
def fixedPreconditionChecked (atLabel : List (Nat × HeapKnowledge.Knowledge)) (label : Nat)
    (effect : CallEffects.Effect) (recv : Tm) (args : List Tm) : Bool :=
  let check := fun knowledge => PromiseCalls.preconditionHolds knowledge effect (.invoke .undef recv args)
  effect.pre.isEmpty || (readyOperand recv && args.all readyOperand &&
    (check {} || atLabel.any fun (l,k) => l == label && check k))

private theorem fixedPrecondition_sound {asserts l effect recv args fn ρ h frame count ε}
    (checked : fixedPreconditionChecked asserts l effect recv args = true)
    (point : ∀ k, (l,k) ∈ asserts → HeapKnowledge.Holds k ε ρ h)
    (vars : ∀ i, isVal (ρ i) = true)
    (trace : Prepared h count ⟨ρ fn,instantiate 0 ρ recv,instantiateArgs 0 ρ args⟩ frame) :
    ∀ fact ∈ effect.pre, fact.HoldsAt ⟨CallEffects.callEnv frame.recv frame.args,h⟩ (CallEffects.callEnv frame.recv frame.args) h := by
  simp only [fixedPreconditionChecked,Bool.or_eq_true,Bool.and_eq_true] at checked
  rcases checked with empty | ⟨⟨rc,arguments⟩,proof⟩
  · simp [List.isEmpty_iff.mp empty]
  · have vals : Values (instantiateArgs 0 ρ args) := by
      intro a ha
      rw [instantiateArgs_eq_map] at ha
      obtain ⟨t,mem,rfl⟩ := List.mem_map.mp ha
      exact readyOperand_value (List.all_eq_true.mp arguments t mem) vars
    have fixed := preparedValues trace (vars fn) (readyOperand_value rc vars) vals
    subst frame
    have holds : effect.Requires (instantiate 0 ρ recv) (instantiateArgs 0 ρ args) h := by
      rcases proof with basic | byLabel
      · exact PromiseCalls.preconditionHolds_sound basic (HeapKnowledge.empty (ε := ε) ρ h)
      · obtain ⟨⟨label,k⟩,mem,checked⟩ := List.any_eq_true.mp byLabel
        obtain ⟨same,ok⟩ := Bool.and_eq_true_iff.mp checked
        cases (beq_iff_eq.mp same : label = l)
        exact PromiseCalls.preconditionHolds_sound ok (point k mem)
    exact holds.2

/-- Direct, fixed callback calls carry their declared signature across the
module boundary. Non-call nodes need no operand certificate. -/
@[nospecialize] def checkFixedCall {ι : Type} [Labels ι] [Instantiates ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (pool : List (Ty ι)) (aliases : List (ι × ι))
    (fuel : Nat) (Γ : List (Ty ι)) (answers : Answered G)
    (atLabel : List (Nat × HeapKnowledge.Knowledge)) (label : Nat) (row : CallEffects.Arrow (Ty ι))
    (recv : Tm) (args : List Tm) : Bool :=
  fixedPreconditionChecked atLabel label row.effect recv args && checkedOperand G images pool aliases fuel Γ answers recv row.receiver &&
    checkedArgs G images pool aliases fuel Γ answers args row.arguments

@[nospecialize] def fixedCallsChecked {f : FilePlans} (r : Req f) (fuel : Nat)
    (origins : Table) (marked : List Nat) (out : Interface) : Bool :=
  let G := RequestJson.graph r.toRequest
  let pool := vocabulary G r.searchLabels r.claims r.inputs
  r.program.zipIdx.all fun (nd,l) => match nd.expression with
    | .invoke (.var fn) recv args => match (origins.at l)[fn]? with
      | some [.input p] =>
        if marked.contains p && out.demands.any (fun d => d.parameter == p && !d.support.normal.isEmpty) then
          (r.inputs[p]?.bind (fixedCallbackSignature G)).all fun row =>
            checkFixedCall G (StoreView.images r.types) pool r.aliases fuel
              (((r.claims[l]?).map (·.context)).getD []) {} r.assertions l row recv args
        else true
      | _ => true
    | _ => true

theorem publicDemands_supply {f : FilePlans} {r : Req f} {fuel origins marked own pub}
    (out : ∀ d ∈ own.demands, d ∈ pub.demands) (checked : fixedCallsChecked r fuel origins marked pub = true)
    (source : r.program.all (fun nd => ObjectCoherence.sourceTerm nd.expression) = true)
    {privateSites L d initial I η}
    (persist : ∀ {k} {U : WorldT (k+1)} {V : WorldT k}, I (k+1) U → WExt (trunc k (Nat.le_succ _) U) V → I k V)
    (supply : PublicDemandsWith I (formalDomain (reassign (RequestJson.graph r.toRequest) η) r.inputs)
      pub (envOf L d)) :
    SuppliedDemandsAt (ProducerPoint (reassign (RequestJson.graph r.toRequest) η)
      (fun l => ((r.claims[l]?).map (·.context)).getD []) r.assertions ⟨envOf L d,initial⟩) I r.program origins privateSites marked own r.start (envOf L d) initial := by
  intro fn recv args p proposal l nd ρ ticks after v j s slots keep typed reached atNode invoked member hm origin cb realized ready vals refs steps room finished
  let demand := (atCall slots privateSites p proposal (.invoke (.var fn) recv args)).demand
  have member' := out demand member
  cases support : demand.support.normal with
  | nil => simp [Supported]
  | cons e es =>
    have anyD : pub.demands.any (fun r => r.parameter == p && !r.support.normal.isEmpty) = true := by
      apply List.any_eq_true.mpr
      exact ⟨demand,member',by simp [show demand.parameter = p from rfl,support]⟩
    have accept := List.all_eq_true.mp checked (nd,l) (List.mk_mem_zipIdx_iff_getElem?.mpr atNode)
    change (match nd.expression with | .invoke (.var f') br ba => _ | _ => _) = true at accept
    rw [invoked] at accept
    dsimp only at accept
    rw [origin] at accept
    simp only [List.contains_iff_mem.mpr hm,anyD,Bool.true_and,ite_true] at accept
    have sourceTerm := List.all_eq_true.mp source nd (List.mem_of_getElem? atNode)
    rw [invoked] at sourceTerm
    have allRefs : RefsOk s.W (instantiate 0 ρ (.invoke (.var fn) recv args)) := by
      intro loc mem
      exact (Kinds.instantiate_refs _ _ _ loc mem).elim (sourceTerm_refsOk sourceTerm s.W loc) (fun ⟨i,hit⟩ => refs i loc hit)
    have frameRefs := RefsOk_invoke.mp allRefs
    have hvals : ∀ (i : Nat) t, s.h[i]? = some t → isVal t = true := by
      obtain ⟨n,W,h,pos,adm,heap⟩ := s; cases n with | zero => contradiction | succ => exact HeapExpressionRules.heap_values adm heap
    obtain ⟨spent,q,frame,body,count,trace,dispatch,tail⟩ := readCall_dispatch steps finished (readCall_instantiate ready vals) hvals
    have callee := trace.keepsCallee (v := ρ fn) (by simp [instantiate]) (vals fn)
    have ⟨rv,av⟩ : isVal frame.recv = true ∧ Values frame.args := by cases dispatch <;> exact ⟨by assumption,by assumption⟩
    have finish (u : IndexedHeap) (same : u.h = s.h) (reach : WorldReach s.W u.W) (ui : I u.n u.W)
        (time : q+1 < u.n) (domain : formalDomain (reassign (RequestJson.graph r.toRequest) η) r.inputs p u frame.recv frame.args) :
        Supported demand.support.normal (envOf L d) s.h after := by
      obtain ⟨le,ext⟩ := reach
      have fr := RefsOk_invoke.mp (RefsOk_mono ext (RefsOk_trunc le (preparedRefs trace s.ok allRefs)))
      have atCall : Steps (q+1) u.h (.invoke (envOf L d demand.parameter) frame.recv frame.args) after v := by
        change Steps _ _ (.invoke (envOf L d p) _ _) _ _
        rw [same,cb,← callee]
        exact .next (dispatch.step _) tail
      rw [← same]
      apply supply demand member' u frame.recv frame.args ui domain rv av _ fr.2.1 fr.2.2 _ _ _ _ atCall time finished
      · change RefsOk u.W (envOf L d p); rw [cb,← callee]; exact fr.1
      · intro i x path hit
        have empty := fullRoot hit; subst path
        simpa [HeapKnowledge.readPath] using congrArg some (atCall_actualRoots realized ready vals hvals trace hit)
    rw [← support]
    cases rowAt : r.inputs[p]?.bind (fixedCallbackSignature (RequestJson.graph r.toRequest)) with
    | none => exact finish s rfl (.refl _) keep (by omega) (fun row hit => by rw [show r.inputs[p]?.bind (fixedCallbackSignature (reassign (RequestJson.graph r.toRequest) η)) = none from rowAt] at hit; contradiction)
    | some row =>
      simp only [rowAt, Option.all_some] at accept
      obtain ⟨⟨pre,recvOk⟩,argsOk⟩ := (Bool.and_eq_true_iff.mp accept).imp_left Bool.and_eq_true_iff.mp
      obtain ⟨le,reads,missing,argsTypes⟩ := checkedArgs_sound argsOk s typed.1
        (fun a ha => frameRefs.2.2 _ (by simpa [instantiateArgs_eq_map] using List.mem_map_of_mem (f := instantiate 0 ρ) ha))
      have recvTy := @checkedOperand_sound _ _ _ _ _ _ _ _ _ _ _ _ recvOk _ η s typed.1 frameRefs.2.1
      have operandReads : ((instantiate 0 ρ recv)::instantiateArgs 0 ρ args).all Purity.readTerm = true := by
        simp only [List.all_cons,Bool.and_eq_true,instantiateArgs_eq_map,List.all_map,List.all_eq_true] at reads ⊢
        exact ⟨read_instantiate (Bool.and_eq_true_iff.mp recvOk).1 vals,fun a ha => read_instantiate (reads a ha) vals⟩
      have runs := trace.fixedOperandRuns (by simp [instantiate,vals]) operandReads hvals
      let fams := (row.receiver :: row.arguments.take args.length).map (meaning (reassign (RequestJson.graph r.toRequest) η))
      have types : OperandTypes (excOf (reassign (RequestJson.graph r.toRequest) η)) s fams
          (instantiate 0 ρ recv :: instantiateArgs 0 ρ args) := .cons recvTy argsTypes
      obtain ⟨u,uh,un,uw,ui,rcTy,asTy⟩ := runs.typed persist types (by
        intro A ha; obtain ⟨B,_,rfl⟩ := List.mem_map.mp ha; exact meaning_adm _ _) (by
        intro a ha; rcases List.mem_cons.mp ha with rfl | mem; exact rv; exact av a mem) keep (by omega)
      have lens := ArgsT_length asTy
      have len : frame.args.length = args.length := by simpa [List.length_take, Nat.min_eq_left le] using lens
      apply finish u uh uw ui (by omega)
      intro other hit
      change r.inputs[p]?.bind (fixedCallbackSignature (RequestJson.graph r.toRequest)) = some other at hit
      cases rowAt.symm.trans hit
      refine ⟨rcTy,⟨by simpa [len] using le,by simpa [len,List.map_take] using asTy,?_⟩,by rw [uh]; exact fixedPrecondition_sound pre typed.2 vals trace⟩
      rw [len,← List.map_drop]
      intro B hB
      obtain ⟨A,hm,rfl⟩ := List.mem_map.mp hB
      exact PromiseCalls.admitsUndef_sound (G := reassign (RequestJson.graph r.toRequest) η) (missing A hm) _ _


end Verification.SourceClaimJson.CallbackInferencePlan
