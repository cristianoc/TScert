import Verification.Source.Claims.CallbackSupplyCases
import Verification.Source.Claims.PassUnitPlans
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins CallbackPreservation CallbackEffectInference ControlFlow LabelStore SourceElaboration PassUnit

private theorem filterMapM_checked {α β ε : Type} {f : α → Except ε (Option β)} {xs : List α} {out : List β}
    (ok : xs.filterMapM f = .ok out) : ∀ x ∈ xs, ∃ y, f x = .ok y ∧ ∀ v, y = some v → v ∈ out := by
  induction xs generalizing out with
  | nil => simp
  | cons a xs ih =>
    rw [List.filterMapM_cons] at ok
    obtain ⟨y,hy,ok⟩ := except_bind_ok ok
    cases y with
    | none =>
      intro x member
      rcases List.mem_cons.mp member with rfl | hx
      · exact ⟨none,hy,fun _ h => by cases h⟩
      · exact ih ok x hx
    | some b =>
      obtain ⟨bs,hbs,ok⟩ := except_bind_ok ok
      cases ok
      intro x member
      rcases List.mem_cons.mp member with rfl | hx
      · exact ⟨_,hy,fun _ eq => by cases eq; exact List.mem_cons_self⟩
      · obtain ⟨found,hf,keep⟩ := ih hbs x hx
        exact ⟨found,hf,fun v eq => List.mem_cons_of_mem _ (keep v eq)⟩

def DemandDecision {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (codes : Array (CheckedCode ι)) (origins : Table) (forwarding : List Nat)
    (producer : Published) (label : Nat) (receiver : Tm) (args : List Tm) (d : Demand) (out : Option Demand) : Prop :=
  let fixedArgs := CallbackInferencePlan.positionalPrefix args
  let frame := checkedCallFrame producer receiver args
  let slots := origins.at label
  let roots := argumentRoots r.inputs.length r.program.length slots frame
  (d.support.normal.isEmpty = true ∧ d.support.exceptional.isEmpty = true) ∨
    (absentCallback r label frame d.parameter = true ∧ ¬(frame[d.parameter]? = none ∧ fixedArgs.length < args.length)) ∨
    (∃ pos forwarded, frame[d.parameter]?.bind (originOf slots) = some (.input pos) ∧ pos ∈ forwarding ∧
      d.forward pos (publicOperand r.inputs.length roots) = some forwarded ∧ out = some forwarded) ∨
    d.check roots (fun param => frame[param]?.bind (closure codes r.program.toArray origins r.inputs.length slots
      (invocationBindings d roots))) (separation r.inputs.length r.program.length slots) = true

theorem checkDemand_decision {σ ι : Type} [Labels ι] [StoreView σ ι]
    {r : SourceRequest σ ι} {codes origins forwarding producer label receiver args d out}
    (ok : checkDemand r codes origins forwarding producer label receiver args d = .ok out) :
    DemandDecision r codes origins forwarding producer label receiver args d out := by
  unfold checkDemand at ok
  unfold DemandDecision
  dsimp only [List.size_toArray] at ok ⊢
  split at ok
  next empty => exact .inl (Bool.and_eq_true_iff.mp empty)
  next =>
    split at ok
    next => contradiction
    next clear =>
      split at ok
      next absent => exact .inr (.inl ⟨absent,by simpa using clear⟩)
      next =>
        split at ok
        next pos origin =>
          split at ok
          next forwarded =>
            split at ok
            next rebased good =>
              cases ok
              exact .inr (.inr (.inl ⟨pos,rebased,origin,List.contains_iff_mem.mp forwarded,good,rfl⟩))
            next => contradiction
          next =>
            split at ok
            next => contradiction
            next checked => exact .inr (.inr (.inr (by simpa using checked)))
        next =>
          split at ok
          next => contradiction
          next checked => exact .inr (.inr (.inr (by simpa using checked)))

theorem checkedNode_demands {σ ι : Type} [Labels ι] [StoreView σ ι]
    {r : SourceRequest σ ι} {codes origins known forwarding node label out callee recv args root producer}
    (ok : checkNode r codes origins known forwarding node label = .ok out)
    (invoke : node.expression = .invoke callee recv args) (resolved : originOf (origins.at label) callee = some (.input root))
    (lookup : known.find? (·.1 == root) = some (root,producer)) :
    ∃ results, out = some (producer.name,results) ∧ ∀ d ∈ producer.interface.demands,
      ∃ decision, DemandDecision r codes origins forwarding producer label recv args d decision ∧
        ∀ f, decision = some f → f ∈ results := by
  unfold checkNode at ok
  dsimp only at ok
  split at ok
  next => contradiction
  next =>
    simp only [invoke,resolved,lookup] at ok
    obtain ⟨results,hs,ok⟩ := except_bind_ok ok
    cases ok
    refine ⟨results,rfl,?_⟩
    intro d hd
    obtain ⟨y,hy,keep⟩ := filterMapM_checked hs d hd
    exact ⟨y,checkDemand_decision hy,keep⟩

private theorem forwarded_mem {sites : List (String × List Demand)} {acc : List Demand} {x : Demand}
    (member : x ∈ acc ∨ ∃ site ∈ sites, x ∈ site.2) :
    x ∈ sites.foldl (fun xs site => site.2.reverse ++ xs) acc := by
  induction sites generalizing acc with
  | nil => simpa using member
  | cons site rest ih =>
    apply ih
    rcases member with early | ⟨s,hs,hx⟩
    · exact .inl (List.mem_append_right _ early)
    · rcases List.mem_cons.mp hs with rfl | later
      · exact .inl (List.mem_append_left _ (List.mem_reverse.mpr hx))
      · exact .inr ⟨s,later,hx⟩

structure AcceptedCaller (f : FilePlans) (i fuel : Nat) (interfaces : List Published) (forwarding : List Nat)
    (forwarded : List Demand) where
  name : String
  position : Span
  request : Req f
  plan : PlanAt f i name position request
  codes : Array (CheckedCode (EquationStore.CheckedLabel f.F.equations f.F.primitive))
  evidence : List (ProgramCertificates.Evidence (EquationStore.CheckedLabel f.F.equations f.F.primitive))
  answers : CertificateProducer.Answered (RequestJson.graph request.toRequest)
  codeAnswers : inferCodes request fuel = .ok (codes,evidence,answers)
  origins : Table
  names : checkNames request.program.toArray (namedSites request.program.toArray) request.start request.inputs.length origins = true
  layout : request.siblings.length ≤ request.inputs.length
  checkedMay : checkMayInputs request.program.toArray origins request.start request.inputs.length
    ((knownSiblings request.inputs.length request.siblings interfaces).map Prod.fst) = true
  checked : ∀ {label node}, request.program[label]? = some node →
    let known := knownSiblings request.inputs.length request.siblings interfaces
    escapesDeclaration (origins.at label) known node = false ∧
    ∀ {callee recv args root producer}, node.expression = .invoke callee recv args →
      originOf (origins.at label) callee = some (.input root) →
      known.find? (·.1 == root) = some (root,producer) → ∀ d ∈ producer.interface.demands,
      ∃ decision, DemandDecision request codes origins forwarding producer label recv args d decision ∧
        ∀ next, decision = some next → next ∈ forwarded

/-- The exact single caller scan checked every selected demand and
published each forwarded requirement its branch produced. -/
theorem check_accepted_origins {f i fuel interfaces forwarding out} (ok : check f i fuel interfaces forwarding = .ok out) :
    ∃ a : AcceptedCaller f i fuel interfaces forwarding out,
      (CallbackOrigins.infer a.request.program (a.request.claims.map (·.context.length)).toArray a.request.start a.request.inputs.length).map
        (nameable (namedSites a.request.program.toArray)) = some a.origins := by
  unfold check at ok
  split at ok
  next p hp =>
    obtain ⟨plan,ep,ok⟩ := except_bind_ok ok
    obtain ⟨cp,ec,ok⟩ := except_bind_ok ok
    cases ep
    cases plan with
    | graph name pos r =>
      cases ec
      dsimp only at ok
      obtain ⟨⟨codes,evidence,answers⟩,codeAnswers,ok⟩ := except_bind_ok ok
      dsimp only at ok
      split at ok
      next raw hraw =>
        unfold checkUses at ok
        dsimp only at ok
        split at ok
        next => contradiction
        next names =>
          split at ok
          next => contradiction
          next layout =>
            split at ok
            next => contradiction
            next may =>
              obtain ⟨sites,checks,ok⟩ := except_bind_ok ok
              split at ok
              next => contradiction
              next =>
                cases ok
                refine ⟨⟨name,pos,r,hp,codes,evidence,answers,codeAnswers,_,by simpa using names,
                  by omega,by simpa using may,?_⟩,?_⟩
                case refl.refine_2 => simp [hraw]
                intro label node atNode
                obtain ⟨res,nodeOK,keep⟩ := filterMapM_checked checks (node,label)
                  (List.mem_zipIdx_iff_getElem?.mpr atNode)
                constructor
                · apply Bool.eq_false_iff.mpr
                  intro escape
                  unfold checkNode at nodeOK
                  simp [escape,throw,Except.bind,Bind.bind] at nodeOK
                · intro callee recv args root producer inv resolved lookup d hd
                  obtain ⟨results,rfl,decisions⟩ := checkedNode_demands nodeOK inv resolved lookup
                  obtain ⟨opt,hdec,forward⟩ := decisions d hd
                  exact ⟨opt,hdec,fun next eq => List.mem_eraseDups.mpr
                    (forwarded_mem (.inr ⟨_,keep _ rfl,forward _ eq⟩))⟩
      next => contradiction
  next => contradiction

theorem check_accepted {f i fuel interfaces forwarding out} (ok : check f i fuel interfaces forwarding = .ok out) :
    Nonempty (AcceptedCaller f i fuel interfaces forwarding out) := by
  obtain ⟨a,_⟩ := check_accepted_origins ok
  exact ⟨a⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck
