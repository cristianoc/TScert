import Verification.Source.Claims.CallbackProducerClosure
import Verification.Source.Claims.CallbackPublicApplication
import Verification.Source.Claims.CallbackCallerAssertions
import Verification.Source.Claims.CallbackLinkedEntry

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackInferencePlan GraphCode ControlFlow ProgramTyping PositiveGraphs PositiveRules LabelStore
open PassUnit HeapObservations TolerantFrames

private abbrev FileTy (f : FilePlans) :=
  Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive)

private def inspect (value : α) : {v // v = value} := ⟨value,rfl⟩

private def requireCheck (reason : String) (p : Prop) [Decidable p] : Except String (PLift p) :=
  if checked : p then .ok ⟨checked⟩ else .error reason

/-- The producer checks its source binding once. Callers receive the
published requirements and types, and never inspect the producer plan. -/
structure SourceProducer (f : FilePlans) (member : Nat) (p : Published) where
  source : SourceModule f
  sourceBinding : readSourceModule f member member member = .ok source
  formals : List (FileTy f)
  result : FileTy f
  callable : ∀ (outside : String → Nat → Tm) fields oid captures,
    captures.length = source.types.length →
    let G := StoreView.graph f.F.store
    ConditionalCall G formals result p.interface ((source.realize outside fields oid).closure captures)
      (fun n W => EnvOk G source.types (envOf captures .undef) n W)
  captureWidth : source.types.length = source.bindings.length

def certifySourceProducer {f : FilePlans} {i : Nat} {p : Published}
    (over : OverStore f) (safe : ProducerMemberSafe f i p) : Except String (SourceProducer f i p) := do
  let ⟨some (.ok (.graph name pos r)),found⟩ := inspect (f.plans[i]?) | throw "missing source producer plan"
  let ⟨source, sourceBinding⟩ ← match checked : readSourceModule f i i i with
    | .error why => .error why
    | .ok source => .ok (⟨source,checked⟩ : {source // readSourceModule f i i i = .ok source})
  let ⟨agreement⟩ ← requireCheck "published binding and producer module layout disagree"
    (source.agrees r p.name .outside)
  let formals := r.inputs.take source.graph.ar
  let ⟨width⟩ ← requireCheck "publication does not have the producer's fixed arity" (p.formals = formals.length)
  let ⟨resultEq⟩ ← requireCheck (CallbackPreservation.scopeRefusal "emptyProducerEntryFacts"
    "producer entry has unchecked index or separation facts")
    (r.entryIndices = [] ∧ r.entrySeparation.facts = [])
  let ⟨.plain result,goal⟩ := inspect r.goal | throw (CallbackPreservation.scopeRefusal "plainProducerResult" "expected a plain producer result")
  let ⟨valid⟩ ← requireCheck "invalid published callback interface" (p.referencesFixedParameters = true)
  let ⟨captureWidth⟩ ← requireCheck "published source capture widths disagree"
    (source.types.length = source.bindings.length)
  return ⟨source,sourceBinding,formals,result,by
    intro outside fields oid captures capWidth G
    obtain ⟨_,otherName,otherPos,other,plan,_,_,body,_,_,_,_⟩ := safe
    have same := plan.symm.trans found.symm
    simp only [Option.some.injEq, Except.ok.injEq, FunctionPlan.graph.injEq] at same
    obtain ⟨_,_,requestEq⟩ := same
    subst other
    have arity := agreement.2.2.1
    have bodyCode := agreement.2.1
    have layout : r.inputs = formals ++ source.types := by
      rw [agreement.2.2.2.2.2, ← arity, List.take_append_drop]
    have exactArity : formals.length = source.graph.ar := by
      simp [formals,arity,Nat.min_eq_left (Nat.sub_le ..)]
    have closure : (source.realize outside fields oid).closure captures =
        sourceClosure r formals.length captures fields oid := by
      simp [SourceModule.realize,ModuleCode.closure,sourceClosure,bodyCode,exactArity,
        agreement.2.2.2.1,realizedCode]
    rw [closure]
    have h := producerClosure_conditionalCall (fields := fields) (oid := oid) body
      (by simp [Published.validate,valid]) width layout capWidth goal.symm resultEq.1 resultEq.2
    simpa [G,RequestJson.graph,over.graph (show PlanAt f i name pos r from found.symm)] using h,
    captureWidth⟩

/-- The installed source module uses the caller's checked binding order.
Producer code enters this judgment through its certified publication. -/
def PublicModuleCallerSafe {f : FilePlans} {j : Nat} (r : Req f) (p : Published)
    (producer : SourceProducer f j p) (caller : SourceModule f) (k : Nat) : Prop :=
  ∀ (outside : String → Nat → Tm) fields identities,
    let code := sourceModules caller producer.source outside fields identities
    ∀ depth (args : List Tm) d n (W : WorldT n) h,
    args.length = r.inputs.length - r.siblings.length →
    let captures := (code .producer).captured (approxEnv code depth) depth
    let L := args ++ (code .caller).captured (approxEnv code (depth+1)) (depth+1) ++ [approx code (depth+1) .caller]
    let ρ := envOf L d
    let G := RequestJson.graph r.toRequest
    EnvOk G producer.source.types (envOf captures .undef) n W →
    PartialEnv G (callerEntryTypes r.inputs (r.inputs.length - r.siblings.length + k)) ρ n W →
    RootsOk W ρ → (∀ i, isVal (ρ i) = true) → WorldAdm W → HeapOk n W h →
    HeapSeparation.Holds r.entrySeparation ρ → HeapKnowledge.IndexHolds ⟨ρ,h⟩ r.entryIndices ρ h →
    SafePostExc (excOf G) (GoalHolds G r.goal (r.goal.argument ρ)) (fun _ _ => True) (fun _ => True)
      n W h (gotoOf r.program r.start L d r.comp) ∧
    ∀ l K, (l,K) ∈ r.assertions → ∀ j h' ρ', j < n → ReachesIn r.program j h (.at r.start ρ) h' (.at l ρ') →
      HeapKnowledge.Holds K ⟨ρ,h⟩ ρ' h'

private theorem sourceCaller_safe {f : FilePlans} {r : Req f} {p : Published} {j : Nat}
    {producer : SourceProducer f j p} {caller : SourceModule f} {name k}
    (agreement : caller.agrees r name (fun n => if n = p.name then .linked .producer else .outside n))
    (sibling : r.siblings[k]? = some p.name)
    (store : RequestJson.graph r.toRequest = StoreView.graph f.F.store)
    (call : PublicCallerEntry r (r.inputs.length - r.siblings.length + k) p producer.formals producer.result)
    (assertions : OpaqueAssertions r (r.inputs.length - r.siblings.length + k)) :
    PublicModuleCallerSafe r p producer caller k := by
  intro outside fields identities code depth args d n W h arity captures L ρ G hosts typed roots values world heap sep idx
  let input := r.inputs.length - r.siblings.length + k
  have capLen : captures.length = producer.source.types.length := by
    simp [captures,code,sourceModules,SourceModule.realize,ModuleCode.captured,producer.captureWidth]
  have slotLook : ((code .caller).captured (approxEnv code (depth+1)) (depth+1))[k]? =
      some ((code .producer).closure captures) := by
    simp [code,sourceModules,SourceModule.realize,ModuleCode.captured,agreement.2.2.2.2.1,
      List.getElem?_map,sibling,Slot.valueAt,approxEnv,captures]
  have linked : ρ input = (code .producer).closure captures := by
    have small := (List.getElem?_eq_some_iff.mp slotLook).1
    have offset : input = args.length + k := by simp [input,arity]
    simp [offset,ρ,L,envOf,List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : args.length ≤ args.length+k),
      List.getElem?_append_left small,slotLook]
  have closure := producer.callable outside (fields .producer) (identities .producer) captures capLen
  change ConditionalCall (StoreView.graph f.F.store) producer.formals producer.result p.interface
    ((code .producer).closure captures) _ at closure
  rw [← linked, ← store] at closure
  have sourceValue : excOf G n W (ρ input) := by
    have scope := typed.1 input
    rw [linked] at scope ⊢
    exact opaqueObject_source (by simp) scope
  constructor
  · exact call L d n W h (fun j U => EnvOk G producer.source.types (envOf captures .undef) j U)
      (fun {_ _ _} le {_} ext keep => keep.transfer _ le _ ext) hosts closure typed roots values world heap
  · have q := assertions G.env n W h ρ
    dsimp only at q
    rw [reassign_env] at q
    exact q typed sourceValue sep idx world heap roots

def PublicModuleMemberSafe {f : FilePlans} {j : Nat} (i : Nat) (p : Published) (producer : SourceProducer f j p) : Prop :=
  f.fr.group i = [i] ∧
  ∃ (r : Req f) (name : String) (pos : Span) (caller : SourceModule f) (k : Nat), PlanAt f i name pos r ∧
    readSourceModule f i j i = .ok caller ∧
    caller.agrees r name (fun n => if n = p.name then .linked .producer else .outside n) ∧
    r.siblings[k]? = some p.name ∧ PublicModuleCallerSafe r p producer caller k ∧
    FootprintClause r ∧ EnsuresClause r ∧ RegionalClause r ∧ CodeAssertionsClause r ∧ declaredEffect r = true

/-- The verified caller currently exports a plain exit contract. -/
def callerPlainExit {f : FilePlans} (r : Req f) : Bool :=
  r.footprint == .top && !r.fresh && !r.onThrow && r.ensures.isEmpty && r.regional.isNone

def certifyModuleCaller {f : FilePlans} (i j fuel : Nat) {p : Published}
    (producer : SourceProducer f j p) (over : OverStore f) :
    Except String (PLift (PublicModuleMemberSafe i p producer)) := do
  let ⟨group⟩ ← requireCheck "caller must be a singleton source unit" (f.fr.group i = [i])
  let ⟨some (.ok (.graph name pos r)),found⟩ := inspect (f.plans[i]?) | throw "missing source caller plan"
  let plan : PlanAt f i name pos r := found.symm
  let ⟨stated⟩ ← requireCheck "caller body contract exceeds its declared effect" (declaredEffect r = true)
  let ⟨exits⟩ ← requireCheck (CallbackPreservation.scopeRefusal "callerPlainExit"
    "caller exit contract requires a separate footprint or postcondition proof")
    (callerPlainExit r = true)
  let ⟨caller, sourceBinding⟩ ← match checked : readSourceModule f i j i with
    | .error why => .error why
    | .ok caller => .ok (⟨caller,checked⟩ : {caller // readSourceModule f i j i = .ok caller})
  let ⟨agreement⟩ ← requireCheck "caller module layout disagrees with its plan"
    (caller.agrees r name (fun n => if n = p.name then .linked .producer else .outside n))
  let some k := r.siblings.idxOf? p.name | throw "producer is not a caller capture"
  let ⟨slot⟩ ← requireCheck "caller capture names a different declaration" (r.siblings[k]? = some p.name)
  let input := r.inputs.length - r.siblings.length + k
  let ⟨checked⟩ ← certifyPublicCaller r plan fuel p producer.formals producer.result input
  let ⟨assertions⟩ ← certifyOpaqueAssertions r input fuel
  return ⟨by
    have store : RequestJson.graph r.toRequest = StoreView.graph f.F.store := by simp [RequestJson.graph,over.graph plan]
    simp only [callerPlainExit,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',List.isEmpty_iff,Option.isNone_iff_eq_none] at exits
    exact ⟨group,r,name,pos,caller,k,plan,sourceBinding,agreement,slot,sourceCaller_safe agreement slot store checked.1 assertions,
      by simp [FootprintClause,exits.1.1.1.1,exits.1.1.1.2,exits.1.1.2],by simp [EnsuresClause,exits.1.2],
      by simp [RegionalClause,exits.2],checked.2,stated⟩⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck
