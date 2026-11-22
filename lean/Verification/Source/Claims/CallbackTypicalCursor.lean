import Verification.Source.Claims.CallbackProducerReturns
import Verification.Source.Claims.CallbackCallerAccepted
namespace Verification.SourceClaimJson.CallbackInferencePlan
open ControlFlow GraphCode HeapObservations CallbackOrigins CallbackPreservation CallbackInterfaceCheck
open TolerantFrames Footprints

/-- The empty function expression as the source lowerer emits it. Its sole
variable read returns the preceding implicit undefined result. -/
def emptyExpressions : List Tm := [.nul,.var 0,.undef,.nul]
def emptyContinuations : List (Continuation × Option Target) :=
  [(.effect ⟨2,none⟩,none),(.ret,none),(.bind ⟨1,some [0,1,2]⟩,none),(.effect ⟨0,some [0,1]⟩,none)]

def emptyCallback : Tm → Bool
  | .objAt _ (.graph 0 E K 3 _ .call false _) _ => E == emptyExpressions && K == emptyContinuations
  | _ => false

private theorem emptyExecution (h : Heap) (ρ : Env) :
    Execution (program emptyExpressions emptyContinuations) 8 h (.at 3 ρ) h (.done .undef) := by
  refine .next (.enter (node := ⟨.nul,.effect ⟨0,some [0,1]⟩,none⟩) rfl) (.next (.effect rfl) ?_)
  refine .next (.enter (node := ⟨.nul,.effect ⟨2,none⟩,none⟩) rfl) (.next (.effect rfl) ?_)
  refine .next (.enter (node := ⟨.undef,.bind ⟨1,some [0,1,2]⟩,none⟩) rfl) (.next (.bind rfl) ?_)
  exact .next (.enter (node := ⟨.var 0,.ret,none⟩) rfl) (.next (.ret rfl) .refl)

private theorem doneUnique {P k h st h₁ v j h₂ w}
    (a : Execution P k h st h₁ (.done v)) (b : Execution P j h st h₂ (.done w)) : h₁ = h₂ := by
  generalize eq : State.done v = terminal at a
  induction a generalizing j with
  | refl => cases eq; cases b with | refl => rfl | next step _ => cases step
  | next step _ ih =>
    cases b with
    | refl => cases step
    | next other tail =>
      obtain ⟨rfl,rfl⟩ := transition_det step other
      exact ih tail eq

private theorem emptyShape {v} (test : emptyCallback v = true) :
    ∃ fs caps comp oid, v = .objAt fs (.graph 0 emptyExpressions emptyContinuations 3 caps .call false comp) oid := by
  unfold emptyCallback at test
  split at test
  · simp only [Bool.and_eq_true,beq_iff_eq] at test
    obtain ⟨rfl,rfl⟩ := test
    exact ⟨_,_,_,_,rfl⟩
  · contradiction

theorem emptyCall_heap {s : IndexedHeap} {fn br ba ρ ticks after v}
    (literal : emptyCallback (ρ fn) = true)
    (ready : readCall (.invoke (.var fn) br ba) = true) (values : ∀ i, isVal (ρ i) = true)
    (run : Steps ticks s.h (instantiate 0 ρ (.invoke (.var fn) br ba)) after v) (value : isVal v = true) :
    s.h = after := by
  have heapVals : ∀ (i : Nat) (t : Tm), s.h[i]? = some t → isVal t = true := by
    obtain ⟨n,W,h,pos,adm,ok⟩ := s
    cases n with | zero => contradiction | succ k => exact HeapExpressionRules.heap_values adm ok
  obtain ⟨_,_,frame,body,_,trace,dispatch,bodyRun⟩ := readCall_dispatch run value (readCall_instantiate ready values) heapVals
  obtain ⟨fs,caps,comp,oid,closed⟩ := emptyShape literal
  have callee : instantiate 0 ρ (.var fn) = .objAt fs (.graph 0 emptyExpressions emptyContinuations 3 caps .call false comp) oid := by simpa [instantiate] using closed
  obtain ⟨_,_,_,rfl⟩ := graph_dispatch trace callee dispatch
  exact doneUnique (emptyExecution s.h _) (execution_of_sim .goto bodyRun value)

theorem emptySupplies {P table privateRoots params out start entry h₀}
    (literals : ∀ i ∈ params, emptyCallback (entry i) = true) :
    SuppliedDemands P table privateRoots params out start entry h₀ := by
  intro fn br ba param state l node ρ ticks after v j s _ _ _ _ _ member eq _ ready vals _ steps _ value
  have same := emptyCall_heap (eq ▸ literals param member) ready vals steps value
  rw [← same]
  exact fun e _ _ u _ hu => ⟨u,hu,Change.Holds.refl ..⟩


def emptyMaker : Tm → Bool
  | .makeAt (.graph 0 E K 3 _ .call false _) _ _ => E == emptyExpressions && K == emptyContinuations
  | _ => false

/-- Inspect the same allocation identity checked for a literal at a lowered
call operand. The history proof below permits intermediate graph nodes. -/
def emptyArgumentAt (P : Program) (table : Table) (label arg : Nat) : Bool := Id.run do
  let some (.allocated site) := originOf (table.at label) (.var arg) | return false
  let some node := P[site]? | return false
  return emptyMaker node.expression

theorem emptyArgument_reached {P table entry inputs start label ρ h₀ h k arg}
    (names : checkNames P.toArray (namedSites P.toArray) start inputs table = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (run : Execution P k h₀ (.at start entry) h (.at label ρ))
    (argument : emptyArgumentAt P table label arg = true) : emptyCallback (ρ arg) = true := by
  unfold emptyArgumentAt at argument
  dsimp only [Id.run,pure,Pure.pure] at argument
  split at argument <;> try contradiction
  rename_i site orig
  split at argument <;> try contradiction
  rename_i node lookup
  obtain ⟨hist,b,valid,hb,born,eq,_,_⟩ := namedArguments_and_captureFrame (frame := [])
    (checkedNames_reached names values run) orig
  have atBirth := born.1
  rw [(valid site b hb).1,lookup] at atBirth
  cases Option.some.inj atBirth
  unfold emptyMaker at argument
  split at argument <;> try contradiction
  rename_i E K caps comp fields args literal
  simp only [Bool.and_eq_true,beq_iff_eq] at argument
  obtain ⟨rfl,rfl⟩ := argument
  obtain ⟨fs,oid,value⟩ := literalBirth born literal
  change ρ arg = b.value at eq
  rw [eq,value]
  rfl

/-- Safety of the accepted walker's source body at the two actuals of the
reached direct call. All ordinary source-entry hypotheses refer to the
particular frame installed by that call. -/
theorem typicalEmpty_body_safe {f caller producer fuel published forwarded own}
    (callerRun : AcceptedCaller f caller fuel [published] [] forwarded)
    (producerRun : AcceptedProducer f producer fuel [1] own) (over : PassUnit.OverStore f)
    {callerEntry k before label ρ h xsSlot cbSlot functionSlot}
    (callerValues : ∀ i < callerRun.request.inputs.length, isVal (callerEntry i) = true)
    (reached : Execution callerRun.request.program k before (.at callerRun.request.start callerEntry) h (.at label ρ))
    {node : Node} (_callNode : callerRun.request.program[label]? = some node)
    (_direct : node.expression = .invoke (.var functionSlot) .undef [.var xsSlot,.var cbSlot])
    (empty : emptyArgumentAt callerRun.request.program callerRun.origins label cbSlot = true)
    {siblings : List Tm} {d n} {W : WorldT n} {η} :
    let L := ρ xsSlot :: ρ cbSlot :: siblings
    Target.EntryHolds (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η)
      producerRun.request.inputs producerRun.request.entrySeparation producerRun.request.entryIndices (envOf L d) n W h →
    RootsOk W (envOf L d) → (∀ i, isVal (envOf L d i) = true) →
    SafePostExcW (PositiveRules.excOf (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η))
      (GoalHolds (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η) producerRun.request.goal
        (producerRun.request.goal.argument (envOf L d))) (fun _ _ _ _ => True) (fun _ _ _ => True) n W h
      (PassUnit.gotoOf producerRun.request.program producerRun.request.start L d producerRun.request.comp) := by
  intro L entry refs vals
  apply producerRun.safe over entry refs vals
  apply emptySupplies
  intro i hi
  cases List.mem_singleton.mp hi
  change emptyCallback (ρ cbSlot) = true
  exact emptyArgument_reached callerRun.names callerValues reached empty

end Verification.SourceClaimJson.CallbackInferencePlan
