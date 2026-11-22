import Verification.Source.Claims.CallbackTypicalCaptures
import Verification.Source.Claims.CallbackTypicalDispatch
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open ControlFlow CallbackOrigins CallbackInferencePlan GraphCode ProgramTyping PositiveGraphs PositiveRules
open CallbackPreservation CallbackEffectInference TolerantFrames HeapObservations PassUnit LabelStore

theorem reachedHeapClosed {E K j h st h' st' t}
    (run : Execution (program E K) j h st h' st') (sim : Sim E K t st)
    (closed : Scoped 0 t) (heap : ∀ v ∈ h, Scoped 0 v) : ∀ v ∈ h', Scoped 0 v := by
  induction run generalizing t with
  | refl => exact heap
  | next tr tail ih =>
    obtain ⟨u,step,next⟩ := sim_step sim tr
    have both := TolerantFrames.ReadOnly.step_scoped step closed heap
    exact ih next both.1 both.2

/-- Syntactic witness for the checked literal and its ordinary fixed signature.
The claim contexts and code rows belong to the successful caller run. -/
structure CollectorLiteral {f caller fuel p forwarded} (a : AcceptedCaller f caller fuel [p] [] forwarded)
    (label cb : Nat) where
  site : Nat
  node : Node
  q : RequestJson.CodeRequest (EquationStore.CheckedLabel f.F.equations f.F.primitive)
  summary : Summary
  caps : List Tm
  kind : Invoke
  comp : ComponentTag
  fields : List PropKey
  vals : List Tm
  A : Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive)
  origin : originOf (a.origins.at label) (.var cb) = some (.allocated site)
  lookup : a.request.program[site]? = some node
  literal : node.expression = .makeAt (.graph q.entry.arity q.entry.exprs q.entry.conts q.entry.start caps kind q.entry.spine.isSome comp) fields vals
  width : caps.length = q.entry.captures.length
  member : (⟨q.entry,summary⟩ : CheckedCode _) ∈ a.codes
  singleArg : q.entry.row.arguments = [A]
  numeric : Represents (RequestJson.graph a.request.toRequest) A .num
  receiver : PromiseCalls.admitsUndef (RequestJson.graph a.request.toRequest) q.entry.row.receiver = true
  precondition : q.entry.row.effect.pre = []
  fixed : q.entry.spine = none
  arity : q.entry.arity = 1
  slotTypes : List (Option (Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive)))
  fromClaims : ∀ (i : Nat) A, slotTypes[i]?.join = some A → (a.request.claims[label]?.bind (·.context[i]?)) = some A
  named : checkCaptureSlots (a.origins.at site) (visibleNames slotTypes (a.origins.at label))
    (slotTypes.map (·.getD [])) caps q.entry.captures = true

def numericInvoke {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) : Tm → Bool
  | .invoke (.var _) .undef [.var arg] => (Γ[arg]?).any fun A => expand G A == [.num]
  | _ => false

theorem numericInvoke_spec {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {Γ fn br ba}
    (ok : numericInvoke G Γ (.invoke (.var fn) br ba) = true) :
    ∃ idx A, br = .undef ∧ ba = [.var idx] ∧ Γ[idx]? = some A ∧ Represents G A .num := by
  unfold numericInvoke at ok
  split at ok
  next slot arg eq =>
    simp only [Tm.invoke.injEq] at eq
    cases hit : Γ[arg]? with
    | none => simp [hit] at ok
    | some A =>
      simp [hit] at ok
      exact ⟨arg,A,eq.2.1,eq.2.2,hit,ok⟩
  next => contradiction

theorem TypicalPair.collectorBody {f caller producer fuel p forwarded}
    (pair : TypicalPair f caller producer fuel p forwarded) (over : PassUnit.OverStore f)
    {callerEntry k h₀ label h ρ x cb fn input} {node : Node}
    (callerValues : ∀ i < pair.callerRun.request.inputs.length, isVal (callerEntry i) = true)
    {n₀} {W₀ : WorldT n₀} (callerRoots : RootsOk W₀ callerEntry) (callerHeap : HeapOk n₀ W₀ h₀)
    (reached : Execution pair.callerRun.request.program k h₀ (.at pair.callerRun.request.start callerEntry) h (.at label ρ))
    (loc : pair.callerRun.request.program[label]? = some node)
    (direct : node.expression = .invoke (.var fn) .undef [.var x,.var cb])
    (binding : originOf (pair.callerRun.origins.at label) (.var fn) = some (.input input))
    (selected : (knownSiblings pair.callerRun.request.inputs.length pair.callerRun.request.siblings [p]).find? (·.1 == input) = some (input,p))
    (abi : checkedCallFrame p .undef [.var x,.var cb] = [.var x,.var cb])
    (present : absentCallback pair.callerRun.request label [.var x,.var cb] 1 = false)
    (literal : CollectorLiteral pair.callerRun label cb)
    {extra : List Tm} {n} {W : WorldT n} (heapClosed : ∀ v ∈ h, Scoped 0 v)
    (typed : PartialEnv (RequestJson.graph pair.callerRun.request.toRequest) literal.slotTypes ρ n W)
    (pointShape : ∀ l nd, pair.producerRun.request.program[l]? = some nd →
      ∀ slot br ba, nd.expression = .invoke (.var slot) br ba →
      (pair.producerRun.origins.at l)[slot]? = some [.input 1] →
      numericInvoke (StoreView.graph f.F.store) (((pair.producerRun.request.claims[l]?).map (·.context)).getD []) nd.expression = true) :
    let args := ρ x :: ρ cb :: extra
    let actual := envOf args .undef
    let G := StoreView.graph f.F.store
    TolerantFrames.Target.EntryHolds G pair.producerRun.request.inputs pair.producerRun.request.entrySeparation
      pair.producerRun.request.entryIndices actual n W h →
    RootsOk W actual → (∀ i, isVal (actual i) = true) →
    SafePostExcW (excOf G) (GoalHolds G pair.producerRun.request.goal (pair.producerRun.request.goal.argument actual))
      (fun _ _ _ _ => True) (fun _ _ _ => True) n W h
      (gotoOf pair.producerRun.request.program pair.producerRun.request.start args .undef pair.producerRun.request.comp) := by
  intro args actual G entry roots vals
  let a := pair.callerRun
  let b := pair.producerRun
  have hist := checkedNames_reached a.names callerValues reached
  let I := fun j (U : WorldT j) => RootsOk U actual ∧ PartialEnv (RequestJson.graph a.request.toRequest) literal.slotTypes ρ j U
  apply b.safeWithContext (η := G.env) (I := I) over entry roots vals ⟨roots,typed⟩
  · intro j U V hold ext
    exact ⟨fun i => RefsOk_mono ext (RefsOk_trunc _ (hold.1 i)),hold.2.transfer _ (Nat.le_succ _) _ ext⟩
  intro function br ba parameter state l nd env ticks after value j s slots inherited point path atNode invoked inOwn marked origin callback realized ready values refs steps budget finished
  have param : parameter = 1 := by simpa using marked
  subst parameter
  have publicMem := List.mem_eraseDups.mpr inOwn
  rw [← pair.emitted] at publicMem
  have decision := (a.checked loc).2 direct binding selected _ publicMem
  obtain ⟨_,check,_⟩ := decision
  unfold DemandDecision at check
  dsimp only at check
  rw [abi] at check
  rcases check with empty | absent | forwarded | accepted
  · exact empty_supply empty.1
  · have bad := present.symm.trans absent.1; contradiction
  · obtain ⟨pos,_,_,mem,_⟩ := forwarded
    cases mem
  · have numCheck := pointShape l nd atNode function br ba invoked origin
    rw [invoked] at numCheck
    obtain ⟨idx,A,rfl,rfl,slot,number⟩ := numericInvoke_spec numCheck
    have numeric := point_number point slot number
    have scope := TolerantFrames.ReadOnly.instantiate_scoped point.choose_spec.2.1 (.invoke (.var function) .undef [.var idx]) 0
    have closedStart : Scoped 0 (gotoOf b.request.program b.request.start args .undef b.request.comp) := by
      refine ⟨(scopedArgs_iff ..).mpr ?_,trivial⟩
      intro t member
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp member
      simpa [actual,envOf,List.getD_eq_getElem?_getD,hi] using entry.1.1 i
    have heapScope : ∀ v ∈ s.h, Scoped 0 v := by
      rw [← SourceElaboration.program_nodes b.request.program] at path
      exact reachedHeapClosed path .goto closedStart heapClosed
    have heapVals : ∀ (loc : Nat) (val : Tm), s.h[loc]? = some val → isVal val = true := by
      obtain ⟨n,W,h,pos,world,heap⟩ := s
      cases n with
      | zero => contradiction
      | succ n => exact HeapExpressionRules.heap_values world heap
    let demand := (atCall slots (certifiedPrivate b.request.program.toArray b.origins
      (privateAllocations b.request.program b.origins)) 1 state (.invoke (.var function) .undef [.var idx])).demand
    have passed : ∀ i t o j, ([Tm.var x,.var cb])[i]? = some t → originOf (a.origins.at label) t = some o →
        identity a.request.inputs.length o = some j → actual i = instantiate 0 ρ t := by
      intro i t _ _ lookup _ _
      cases i with
      | zero => simp at lookup; subst t; simp [actual,args,envOf,instantiate]
      | succ i =>
        cases i with
        | zero => simp at lookup; subst t; simp [actual,args,envOf,instantiate]
        | succ i => simp at lookup
    apply checkedNumericLiteral_supported a.names callerValues callerRoots callerHeap reached value accepted
      (by rfl : ([Tm.var x,.var cb])[demand.parameter]? = some (.var cb)) literal.origin literal.lookup
      literal.literal literal.width literal.member a.codeAnswers passed rfl callback ready values heapVals scope heapScope
      realized steps finished rfl budget inherited.1 refs numeric literal.singleArg literal.numeric literal.receiver
      literal.precondition literal.fixed literal.arity
    intro fs vs oid obj
    have same : instantiate 0 ρ (.var cb) = env function := by simpa [actual,args,envOf,instantiate] using callback
    have fromCaller := reached_partialCaptureTypes hist literal.origin literal.lookup literal.literal
      (checkCaptureSlots_sound literal.named) inherited.2 (by simpa [instantiate] using inherited.2.1 cb)
    rw [same,literal.fixed] at fromCaller
    exact fromCaller fs vs oid obj

end Verification.SourceClaimJson.CallbackInterfaceCheck
