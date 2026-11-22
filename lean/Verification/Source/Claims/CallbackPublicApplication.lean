import Verification.Source.Claims.CallbackPublicLiteral
import Verification.Source.Claims.CallbackPrefixWitness

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins CallbackPreservation CallbackEffectInference CallbackInferencePlan LabelStore CertificateProducer
open ProgramTyping PositiveGraphs PositiveRules GraphCode CallEffects Footprints HeapObservations TolerantFrames
open ControlFlow ProgramCertificates CallArguments PassUnit

private def inspect (x : α) : {y // x = y} := ⟨x,rfl⟩

private def requireCheck (why : String) (p : Prop) [Decidable p] : Except String (PLift p) :=
  if h : p then .ok ⟨h⟩ else .error why

/-- A fixed argument at a source application is a saved operand. Each slot
type is checked against the corresponding public declaration parameter. -/
inductive FixedArguments {ι : Type} (G : NormalGraph ι) (slots : List (Option (Ty ι))) :
    List Tm → List (Ty ι) → Prop where
  | nil : FixedArguments G slots [] []
  | cons {i x y rest types} : slots[i]?.join = some x → FamLe (meaning G x) (meaning G y) →
      FixedArguments G slots rest types → FixedArguments G slots (.var i :: rest) (y :: types)

@[nospecialize] def readFixedArguments {ι : Type} [Labels ι] [Instantiates ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (slots : List (Option (Ty ι))) :
    (terms : List Tm) → (formals : List (Ty ι)) → Except String (PLift (FixedArguments G slots terms formals))
  | [], [] => return ⟨.nil⟩
  | .var i :: rest, y :: types => do
    let ⟨some x,slot⟩ := inspect (slots[i]?.join) | throw "untyped producer operand"
    let some evidence := (subtypeSearch G images x y).value | throw "producer operand fails its declared type"
    let ⟨checked⟩ ← requireCheck "invalid producer operand comparison" (PositiveCertificates.checkUsing G images x y evidence = true)
    let ⟨tail⟩ ← readFixedArguments G images slots rest types
    return ⟨.cons slot (PositiveCertificates.acceptedUsing checked) tail⟩
  | _, _ => throw (CallbackPreservation.scopeRefusal "readFixedArguments" "expected the fixed declared arguments in saved slots")

theorem FixedArguments.typed {ι : Type} {G : NormalGraph ι} {slots frame formals}
    (fixed : FixedArguments G slots frame formals) {ρ n W}
    (typed : PartialEnv G slots ρ n W) : ArgsT (formals.map (meaning G)) n W (instantiateArgs 0 ρ frame) := by
  induction fixed with
  | nil => trivial
  | cons pos compare _ ih => exact ⟨compare _ _ _ (typed.2 _ _ pos),ih⟩

theorem FixedArguments.refs {ι : Type} {G : NormalGraph ι} {slots frame formals}
    (fixed : FixedArguments G slots frame formals) {ρ n} {W : WorldT n}
    (roots : RootsOk W ρ) : RootsOk W (envOf (instantiateArgs 0 ρ frame) .undef) := by
  apply envOf_refs_of _ RefsOk_undef
  induction fixed with
  | nil => simp [instantiateArgs]
  | cons _ _ _ ih => simpa [instantiateArgs,instantiate] using And.intro (roots _) ih

/-- Read each demand solely from the interface already available to the
caller, selecting its supplied closure from the caller's own checked code. -/
def CanSupply {τ ι : Type} [Labels ι] [StoreView τ ι] (r : SourceElaboration.SourceRequest τ ι)
    (origins : Table) (codes : Array (CheckedCode ι)) (slots : List (Option (Ty ι))) (l : Nat)
    (frame : List Tm) (formals : List (Ty ι)) (d : Demand) : Prop :=
  d.support.normal.isEmpty = true ∨
    ∃ argument row, ∃ lit : FixedLiteral r.program origins codes l argument slots,
      frame[d.parameter]? = some argument ∧ absentCallback r l frame d.parameter = false ∧
      formals[d.parameter]?.bind (fixedCallbackSignature (RequestJson.graph r.toRequest)) = some row ∧
      LiteralDomain (RequestJson.graph r.toRequest) row lit.q.entry.row

@[nospecialize] def readSupplies {τ ι : Type} [Labels ι] [StoreView τ ι] [Instantiates ι]
    (r : SourceElaboration.SourceRequest τ ι) (origins : Table) (codes : Array (CheckedCode ι))
    (slots : List (Option (Ty ι))) (l : Nat) (frame : List Tm) (formals : List (Ty ι)) :
    (demands : List Demand) → Except String (PLift (∀ d ∈ demands, CanSupply r origins codes slots l frame formals d))
  | [] => return ⟨by simp⟩
  | d :: ds => do
    let G := RequestJson.graph r.toRequest
    let head : Except String (PLift (CanSupply r origins codes slots l frame formals d)) := do
      if empty : d.support.normal.isEmpty = true then return ⟨.inl empty⟩
      let ⟨some arg,position⟩ := inspect (frame[d.parameter]?) | throw (CallbackPreservation.scopeRefusal "presentCallback" "missing demanded literal")
      let ⟨some row,sig⟩ := inspect (formals[d.parameter]?.bind (fixedCallbackSignature G))
        | throw (CallbackPreservation.scopeRefusal "fixedCallbackSignature" "expected one declared fixed callback signature")
      let ⟨present⟩ ← requireCheck (CallbackPreservation.scopeRefusal "presentCallback" "demanded literal is absent") (absentCallback r l frame d.parameter = false)
      let ⟨literal,domain⟩ ← readFixedLiteral G (StoreView.images r.types) r.program origins codes r.codes l arg slots row
      return ⟨.inr ⟨arg,row,literal,position,present,sig,domain.down⟩⟩
    let ⟨supply⟩ ← head
    let ⟨tail⟩ ← readSupplies r origins codes slots l frame formals ds
    return ⟨fun d' mem => (List.mem_cons.mp mem).elim (fun eq => eq ▸ supply) (tail d')⟩

theorem suppliedAtCall {f caller fuel p forwarded} (a : AcceptedCaller f caller fuel [p] [] forwarded)
    {slots label node frame formals fn input}
    (found : a.request.program[label]? = some node) (invoked : node.expression = .invoke (.var fn) .undef frame)
    (binding : originOf (a.origins.at label) (.var fn) = some (.input input))
    (selected : (knownSiblings a.request.inputs.length a.request.siblings [p]).find? (·.1 == input) = some (input,p))
    (abi : checkedCallFrame p .undef frame = frame)
    (supplies : ∀ d ∈ p.interface.demands, CanSupply a.request a.origins a.codes slots label frame formals d)
    {entry h₀ h ρ k n₀} {W₀ : WorldT n₀}
    (callerValues : ∀ i < a.request.inputs.length, isVal (entry i) = true)
    (callerRoots : RootsOk W₀ entry) (callerHeap : HeapOk n₀ W₀ h₀)
    (reached : Execution a.request.program k h₀ (.at a.request.start entry) h (.at label ρ)) :
    let G := RequestJson.graph a.request.toRequest
    let actual := envOf (instantiateArgs 0 ρ frame) .undef
    PublicDemandsWith (fun n W => RootsOk W actual ∧ PartialEnv G slots ρ n W)
      (formalDomain G formals) p.interface actual := by
  intro G actual d member s recv args keep domain _ values _ recvRefs argRefs correspondence
  intro ticks after v run budget finish
  rcases supplies d member with empty | ⟨arg,row,lit,pos,present,sig,domainOk⟩
  · exact empty_supply empty
  obtain ⟨_,decided,_⟩ := (a.checked found).2 invoked binding selected d member
  unfold DemandDecision at decided
  dsimp only at decided
  rw [abi] at decided
  rcases decided with empty | absent | forward | use
  · exact empty_supply empty.1
  · exact (by simp [present] at absent)
  · obtain ⟨_,_,_,mem,_⟩ := forward; cases mem
  · apply lit.satisfies callerValues callerRoots callerHeap reached use pos _ s keep.2 keep.1 recvRefs argRefs
      (domainOk.holds (domain row sig)) values _ run budget finish
    · intro i term _ _ atI _ _
      simp [actual,envOf,instantiateArgs_eq_map,List.getD_eq_getElem?_getD,List.getElem?_map,atI]
    · intro i x named
      exact Option.some.inj (correspondence i x [] named)

/-- Application of an opaque conditional binding at any reached fixed call.
The enclosing continuation, its proof, and the producer body play no role
in establishing safety of the invocation. -/
theorem publicInvoke_safe {f caller fuel p forwarded} (a : AcceptedCaller f caller fuel [p] [] forwarded)
    {slots label node frame formals fn input result}
    (found : a.request.program[label]? = some node) (invoked : node.expression = .invoke (.var fn) .undef frame)
    (binding : originOf (a.origins.at label) (.var fn) = some (.input input))
    (selected : (knownSiblings a.request.inputs.length a.request.siblings [p]).find? (·.1 == input) = some (input,p))
    (abi : checkedCallFrame p .undef frame = frame)
    (fixed : FixedArguments (RequestJson.graph a.request.toRequest) slots frame formals)
    (supplies : ∀ d ∈ p.interface.demands, CanSupply a.request a.origins a.codes slots label frame formals d)
    {entry h₀ h ρ j n₀} {W₀ : WorldT n₀}
    (callerValues : ∀ i < a.request.inputs.length, isVal (entry i) = true)
    (callerRoots : RootsOk W₀ entry) (callerHeap : HeapOk n₀ W₀ h₀)
    (reached : Execution a.request.program j h₀ (.at a.request.start entry) h (.at label ρ))
    {Allowed : ∀ n, WorldT n → Prop}
    (linked : ConditionalCall (RequestJson.graph a.request.toRequest) formals result p.interface (entry input) Allowed)
    {n} {W : WorldT n} (allowed : Allowed n W)
    (typed : PartialEnv (RequestJson.graph a.request.toRequest) slots ρ n W) (roots : RootsOk W ρ)
    (adm : WorldAdm W) (heap : HeapOk n W h) :
    let G := RequestJson.graph a.request.toRequest
    SafePostExc (excOf G) (meaning G result) (fun _ _ => True) (fun _ => True) n W h (instantiate 0 ρ node.expression) := by
  intro G
  let args := instantiateArgs 0 ρ frame
  let actual := envOf args .undef
  obtain ⟨_,_,_,_,_,held⟩ := checkedNames_reached a.names callerValues reached
  obtain ⟨_,hvar,slot⟩ := namedOrigin_slot binding
  cases hvar
  have same : entry input = ρ fn := (held fn (.input input) (by simp [CallbackOrigins.namedAt,slot])).1.2
  rw [invoked]
  change SafePostExc _ _ _ _ _ _ _ (.invoke (ρ fn) .undef args)
  rw [← same]
  let I := fun k (V : WorldT k) => RootsOk V actual ∧ PartialEnv G slots ρ k V
  have persist : ∀ {k} {V : WorldT (k+1)} {Z : WorldT k}, I (k+1) V → WExt (trunc k (Nat.le_succ _) V) Z → I k Z :=
    fun keep ext => ⟨fun i => RefsOk_mono ext (RefsOk_trunc _ (keep.1 i)),keep.2.transfer _ (Nat.le_succ _) _ ext⟩
  have argRoots := fixed.refs roots
  exact linked args n W h I persist allowed ⟨argRoots,typed⟩ (fixed.typed typed) argRoots
    (same.symm ▸ roots fn) adm heap (suppliedAtCall a found invoked binding selected abi supplies callerValues callerRoots callerHeap reached)

/-- A checked application in tail position. The declaration and its result
type are public. The caller prefix is checked using only the caller's code
table. Its continuation returns the result of this particular invocation. -/
structure PublicTail {f : FilePlans} (r : Req f) (p : Published) (formals : List (Ty _))
    (result : Ty _) (origins : Table) (codes : Array (CheckedCode _)) (input : Nat) where
  label : Nat
  node : Node
  fn : Nat
  frame : List Tm
  loc : r.program[label]? = some node
  direct : node.expression = .invoke (.var fn) .undef frame
  binding : originOf (origins.at label) (.var fn) = some (.input input)
  selected : (knownSiblings r.inputs.length r.siblings [p]).find? (·.1 == input) = some (input,p)
  abi : checkedCallFrame p .undef frame = frame
  slots : List (Option (Ty _))
  args : FixedArguments (RequestJson.graph r.toRequest) slots frame formals
  supplies : ∀ d ∈ p.interface.demands, CanSupply r origins codes slots label frame formals d
  prefixPlan : PrefixPlan (RequestJson.graph r.toRequest) (StoreView.images r.types)
    (admits (codes.toList.map (·.entry))) r.program label slots r.start (callerEntryTypes r.inputs input)
  ret : Nat
  mapping : List Nat
  cont : node.continuation = .bind ⟨ret,some (0::mapping)⟩
  last : r.program[ret]? = some ⟨.var 0,.ret,none⟩
  noHandler : node.handler = none
  source : r.program.all (fun nd => ObjectCoherence.sourceTerm nd.expression) = true
  callerResult : Ty _
  goal : r.goal = .plain callerResult
  returns : FamLe (meaning (RequestJson.graph r.toRequest) result) (meaning (RequestJson.graph r.toRequest) callerResult)

private theorem singleSelection {inputs names p slot i selected}
    (hit : (knownSiblings inputs names [p]).find? (·.1 == slot) = some (i,selected)) : i = slot ∧ selected = p := by
  have matchesSlot := List.find?_some hit
  refine ⟨eq_of_beq matchesSlot,?_⟩
  have member := List.mem_of_find?_eq_some hit
  obtain ⟨⟨name,j⟩,_,row⟩ := List.mem_filterMap.mp member
  obtain ⟨found,whereAt,same⟩ := Option.map_eq_some_iff.mp row
  have picked := List.mem_of_find?_eq_some whereAt
  cases same
  simpa using picked

def readPublicTail {f : FilePlans} (r : Req f) (p : Published) (formals : List (Ty _)) (result : Ty _)
    (origins : Table) (codes : Array (CheckedCode _)) (answers : Answered (RequestJson.graph r.toRequest))
    (fuel input : Nat) : Except String (PublicTail r p formals result origins codes input) := do
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let some (_,label) := r.program.zipIdx.find? (fun (nd,l) => match nd.expression with
    | .invoke fn _ _ => originOf (origins.at l) fn == some (.input input)
    | _ => false) | throw (CallbackPreservation.scopeRefusal "fixedDirectApplication" "missing direct application of published declaration")
  let ⟨some node,loc⟩ := inspect (r.program[label]?) | throw "missing application node"
  let ⟨.invoke (.var fn) .undef frame,direct⟩ := inspect node.expression | throw (CallbackPreservation.scopeRefusal "fixedDirectApplication" "expected a receiverless direct application")
  let ⟨binding⟩ ← requireCheck "callee does not resolve to the selected declaration" (originOf (origins.at label) (.var fn) = some (.input input))
  let ⟨some (selectedSlot,selectedInterface),found⟩ := inspect ((knownSiblings r.inputs.length r.siblings [p]).find? (·.1 == input))
    | throw "caller capture does not identify the publication"
  have selected : (knownSiblings r.inputs.length r.siblings [p]).find? (·.1 == input) = some (input,p) := by
    obtain ⟨rfl,rfl⟩ := singleSelection found
    exact found
  let ⟨abi⟩ ← requireCheck (CallbackPreservation.scopeRefusal "fixedDirectApplication"
    "application disagrees with fixed receiverless public signature") (checkedCallFrame p .undef frame = frame)
  let ⟨.bind ⟨ret,some (0::mapping)⟩,cont⟩ := inspect node.continuation | throw (CallbackPreservation.scopeRefusal "directCallbackReturn" "expected a direct return")
  let ⟨last⟩ ← requireCheck (CallbackPreservation.scopeRefusal "directCallbackReturn"
    "application result is not returned directly") (r.program[ret]? = some ⟨.var 0,.ret,none⟩)
  let ⟨noHandler⟩ ← requireCheck (CallbackPreservation.scopeRefusal "directCallbackReturn" "handler on the direct application") (node.handler = none)
  let ⟨source⟩ ← requireCheck "non-source caller expression" (r.program.all (fun nd => ObjectCoherence.sourceTerm nd.expression) = true)
  let ⟨.plain callerResult,goal⟩ := inspect r.goal | throw (CallbackPreservation.scopeRefusal "plainCallerResult" "expected an ordinary caller result")
  let some evidence := (subtypeSearch G images result callerResult).value | throw "producer result does not meet caller signature"
  let ⟨sub⟩ ← requireCheck "invalid result comparison" (PositiveCertificates.checkUsing G images result callerResult evidence = true)
  let pool := vocabulary G r.searchLabels r.claims r.inputs
  let some filler := pool.find? (PromiseCalls.admitsUndef G) | throw (CallbackPreservation.scopeRefusal "readPrefixPlan" "missing undefined input filler")
  let ⟨fill⟩ ← requireCheck "invalid filler" (PromiseCalls.admitsUndef G filler = true)
  let some ⟨slots,prefixPlan⟩ := readPrefixPlan G images (admits (codes.toList.map (·.entry))) pool r.aliases fuel answers
    r.program r.claims label filler fill (r.program.length+1) r.start (callerEntryTypes r.inputs input)
    | throw (CallbackPreservation.scopeRefusal "readPrefixPlan" "uncertified caller prefix")
  let ⟨args⟩ ← readFixedArguments G images slots frame formals
  let ⟨supplies⟩ ← readSupplies r origins codes slots label frame formals p.interface.demands
  return ⟨label,node,fn,frame,loc,direct,binding,selected,abi,slots,args,supplies,prefixPlan,ret,mapping,
    cont,last,noHandler,source,callerResult,goal,PositiveCertificates.acceptedUsing sub⟩

theorem PublicTail.safe {f caller fuel p forwarded} {a : AcceptedCaller f caller fuel [p] [] forwarded}
    {formals result input} (site : PublicTail a.request p formals result a.origins a.codes input)
    {startL startD n} {W : WorldT n} {h₀}
    (typed : PartialEnv (RequestJson.graph a.request.toRequest) (callerEntryTypes a.request.inputs input) (envOf startL startD) n W)
    (roots : RootsOk W (envOf startL startD)) (vals : ∀ i, isVal (envOf startL startD i) = true)
    {Allowed : ∀ n, WorldT n → Prop}
    (stable : ∀ {k} {U : WorldT k} {j} (le : j ≤ k) {V}, WExt (trunc j le U) V → Allowed k U → Allowed j V)
    (allowed : Allowed n W)
    (linked : ConditionalCall (RequestJson.graph a.request.toRequest) formals result p.interface (envOf startL startD input) Allowed)
    (world : WorldAdm W) (heap : HeapOk n W h₀) :
    let G := RequestJson.graph a.request.toRequest
    SafePostExc (excOf G) (GoalHolds G a.request.goal (a.request.goal.argument (envOf startL startD)))
      (fun _ _ => True) (fun _ => True) n W h₀ (gotoOf a.request.program a.request.start startL startD a.request.comp) := by
  intro G
  rw [site.goal]
  let entry := envOf startL startD
  apply site.prefixPlan.safe (Keep := Allowed) (inferCodes_table_sound a.codeAnswers) site.source stable _ (.refl : Execution a.request.program 0 h₀ (.at a.request.start entry) _ _)
    typed roots vals allowed world heap
  intro j h L d m U reached current point root values adm ok
  let P := a.request.program
  let c := a.request.comp
  let ρ := envOf L d
  have outer := gotoOf_refsOk (start := site.label) (comp := c) site.source root
  let E := P.map (·.expression)
  let K := P.map fun nd => (nd.continuation,nd.handler)
  have atExpr : E[site.label]? = some site.node.expression := by simp [E,P,List.getElem?_map,site.loc]
  have atCont : K[site.label]? = some (.bind ⟨site.ret,some (0::site.mapping)⟩,none) := by simp [K,P,List.getElem?_map,site.loc,site.cont,site.noHandler]
  have endExpr : E[site.ret]? = some (.var 0) := by simp [E,P,List.getElem?_map,site.last]
  have endCont : K[site.ret]? = some (.ret,none) := by simp [K,P,List.getElem?_map,site.last]
  have enter : Step h (gotoOf P site.label L d c) h
      (.frame E K (instantiate 0 ρ site.node.expression) L d (.bind ⟨site.ret,some (0::site.mapping)⟩) none c) := .gotoEnter atExpr atCont
  have pre : AdminPrefix U h _ _ := .next outer enter .refl
  apply pre.safe adm ok
  intro k le
  have w := WorldAdm_trunc le adm
  have hh := heapAtLower le ok
  have pt := point.transfer k le _ (WExt_refl _)
  apply returnCall_safe (PositiveGraphs.builtinExc_adm G _) (meaning_adm G site.callerResult) endExpr endCont
    w hh (RefsOk_trunc le outer)
  have run := publicInvoke_safe a site.loc site.direct site.binding site.selected site.abi site.args site.supplies
    (fun i _ => vals i) roots heap reached linked (stable le (WExt_refl _) current) pt
    (fun i => RefsOk_trunc le (root i)) w hh
  exact SafePostExcV.iff_lift.mp (SafePostExcV.mono_result site.returns (SafePostExcV.iff_lift.mpr run))

/-- The whole caller statement names only the conditional contract of the
producer value in its resolved sibling slot and ordinary entry evidence. -/
def PublicCallerEntry {f : FilePlans} (r : Req f) (input : Nat) (p : Published)
    (formals : List (Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive)))
    (result : Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive)) : Prop :=
  ∀ (L : List Tm) (d : Tm) n (W : WorldT n) h (Allowed : ∀ j, WorldT j → Prop),
    let G := RequestJson.graph r.toRequest
    let ρ := envOf L d
    (∀ {k} {U : WorldT k} {j} (le : j ≤ k) {V}, WExt (trunc j le U) V → Allowed k U → Allowed j V) →
    Allowed n W → ConditionalCall G formals result p.interface (ρ input) Allowed →
    PartialEnv G (callerEntryTypes r.inputs input) ρ n W → RootsOk W ρ → (∀ i, isVal (ρ i) = true) →
    WorldAdm W → HeapOk n W h →
    SafePostExc (excOf G) (GoalHolds G r.goal (r.goal.argument ρ)) (fun _ _ => True) (fun _ => True) n W h
      (gotoOf r.program r.start L d r.comp)

private def readChecked (answer : Except String α) : Except String {x // answer = .ok x} :=
  match answer with
  | .ok x => .ok ⟨x,rfl⟩
  | .error why => .error why

/-- Retain the tables from the caller's ordinary use check. The certificate
for the rest of this caller consumes those same tables. -/
def certifyPublicCaller {f : FilePlans} {i name pos} (r : Req f) (plan : PlanAt f i name pos r) (fuel : Nat)
    (p : Published) (formals : List (Ty _)) (result : Ty _) (input : Nat) :
    Except String (PLift (PublicCallerEntry r input p formals result ∧ CodeAssertionsClause r)) := do
  let ⟨⟨codes,evidence,answers⟩,codeRead⟩ ← readChecked (inferCodes r fuel)
  let ⟨some raw,originRead⟩ := inspect (CallbackOrigins.infer r.program (r.claims.map (·.context.length)).toArray r.start r.inputs.length)
    | throw "caller origin analysis did not settle"
  let origins := nameable (namedSites r.program.toArray) raw
  let ⟨forwarded,uses⟩ ← readChecked (checkUses r codes origins [p] [])
  let site ← readPublicTail r p formals result origins codes answers fuel input
  return ⟨by
    refine ⟨?_,inferCodes_assertions codeRead⟩
    have accepted : check f i fuel [p] [] = .ok forwarded := by
      simp [check,show f.plans[i]? = _ from plan,FunctionPlan.certify,codeRead,originRead,origins,uses,bind,Except.bind,pure,Except.pure]
    obtain ⟨a,tableEq⟩ := check_accepted_origins accepted
    have graphs := a.plan.symm.trans plan
    simp only [Option.some.injEq,Except.ok.injEq,FunctionPlan.graph.injEq] at graphs
    obtain ⟨_,_,rfl⟩ := graphs
    simp only [originRead,Option.map_some] at tableEq
    have originEq : origins = a.origins := Option.some.inj tableEq
    rw [originEq] at site
    cases a.codeAnswers.symm.trans codeRead
    intro L d n W h Allowed G ρ stable allowed linked typed roots vals adm heap
    exact site.safe (a := a) typed roots vals stable allowed linked adm heap⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck
