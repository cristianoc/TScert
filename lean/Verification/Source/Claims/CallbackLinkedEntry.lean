import Verification.Source.Claims.CallbackPrefixWitness
import Verification.Source.Claims.FlowProbe

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins CallbackEffectInference CallbackInferencePlan ControlFlow ProgramTyping
open PositiveRules LabelStore PassUnit GraphCode CertificateProducer

/-- The closed component being checked contains exactly two declarations. -/
inductive LocalMember where
  | caller | producer
  deriving DecidableEq

inductive SourceSlot where
  | linked (declaration : LocalMember)
  | outside (name : String)
  deriving DecidableEq

/-- The code and ordered captures read from the file's existing module
code and interface layout projections. A local capture resolves to a
declaration and an outside capture must have a modeled realm binding. -/
structure SourceModule (f : FilePlans) where
  graph : ProbeModule
  bindings : List SourceSlot
  types : List (Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive))

def readSourceModule (f : FilePlans) (caller producer i : Nat) : Except String (SourceModule f) := do
  let [graph] := f.moduleCodes [i] | throw "missing receiverless source module code"
  let caps := f.captures i
  if graph.rest || caps.map Prod.fst != f.fr.captureNames i || caps.map Prod.fst != graph.siblings then
    throw "source capture names disagree with the lowered module frame"
  let names ← caps.mapM fun (name,_) => do
    let owners := f.fr.units.zipIdx.filterMap fun ((fn,_,init),j) =>
      if init.isNone && fn.name == name then some j else none
    match owners with
    | [] =>
      if !(SourceTypes.prototypeNames.contains name || (hostModel? name).isSome) then
        throw s!"capture {name} has no modeled outside binding"
      return SourceSlot.outside name
    | [owner] =>
      if owner == caller then return SourceSlot.linked .caller
      if owner == producer then return SourceSlot.linked .producer
      throw s!"capture {name} is a third local declaration"
    | _ => throw s!"capture {name} names several local declarations"
  return ⟨graph,names,caps.map Prod.snd⟩

def SourceModule.realize {f : FilePlans} (m : SourceModule f)
    (outside : String → Nat → Tm) (fields : List (PropKey × Nat)) (oid : Nat) :
    PassUnit.ModuleCode (EquationStore.CheckedLabel f.F.equations f.F.primitive) LocalMember :=
  { arity := m.graph.ar, exprs := m.graph.code.1, conts := m.graph.code.2,
    start := m.graph.code.1.length - 1, kind := .call, fields, oid, captures := m.types,
    slots := m.bindings.map fun
      | .linked owner => Slot.linked owner
      | .outside name => Slot.outside (outside name)
    comp := m.graph.comp }

def sourceModules {f : FilePlans} (a b : SourceModule f) (outside : String → Nat → Tm)
    (fields : LocalMember → List (PropKey × Nat)) (identity : LocalMember → Nat) :
    LocalMember → PassUnit.ModuleCode (EquationStore.CheckedLabel f.F.equations f.F.primitive) LocalMember
  | .caller => a.realize outside (fields .caller) (identity .caller)
  | .producer => b.realize outside (fields .producer) (identity .producer)

/-- An internal correspondence between the module values and the graph
proof. The executable source manifest establishes all these equalities. -/
structure LinkedLayout {f : FilePlans} (a b : Req f) (bn : String)
    (code : LocalMember → PassUnit.ModuleCode (EquationStore.CheckedLabel f.F.equations f.F.primitive) LocalMember)
    (outside : String → Nat → Tm) : Prop where
  callerSlots : (code .caller).slots = a.siblings.map fun name =>
    if name = bn then Slot.linked .producer else Slot.outside (outside name)
  producerSlots : (code .producer).slots = b.siblings.map fun name => Slot.outside (outside name)
  arity : (code .producer).arity = 2
  body : ((code .producer).exprs,(code .producer).conts) = realizedCode b
  start : (code .producer).start = b.program.length
  kind : (code .producer).kind = .call
  component : (code .producer).comp = b.comp

/-- Actual entry of the caller in the module environment. -/
def ModuleEntrySafe {f : FilePlans} (a b : Req f) (k : Nat)
    (code : LocalMember → PassUnit.ModuleCode (EquationStore.CheckedLabel f.F.equations f.F.primitive) LocalMember) : Prop :=
  ∀ (depth : Nat) (args : List Tm) (defaultValue : Tm) (n : Nat) (W : WorldT n) (h : Heap),
    args.length = a.inputs.length - a.siblings.length →
    let captures := (code .producer).captured (approxEnv code depth) depth
    let L := args ++ (code .caller).captured (approxEnv code (depth+1)) (depth+1) ++ [approx code (depth+1) .caller]
    let ρ := envOf L defaultValue
    let G := StoreView.graph f.F.store
    EnvOk G (b.inputs.drop 2) (envOf captures .undef) n W →
    OutsideValues code →
    PartialEnv (RequestJson.graph a.toRequest) (callerEntryTypes a.inputs (args.length+k)) ρ n W →
    RootsOk W ρ → (∀ i, isVal (ρ i) = true) → WorldAdm W → HeapOk n W h →
    HeapObservations.SafePostExc (excOf G) (GoalHolds G a.goal (a.goal.argument ρ))
      (fun _ _ => True) (fun _ => True) n W h (gotoOf a.program a.start L defaultValue a.comp)

/-- Identity, code, fixed arity, component and the typed capture order of
a source declaration, compared with the request used for its proof. -/
def SourceModule.agrees {f : FilePlans} (m : SourceModule f) (r : Req f) (name : String)
    (binding : String → SourceSlot) : Prop :=
  m.graph.name = name ∧ m.graph.code = realizedCode r ∧ m.graph.ar = r.inputs.length - r.siblings.length ∧
  m.graph.comp = r.comp ∧ m.bindings = r.siblings.map binding ∧
  m.types = r.inputs.drop (r.inputs.length - r.siblings.length)

private instance {f : FilePlans} {m : SourceModule f} {r : Req f} {n : String} {keep : String → SourceSlot} :
    Decidable (m.agrees r n keep) := by unfold SourceModule.agrees; infer_instance

def LinkedEntrySafe {f : FilePlans} (a b : Req f) (an bn : String) (caller producer k : Nat) : Prop :=
  ∃ ca cb, readSourceModule f caller producer caller = .ok ca ∧ readSourceModule f caller producer producer = .ok cb ∧
    ca.agrees a an (fun n => if n = bn then .linked .producer else .outside n) ∧ cb.agrees b bn .outside ∧
    ∀ outside fields identities, ModuleEntrySafe a b k (sourceModules ca cb outside fields identities)

structure TailSite (f : FilePlans) (a b : Req f) (origins : Table)
    (codes : Array (CheckedCode (EquationStore.CheckedLabel f.F.equations f.F.primitive))) (input : Nat) where
  label : Nat
  fn : Nat
  x : Nat
  cb : Nat
  node : Node
  loc : a.program[label]? = some node
  direct : node.expression = .invoke (.var fn) .undef [.var x,.var cb]
  binding : originOf (origins.at label) (.var fn) = some (.input input)
  empty : emptyArgumentAt a.program origins label cb = true
  ret : Nat
  mapping : List Nat
  cont : node.continuation = .bind ⟨ret,some (0::mapping)⟩
  unhandled : node.handler = none
  last : a.program[ret]? = some ⟨.var 0,.ret,none⟩
  retTy : Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive)
  producerGoal : b.goal = .plain retTy
  callerGoal : a.goal = .plain retTy
  source : a.program.all (fun nd => ObjectCoherence.sourceTerm nd.expression) = true
  final : List (Option (Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive)))
  prefixPlan : PrefixPlan (RequestJson.graph a.toRequest) (StoreView.images a.types)
    (admits (codes.toList.map (·.entry))) a.program label final a.start (callerEntryTypes a.inputs input)
  fixed : FixedInputs (StoreView.graph f.F.store) (StoreView.images f.F.store) final x cb b.inputs (b.inputs.drop 2)
  noSep : b.entrySeparation.facts = []
  noIdx : b.entryIndices = []
  hostWidth : (b.inputs.drop 2).length = b.siblings.length

theorem TailSite.safe {f : FilePlans} {caller producer fuel p forwarded}
    (pair : TypicalPair f caller producer fuel p forwarded) {k}
    (slot : pair.callerRun.request.siblings[k]? = some pair.producerRun.name)
    (site : TailSite f pair.callerRun.request pair.producerRun.request pair.callerRun.origins pair.callerRun.codes
      (pair.callerRun.request.inputs.length - pair.callerRun.request.siblings.length + k))
    (over : OverStore f) {code outside}
    (layout : LinkedLayout pair.callerRun.request pair.producerRun.request pair.producerRun.name code outside) :
    ModuleEntrySafe pair.callerRun.request pair.producerRun.request k code := by
  intro depth args defaultValue n W h arity captures L ρ G hostTypes valuesOutside typed roots values world heap
  let a := pair.callerRun
  let b := pair.producerRun
  have capLen : captures.length = b.request.siblings.length := by
    simp [captures,PassUnit.ModuleCode.captured,layout.producerSlots,b]
  have arityWidth : b.request.inputs.length = 2 + captures.length := by
    have fixed := site.fixed.formals
    have w := site.hostWidth
    change b.request.inputs = _ :: _ :: b.request.inputs.drop 2 at fixed
    change (b.request.inputs.drop 2).length = b.request.siblings.length at w
    have lengths := congrArg List.length fixed
    simp only [List.length_cons] at lengths
    omega
  have native : (code .producer).closure captures = nativeWalker b.request.program b.request.start
      b.request.comp captures (code .producer).fields (code .producer).oid := by
    have E := congrArg Prod.fst layout.body
    have K := congrArg Prod.snd layout.body
    change (code .producer).exprs = _ at E
    change (code .producer).conts = _ at K
    simp only [realizedCode] at E K
    change pair.producerRun.request.inputs.length = _ at arityWidth
    simp [PassUnit.ModuleCode.closure,nativeWalker,b,layout.arity,layout.kind,layout.component,
      layout.start,E,K,arityWidth]
  have siblingLook : ((code .caller).captured (approxEnv code (depth+1)) (depth+1))[k]? =
      some ((code .producer).closure captures) := by
    simp [PassUnit.ModuleCode.captured,layout.callerSlots,List.getElem?_map,slot,Slot.valueAt,approxEnv,captures]
  have linked : ρ (args.length+k) = nativeWalker b.request.program b.request.start b.request.comp captures
      (code .producer).fields (code .producer).oid := by
    have small := (List.getElem?_eq_some_iff.mp siblingLook).1
    simp [ρ,L,envOf,List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : args.length ≤ args.length+k),
      List.getElem?_append_left small,siblingLook,native,b]
  have capVals : ∀ v ∈ captures, isVal v = true := by
    intro v mem
    exact (captured_values valuesOutside (fun u => approxEnv_value valuesOutside depth u) .producer depth v mem).1
  rw [arity] at typed linked
  refine TypicalPair.noopEntry pair over site.loc site.direct site.binding site.empty linked site.cont site.unhandled
    site.last site.producerGoal site.source site.prefixPlan site.fixed site.noSep site.noIdx site.callerGoal
    (site.hostWidth.trans capLen.symm) ?_ capVals typed roots values world heap
  change EnvOk G _ (envOf (captures ++ [ρ (a.request.inputs.length - a.request.siblings.length+k)]) .undef) n W
  constructor
  · intro i
    change Scoped 0 ((captures ++ [ρ (pair.callerRun.request.inputs.length - pair.callerRun.request.siblings.length + k)]).getD i .undef)
    rcases getD_mem_or (captures ++ [ρ (pair.callerRun.request.inputs.length - pair.callerRun.request.siblings.length + k)]) i .undef with mem | deflt
    · rcases List.mem_append.mp mem with cap | bound
      · obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp cap
        simpa [envOf,List.getD_eq_getElem?_getD,hj] using hostTypes.1 j
      · rw [List.mem_singleton.mp bound]
        exact typed.1 _
    · rw [deflt]
      trivial
  · intro i A hit
    have bound := (List.getElem?_eq_some_iff.mp hit).1
    have width : (pair.producerRun.request.inputs.drop 2).length = captures.length := site.hostWidth.trans capLen.symm
    have small : i < captures.length := by omega
    simpa only [envOf,List.getD_eq_getElem?_getD,List.getElem?_append_left small] using hostTypes.2 i A hit

private def need (message : String) (p : Prop) [Decidable p] : Except String (PLift p) :=
  if hp : p then .ok ⟨hp⟩ else .error message

private def inspected (value : α) : {v // value = v} := ⟨value,rfl⟩

private def readSite {f : FilePlans} (a b : Req f) (origins : Table) (codes : Array (CheckedCode _))
    (answers : Answered (RequestJson.graph a.toRequest)) (fuel input label : Nat) : Except String (TailSite f a b origins codes input) := do
  let ⟨some node,hn⟩ := inspected (a.program[label]?) | throw "missing direct call"
  let ⟨.invoke (.var fn) .undef [.var x,.var cb],he⟩ := inspected (node.expression) | throw "expected a fixed direct call"
  let ⟨.bind ⟨ret,some (0::mapping)⟩,hc⟩ := inspected (node.continuation) | throw "expected a direct return"
  let ⟨binding⟩ ← need "unresolved local declaration" (originOf (origins.at label) (.var fn) = some (.input input))
  let ⟨empty⟩ ← need "callback has no checked heap-preserving body" (emptyArgumentAt a.program origins label cb = true)
  let ⟨handler⟩ ← need "handler on the direct call" (node.handler = none)
  let ⟨last⟩ ← need "unchecked call continuation" (a.program[ret]? = some ⟨.var 0,.ret,none⟩)
  let ⟨.plain result,hg⟩ := inspected (b.goal) | throw "expected an ordinary result"
  let ⟨goal⟩ ← need "producer and caller result types differ" (a.goal = .plain result)
  let ⟨source⟩ ← need "non-source caller expression" (a.program.all (fun nd => ObjectCoherence.sourceTerm nd.expression) = true)
  let ⟨noSep⟩ ← need "producer requires entry separation" (b.entrySeparation.facts = [])
  let ⟨noIdx⟩ ← need "producer requires entry index facts" (b.entryIndices = [])
  let ⟨width⟩ ← need "producer capture width disagrees with its formals" ((b.inputs.drop 2).length = b.siblings.length)
  let G := RequestJson.graph a.toRequest
  let I := StoreView.images a.types
  let pool := vocabulary G a.searchLabels a.claims a.inputs
  let some filler := pool.find? (PromiseCalls.admitsUndef G) | throw "missing undefined input filler"
  let ⟨fill⟩ ← need "invalid undefined input filler" (PromiseCalls.admitsUndef G filler = true)
  let some ⟨final,prefixPlan⟩ := readPrefixPlan G I (admits (codes.toList.map (·.entry))) pool a.aliases fuel answers
    a.program a.claims label filler fill (a.program.length+1) a.start (callerEntryTypes a.inputs input) | throw "uncertified caller prefix"
  let ⟨some xt,hx⟩ := inspected (final[x]?.join) | throw "unknown first actual"
  let ⟨some ct,hj⟩ := inspected (final[cb]?.join) | throw "unknown callback actual"
  let ⟨xf :: cf :: hosts,hb⟩ := inspected (b.inputs) | throw "missing producer formals"
  let Gf := StoreView.graph f.F.store
  let If := StoreView.images f.F.store
  let some xs := (subtypeSearch Gf If xt xf).value | throw "first actual fails its formal"
  let some cs := (subtypeSearch Gf If ct cf).value | throw "callback actual fails its formal"
  let ⟨xok⟩ ← need "invalid first actual evidence" (PositiveCertificates.checkUsing Gf If xt xf xs = true)
  let ⟨cok⟩ ← need "invalid callback actual evidence" (PositiveCertificates.checkUsing Gf If ct cf cs = true)
  return ⟨label,fn,x,cb,node,hn,he,binding,empty,ret,mapping,hc,handler,last,result,hg,goal,source,final,
    prefixPlan,⟨xt,ct,xf,cf,hx,hj,by simp [hb],xs,cs,xok,cok⟩,noSep,noIdx,width⟩

/-- The caller has no further claimed exit or assertion obligations.
Retain the semantic clauses rather than losing them at a new print site. -/
private def plainContract {f : FilePlans} (r : Req f) : Bool :=
  decide (r.footprint = .top) && !r.onThrow && !r.fresh && r.regional.isNone &&
    r.ensures.isEmpty && r.assertions.isEmpty && r.codeHints.all (fun hints => hints.requirements.isEmpty)

private theorem plainContract_sound {f : FilePlans} {r : Req f} (ok : plainContract r = true) :
    FootprintClause r ∧ EnsuresClause r ∧ RegionalClause r ∧ AssertionsClause r ∧ CodeAssertionsClause r := by
  simp only [plainContract,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
    Option.isNone_iff_eq_none,List.isEmpty_iff] at ok
  obtain ⟨⟨⟨⟨⟨⟨hf,ht⟩,fresh⟩,reg⟩,ens⟩,main⟩,codes⟩ := ok
  refine ⟨by simp [FootprintClause,hf,ht,fresh],by simp [EnsuresClause,ens],by simp [RegionalClause,reg],
    by simp [AssertionsClause,main],?_⟩
  intro ci q _ η n W h ρ _ _ l k member
  cases atIndex : r.codeHints[ci]? with
  | none => simp [codeHintsAt,atIndex] at member
  | some hints =>
    have empty := List.all_eq_true.mp codes hints (List.mem_of_getElem? atIndex)
    simp only [List.isEmpty_iff] at empty
    simp [codeHintsAt,atIndex,empty] at member

/-- The identity and both graph plans are part of the result. Source safety
uses every admitted user argument, host environment, world and heap. -/
def LinkedMemberSafe (f : FilePlans) (caller producer : Nat) : Prop :=
  (f.fr.group caller = [caller] ∧ f.fr.group producer = [producer] ∧
    f.dependencies [caller] = [f.fr.unitId producer] ∧ f.dependencies [producer] = []) ∧
  ∃ an ap bn bp, ∃ (a b : Req f) (k : Nat), PlanAt f caller an ap a ∧ PlanAt f producer bn bp b ∧
    a.siblings[k]? = some bn ∧ LinkedEntrySafe a b an bn caller producer k ∧
    FootprintClause a ∧ EnsuresClause a ∧ RegionalClause a ∧ AssertionsClause a ∧ CodeAssertionsClause a

private def observed (result : Except String α) : Except String {x // result = .ok x} :=
  match result with
  | .ok x => .ok ⟨x,rfl⟩
  | .error why => .error why

private def present (why : String) (result : Option α) : Except String {x // result = some x} :=
  match result with
  | some x => .ok ⟨x,rfl⟩
  | none => .error why

private structure NamedGraph (f : FilePlans) (i : Nat) where
  name : String
  pos : Span
  request : Req f
  plan : PlanAt f i name pos request

private def graphMember (f : FilePlans) (i : Nat) : Except String (NamedGraph f i) :=
  match h : f.plans[i]? with
  | some (.ok (.graph name pos request)) => .ok ⟨name,pos,request,h⟩
  | some (.error why) => .error why
  | _ => .error "missing ordinary graph for linked declaration"

private theorem sourceLayout {f : FilePlans} {a b : Req f} {an bn ca cb}
    (caller : ca.agrees a an (fun n => if n = bn then .linked .producer else .outside n))
    (producer : cb.agrees b bn .outside)
    (arity : b.inputs.length = 2 + b.siblings.length) (outside fields ids) :
    LinkedLayout a b bn (sourceModules ca cb outside fields ids) outside := by
  obtain ⟨_,_,_,_,cSlots,_⟩ := caller
  obtain ⟨_,pCode,pAr,pComp,pSlots,_⟩ := producer
  refine ⟨?_,?_,?_,pCode,?_,rfl,pComp⟩
  · simp only [sourceModules,SourceModule.realize,cSlots,List.map_map]
    apply List.map_congr_left
    intro n _
    by_cases h : n = bn
    · subst n; simp
    · simp [h]
  · simp [sourceModules,SourceModule.realize,pSlots,List.map_map,Function.comp_def]
  · change cb.graph.ar = 2
    omega
  · change cb.graph.code.1.length - 1 = b.program.length
    simp [pCode,realizedCode]

private theorem planAt_eq {f : FilePlans} {i n₁ n₂ p₁ p₂ r₁ r₂}
    (h₁ : PlanAt f i n₁ p₁ r₁) (h₂ : PlanAt f i n₂ p₂ r₂) : n₁ = n₂ ∧ p₁ = p₂ ∧ r₁ = r₂ := by
  have h := h₁.symm.trans h₂
  simpa using h

/-- A returned certificate contains the semantic judgment, erased during
compilation. Every decision comes from the two actual plans in this store. -/
def certifyLinked (f : FilePlans) (caller producer fuel : Nat) : Except String (PLift (OverStore f → LinkedMemberSafe f caller producer)) := do
  let ⟨boundary⟩ ← need "the direct call must close its only dependency" (f.fr.group caller = [caller] ∧
    f.fr.group producer = [producer] ∧ f.dependencies [caller] = [f.fr.unitId producer] ∧ f.dependencies [producer] = [])
  let ⟨⟨decl,producerTypeParams,producerInit⟩,header⟩ ← present "missing linked declaration" f.fr.units[producer]?
  let ⟨marker⟩ ← need "expected the second fixed formal to carry the callback demand"
    ((decl.params.zipIdx.filterMap fun (param,slot) => if param.inferPreserves then some slot else none) = [1])
  let ⟨⟨client,callerTypeParams,callerInit⟩,_⟩ ← present "missing caller declaration" f.fr.units[caller]?
  let a ← graphMember f caller
  let b ← graphMember f producer
  let ⟨pub,published⟩ ← observed (writeInterface f producer fuel [])
  let ⟨out,checked⟩ ← observed (check f caller fuel [pub] [])
  if producerInit.isSome || callerInit.isSome || !producerTypeParams.isEmpty || !callerTypeParams.isEmpty ||
      decl.convertsReceiver || client.convertsReceiver || client.params.any (·.inferPreserves) ||
      a.name != client.name || a.pos != client.namePos || a.name == b.name ||
      client.params.length + a.request.siblings.length != a.request.inputs.length ||
      b.name != decl.name || b.pos != decl.namePos || decl.params.length != 2 ||
      a.request.receiver || a.request.restParam || b.request.receiver || b.request.restParam ||
      a.request.async || a.request.sourceScheme.isSome || b.request.sourceScheme.isSome ||
      a.request.qualification.isSome || a.request.stated.isSome then
    throw "unsupported declaration or capture layout at linked call"
  let ⟨ca,sourceCaller⟩ ← observed (readSourceModule f caller producer caller)
  let ⟨cb,sourceProducer⟩ ← observed (readSourceModule f caller producer producer)
  let ⟨callerLayout⟩ ← need "source module code or caller slots disagree with its plan"
    (ca.agrees a.request a.name (fun n => if n = b.name then .linked .producer else .outside n))
  let ⟨producerLayout⟩ ← need "source module code or producer slots disagree with its plan"
    (cb.agrees b.request b.name .outside)
  let ⟨width⟩ ← need "the producer capture layout disagrees with its two fixed formals"
    (b.request.inputs.length = 2 + b.request.siblings.length)
  let ⟨contract⟩ ← need "caller has an exit or assertion obligation outside its linked certificate"
    (plainContract a.request = true)
  let some k := a.request.siblings.idxOf? b.name | throw "producer is not a caller capture"
  let ⟨slot⟩ ← need "producer capture has a different declaration" (a.request.siblings[k]? = some b.name)
  let input := a.request.inputs.length - a.request.siblings.length + k
  let ⟨origins,originRead⟩ ← present "unsettled caller origins"
    ((CallbackOrigins.infer a.request.program (a.request.claims.map (·.context.length)).toArray
      a.request.start a.request.inputs.length).map (nameable (namedSites a.request.program.toArray)))
  let some (_,label) := a.request.program.zipIdx.find? (fun (nd,l) => match nd.expression with
    | .invoke fn _ _ => originOf (origins.at l) fn == some (.input input)
    | _ => false) | throw "missing direct call to the linked declaration"
  let ⟨⟨codes,_,answers⟩,codeRead⟩ ← observed (inferCodes a.request fuel)
  let site ← readSite a.request b.request origins codes answers fuel input label
  return ⟨by
    intro over
    obtain ⟨pair,callerOrigins,_⟩ := typicalPair_of_checks_recorded published checked header marker
    obtain ⟨an,ap,ar,ah⟩ := a
    obtain ⟨bn,bp,br,bh⟩ := b
    dsimp only at *
    obtain ⟨rfl,rfl,rfl⟩ := planAt_eq pair.callerRun.plan ah
    obtain ⟨rfl,rfl,rfl⟩ := planAt_eq pair.producerRun.plan bh
    cases callerOrigins.symm.trans originRead
    cases pair.callerRun.codeAnswers.symm.trans codeRead
    exact ⟨boundary,_,_,_,_,_,_,k,pair.callerRun.plan,pair.producerRun.plan,slot,⟨ca,cb,sourceCaller,sourceProducer,callerLayout,producerLayout,fun outside fields ids =>
      site.safe pair slot over (sourceLayout callerLayout producerLayout width outside fields ids)⟩,plainContract_sound contract⟩⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck
