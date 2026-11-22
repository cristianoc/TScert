import Verification.Programs.AssertionSlice
import Verification.Source.Claims.CallbackPrefixWitness
import Verification.Source.Claims.PassUnitHeadline

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open RequestJson SourceElaboration ProgramTyping PositiveGraphs PositiveRules CertificateProducer LabelStore ControlFlow
open ProgramCertificates CallbackEffectInference TolerantFrames PassUnit

/-- Source assertions in the actual caller environment. Only the producer
slot's source-value type is required. Its arrow contract is never assumed. -/
def OpaqueAssertions {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι) (slot : Nat) : Prop :=
  ∀ η n W h ρ,
    let G := reassign (RequestJson.graph r.toRequest) η
    PartialEnv G (callerEntryTypes r.inputs slot) ρ n W →
    excOf G n W (ρ slot) → HeapSeparation.Holds r.entrySeparation ρ →
    HeapKnowledge.IndexHolds ⟨ρ,h⟩ r.entryIndices ρ h → WorldAdm W → HeapOk n W h → RootsOk W ρ →
    ∀ l k, (l,k) ∈ r.assertions → ∀ j h' ρ', j < n →
      ReachesIn r.program j h (.at r.start ρ) h' (.at l ρ') → HeapKnowledge.Holds k ⟨ρ,h⟩ ρ' h'

/-- Every closed function object is a source value, independently of its
code, fields, or the results of invoking it. -/
theorem opaqueObject_source {ι : Type} {G : NormalGraph ι} {n W fields code oid}
    (callable : code ≠ .absent) (scope : Scoped 0 (.objAt fields code oid)) :
    excOf G n W (.objAt fields code oid) :=
  ⟨⟨rfl,scope⟩,builtinInvariant_of_not_plain (by intro fs i eq; cases eq; contradiction)⟩

private theorem opaqueEnv {ι : Type} [Labels ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {Γ slot ρ n W U} (typed : PartialEnv (reassign G η) (callerEntryTypes Γ slot) ρ n W)
    (unknown : unknownTy G U = true) (value : excOf (reassign G η) n W (ρ slot)) :
    EnvOk (reassign G η) (Γ.set slot U) ρ n W := by
  refine ⟨typed.1,?_⟩
  intro i A found
  by_cases same : slot = i
  · subst i
    rw [List.getElem?_set_self'] at found
    cases hs : Γ[slot]? <;> simp [hs] at found
    subst A
    exact unknownTy_sound (G := G) (η := η) unknown value
  · rw [List.getElem?_set_ne same] at found
    exact typed.2 i A (by simp [callerEntryTypes,List.getElem?_map,List.getElem?_zipIdx,found,Ne.symm same])

private theorem reachLast {P : Program} {j h state h' state'}
    (path : ReachesIn P j h state h' state') :
    (j = 0 ∧ h' = h ∧ state' = state) ∨
    ∃ k middle atMiddle, j = k + 1 ∧ ReachesIn P k h state middle atMiddle ∧
      Transition P middle atMiddle h' state' := by
  induction path with
  | refl => exact .inl ⟨rfl,rfl,rfl⟩
  | step first rest ih =>
    rcases ih with ⟨zero,hh,ss⟩ | ⟨k,middle,atMiddle,ticks,front,last⟩
    · subst_vars
      exact .inr ⟨0,_,_,rfl,.refl,first⟩
    · exact .inr ⟨k+1,middle,atMiddle,by omega,.step first front,last⟩

private theorem reachedEval {P : Program} {j h start ρ h' term env k handler}
    (path : ReachesIn P j h (.at start ρ) h' (.eval term env k handler)) :
    ∃ steps label heap node, steps < j ∧ ReachesIn P steps h (.at start ρ) heap (.at label env) ∧
      P[label]? = some node ∧ node.continuation = k ∧ node.handler = handler := by
  rcases reachLast path with ⟨_,_,impossible⟩ | ⟨ticks,middle,state,rfl,front,last⟩
  · cases impossible
  · cases last with
    | enter found => exact ⟨ticks,_,_,_,by omega,front,found,rfl,rfl⟩
    | expr _ =>
      obtain ⟨steps,label,heap,node,less,reach,found,hk,hx⟩ := reachedEval front
      exact ⟨steps,label,heap,node,by omega,reach,found,hk,hx⟩
termination_by j

private def goesTo (label : Nat) (node : Node) : Bool :=
  AssertionSlice.returnsTo (· == label) node.continuation node.handler

private def solePredecessor (P : Program) (label predLabel : Nat) : Bool :=
  P.zipIdx.all fun (node,l) => !goesTo label node || l == predLabel

private theorem reachedPredecessor {P : Program} {start label predLabel steps ρ h h' env flag dest expression}
    (different : label ≠ start) (pred : solePredecessor P label predLabel = true)
    (node : P[predLabel]? = some ⟨expression,PrefixMap flag dest,none⟩) (target : dest.label = label)
    (path : ReachesIn P steps h (.at start ρ) h' (.at label env)) :
    ∃ before heap prior v, before < steps ∧ ReachesIn P before h (.at start ρ) heap (.at predLabel prior) ∧
      env = PointClaims.mapEnv dest.mapping (prefixPushEnv flag v prior) := by
  rcases reachLast path with ⟨_,_,same⟩ | ⟨ticks,middle,state,rfl,front,last⟩
  · exact False.elim (different (State.at.inj same).1)
  have origin {term ρ' k x} (evaluated : ReachesIn P ticks h (.at start ρ) middle (.eval term ρ' k x))
      (goes : AssertionSlice.returnsTo (· == label) k x = true) :
      ∃ earlier heap, earlier < ticks ∧ ReachesIn P earlier h (.at start ρ) heap (.at predLabel ρ') ∧
        k = PrefixMap flag dest ∧ x = none := by
    obtain ⟨earlier,src,heap,nd,less,reach,location,hk,hx⟩ := reachedEval evaluated
    have unique := List.all_eq_true.mp pred _ (List.mk_mem_zipIdx_iff_getElem?.mpr location)
    simp [goesTo,hk,hx,goes] at unique
    subst src
    rw [node] at location
    cases location
    exact ⟨earlier,heap,less,reach,hk.symm,hx.symm⟩
  cases last with
  | bind hv =>
    obtain ⟨before,heap,less,reach,hk,_⟩ := origin front (by simp [AssertionSlice.returnsTo,successors])
    cases flag with
    | false => simp [PrefixMap] at hk
    | true =>
      cases (Continuation.bind.inj hk)
      exact ⟨before,heap,_,_,by omega,reach,rfl⟩
  | effect hv =>
    obtain ⟨before,heap,less,reach,hk,_⟩ := origin front (by simp [AssertionSlice.returnsTo,successors])
    cases flag with
    | true => simp [PrefixMap] at hk
    | false =>
      cases (Continuation.effect.inj hk)
      exact ⟨before,heap,_,.undef,by omega,reach,rfl⟩
  | tagBind hv =>
    obtain ⟨_,_,_,_,hk,_⟩ := origin front (by
      simp only [AssertionSlice.returnsTo,successors,List.any_cons,List.any_nil,Bool.or_false]
      split <;> simp)
    cases flag <;> simp [PrefixMap] at hk
  | handle raised =>
    obtain ⟨_,_,_,_,_,hx⟩ := origin front (by simp [AssertionSlice.returnsTo])
    cases hx
  | yes | no | yesBind | noBind =>
    obtain ⟨_,_,_,_,hk,_⟩ := origin front (by simp [AssertionSlice.returnsTo,successors])
    cases flag <;> simp [PrefixMap] at hk

private abbrev Assertions := List (Nat × HeapKnowledge.Knowledge)

private def AssertionCoverage (P : Program) (start : Nat) (basis : Assertions)
    (label : Nat) (S : HeapSeparation.Separation) : Prop :=
  ∀ {ρ h budget},
    (∀ l k, (l,k) ∈ basis → ∀ j h' env, j < budget →
      ReachesIn P j h (.at start ρ) h' (.at l env) → HeapKnowledge.Holds k ⟨ρ,h⟩ env h') →
    ∀ j h' env, j < budget → ReachesIn P j h (.at start ρ) h' (.at label env) →
      HeapSeparation.Holds S env

/-- A candidate preimage under the edge mapping. The separation checker
validates it before it can justify any inherited assertion. -/
private def separationBefore (S : HeapSeparation.Separation) (flag : Bool) (mapping : PointClaims.Mapping) :
    HeapSeparation.Separation :=
  let depth := S.depth + (mapping.getD []).foldl max 0 + 1
  let level := fun l => depth - 1 - (PointClaims.slot mapping (S.depth - 1 - l) - flag.toNat)
  ⟨depth,S.facts.map fun a => ⟨level a.slot,a.fields,a.partners.map fun (l,fs) => (level l,fs)⟩⟩

private def readSeparationCoverage (P : Program) (start : Nat) (basis : Assertions) :
    Nat → (l : Nat) → (S : HeapSeparation.Separation) → Option (PLift (AssertionCoverage P start basis l S))
  | 0, _, _ => none
  | fuel+1, l, S => do
    if found : ∃ a ∈ basis, a.1 = l ∧ HeapSeparation.check a.2.separation S none = true then
      return ⟨by
        obtain ⟨⟨label,k⟩,mem,same,implies⟩ := found
        cases same
        exact fun base j h' env small path =>
          HeapSeparation.check_sound implies (base label k mem j h' env small path).2.2.2.1⟩
    let some (node,predLabel) := P.zipIdx.find? (fun (nd,_) => goesTo l nd) | none
    let (flag,dest) ← match node.continuation with
      | .effect t => some (false,t)
      | .bind t => some (true,t)
      | _ => none
    if diff : l ≠ start then
      if unique : solePredecessor P l predLabel = true then
        if loc : P[predLabel]? = some ⟨node.expression,PrefixMap flag dest,none⟩ then
          if target : dest.label = l then
            let prior := separationBefore S flag dest.mapping
            if entails : HeapSeparation.check (if flag then HeapSeparation.shift prior else prior) S dest.mapping = true then
              let ⟨earlier⟩ ← readSeparationCoverage P start basis fuel predLabel prior
              return ⟨by
                intro ρ h budget base j h' env small path
                obtain ⟨b,hb,envb,v,less,reach,rfl⟩ := reachedPredecessor diff unique loc target path
                apply HeapSeparation.check_sound entails
                have prev := earlier base b hb envb (by omega) reach
                cases flag
                · exact prev
                · exact HeapSeparation.shift_holds prev⟩
    none

private structure AssertionProjection (P : Program) (start : Nat) (original : Assertions) where
  basis : Assertions
  replay : ∀ {ρ h budget},
    (∀ l k, (l,k) ∈ basis → ∀ j h' env, j < budget →
      ReachesIn P j h (.at start ρ) h' (.at l env) → HeapKnowledge.Holds k ⟨ρ,h⟩ env h') →
    ∀ l k, (l,k) ∈ original → ∀ j h' env, j < budget →
      ReachesIn P j h (.at start ρ) h' (.at l env) → HeapKnowledge.Holds k ⟨ρ,h⟩ env h'

/-- Keep the assertions that need the ordinary replay. An assertion made
solely of separation facts can reuse an earlier checked assertion when
every edge carries the same bindings. Heap writes cannot affect this proof. -/
private def projectAssertions (P : Program) (start : Nat) : (xs : Assertions) → AssertionProjection P start xs
  | [] => ⟨[],by intros; simp_all⟩
  | (l,k) :: tail => Id.run do
    let rest := projectAssertions P start tail
    if pureSep : k = { separation := k.separation } then
      if let some ⟨coverage⟩ := readSeparationCoverage P start rest.basis (P.length+1) l k.separation then
        return ⟨rest.basis,by
          intro ρ h budget basis label knowledge member j h' env bound path
          rcases List.mem_cons.mp member with same | other
          · cases same
            have separated := coverage basis j h' env bound path
            rw [pureSep]
            exact ⟨by simp [HeapFacts.Holds],by simp [HeapKnowledge.ValueHolds],by simp [HeapLinks.Holds],separated,
              HeapKnowledge.elemsHolds_nil _ _,HeapKnowledge.indexHolds_nil _ _⟩
          · exact rest.replay basis label knowledge other j h' env bound path⟩
    return ⟨(l,k) :: rest.basis,by
      intro ρ h budget basis label knowledge member j h' env bound path
      rcases List.mem_cons.mp member with same | other
      · exact basis label knowledge (List.mem_cons.mpr (.inl same)) j h' env bound path
      · exact rest.replay (fun a b mem => basis a b (List.mem_cons_of_mem _ mem)) label knowledge other j h' env bound path⟩

/-- The auxiliary ordinary run has the source assertions, the original
entry facts, and an unknown producer slot. Graph claims are proposals and
are checked after retyping occurrences that may originate at that slot. -/
@[nospecialize] private def assertionCall {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι)
    (assertions : Assertions) (slot fuel : Nat) (live : Nat → Bool) (origins : CallbackOrigins.Table) (U result : Ty ι)
    (pool : List (Ty ι)) (rows : Array (CheckedCode ι)) (known : List (Evidence ι))
    (answers : Answered (RequestJson.graph r.toRequest)) :
    Target.RunCall (RequestJson.graph r.toRequest) (StoreView.images r.types) :=
  let claims := r.claims.zipIdx.map fun ((claim,l) : PointClaim ι × Nat) =>
    let Γ := claim.context.zipIdx.map fun (A,i) =>
      if ((origins.at l).getD i []).contains (.input slot) then U else A
    let retained := (r.program[l]?).any fun node => AssertionSlice.returnsTo live node.continuation node.handler
    { claim with context := Γ, type := if retained then claim.type else result }
  { pool, fuel, P := AssertionSlice.project r.program live .nul, claims, start := r.start, inputs := r.inputs.set slot U,
    goal := .plain result, assertions, cuts := r.cuts, candidates := r.candidates,
    entryIndices := r.entryIndices, suggestions := [], known, codes := GraphCode.admits (rows.toList.map (·.entry)),
    aliases := r.aliases, passChecker := .ordinary, answers, reference := #[], debugNode := 1000000000, bound := none,
    givenImplies := #[], givenArgs := #[], «ensures» := [], givenInputs := #[], entrySeparation := r.entrySeparation,
    observe := none, tracing := false, observeEntry := false, regional := none }

private def inspect (x : α) : {v // x = v} := ⟨x,rfl⟩

/-- Read a checked source assertion certificate for a caller importing an
opaque function, replaying only its own graph and code table. -/
@[nospecialize] def certifyOpaqueAssertions {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceRequest σ ι) (slot fuel : Nat) : Except String (PLift (OpaqueAssertions r slot)) := do
  if noAssertions : r.assertions = [] then
    return ⟨by intro η n W h ρ G typed src sep idx aw hh roots l k mem; simp [noAssertions] at mem⟩
  let projected := projectAssertions r.program r.start r.assertions
  let nodes := AssertionSlice.labels r.program (projected.basis.map Prod.fst)
  let live := nodes.contains
  if hc : AssertionSlice.closed r.program live then
    if covers : projected.basis.all (fun a => live a.1) then
      let G := RequestJson.graph r.toRequest
      let pool := vocabulary G r.searchLabels r.claims r.inputs
      let some U := pool.find? (unknownTy G) | throw "the caller graph has no source-value type"
      if hu : unknownTy G U then
        let some T := pool.find? (fun A => (expand G A).contains .nul) | throw "missing type for the assertion slice's return"
        let widths := (r.claims.map (fun c => c.context.length)).toArray
        let some origins := CallbackOrigins.infer r.program widths r.start r.inputs.length | throw "caller origin search did not settle"
        let ⟨.ok (rows,known,answers),inferred⟩ := inspect (inferCodes r fuel) | throw "uncertified caller code table"
        let c := assertionCall r projected.basis slot fuel live origins U T pool rows known answers
        let ⟨(outcome,counts,after,trace),run⟩ := inspect c.result
        match ho : outcome with
        | .accepted =>
          if sums : SourceClaimJson.summariesChecked r after.summaries.toList then
            have accepted : c.Accepts after := ⟨⟨counts,trace,by simpa [ho] using run⟩,rfl⟩
            have graph := run_sound_single_pass G (StoreView.images r.types) c after (fun _ => True)
              accepted .ordinary (inferCodes_table_sound (r := r) (fuel := fuel) (rows := rows) (known := known) (final := answers) inferred)
              (checkReadSummaries_sound (Bool.and_eq_true_iff.mp sums).2) (by intros; contradiction)
            return ⟨by
              intro η n W h ρ _ typed src sep idx aw hh roots
              apply projected.replay (budget := n)
              intro l k mem j h' ρ' budget path
              have reached := AssertionSlice.reaches (result := .nul) hc path (List.all_eq_true.mp covers _ mem)
              exact graph.asserted η trivial n W h ρ ⟨opaqueEnv typed hu src,sep,idx,aw,hh⟩
                (program_source_refsOk graph.source W) roots l k mem j h' ρ' budget reached⟩
          throw "unchecked read summaries in caller assertion proof"
        | _ => throw s!"ordinary caller assertion check: {outcome}"
      throw "invalid source-value type"
    throw "assertion label missing from the caller graph slice"
  throw "the caller assertion graph is not closed under predecessors"

end Verification.SourceClaimJson.CallbackInterfaceCheck
