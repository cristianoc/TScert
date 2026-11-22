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

/-- The auxiliary ordinary run has the source assertions, the original
entry facts, and an unknown producer slot. Graph claims are proposals and
are checked after retyping occurrences that may originate at that slot. -/
@[nospecialize] private def assertionCall {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι)
    (slot fuel : Nat) (live : Nat → Bool) (origins : CallbackOrigins.Table) (U result : Ty ι)
    (pool : List (Ty ι)) (rows : Array (CheckedCode ι)) (known : List (Evidence ι))
    (answers : Answered (RequestJson.graph r.toRequest)) :
    Target.RunCall (RequestJson.graph r.toRequest) (StoreView.images r.types) :=
  let claims := r.claims.zipIdx.map fun ((claim,l) : PointClaim ι × Nat) =>
    let Γ := claim.context.zipIdx.map fun (A,i) =>
      if ((origins.at l).getD i []).contains (.input slot) then U else A
    let retained := (r.program[l]?).any fun node => AssertionSlice.returnsTo live node.continuation node.handler
    { claim with context := Γ, type := if retained then claim.type else result }
  { pool, fuel, P := AssertionSlice.project r.program live .nul, claims, start := r.start, inputs := r.inputs.set slot U,
    goal := .plain result, assertions := r.assertions, cuts := r.cuts, candidates := r.candidates,
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
  let nodes := AssertionSlice.labels r.program (r.assertions.map Prod.fst)
  let live := nodes.contains
  if hc : AssertionSlice.closed r.program live then
    if covers : r.assertions.all (fun a => live a.1) then
      let G := RequestJson.graph r.toRequest
      let pool := vocabulary G r.searchLabels r.claims r.inputs
      let some U := pool.find? (unknownTy G) | throw "the caller graph has no source-value type"
      if hu : unknownTy G U then
        let some T := pool.find? (fun A => (expand G A).contains .nul) | throw "missing type for the assertion slice's return"
        let widths := (r.claims.map (fun c => c.context.length)).toArray
        let some origins := CallbackOrigins.infer r.program widths r.start r.inputs.length | throw "caller origin search did not settle"
        let ⟨.ok (rows,known,answers),inferred⟩ := inspect (inferCodes r fuel) | throw "uncertified caller code table"
        let c := assertionCall r slot fuel live origins U T pool rows known answers
        let ⟨(outcome,counts,after,trace),run⟩ := inspect c.result
        match ho : outcome with
        | .accepted =>
          if sums : SourceClaimJson.summariesChecked r after.summaries.toList then
            have accepted : c.Accepts after := ⟨⟨counts,trace,by simpa [ho] using run⟩,rfl⟩
            have graph := run_sound_single_pass G (StoreView.images r.types) c after (fun _ => True)
              accepted .ordinary (inferCodes_table_sound (r := r) (fuel := fuel) (rows := rows) (known := known) (final := answers) inferred)
              (checkReadSummaries_sound (Bool.and_eq_true_iff.mp sums).2) (by intros; contradiction)
            return ⟨by
              intro η n W h ρ _ typed src sep idx aw hh roots l k mem j h' ρ' budget path
              have reached := AssertionSlice.reaches (result := .nul) hc path (List.all_eq_true.mp covers _ mem)
              exact graph.asserted η trivial n W h ρ ⟨opaqueEnv typed hu src,sep,idx,aw,hh⟩
                (program_source_refsOk graph.source W) roots l k mem j h' ρ' budget reached⟩
          throw "unchecked read summaries in caller assertion proof"
        | _ => throw s!"ordinary caller assertion check: {outcome}"
      throw "invalid source-value type"
    throw "assertion label missing from the caller graph slice"
  throw "the caller assertion graph is not closed under predecessors"

end Verification.SourceClaimJson.CallbackInterfaceCheck
