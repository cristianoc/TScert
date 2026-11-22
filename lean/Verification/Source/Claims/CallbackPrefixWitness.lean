import Verification.Source.Claims.CallbackTypicalEntry
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open ControlFlow GraphCode ProgramTyping PositiveGraphs PositiveRules ProgramCertificates HeapObservations
open CallbackInferencePlan TolerantFrames PointClaims PassUnit CertificateProducer LabelStore

def mappedPrefixTypes (m : Mapping) (slots : List (Option (Ty ι))) : List (Option (Ty ι)) :=
  match m with
  | none => slots
  | some indices => indices.map fun i => slots[i]?.join

private theorem mappedPrefixTypes_checked {ι : Type} {A : Ty ι} {slots : List (Option (Ty ι))} {i : Nat} {m : Mapping}
    (hit : (mappedPrefixTypes m slots)[i]?.join = some A) : slots[PointClaims.slot m i]?.join = some A := by
  cases m with
  | none => exact hit
  | some ids =>
    cases position : ids[i]? with
    | none => simp [mappedPrefixTypes,position] at hit
    | some j => simpa [mappedPrefixTypes,PointClaims.slot,position] using hit

/-- Compile ordinary prefix evidence against the actual graph and checked code
table. The returned dependent value contains all the decisions read by
PrefixPlan.safe. This function is a theorem-side reader. -/
def readPrefixPlan {ι : Type} [Labels ι] (G : NormalGraph ι) (I : PositiveCertificates.InstanceImageCheck G)
    (codes : CodeEntry ι → Bool) (pool : List (Ty ι)) (aliases : List (ι × ι)) (searchFuel : Nat)
    (answers : Answered G) (P : Program) (claims : List (PointClaim ι)) (cut : Nat) (filler : Ty ι)
    (fill : PromiseCalls.admitsUndef G filler = true) :
    (budget l : Nat) → (Γ : List (Option (Ty ι))) → Option (Σ final, PrefixPlan G I codes P cut final l Γ)
  | 0, _, _ => none
  | budget+1, l, Γ => do
    if atCut : l = cut then return ⟨Γ,atCut ▸ PrefixPlan.done⟩
    match hp : P[l]? with
    | none => none
    | some node => do
      let cl ← claims[l]?
      let (flag,dest) ← match node.continuation with
        | .effect dest => some (false,dest)
        | .bind dest => some (true,dest)
        | _ => none
      if same : node = ⟨node.expression,PrefixMap flag dest,none⟩ then
        if indep : prefixReads (fun (i : Nat) => Γ[i]?.join.isSome) 0 node.expression = true then
          let masked := Γ.map (·.getD filler)
          let tree ← (expressionWithUsing G I pool [] aliases (fun _ _ => true) searchFuel masked node.expression cl.type answers).1.value
          if sq : claim tree = ⟨masked,node.expression,cl.type⟩ then
            if verified : checkTreeUsing G I tree codes [] = true then
              let next := mappedPrefixTypes dest.mapping (prefixPush flag (some cl.type) Γ)
              let ⟨final,tail⟩ ← readPrefixPlan G I codes pool aliases searchFuel answers P claims cut filler fill budget dest.label next
              return ⟨final,.step (hp.trans (congrArg some same)) ⟨filler,fill,indep,tree,sq,verified⟩
                (fun _ _ hit => mappedPrefixTypes_checked hit) tail⟩
      none

/-- Choosing the witnesses for an actual joint check retains the two exact
origin readers, so a finite certificate checked on the decoded tables
applies to these same caller and producer runs. -/
theorem typicalPair_of_checks_recorded {f : FilePlans} {caller producer fuel pub outgoing fn plan source}
    (published : writeInterface f producer fuel [] = .ok pub)
    (checked : check f caller fuel [pub] [] = .ok outgoing)
    (header : f.fr.units[producer]? = some (fn,plan,source))
    (marker : (fn.params.zipIdx.filterMap fun (param,slot) =>
      if param.inferPreserves then some slot else none) = [1]) :
    ∃ pair : TypicalPair f caller producer fuel pub outgoing,
      let a := pair.callerRun
      let b := pair.producerRun
      (CallbackOrigins.infer a.request.program (a.request.claims.map (·.context.length)).toArray a.request.start a.request.inputs.length).map
        (CallbackOrigins.nameable (CallbackOrigins.namedSites a.request.program.toArray)) = some a.origins ∧
      CallbackOrigins.infer b.request.program (b.request.claims.map (·.context.length)).toArray b.request.start b.request.inputs.length = some b.origins := by
  obtain ⟨other,p,s,own,fd,unit,inf,passes,_,_,_,_,out⟩ := writeInterface_accepted published
  rw [header] at unit
  cases Option.some.inj unit
  rw [marker] at inf
  change Except.ok [] = Except.ok fd at passes
  cases passes
  obtain ⟨b,beq⟩ := infer_accepted_origins inf
  obtain ⟨a,aeq⟩ := check_accepted_origins checked
  exact ⟨⟨own,a,b,by simpa using out⟩,aeq,beq⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck
