import Verification.Source.Claims.Json
import Verification.Programs.Linking

/-! # Entry requests under acyclic stable links -/
namespace Verification.Linking
open PositiveGraphs PositiveRules Tower ProgramTyping SourceClaimJson SourceExtraction RequestJson ControlFlow

/-- Checked request code supplies an export's invocation specification when
its exact code, captures and offered rows pass the existing table lookup.
`codeTable_sound` uses `GraphCode.checkCodes_sound` and
`GraphCode.codeChecked_sound`. This does not identify a top-level request
with an invocation frame or construct concrete captures. -/
theorem code_of_checked_table {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    {r : Request σ ι} {c : Response ι} {table : List (CodeEntry ι)}
    (checked : codeTable r c = some table)
    {e : Export ι}
    (offers : ProgramCertificates.offersChecked (graph r) (GraphCode.admits table)
      e.arity e.expressions e.continuations e.start (e.captureTypes ++ [e.signature])
      false e.arrows e.rests [] = true) (η : MixedAssignment ι) :
    CodeOffers (reassign (graph r) η) e.arity e.expressions e.continuations e.start
      (e.captureTypes ++ [e.signature]) false e.arrows e.rests [] :=
  ProgramCertificates.offersChecked_sound (codeTable_sound checked) offers η

/-- Request acceptance supplies the checked table, so matching invocation
code obtains its specification from the same evidence used for acceptance.
The lookup compares code, capture types, signatures and rest mode exactly. -/
theorem code_of_accepted_request {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (accepted : checkRequests rs b = true) {r c}
    (member : (r, c) ∈ rs.zip b.functions) {e : Export ι}
    (offers : ProgramCertificates.offersChecked (graph r.toRequest)
      (GraphCode.admits ((codeTable r.toRequest c).getD []))
      e.arity e.expressions e.continuations e.start (e.captureTypes ++ [e.signature])
      false e.arrows e.rests [] = true) (η : MixedAssignment ι) :
    CodeOffers (reassign (graph r.toRequest) η) e.arity e.expressions e.continuations e.start
      (e.captureTypes ++ [e.signature]) false e.arrows e.rests [] := by
  obtain ⟨es, _, hc⟩ := checkRequests_pair accepted member
  obtain ⟨_, _, _, table, ht, _⟩ := (checkRequestResult_accepted_iff _ _ _).mp hc
  rw [ht] at offers
  exact code_of_checked_table ht offers η

/-- Top-level acceptance certifies invocation code when the invocation frame
contains the request inputs at the same slots. Extra capture/self slots may
follow them. Separation must follow from that frame. This applies to ordinary,
synchronous fixed signatures; qualified effects require their own body proof.
A request without an explicit receiver needs a slot adapter before this lemma
applies: invocation slot zero is the receiver, request slot zero is its first
parameter. -/
theorem code_of_top_level_request {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (accepted : checkRequests rs b = true) {r c}
    (member : (r, c) ∈ rs.zip b.functions)
    (η : MixedAssignment ι) (admitted : r.Admits η)
    {arity : Nat} {Cs : List (Ty ι)} {row : CallEffects.Arrow (Ty ι)}
    (arityOk : arity ≤ row.arguments.length)
    (ordinary : row.effect = CallEffects.Effect.ordinary)
    (result : r.result = row.result) (promise : r.promise = none)
    (frame : ∀ (k : Nat) (A : Ty ι), r.inputs[k]? = some A →
      (codeFrame arity row Cs none)[k]? = some A)
    (separation : ∀ ρ, HeapSeparation.Holds r.entrySeparation ρ) :
    CodeOffers (reassign (graph r.toRequest) η) arity
      (r.program.map (·.expression))
      (r.program.map fun node => (node.continuation, node.handler)) r.start Cs
      false [row] [] [] := by
  intro p hp
  have hp : p = row := by simpa [offerRows] using hp
  subst p
  refine ⟨arityOk, ?_, ?_⟩
  · simp [ordinary, CallEffects.Effect.ordinary, CallEffects.Effect.ofFootprint,
      CallEffects.Effect.below]
  intro n W heap L he hw hh _
  have inputs : EnvOk (reassign (graph r.toRequest) η) r.inputs (envOf L .nul) n W :=
    ⟨he.1, fun k A hA => he.2 k A (frame k A hA)⟩
  have hs := checkRequests_safe_at accepted member η admitted n W heap (envOf L .nul)
    inputs hw hh (separation _)
  have hg := program_nodes r.program
  rw [← hg] at hs
  have safe := GraphCode.safe_of_sim n W heap GraphCode.Sim.goto hs
  have goal : GoalHolds (reassign (graph r.toRequest) η) r.goal
      (r.goal.argument (envOf L .nul)) = meaning (reassign (graph r.toRequest) η) row.result := by
    simp [Request.goal, promise, GoalHolds, result]
  rw [goal] at safe
  simp only [ordinary, CallEffects.Effect.result, CallEffects.Effect.ordinary,
    CallEffects.Effect.ofFootprint]
  apply HeapObservations.SafePostExc.of_post
    (fun _ _ h => Bool.noConfusion h)
  refine HeapObservations.weaken (fun _ _ hp _ => ?_) (Footprints.Closed.top_safe safe)
  exact ⟨CallEffects.Effect.within_of_holds hp, by simp, by simp, by simp⟩

/-- An accepted request runs safely under the assembled environment.
`accepted` is the request component of `checkUnitJson_safe`; `WellLinked`
supplies independently certified export code, capture layout, acyclic links,
external contracts and signature transport. Initialization is complete,
exports are stable, and live-binding writes and re-exports are excluded.
Entry separation, admitted parameters and the shared world/heap invariants
remain explicit premises. Export effects follow from `exports_safe`. -/
theorem entries_safe {labels : Fin count → Type} {exports : (i : Fin count) → Export (labels i)}
    (linked : WellLinked exports) {F : EquationStore.Frozen}
    {rs : List (SourceRequest (EquationStore.Checked F.equations F.primitive)
      (EquationStore.CheckedLabel F.equations F.primitive))}
    {b : Bundle (EquationStore.CheckedLabel F.equations F.primitive)}
    (accepted : RequestsSafe F rs b) {r c} (member : (r, c) ∈ rs.zip b.functions)
    {η} (admitted : r.Admits η) {ρ : Env}
    (closed : ∀ k, Scoped 0 (ρ k))
    (slots : ∀ k A, r.inputs[k]? = some A →
      ((∀ j, ρ k ≠ (exports j).value) ∧
        ∀ n W, meaning (reassign F.equations.graph η) A n W (ρ k)) ∨
      ∃ j, ρ k = (exports j).value ∧ ∀ n W v,
        meaning (exports j).graph (exports j).signature n W v ↔
          meaning (reassign F.equations.graph η) A n W v)
    {n W heap} (separation : HeapSeparation.Holds r.entrySeparation ρ)
    (world : WorldAdm W) (heapOk : HeapOk n W heap) :
    SafeGraph (excOf (reassign F.equations.graph η)) r.program
      (GoalHolds (reassign F.equations.graph η) r.goal (r.goal.argument ρ))
      n W heap (.at r.start ρ) :=
  accepted.2.1 r c member η admitted n W heap ρ
    (entry_env linked closed slots n W) separation world heapOk

end Verification.Linking
