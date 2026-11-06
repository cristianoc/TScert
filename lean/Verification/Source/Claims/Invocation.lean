import Verification.Source.Claims.Linking

/-! # Invocation adapters for accepted top-level requests

A top-level request binds parameters and module bindings directly. A closure
invocation binds a receiver before these and self after its captures. The
adapter evaluates the exact accepted graph with a checked projection of that
invocation frame. The embedded expression and continuation lists are unchanged.
-/
namespace Verification.Linking
open PositiveGraphs PositiveRules Tower ProgramTyping SourceExtraction RequestJson ControlFlow

/-- Returning an embedded graph's result preserves ordinary safety. -/
theorem return_frame_safe {Ξ T : Fam} (hΞ : Adm Ξ) (hT : Adm T) {E K L d} :
    ∀ {n W heap t}, WorldAdm W → HeapOk n W heap → Safe Ξ T n W heap t →
      Safe Ξ T n W heap (.frame E K t L d .ret none) := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W heap t hw hh hs
    rcases hs with (⟨hv, ht⟩ | ⟨v, hr, closed, hx⟩) | ⟨U, heap', t', ext, adm, st, hok, rest⟩
    · refine .inr ⟨_, heap, t, WExt_refl _, WorldAdm_trunc _ hw,
        .frameRet hv, HeapOk_trunc n W heap hh, ?_⟩
      cases n with
      | zero => trivial
      | succ n => exact .inl (.inl ⟨hv, hT.down _ _ _ ht⟩)
    · refine .inr ⟨_, heap, .throw v, WExt_refl _, WorldAdm_trunc _ hw,
        .frameRaise hr, HeapOk_trunc n W heap hh, ?_⟩
      cases n with
      | zero => trivial
      | succ n => exact .inl (.inr ⟨v, .throwV (raises_val hr) (raises_sourceVal hr),
          closed, hΞ.down _ _ _ hx⟩)
    · exact .inr ⟨U, heap', _, ext, adm, .frameC st, hok, ih adm hok rest⟩

/-- The return adapter preserves both normal and exceptional heap posts. -/
theorem return_frame_post {Ξ T : Fam} (hΞ : Adm Ξ) (hT : Adm T)
    {Q : HeapObservations.Post} {R : Heap → Prop} {E K L d} :
    ∀ {n W heap t}, WorldAdm W → HeapOk n W heap →
      HeapObservations.SafePostExc Ξ T Q R n W heap t →
      HeapObservations.SafePostExc Ξ T Q R n W heap (.frame E K t L d .ret none) := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W heap t hw hh hs
    rcases hs with (⟨hv, ht, hq⟩ | ⟨⟨v, hr, closed, hx⟩, hpost⟩) |
      ⟨U, heap', t', ext, adm, st, hok, rest⟩
    · refine .inr ⟨_, heap, t, WExt_refl _, WorldAdm_trunc _ hw,
        .frameRet hv, HeapOk_trunc n W heap hh, ?_⟩
      cases n with
      | zero => trivial
      | succ n => exact .inl (.inl ⟨hv, hT.down _ _ _ ht, hq⟩)
    · refine .inr ⟨_, heap, .throw v, WExt_refl _, WorldAdm_trunc _ hw,
        .frameRaise hr, HeapOk_trunc n W heap hh, ?_⟩
      cases n with
      | zero => trivial
      | succ n => exact .inl (.inr ⟨⟨v, .throwV (raises_val hr) (raises_sourceVal hr),
          closed, hΞ.down _ _ _ hx⟩, hpost⟩)
    · exact .inr ⟨U, heap', _, ext, adm, .frameC st, hok, ih adm hok rest⟩

@[nospecialize] def invocationExpression {σ ι : Type} (r : Request σ ι) (slots : List Nat) : Tm :=
  .goto (r.program.map (·.expression))
    (r.program.map fun node => (node.continuation, node.handler)) r.start
    (slots.map Tm.var) .nul

/-- A typed projection of the invocation frame supplies the request inputs. -/
theorem projected_env {G : NormalGraph ι} {inputs frame : List (Ty ι)} {slots : List Nat}
    (_length : slots.length = inputs.length)
    (types : ∀ (k : Nat) (A : Ty ι), inputs[k]? = some A →
      ∃ j, slots[k]? = some j ∧ frame[j]? = some A)
    {ρ n W} (he : EnvOk G frame ρ n W) :
    EnvOk G inputs (envOf (slots.map ρ) .nul) n W := by
  constructor
  · intro k
    simp only [envOf, List.getD]
    cases h : (slots.map ρ)[k]? with
    | none => trivial
    | some v =>
      obtain ⟨j, _, rfl⟩ := Option.map_eq_some_iff.mp (List.getElem?_map ▸ h)
      exact he.1 j
  · intro k A hA
    obtain ⟨j, hj, ht⟩ := types k A hA
    simpa [envOf, List.getD, List.getElem?_map, hj] using he.2 j A ht

/-- Top-level acceptance certifies the closure's actual invocation adapter.
The code embeds the exact request graph; `slots` supplies parameters, module
captures and self at their entry positions. Ordinary fixed signatures are
admitted. Entry separation must hold for every projected value frame; empty
separation discharges this premise. Capture membership is not assumed. -/
theorem code_of_adapted_request {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (accepted : checkRequests rs b = true) {r c}
    (member : (r, c) ∈ rs.zip b.functions)
    (η : MixedAssignment ι) (admitted : r.Admits η)
    {arity : Nat} {Cs : List (Ty ι)} {row : CallEffects.Arrow (Ty ι)}
    (arityOk : arity ≤ row.arguments.length)
    (ordinary : row.effect = CallEffects.Effect.ordinary)
    (result : r.result = row.result) (promise : r.promise = none)
    (slots : List Nat) (length : slots.length = r.inputs.length)
    (types : ∀ (k : Nat) (A : Ty ι), r.inputs[k]? = some A →
      ∃ j, slots[k]? = some j ∧ (codeFrame arity row Cs none)[j]? = some A)
    (separation : ∀ ρ, HeapSeparation.Holds r.entrySeparation ρ) :
    CodeOffers (reassign (graph r.toRequest) η) arity
      [invocationExpression r.toRequest slots] [(.ret, none)] 0 Cs false [row] [] [] := by
  intro p hp
  have hp : p = row := by simpa [offerRows] using hp
  subst p
  refine ⟨arityOk, ?_, ?_⟩
  · simp [ordinary, CallEffects.Effect.ordinary, CallEffects.Effect.ofFootprint,
      CallEffects.Effect.below]
  intro n W heap L he hw hh _
  have run : ∀ (j : Nat) (V : WorldT j) heap (ρ : Env),
      EnvOk (reassign (graph r.toRequest) η) (codeFrame arity row Cs none) ρ j V →
      WorldAdm V → HeapOk j V heap →
      Safe (excOf (reassign (graph r.toRequest) η))
        (meaning (reassign (graph r.toRequest) η) row.result) j V heap
        (.goto (r.program.map (·.expression))
          (r.program.map fun node => (node.continuation, node.handler)) r.start (slots.map ρ) .nul) := by
    intro j V heap ρ he hw hh
    have hs := checkRequests_safe_at accepted member η admitted j V heap _
      (projected_env length types he) hw hh (separation _)
    rw [← program_nodes r.program] at hs
    have safe := GraphCode.safe_of_sim j V heap GraphCode.Sim.goto hs
    simpa [Request.goal, promise, GoalHolds, result] using safe
  have safe : Safe (excOf (reassign (graph r.toRequest) η))
      (meaning (reassign (graph r.toRequest) η) row.result) n W heap
      (.goto [invocationExpression r.toRequest slots] [(.ret, none)] 0 L .nul) := by
    cases n with
    | zero => trivial
    | succ n =>
      refine .inr ⟨_, heap, _, WExt_refl _, WorldAdm_trunc _ hw,
        Step.gotoEnter rfl rfl, HeapOk_trunc n W heap hh, ?_⟩
      apply return_frame_safe (builtinExc_adm _ _) (meaning_adm _ _)
        (WorldAdm_trunc _ hw) (HeapOk_trunc n W heap hh)
      simpa [invocationExpression, instantiate, instantiateArgs_eq_map, List.map_map,
        Function.comp_def] using run n _ heap (envOf L .nul)
          (he.transfer n (Nat.le_succ n) _ (WExt_refl _))
          (WorldAdm_trunc _ hw) (HeapOk_trunc n W heap hh)
  simp only [ordinary, CallEffects.Effect.result, CallEffects.Effect.ordinary,
    CallEffects.Effect.ofFootprint]
  apply HeapObservations.SafePostExc.of_post (fun _ _ h => Bool.noConfusion h)
  refine HeapObservations.weaken (fun _ _ hp _ => ?_) (Footprints.Closed.top_safe safe)
  exact ⟨CallEffects.Effect.within_of_holds hp, by simp, by simp, by simp⟩

/-- Accepted footprint claims also survive the invocation adapter, including
preservation on throws when the request states it. This covers the qualified
module bindings emitted for ordinary synchronous functions. Promises, fresh
results and receiver-relative effects need their corresponding source proof. -/
theorem code_of_effectful_adapted_request {σ ι : Type}
    [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (accepted : checkRequests rs b = true) {r c}
    (member : (r, c) ∈ rs.zip b.functions) (η : MixedAssignment ι)
    {arity : Nat} {Cs : List (Ty ι)} {row : CallEffects.Arrow (Ty ι)}
    (arityOk : arity ≤ row.arguments.length)
    (effect : row.effect = { CallEffects.Effect.ofFootprint r.footprint with onThrow := r.onThrow })
    (effectful : r.footprint ≠ .top ∨ r.onThrow = true)
    (result : r.result = row.result) (promise : r.promise = none)
    (slots : List Nat) (length : slots.length = r.inputs.length)
    (types : ∀ (k : Nat) (A : Ty ι), r.inputs[k]? = some A →
      ∃ j, slots[k]? = some j ∧ (codeFrame arity row Cs none)[j]? = some A)
    (separation : ∀ ρ, HeapSeparation.Holds r.entrySeparation ρ) :
    CodeOffers (reassign (graph r.toRequest) η) arity
      [invocationExpression r.toRequest slots] [(.ret, none)] 0 Cs false [row] [] [] := by
  intro p hp
  have hp : p = row := by simpa [offerRows] using hp
  subst p
  refine ⟨arityOk, ?_, ?_⟩
  · simp [effect, CallEffects.Effect.ofFootprint, CallEffects.Effect.below]
  intro n W heap L he hw hh values
  simp only [effect, CallEffects.Effect.ofFootprint, CallEffects.Effect.result]
  cases n with
  | zero => trivial
  | succ n =>
    have hvalues : ∀ v ∈ slots.map (envOf L .nul), isVal v = true := by
      intro v hv
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
      simp only [envOf, List.getD]
      cases hj : L[j]? with
      | none => rfl
      | some v => exact values v (List.mem_of_getElem? hj)
    have hs := checkRequests_footprint_at accepted member effectful η n _ heap
      (slots.map (envOf L .nul)) .nul
      (projected_env length types (he.transfer n (Nat.le_succ n) _ (WExt_refl _)))
      (WorldAdm_trunc _ hw) (HeapOk_trunc n W heap hh) hvalues rfl (separation _)
    have goal : GoalHolds (reassign (graph r.toRequest) η) r.goal
        (r.goal.argument (envOf (slots.map (envOf L .nul)) .nul)) =
        meaning (reassign (graph r.toRequest) η) row.result := by
      simp [Request.goal, promise, GoalHolds, result]
    rw [goal] at hs
    have normal : ∀ after v, r.footprint.Holds heap after →
        ∀ receiver, ({ CallEffects.Effect.ofFootprint r.footprint with onThrow := r.onThrow } :
          CallEffects.Effect).post receiver heap after v := by
      intro after v hp receiver
      exact ⟨CallEffects.Effect.within_of_holds hp, by simp [CallEffects.Effect.ofFootprint],
        by simp [CallEffects.Effect.ofFootprint], by simp [CallEffects.Effect.ofFootprint]⟩
    have exceptional : ∀ after, (r.onThrow = true → r.footprint.Holds heap after) →
        ∀ receiver, ({ CallEffects.Effect.ofFootprint r.footprint with onThrow := r.onThrow } :
          CallEffects.Effect).excPost receiver heap after := by
      intro after hp receiver ht
      exact CallEffects.Effect.within_of_holds (hp ht)
    have inner := HeapObservations.SafePostExc.weaken normal exceptional hs
    refine .inr ⟨_, heap, _, WExt_refl _, WorldAdm_trunc _ hw,
      Step.gotoEnter rfl rfl, HeapOk_trunc n W heap hh, ?_⟩
    apply return_frame_post (builtinExc_adm _ _) (meaning_adm _ _)
      (WorldAdm_trunc _ hw) (HeapOk_trunc n W heap hh)
    simpa [invocationExpression, instantiate, instantiateArgs_eq_map, List.map_map,
      Function.comp_def, CallEffects.Effect.ofFootprint] using inner

/-- No captures: the adapter drops the invocation receiver and ignores self.
Its checked projection is determined entirely by the parameter count. -/
theorem code_of_capture_free_request {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι]
    {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (accepted : checkRequests rs b = true) {r c}
    (member : (r, c) ∈ rs.zip b.functions)
    (η : MixedAssignment ι) (admitted : r.Admits η)
    {row : CallEffects.Arrow (Ty ι)} (signature : Ty ι)
    (ordinary : row.effect = CallEffects.Effect.ordinary)
    (parameters : r.inputs = row.arguments) (result : r.result = row.result)
    (promise : r.promise = none) (separation : r.entrySeparation.facts = []) :
    CodeOffers (reassign (graph r.toRequest) η) row.arguments.length
      [invocationExpression r.toRequest ((List.range row.arguments.length).map (· + 1))]
      [(.ret, none)] 0 [signature] false [row] [] [] := by
  apply code_of_adapted_request accepted member η admitted (Nat.le_refl _) ordinary result promise
    ((List.range row.arguments.length).map (· + 1))
  · simp [parameters]
  · intro k A hA
    rw [parameters] at hA
    have hk := (List.getElem?_eq_some_iff.mp hA).1
    refine ⟨k + 1, ?_, ?_⟩
    · simp [hk]
    · simpa [codeFrame, bodyFrame, List.getElem?_append, hk] using hA
  · intro ρ
    simp [HeapSeparation.Holds, separation]

end Verification.Linking
