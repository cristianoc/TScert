import Verification.Source.Claims.PassUnit

/-! # The single pass's unit theorem: the code table

The code requests of a unit, each passed over its own graph against the
codes admitted before it (`FilePlans.passGroup`'s loop over `r.codes`), and
the induction that makes the table they build sound
(`codesAccepted_sound`), the pass's counterpart of
`GraphCode.extendTable_sound`. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open PositiveCertificates (InstanceImageCheck)
open HeapExpressionRules (Checker)
open CertificateProducer (Answered)

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- A code's signature conditions, as `passGroup` checks them before its run:
its arity within its arguments, its effect below its arity, and no fresh
object, precondition, element promise, receiver growth or element write. -/
def codeConditions (c : CodeEntry ι) : Bool :=
  decide (c.arity ≤ c.row.arguments.length) && c.row.effect.below c.arity &&
    !c.row.effect.freshObject && c.row.effect.requires.isNone && c.row.effect.elements.isNone &&
    !c.row.effect.receiverGrows && c.row.effect.elementWrite.isNone

/-- The bound a code's run is given, as `passGroup` computes it: none for the
footprint letting everything change on normal return alone, none for a pure
graph promising no fresh result, its footprint, fresh flag and throw flag
otherwise. -/
def codeBound (c : CodeEntry ι) : Option (Footprints.Closed × Bool × Bool) :=
  if c.row.effect.footprint == .top && !c.row.effect.fresh && !c.row.effect.onThrow then none
  else if !c.row.effect.fresh && c.exprs.all Purity.pureTerm then none
  else some (c.row.effect.footprint, c.row.effect.fresh, c.row.effect.onThrow)

/-- **A code request's run, as `passGroup` makes it**: its conditions hold,
and a call of the pass over its graph from its start, at its goal, its
requirements as assertions, its entry indices, the codes `table` admits, the
ordinary checker, starting from the answers `a`, at its bound, with no
postcondition, separation or regional option, accepted leaving `a'`. -/
def CodeRunAccepted (G : NormalGraph ι) (I : InstanceImageCheck G) (r : SourceRequest σ ι)
    (table : List (CodeEntry ι)) (q : CodeRequest ι) (ci : Nat) (a a' : Answered G) : Prop :=
  codeConditions q.entry = true ∧
  ∃ c : RunCall G I, c.P = (codeRequest r q).program ∧ c.claims = q.claims ∧ c.start = q.entry.start ∧
    c.goal = q.entry.goal ∧ c.assertions = (codeHintsAt r ci).requirements ∧
    c.entryIndices = GraphCode.codeEntryIndices q.entry ∧ c.codes = GraphCode.admits table ∧
    c.checker = Checker.ordinary G I ∧ c.answers = a ∧ c.bound = codeBound q.entry ∧ c.ensures = [] ∧
    c.entrySeparation = {} ∧ c.regional = none ∧ c.Accepts a'

/-- The code requests `rest` (with their positions) accepted in order, each
against `table` and the codes accepted before it, the answers threaded from
`a` to `a'`. -/
def CodesAccepted (G : NormalGraph ι) (I : InstanceImageCheck G) (r : SourceRequest σ ι) :
    List (CodeEntry ι) → List (CodeRequest ι × Nat) → Answered G → Answered G → Prop
  | _, [], a, a' => a' = a
  | table, (q, ci) :: rest, a, a' => ∃ a₁, CodeRunAccepted G I r table q ci a a₁ ∧
      CodesAccepted G I r (table ++ [q.entry]) rest a₁ a'

end

section
variable {ι : Type}

/-- The goal a code's graph is checked at is its signature's result, its
promise included (as in `GraphCode.codeChecked_sound`). -/
theorem code_goal (G : NormalGraph ι) (c : CodeEntry ι) (L : List Tm) :
    GoalHolds G c.goal (c.goal.argument (envOf L .nul)) =
      c.row.effect.result (meaning G c.row.result) (framePromised c.row.effect (frameOffset c.store) L) := by
  rcases hpr : c.row.effect.promise with _ | (p | p)
  · have hg : c.goal = .plain c.row.result := by simp [CodeEntry.goal, hpr]
    rw [hg, CallEffects.Effect.result_none hpr]
    rfl
  · have hg : c.goal = .guards c.row.result (frameOffset c.store + p) := by
      simp [CodeEntry.goal, hpr]
    rw [hg]
    simp only [CallEffects.Effect.result, framePromised, hpr, CallEffects.TypePromise.result,
      CallEffects.TypePromise.param]
    rfl
  · have hg : c.goal = .asserts c.row.result (frameOffset c.store + p) := by
      simp [CodeEntry.goal, hpr]
    rw [hg]
    simp only [CallEffects.Effect.result, framePromised, hpr, CallEffects.TypePromise.result,
      CallEffects.TypePromise.param]
    rfl

/-- **A code safe from its frame, within its bound, meets its signature**
(proved): a code meeting its conditions, whose graph is safe at every
assignment from its frame (`codeFrame`) at its goal, and within its bound
(`codeBound`) where it has one, run as its node lists, is graph code at its
signature at every assignment. The step shared by code requests
(`codeSpec_of_guarantee`) and units (`unitSpec_of_requestSafe`). -/
theorem codeSpec_of_clauses {G : NormalGraph ι} {c : CodeEntry ι}
    (hcond : codeConditions c = true)
    (hsafeG : ∀ η n W h ρ, EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.store) {}
      (GraphCode.codeEntryIndices c) ρ n W h →
      SafeGraph (excOf (reassign G η)) (GraphCode.program c.exprs c.conts)
        (GoalHolds (reassign G η) c.goal (c.goal.argument ρ)) n W h (.at c.start ρ))
    (hboundG : ∀ Φ fresh onThrow, codeBound c = some (Φ, fresh, onThrow) → ∀ η n W h L d,
      EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.store) {} (GraphCode.codeEntryIndices c)
        (envOf L d) n W h → (∀ v ∈ L, isVal v = true) → isVal d = true →
      HeapObservations.SafePostExc (excOf (reassign G η))
        (GoalHolds (reassign G η) c.goal (c.goal.argument (envOf L d)))
        (fun h' v => Φ.Holds h h' ∧ (fresh = true → Footprints.FreshAt h.length v))
        (fun h' => onThrow = true → Φ.Holds h h') n W h (.goto c.exprs c.conts c.start L d)) :
    ∀ η, c.Spec (reassign G η) := by
  intro η
  simp only [codeConditions, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hcond
  obtain ⟨⟨⟨⟨⟨⟨harity, hbelow⟩, hfo⟩, _hreq⟩, hel⟩, hgr⟩, hew⟩ := hcond
  refine ⟨harity, hbelow, ?_⟩
  intro n W heap L he hw hh hvalues hpre r args _hframe
  have hentry : EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.store) {}
      (GraphCode.codeEntryIndices c) (envOf L .nul) n W heap :=
    ⟨he, HeapSeparation.empty_holds _, GraphCode.codeEntryIndices_holds hpre, hw, hh⟩
  have hgraph := hsafeG η n W heap (envOf L .nul) hentry
  have hs : Safe (excOf (reassign G η)) (GoalHolds (reassign G η) c.goal (c.goal.argument (envOf L .nul)))
      n W heap (.goto c.exprs c.conts c.start L .nul) :=
    GraphCode.safe_of_sim n W heap .goto hgraph
  have hsafe : Safe (excOf (reassign G η)) (c.row.effect.result (meaning (reassign G η) c.row.result)
      (framePromised c.row.effect (frameOffset c.store) L)) n W heap
      (.goto c.exprs c.conts c.start L .nul) := code_goal (reassign G η) c L ▸ hs
  have hens := CallEffects.Effect.below_ensures hbelow
  have hnrg := CallEffects.Effect.below_regions hbelow
  have hnen : ∀ F, F ∈ c.row.effect.ensures → False := fun F hF => by rw [hens] at hF; cases hF
  have hnel : ∀ R, c.row.effect.elements = some R → False := by
    intro R hR; rw [hel] at hR; cases hR
  have hngr : c.row.effect.receiverGrows = true → False := fun h => by rw [hgr] at h; cases h
  have hnew : ∀ w, c.row.effect.elementWrite = some w → False := fun w h => by rw [hew] at h; cases h
  by_cases htop : c.row.effect.footprint = .top ∧ c.row.effect.fresh = false ∧ c.row.effect.onThrow = false
  · -- No footprint on a throw: the throw's postcondition is vacuous.
    apply HeapObservations.SafePostExc.of_post (fun _ h => absurd h (by simp [htop.2.2]))
    refine HeapObservations.weaken (fun h' v hp => ?_) (Footprints.Closed.top_safe hsafe)
    refine ⟨CallEffects.Effect.within_of_footprint hnrg ?_, fun hf => (by rw [htop.2.1] at hf; cases hf),
      fun hf => (by rw [hfo] at hf; cases hf), fun R hR => (hnel R hR).elim, fun F hF => (hnen F hF).elim,
      fun hg => (hngr hg).elim, fun w hw => (hnew w hw).elim⟩
    rw [htop.1]
    exact hp
  · by_cases hpure : c.row.effect.fresh = false ∧ c.exprs.all Purity.pureTerm = true
    · have hp : ∀ e ∈ c.exprs, Purity.pureTerm e = true := List.all_eq_true.mp hpure.2
      exact HeapObservations.SafePostExc.weaken
        (fun h' v hq => ⟨CallEffects.Effect.within_of_footprint hnrg
          (Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _)
            ((CallEffects.Effect.post_ofFootprint _ .undef [] _ _ _).mp hq)), fun hf => (by rw [hpure.1] at hf; cases hf),
          fun hf => (by rw [hfo] at hf; cases hf), fun R hR => (hnel R hR).elim, fun F hF => (hnen F hF).elim,
          fun hg => (hngr hg).elim, fun w hw => (hnew w hw).elim⟩)
        (fun h' hq _ => CallEffects.Effect.within_of_footprint hnrg
          (Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _) hq))
        (CallEffects.pure_safe_exc (r := .undef) (args := []) (.goto hp hvalues rfl) hsafe)
    · have hbound : codeBound c = some (c.row.effect.footprint, c.row.effect.fresh, c.row.effect.onThrow) := by
        have h1 : (c.row.effect.footprint == .top && !c.row.effect.fresh && !c.row.effect.onThrow) = false := by
          cases hfp : c.row.effect.footprint == .top <;> cases hfr : c.row.effect.fresh <;>
            cases hot : c.row.effect.onThrow <;> simp_all
        have h2 : (!c.row.effect.fresh && c.exprs.all Purity.pureTerm) = false := by
          cases hfr : c.row.effect.fresh <;> cases hal : c.exprs.all Purity.pureTerm <;> simp_all
        simp only [codeBound, h1, h2]
        rfl
      have hb := hboundG _ _ _ hbound η n W heap L .nul hentry
        (fun v hv => hvalues v hv) rfl
      rw [code_goal] at hb
      exact HeapObservations.SafePostExc.weaken
        (fun h' v hq => ⟨CallEffects.Effect.within_of_footprint hnrg hq.1, hq.2, fun hf => (by rw [hfo] at hf; cases hf),
          fun R hR => (hnel R hR).elim, fun F hF => (hnen F hF).elim,
          fun hg => (hngr hg).elim, fun w hw => (hnew w hw).elim⟩)
        (fun h' hq ho => CallEffects.Effect.within_of_footprint hnrg (hq ho)) hb


/-- **A code whose run guarantees its graph meets its signature** (proved):
a code meeting its conditions, whose graph is guaranteed at every assignment
from its frame (`codeFrame`), at its goal and its bound (`codeBound`), is
graph code at its signature at every assignment. The pass's counterpart of
`GraphCode.codeChecked_sound`: its premises are the guarantee and the
conditions, in place of the certificate check. -/
theorem codeSpec_of_guarantee {G : NormalGraph ι} {c : CodeEntry ι}
    {assertions : List (Nat × HeapKnowledge.Knowledge)}
    (hcond : codeConditions c = true)
    (hg : GraphGuarantee G (fun _ => True) (GraphCode.program c.exprs c.conts) c.start c.goal
      (codeFrame c.arity c.row c.captures c.store) {} (GraphCode.codeEntryIndices c) assertions
      (codeBound c) [] none) :
    ∀ η, c.Spec (reassign G η) :=
  codeSpec_of_clauses hcond (fun η => hg.safe η trivial)
    (fun _ _ _ hb η => hg.bounded _ _ _ hb c.exprs c.conts rfl η trivial)

end

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- A sound summary table stays sound on a sub-table. -/
theorem summariesSound_sub {G : NormalGraph ι} {I : InstanceImageCheck G}
    {s t : List (ProgramCertificates.ReadSummary ι)} (hs : ∀ x ∈ s, x ∈ t)
    (ht : ProgramCertificates.SummariesSound G I t) : ProgramCertificates.SummariesSound G I s :=
  fun x hx => ht x (hs x hx)

/-- The table of codes admitting one entry more. -/
theorem codesSound_snoc {G : NormalGraph ι} {table : List (CodeEntry ι)} {e : CodeEntry ι}
    (ht : ProgramCertificates.CodesSound G (GraphCode.admits table)) (he : ∀ η, e.Spec (reassign G η)) :
    ProgramCertificates.CodesSound G (GraphCode.admits (table ++ [e])) := by
  intro c hc η
  simp only [GraphCode.admits, List.contains_append, Bool.or_eq_true, List.contains_cons,
    List.contains_nil, Bool.or_false, beq_iff_eq, List.contains_iff_mem] at hc
  rcases hc with hc | rfl
  · exact ht c (by simp [GraphCode.admits, hc]) η
  · exact he η

/-- The code runs keep the read summaries they start from (under
`RunKeepsSummaries`). -/
theorem codesAccepted_keeps {G : NormalGraph ι} {I : InstanceImageCheck G} {r : SourceRequest σ ι}
    (hkeep : RunKeepsSummaries ι) :
    ∀ {table rest a a'}, CodesAccepted G I r table rest a a' →
      ∀ s ∈ a.summaries.toList, s ∈ a'.summaries.toList
  | _, [], a, a', h => by
    simp only [CodesAccepted] at h; subst h; exact fun _ hs => hs
  | table, (q, ci) :: rest, a, a', h => by
    obtain ⟨a₁, ⟨_, c, -, -, -, -, -, -, -, -, hans, -, -, -, -, counts, trace, hres⟩, hrest⟩ := h
    intro s hs
    have h1 := hkeep G I c s (hans ▸ hs)
    rw [hres] at h1
    exact codesAccepted_keeps hkeep hrest s h1

/-- **The table the pass builds is sound** (proved, under `RunSound` and
`RunKeepsSummaries`): code requests accepted in order, each against the
table of those before it, starting from a sound table, with the summaries
the last run leaves within a sound table, and each code's start claim
stating its frame, extend it to a sound table. The pass's counterpart of
`GraphCode.extendTable_sound`: each step's premise is an accepted run of
the pass (`CodeRunAccepted`) in place of `codeCheckedUsing`, and the
summaries are the final ones the wrapper checks. -/
theorem codesAccepted_sound {G : NormalGraph ι} {I : InstanceImageCheck G} {r : SourceRequest σ ι}
    (hrun : RunSound ι) (hkeep : RunKeepsSummaries ι)
    {final : List (ProgramCertificates.ReadSummary ι)} (hfinal : ProgramCertificates.SummariesSound G I final) :
    ∀ {table rest a a'}, CodesAccepted G I r table rest a a' →
      (∀ p ∈ rest, StartContext p.1.claims p.1.entry.start
        (codeFrame p.1.entry.arity p.1.entry.row p.1.entry.captures p.1.entry.store)) →
      (∀ s ∈ a'.summaries.toList, s ∈ final) →
      ProgramCertificates.CodesSound G (GraphCode.admits table) →
      ProgramCertificates.CodesSound G (GraphCode.admits (table ++ rest.map (·.1.entry)))
  | table, [], a, a', _, _, _, ht => by simpa using ht
  | table, (q, ci) :: rest, a, a', h, hstart, hsub, ht => by
    obtain ⟨a₁, ⟨hcond, c, hP, hcl, hst, hgoal, has, hidx, hcodes, hchk, hans, hbd, hens, hsep, hreg, hacc⟩,
      hrest⟩ := h
    have hsums : ProgramCertificates.SummariesSound G I a₁.summaries.toList :=
      summariesSound_sub (fun s hs => hsub s (codesAccepted_keeps hkeep hrest s hs)) hfinal
    have hscope : CheckerScope G I c.checker (fun _ => True) := hchk ▸ CheckerScope.ordinary
    have hctx : StartContext c.claims c.start
        (codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.store) := by
      rw [hcl, hst]; exact hstart (q, ci) List.mem_cons_self
    have hg := hrun G I c a₁ _ _ hacc hscope hctx (hcodes ▸ ht) hsums
      (fun _ _ _ h => by rw [hreg] at h; cases h)
    rw [hP, hgoal, hst, hsep, hidx, hbd, hens, hreg] at hg
    have hspec := codeSpec_of_guarantee hcond hg
    have := codesAccepted_sound hrun hkeep hfinal hrest (fun p hp => hstart p (List.mem_cons_of_mem _ hp))
      hsub (codesSound_snoc ht hspec)
    simpa [List.append_assoc] using this

/-- **Each accepted code's graph is guaranteed** (proved, under `RunSound`
and `RunKeepsSummaries`): in the setting of `codesAccepted_sound`, every
code request of `rest` has the guarantee of its run, its requirements
included. -/
theorem codesAccepted_guarantees {G : NormalGraph ι} {I : InstanceImageCheck G} {r : SourceRequest σ ι}
    (hrun : RunSound ι) (hkeep : RunKeepsSummaries ι)
    {final : List (ProgramCertificates.ReadSummary ι)} (hfinal : ProgramCertificates.SummariesSound G I final) :
    ∀ {table rest a a'}, CodesAccepted G I r table rest a a' →
      (∀ p ∈ rest, StartContext p.1.claims p.1.entry.start
        (codeFrame p.1.entry.arity p.1.entry.row p.1.entry.captures p.1.entry.store)) →
      (∀ s ∈ a'.summaries.toList, s ∈ final) →
      ProgramCertificates.CodesSound G (GraphCode.admits table) →
      ∀ p ∈ rest, GraphGuarantee G (fun _ => True) (GraphCode.program p.1.entry.exprs p.1.entry.conts)
        p.1.entry.start p.1.entry.goal (codeFrame p.1.entry.arity p.1.entry.row p.1.entry.captures p.1.entry.store)
        {} (GraphCode.codeEntryIndices p.1.entry) (codeHintsAt r p.2).requirements (codeBound p.1.entry) [] none
  | _, [], _, _, _, _, _, _ => fun _ hp => nomatch hp
  | table, (q, ci) :: rest, a, a', h, hstart, hsub, ht => by
    obtain ⟨a₁, ⟨hcond, c, hP, hcl, hst, hgoal, has, hidx, hcodes, hchk, hans, hbd, hens, hsep, hreg, hacc⟩,
      hrest⟩ := h
    have hsums : ProgramCertificates.SummariesSound G I a₁.summaries.toList :=
      summariesSound_sub (fun s hs => hsub s (codesAccepted_keeps hkeep hrest s hs)) hfinal
    have hscope : CheckerScope G I c.checker (fun _ => True) := hchk ▸ CheckerScope.ordinary
    have hctx : StartContext c.claims c.start
        (codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.store) := by
      rw [hcl, hst]; exact hstart (q, ci) List.mem_cons_self
    have hg := hrun G I c a₁ _ _ hacc hscope hctx (hcodes ▸ ht) hsums
      (fun _ _ _ h => by rw [hreg] at h; cases h)
    rw [hP, hgoal, hst, hsep, hidx, hbd, hens, hreg, has] at hg
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hg
    · exact codesAccepted_guarantees hrun hkeep hfinal hrest (fun p hp => hstart p (List.mem_cons_of_mem _ hp))
        hsub (codesSound_snoc ht (codeSpec_of_guarantee hcond hg)) p hp

end

end Verification.SourceClaimJson.PassUnit
