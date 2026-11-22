import Verification.Source.Claims.PassUnitModules

/-! # The single pass's unit theorem: expression obligations

`passGroup` checks each member's expression claims (`ExpressionClaims.checkAllResult`
over the request's obligations and the evidence for them), against the
member's code table and the read summaries its last run left. Each
obligation is a sequent `Γ ⊢ t : A` at a source position. This module proves
what an accepted check gives: each obligation's term, run from every
environment meeting its context, is safe at its type
(docs/SINGLE-PASS-THEOREM.md, section 8). -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore
open ProgramCertificates (CodesSound SummariesSound ReadSummary Evidence CheckResult checkTreeUsing_sound)

section
variable {ι : Type} [DecidableEq ι]

/-- **An accepted expression check types each obligation** (proved): where
the check of obligations `rs` against evidence `es` accepts, over a sound
code table and sound read summaries, each obligation `Γ ⊢ t : A` holds
semantically: from every environment meeting `Γ`, at every budget, world
and heap the world types, `t` is safe at `A`. -/
theorem obligations_sound {G : NormalGraph ι} {images : PositiveCertificates.InstanceImageCheck G}
    {valid : ι → Bool} {rs : List (ExpressionClaims.Required ι)} {es : List (Evidence ι)}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (h : (ExpressionClaims.checkAllResult G images valid rs es codes sums).accepted = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) :
    ∀ o ∈ rs, ∀ n W heap ρ, EnvOk G o.sequent.context ρ n W → WorldAdm W → HeapOk n W heap →
      RefsOk W (instantiate 0 ρ o.sequent.term) →
      Safe (excOf G) (meaning G o.sequent.type) n W heap (instantiate 0 ρ o.sequent.term) := by
  unfold ExpressionClaims.checkAllResult at h
  rw [CheckResult.accepted_bind, CheckResult.accepted_ofBool, CheckResult.accepted_allLocated,
    Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hlen : rs.length = es.length := by simpa using hlen
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
  have hie : i < es.length := hlen ▸ hi
  have hmem : (rs[i], es[i]) ∈ rs.zip es := by
    have := List.getElem_mem (l := rs.zip es) (n := i) (by simp only [List.length_zip]; omega)
    simpa [List.getElem_zip] using this
  have hc := hall _ hmem
  simp only [ExpressionClaims.checkResult, CheckResult.accepted_bind, CheckResult.accepted_ofBool,
    Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨-, hclaim⟩, -⟩, htree⟩ := hc
  have ht := checkTreeUsing_sound es[i] htree hcodes hsums
  rw [hclaim] at ht
  exact ht.sound

end

/-- Two plans at one member are one request (proved). -/
theorem planAt_unique {f : FilePlans} {j : Nat} {n n' : String} {p p' : Span} {r r' : Req f}
    (h : PlanAt f j n p r) (h' : PlanAt f j n' p' r') : r = r' := by
  unfold PlanAt at h h'
  rw [h] at h'
  injection h' with h'
  injection h' with h'
  injection h'

/-- A member's plan is a graph plan or a framed plan, not both (proved). -/
theorem planAt_not_framed {f : FilePlans} {j : Nat} {n n' : String} {p p' : Span} {r r' : Req f}
    {spec : FramedSpec (EquationStore.CheckedLabel f.F.equations f.F.primitive)}
    (h : PlanAt f j n p r) (h' : FramedPlanAt f j n' p' r' spec) : False := by
  unfold PlanAt at h
  unfold FramedPlanAt at h'
  rw [h] at h'
  injection h' with h'
  injection h' with h'
  cases h'

theorem planAt_not_callbackDemands {f : FilePlans} {j : Nat} {name name' : String} {pos pos' : Span} {r r' : Req f}
    {spec : CallbackDemands.CallbackDemandSpec}
    (hp : PlanAt f j name pos r) (hc : CallbackDemandsPlanAt f j name' pos' r' spec) : False := by
  unfold PlanAt at hp; unfold CallbackDemandsPlanAt at hc
  rw [hp] at hc
  injection hc with hc
  injection hc with hc
  cases hc

/-- **An accepted async member claims no footprint** (proved): the declared
effect's conditions `passGroup` checks make an async member's footprint the
one letting every location change, the property `checkRequests_async`
states of the proved checker's requests, outside `RequestsSafe`. -/
theorem member_async {f : FilePlans} {j : Nat} {name : String} {pos : Span} {r : Req f}
    (hm : MemberAccepted f j) (hp : PlanAt f j name pos r) (ha : r.async = true) : r.footprint = .top := by
  have hd : declaredEffect r = true := by
    cases hm with
    | ordinary name' pos' r' _ _ hplan _ hdecl _ _ _ => rw [planAt_unique hp hplan]; exact hdecl
    | qualified name' pos' r' _ _ _ _ hplan _ hdecl _ _ _ _ _ _ _ _ _ _ _ => rw [planAt_unique hp hplan]; exact hdecl
    | framed _ _ _ _ _ hplan _ => exact (planAt_not_framed hp hplan).elim
    | callbackDemands _ _ _ _ _ hplan _ => exact (planAt_not_callbackDemands hp hplan).elim
  simp only [declaredEffect, RequestJson.asyncEffects, Bool.and_eq_true, ha,
    Bool.not_true, Bool.false_or, beq_iff_eq] at hd
  exact hd.1.1

/-- Each code request accepted in order meets the async condition (proved). -/
theorem codesAccepted_async {σ ι : Type} [Labels ι] [StoreView σ ι] {G : NormalGraph ι}
    {I : PositiveCertificates.InstanceImageCheck G} {r : SourceRequest σ ι} :
    ∀ {table rest a a'}, CodesAccepted G I r table rest a a' →
      ∀ p ∈ rest, RequestJson.asyncAdmits p.1.async p.1.entry.row.effect = true
  | _, [], _, _, _ => fun _ hp => nomatch hp
  | _, (q, ci) :: rest, _, _, h => by
    obtain ⟨_, ⟨_, hasync, _⟩, hrest⟩ := h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hasync
    · exact codesAccepted_async hrest p hp

/-- **An accepted member's async code requests admit every change**
(proved, `Effect.admitsAll`): the other half of `checkRequests_async`, from the async condition
`passGroup` checks of each code request before its run. -/
theorem codes_async {f : FilePlans} {j : Nat} {name : String} {pos : Span} {r : Req f}
    (hm : MemberAccepted f j) (hp : PlanAt f j name pos r) :
    ∀ q ∈ r.codes, q.async = true → q.entry.row.effect.admitsAll = true := by
  intro q hq ha
  cases hm with
  | ordinary name' pos' r' _ _ hplan _ _ _ hcodes _ =>
    rw [← planAt_unique hp hplan] at hcodes
    obtain ⟨ci, hci⟩ : ∃ ci, (q, ci) ∈ r.codes.zipIdx := by
      obtain ⟨ci, hci, rfl⟩ := List.getElem_of_mem hq
      exact ⟨ci, List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hci])⟩
    have h := codesAccepted_async hcodes (q, ci) hci
    simp only [RequestJson.asyncAdmits, ha, Bool.not_true, Bool.false_or] at h
    exact h
  | qualified name' pos' r' _ _ _ _ hplan _ _ _ _ _ _ _ hcodes _ _ _ _ _ =>
    rw [← planAt_unique hp hplan] at hcodes
    rw [hcodes] at hq; cases hq
  | framed _ _ _ _ _ hplan _ => exact (planAt_not_framed hp hplan).elim
  | callbackDemands _ _ _ _ _ hplan _ => exact (planAt_not_callbackDemands hp hplan).elim

end Verification.SourceClaimJson.PassUnit
