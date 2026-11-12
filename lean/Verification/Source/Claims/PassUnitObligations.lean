import Verification.Source.Claims.PassUnitModules

/-! # The single pass's unit theorem: expression obligations

`passGroup` checks each member's expression claims (`ExpressionClaims.checkAllResult`
over the request's obligations and the evidence for them), against the
member's code table and the read summaries its last run left. Each
obligation is a sequent `Γ ⊢ t : A` at a source position. This module proves
what an accepted check gives: each obligation's term, run from every
environment meeting its context, is safe at its type
(docs/drafts/pass-unit-theorem.md, section 8). -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
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
  simp only [declaredEffect, RequestJson.asyncEffects, Bool.and_eq_true, ha,
    Bool.not_true, Bool.false_or, beq_iff_eq] at hd
  exact hd.1.1

end Verification.SourceClaimJson.PassUnit
