import Verification.Source.Claims.PassUnitMember

/-! # The single pass's unit theorem: an accepted member is safe

`member_safe`: a member `passGroup` accepts (`MemberAccepted`) is safe
(`MemberSafe`), under `RunSound` and `RunKeepsSummaries`, its plans over the
file's frozen store and stating their start contexts. Then the headline
(`passUnit_safe`) from mode 8's exact acceptance condition. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open PositiveCertificates (InstanceImageCheck)
open HeapExpressionRules (Checker)
open CertificateProducer (Answered)

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- No region has its entry fields' conditions. -/
theorem checkEntryFields_nil (G : NormalGraph ι) (inputs : List (Ty ι)) :
    GraphCode.ArgumentPathTracking.checkEntryFields G inputs [] = true := by
  simp [GraphCode.ArgumentPathTracking.checkEntryFields, GraphCode.ArgumentPathTracking.stableFields]

/-- **A main call's guarantee** (under `RunSound`): a call of the pass over a
request's own graph (`MainCall`), accepted, its checker covering `admits`,
its codes and the summaries it leaves sound, its regions meeting their
entry conditions, the request's start claim stating its inputs, guarantees
the request's graph at its bound, postcondition and regional option. -/
theorem main_guarantee {G : NormalGraph ι} {I : InstanceImageCheck G} {r : SourceRequest σ ι}
    (hrun : RunSound ι) {c : RunCall G I} {codes : CodeEntry ι → Bool} {checker : Checker G I}
    {a after : Answered G} {admits : MixedAssignment ι → Prop}
    (hm : MainCall r c codes checker a) (hscope : CheckerScope G I checker admits)
    (hctx : StartContext r.claims r.start r.inputs) (hcodes : ProgramCertificates.CodesSound G codes)
    (hacc : c.Accepts after) (hsums : ProgramCertificates.SummariesSound G I after.summaries.toList)
    (hreg : ∀ Φ regions exc, regionOf c.regional = some (Φ, regions, exc) →
      GraphCode.ArgumentPathTracking.checkEntryFields G r.inputs regions = true) :
    GraphGuarantee G admits r.program r.start r.goal r.inputs r.entrySeparation r.entryIndices r.assertions
      c.bound r.ensures (regionOf c.regional) := by
  obtain ⟨hP, hcl, hst, hgoal, has, hidx, hc, hchk, -, hens, hsep⟩ := hm
  have hg := hrun G I c after admits r.inputs hacc (hchk ▸ hscope) (by rw [hcl, hst]; exact hctx)
    (hc ▸ hcodes) hsums hreg
  rw [hP, hst, hgoal, hsep, hidx, has, hens] at hg
  exact hg

/-- The node lists of a request's program. -/
abbrev exprsOf (P : Program) : List Tm := P.map (·.expression)

/-- The continuations and handlers of a request's program. -/
abbrev contsOf (P : Program) : List (Continuation × Option Target) := P.map fun n => (n.continuation, n.handler)

omit [Labels ι] [StoreView σ ι] in
/-- A guarantee's safety, as the term running the graph. -/
theorem guarantee_goto {G : NormalGraph ι} {admits : MixedAssignment ι → Prop} {P : Program} {start : Nat}
    {goal : Goal ι} {inputs sep idx assertions bound ensures regional}
    (g : GraphGuarantee G admits P start goal inputs sep idx assertions bound ensures regional)
    {η} (hη : admits η) {n W h L d}
    (he : EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h) :
    Safe (excOf (reassign G η)) (GoalHolds (reassign G η) goal (goal.argument (envOf L d))) n W h
      (gotoOf P start L d) := by
  have hs := g.safe η hη n W h (envOf L d) he
  rw [← program_nodes P] at hs
  exact GraphCode.safe_of_sim n W h .goto hs

/-- **A request's footprint from its main run** (proved): a guarantee at
`mainBound` gives the claimed footprint, the bound's own clause where the
run had one, the purity of the graph otherwise. -/
theorem footprint_of_bound {G : NormalGraph ι} {r : SourceRequest σ ι} {regional}
    (g : GraphGuarantee G (fun _ => True) r.program r.start r.goal r.inputs r.entrySeparation r.entryIndices
      r.assertions (mainBound r) r.ensures regional)
    (heffect : r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true)
    (η : MixedAssignment ι) (n : Nat) (W : WorldT n) (h : Heap) (L : List Tm) (d : Tm)
    (he : EntryHolds (reassign G η) r.inputs r.entrySeparation r.entryIndices (envOf L d) n W h)
    (hvalues : ∀ v ∈ L, isVal v = true) (hd : isVal d = true) :
    HeapObservations.SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) r.goal (r.goal.argument (envOf L d)))
      (fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
      (fun h' => r.onThrow = true → r.footprint.Holds h h') n W h (gotoOf r.program r.start L d) := by
  cases hb : mainBound r with
  | some x =>
    have hx : x = (r.footprint, r.fresh, r.onThrow) := by
      unfold mainBound at hb; split at hb
      · injection hb with hb; exact hb.symm
      · cases hb
    subst hx
    exact g.bounded _ _ _ hb _ _ (program_nodes r.program) η trivial n W h L d he hvalues hd
  | none =>
    have hcond : ¬ ((!(r.footprint == .top && !r.onThrow && !r.fresh) &&
        !(!r.fresh && r.program.all fun n => Purity.pureTerm n.expression)) = true) := by
      intro hc; unfold mainBound at hb; rw [if_pos hc] at hb; cases hb
    have htop : (r.footprint == .top && !r.onThrow && !r.fresh) = false := by
      rcases heffect with hf | ho | hf
      · simp [beq_iff_eq, hf]
      · simp [ho]
      · simp [hf]
    rw [htop] at hcond
    have hpure : (!r.fresh && r.program.all fun n => Purity.pureTerm n.expression) = true := by
      cases hq : (!r.fresh && r.program.all fun n => Purity.pureTerm n.expression)
      · rw [hq] at hcond; exact absurd rfl hcond
      · rfl
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpure
    obtain ⟨hfresh, hall⟩ := hpure
    have hp : ∀ e ∈ r.program.map (·.expression), Purity.pureTerm e = true := by
      intro e he
      obtain ⟨node, hn, rfl⟩ := List.mem_map.mp he
      exact List.all_eq_true.mp hall node hn
    have hs := guarantee_goto g trivial he
    exact HeapObservations.SafePostExc.weaken
      (fun _ _ h => ⟨Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _)
        ((CallEffects.Effect.post_ofFootprint _ .undef [] _ _ _).mp h), fun hf => by rw [hfresh] at hf; cases hf⟩)
      (fun _ h _ => Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _) h)
      (CallEffects.pure_safe_exc (r := .undef) (args := []) (.goto hp hvalues hd) hs)

/-- **A request's footprint from the regional fallback** (proved): a run
within the claimed footprint off no region is within it everywhere. -/
theorem footprint_of_fallback {G : NormalGraph ι} {r : SourceRequest σ ι} {bound}
    (g : GraphGuarantee G (fun _ => True) r.program r.start r.goal r.inputs r.entrySeparation r.entryIndices
      r.assertions bound r.ensures (some (r.footprint, [], r.onThrow)))
    (hfr : r.fresh = false)
    (η : MixedAssignment ι) (n : Nat) (W : WorldT n) (h : Heap) (L : List Tm) (d : Tm)
    (he : EntryHolds (reassign G η) r.inputs r.entrySeparation r.entryIndices (envOf L d) n W h) :
    HeapObservations.SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) r.goal (r.goal.argument (envOf L d)))
      (fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
      (fun h' => r.onThrow = true → r.footprint.Holds h h') n W h (gotoOf r.program r.start L d) :=
  HeapObservations.SafePostExc.weaken
    (fun _ _ hq => ⟨Footprints.ArgumentStoreRegionsWithin.nil_holds hq, fun hf => by rw [hfr] at hf; cases hf⟩)
    (fun _ hq ho => Footprints.ArgumentStoreRegionsWithin.nil_holds (hq ho))
    (g.regionally _ _ _ rfl _ _ (program_nodes r.program) η trivial n W h L d he)

end

end Verification.SourceClaimJson.PassUnit
