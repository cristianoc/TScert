import Verification.Source.Claims.PassUnitMemberRun

/-! # The single pass's unit theorem: an accepted member is safe

`member_safe`: a member `passGroup` accepts (`MemberAccepted`) is safe
(`MemberSafe`), under `RunSound` and `RunKeepsSummaries`, its plans over the
file's frozen store. Then the headline
(`passUnit_safe`) from mode 8's exact acceptance condition. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore
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
entry conditions, guarantees
the request's graph at its bound, postcondition and regional option. -/
theorem main_guarantee {G : NormalGraph ι} {I : InstanceImageCheck G} {r : SourceRequest σ ι}
    (hrun : RunSound ι) {c : RunCall G I} {codes : CodeEntry ι → Bool} {checker : SinglePass.PassChecker G I}
    {a after : Answered G} {admits : MixedAssignment ι → Prop}
    (hm : MainCall r c codes checker a) (hscope : CheckerScope G I checker admits)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (hacc : c.Accepts after) (hsums : ProgramCertificates.SummariesSound G I after.summaries.toList)
    (hreg : ∀ Φ regions exc, regionOf c.regional = some (Φ, regions, exc) →
      GraphCode.ArgumentPathTracking.checkEntryFields G r.inputs regions = true) :
    GraphGuarantee G admits r.program r.start r.goal r.inputs r.entrySeparation r.entryIndices r.assertions
      c.bound r.ensures (regionOf c.regional) := by
  obtain ⟨hP, -, hst, hin, hgoal, has, hidx, hc, hchk, -, hens, hsep⟩ := hm
  have hg := hrun G I c after admits hacc (hchk ▸ hscope) (hc ▸ hcodes) hsums (hin ▸ hreg)
  rw [hP, hst, hin, hgoal, hsep, hidx, has, hens] at hg
  exact hg

omit [Labels ι] [StoreView σ ι] in
/-- An environment's roots of a frame are its values' and its default's. -/
theorem envOf_roots {n : Nat} {W : WorldT n} {L : List Tm} {d : Tm} (h : RootsOk W (envOf L d)) :
    (∀ v ∈ L, RefsOk W v) ∧ RefsOk W d := by
  refine ⟨fun v hv => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have := h i
    simpa [envOf, List.getD_eq_getElem?_getD, hi] using this
  · have := h L.length
    simpa [envOf] using this

omit [Labels ι] [StoreView σ ι] in
/-- **The term running a checked graph has valid references** where its
frame does: the graph's node expressions mention no location. -/
theorem gotoOf_refsOk {P : Program} {start : Nat} {n : Nat} {W : WorldT n} {L : List Tm} {d : Tm} {comp : ComponentTag}
    (hsrc : P.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (hρ : RootsOk W (envOf L d)) : RefsOk W (gotoOf P start L d comp) := by
  obtain ⟨hL, hd⟩ := envOf_roots hρ
  intro r hr
  simp only [gotoOf, refs, refsArgs_eq, List.mem_append, List.mem_flatMap, List.mem_map] at hr
  rcases hr with (⟨e, ⟨node, hn, rfl⟩, he⟩ | ⟨v, hv, hr⟩) | hr
  · exact program_source_refsOk hsrc W node hn r he
  · exact hL v hv r hr
  · exact hd r hr

omit [Labels ι] [StoreView σ ι] in
/-- A guarantee's safety, as the term running the graph. -/
theorem guarantee_goto {G : NormalGraph ι} {admits : MixedAssignment ι → Prop} {P : Program} {start : Nat}
    {goal : Goal ι} {inputs sep idx assertions bound ensures regional} {comp : ComponentTag}
    (g : GraphGuarantee G admits P start goal inputs sep idx assertions bound ensures regional)
    {η} (hη : admits η) {n W h L d}
    (he : EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h) (hroots : RootsOk W (envOf L d)) :
    Safe (excOf (reassign G η)) (GoalHolds (reassign G η) goal (goal.argument (envOf L d))) n W h
      (gotoOf P start L d comp) := by
  obtain ⟨hE, hρ⟩ := GraphCode.goto_refs (gotoOf_refsOk (start := start) (comp := comp) g.source hroots)
  have hs := g.safe η hη n W h (envOf L d) he (program_source_refsOk g.source W) hρ
  rw [← program_nodes P] at hs
  exact GraphCode.safe_of_sim n W h .goto hE hs

/-- **A request's footprint from its main run** (proved): a guarantee at
`mainBound` gives the claimed footprint, the bound's own clause where the
run had one, the purity of the graph otherwise. -/
theorem footprint_of_bound {G : NormalGraph ι} {r : SourceRequest σ ι} {regional}
    (g : GraphGuarantee G (fun _ => True) r.program r.start r.goal r.inputs r.entrySeparation r.entryIndices
      r.assertions (mainBound r) r.ensures regional)
    (heffect : r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true)
    (η : MixedAssignment ι) (n : Nat) (W : WorldT n) (h : Heap) (L : List Tm) (d : Tm)
    (he : EntryHolds (reassign G η) r.inputs r.entrySeparation r.entryIndices (envOf L d) n W h)
    (hroots : RootsOk W (envOf L d))
    (hvalues : ∀ v ∈ L, isVal v = true) (hd : isVal d = true) :
    HeapObservations.SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) r.goal (r.goal.argument (envOf L d)))
      (fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
      (fun h' => r.onThrow = true → r.footprint.Holds h h') n W h (gotoOf r.program r.start L d r.comp) := by
  cases hb : mainBound r with
  | some x =>
    have hx : x = RunBound.ofRequest r.footprint r.onThrow r.fresh := by
      unfold mainBound at hb; split at hb
      · injection hb with hb; exact hb.symm
      · cases hb
    subst hx
    -- A throw bounded by the request is within its footprint: by the
    -- exceptional bound where that is not `⊤`, by the heap's growth where
    -- it is.
    have hg := ProgramTyping.SafePostExc.grow (b := h.length) (Nat.le_refl _)
      (g.bounded _ _ _ hb _ _ (program_nodes r.program) η trivial n W h L d r.comp he (gotoOf_refsOk g.source hroots)
        hvalues hd)
    refine HeapObservations.SafePostExc.weaken (fun _ _ hq => hq.1) (fun h' hq ho => ?_) hg
    by_cases ht : r.footprint = .top
    · rw [ht]; exact Footprints.Closed.holds_top.mpr hq.2
    · have := hq.1
      simp only [ho, ite_true] at this
      exact this ht
  | none =>
    have hcond : ¬ ((!(r.footprint == .top && !r.onThrow && !r.fresh) &&
        !(!r.fresh && r.program.all fun n => Purity.pureTerm n.expression)) = true) := by
      intro hc; unfold mainBound at hb; rw [ite_eq_left hc] at hb; cases hb
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
    have hs := guarantee_goto (comp := r.comp) g trivial he hroots
    exact HeapObservations.SafePostExc.weaken
      (fun _ _ h => ⟨Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _)
        h, fun hf => by rw [hfresh] at hf; cases hf⟩)
      (fun _ h _ => Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _) h)
      (CallEffects.pure_safe_exc (.goto hp hvalues hd) hs)

/-- **A request's footprint from the regional fallback** (proved): a run
within the claimed footprint off no region is within it everywhere. -/
theorem footprint_of_fallback {G : NormalGraph ι} {r : SourceRequest σ ι} {bound}
    (g : GraphGuarantee G (fun _ => True) r.program r.start r.goal r.inputs r.entrySeparation r.entryIndices
      r.assertions bound r.ensures (some (r.footprint, [], r.onThrow)))
    (hfr : r.fresh = false)
    (η : MixedAssignment ι) (n : Nat) (W : WorldT n) (h : Heap) (L : List Tm) (d : Tm)
    (he : EntryHolds (reassign G η) r.inputs r.entrySeparation r.entryIndices (envOf L d) n W h)
    (hroots : RootsOk W (envOf L d)) :
    HeapObservations.SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) r.goal (r.goal.argument (envOf L d)))
      (fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
      (fun h' => r.onThrow = true → r.footprint.Holds h h') n W h (gotoOf r.program r.start L d r.comp) :=
  HeapObservations.SafePostExc.weaken
    (fun _ _ hq => ⟨Footprints.ArgumentSpineRegionsWithin.nil_holds hq, fun hf => by rw [hfr] at hf; cases hf⟩)
    (fun _ hq ho => Footprints.ArgumentSpineRegionsWithin.nil_holds (hq ho))
    (g.regionally _ _ _ rfl _ _ (program_nodes r.program) η trivial n W h L d r.comp he (gotoOf_refsOk g.source hroots))

end

/-! ## The main graph at framed returns, from the framed run -/

section Framed
variable {σ ι : Type} [Labels ι] [StoreView σ ι]
open HeapObservations

omit [Labels ι] [StoreView σ ι] in
/-- **A property of the heap kept along a run, at framed returns**: where
each step of terms meeting `P` from a heap meeting `Rel` reaches a heap
meeting `Rel` and a term meeting `P`, a run safe at framed returns from such
a term and heap meets `Rel` at its exits as well. -/
theorem safeRet_along {J : Heap → Tm → Prop} {Ξ T : Fam} {Q : WPost} {R : WExc} {F : Nat → Bool}
    {Ret RetE : Nat → Env → Heap → Heap → Prop} {P : Tm → Prop} {Rel : Heap → Prop}
    (hstep : ∀ {h t h' t'}, P t → Rel h → Step h t h' t' → Rel h' ∧ P t') :
    ∀ {n W p h t}, P t → Rel h → SafeRet J Ξ T Q R F Ret RetE n W p h t →
      SafeRet J Ξ T (fun k U h' v => Q k U h' v ∧ Rel h') (fun k U h' => R k U h' ∧ Rel h') F Ret RetE n W p h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ hs; exact hs
  | succ n ih =>
    intro W p h t hP hR hs
    obtain ⟨hrf, hJ, hs⟩ := hs
    refine ⟨hrf, hJ, ?_⟩
    rcases hs with (⟨hv, hT, hQ⟩ | ⟨hth, hRr⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, hT, hQ, hR⟩)
    · exact .inl (.inr ⟨hth, hRr, hR⟩)
    · obtain ⟨hR', hP'⟩ := hstep hP hR step
      exact .inr ⟨U, h', t', hx, hu, step, hh, fun hra => ih hP' hR' (hs hra)⟩

omit [Labels ι] [StoreView σ ι] in
/-- **Weaker exit posts, at framed returns.** -/
theorem safeRet_weaken {J : Heap → Tm → Prop} {Ξ T : Fam} {Q Q' : WPost} {R R' : WExc} {F : Nat → Bool}
    {Ret RetE : Nat → Env → Heap → Heap → Prop}
    (hq : ∀ k U h v, Q k U h v → Q' k U h v) (hr : ∀ k U h, R k U h → R' k U h) :
    ∀ {n W p h t}, SafeRet J Ξ T Q R F Ret RetE n W p h t → SafeRet J Ξ T Q' R' F Ret RetE n W p h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ hs; exact hs
  | succ n ih =>
    intro W p h t hs
    obtain ⟨hrf, hJ, hs⟩ := hs
    refine ⟨hrf, hJ, ?_⟩
    rcases hs with (⟨hv, hT, hQ⟩ | ⟨hth, hRr⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, hT, hq _ _ _ _ hQ⟩)
    · exact .inl (.inr ⟨hth, hr _ _ _ hRr⟩)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, fun hra => ih (hs hra)⟩

/-- **A request's footprint from its main run, at framed returns**
(`footprint_of_bound` at framed returns): at the request's bound, by the
bound and the heap's growth; with no bound, by the program's purity. -/
theorem framedFootprint_of_bound {G : NormalGraph ι} {r : SourceRequest σ ι} {regional}
    {F : Nat → Bool} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    (g : Verification.TolerantFrames.GraphGuaranteeR G (fun _ => True) r.program r.start r.goal r.inputs
      r.entrySeparation r.entryIndices r.assertions (mainBound r) r.ensures regional F Ret RetE)
    (hsrc : r.program.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (heffect : r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true)
    (η : MixedAssignment ι) (n : Nat) (W : WorldT n) (h : Heap) (L : List Tm) (d : Tm)
    (he : EntryHolds (reassign G η) r.inputs r.entrySeparation r.entryIndices (envOf L d) n W h)
    (hroots : RootsOk W (envOf L d))
    (hvalues : ∀ v ∈ L, isVal v = true) (hd : isVal d = true) :
    SafeRet (fun _ _ => True) (excOf (reassign G η))
      (GoalHolds (reassign G η) r.goal (r.goal.argument (envOf L d)))
      (WPost.lift fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
      (WExc.lift fun h' => r.onThrow = true → r.footprint.Holds h h') F Ret RetE n W none h
      (gotoOf r.program r.start L d r.comp) := by
  cases hb : mainBound r with
  | some x =>
    have hx : x = RunBound.ofRequest r.footprint r.onThrow r.fresh := by
      unfold mainBound at hb; split at hb
      · injection hb with hb; exact hb.symm
      · cases hb
    subst hx
    have hg := safeRet_along (P := fun _ => True) (Rel := fun h' => h.length ≤ h'.length)
      (fun _ hr st => ⟨Nat.le_trans hr (Footprints.step_length_le st), trivial⟩) trivial (Nat.le_refl _)
      (g.bounded _ _ _ hb _ _ (program_nodes r.program) η trivial n W h L d r.comp he
        (gotoOf_refsOk hsrc hroots) hvalues hd)
    refine safeRet_weaken (fun _ _ _ _ hq => hq.1) (fun _ _ h' hq ho => ?_) hg
    by_cases ht : r.footprint = .top
    · rw [ht]; exact Footprints.Closed.holds_top.mpr hq.2
    · have := hq.1
      simp only [ho, ite_true] at this
      exact this ht
  | none =>
    have hcond : ¬ ((!(r.footprint == .top && !r.onThrow && !r.fresh) &&
        !(!r.fresh && r.program.all fun n => Purity.pureTerm n.expression)) = true) := by
      intro hc; unfold mainBound at hb; rw [ite_eq_left hc] at hb; cases hb
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
    have hs := safeRet_along (P := Purity.CollectingRun) (Rel := fun h' => h.IsPrefix h')
      (fun hP hr st => ⟨hr.trans (Purity.CollectingRun.step hP st).1, (Purity.CollectingRun.step hP st).2⟩)
      (.pure (.goto hp hvalues hd)) (List.prefix_refl _)
      (g.safe _ _ (program_nodes r.program) η trivial n W h L d r.comp he (gotoOf_refsOk hsrc hroots))
    exact safeRet_weaken
      (fun _ _ _ _ hq => ⟨Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _)
        (Footprints.Closed.holds_empty.mpr hq.2), fun hf => by rw [hfresh] at hf; cases hf⟩)
      (fun _ _ _ hq _ => Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _)
        (Footprints.Closed.holds_empty.mpr hq.2)) hs

/-- **The main graph's clauses at framed returns from the run's guarantee**
(proved): a guarantee at framed returns of the request's graph at its
bound and stated regions, its program mentioning no location, gives
`FramedReturnsGuarantee`: each clause read on the term that runs the
graph, the footprint by `framedFootprint_of_bound`. -/
theorem framedReturns_of_guaranteeR {r : SourceRequest σ ι} {F : Nat → Bool}
    {Ret RetE : Nat → Env → Heap → Heap → Prop}
    (hsrc : r.program.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (g : Verification.TolerantFrames.GraphGuaranteeR (RequestJson.graph r.toRequest) (fun _ => True) r.program
      r.start r.goal r.inputs r.entrySeparation r.entryIndices r.assertions (mainBound r) r.ensures
      (regionalSpec r) F Ret RetE) :
    FramedReturnsGuarantee r F Ret RetE := by
  refine ⟨fun η _ n W h L d hE hR => ?_, fun hb η n W h L d hE hR hL hd => ?_,
    fun hn η n W h L d hE hR => ?_, fun Φ regions hreg η n W h L d hE hR => ?_,
    fun η _ n W h L d hE hR => ?_⟩
  · exact g.safe _ _ (program_nodes r.program) η trivial n W h L d r.comp hE (gotoOf_refsOk hsrc hR)
  · exact framedFootprint_of_bound g hsrc hb η n W h L d hE hR hL hd
  · exact g.ensured hn _ _ (program_nodes r.program) η trivial n W h L d r.comp hE (gotoOf_refsOk hsrc hR)
  · exact g.regionally Φ regions _ (by simp [regionalSpec, hreg]) _ _ (program_nodes r.program) η trivial n W h L d
      r.comp hE (gotoOf_refsOk hsrc hR)
  · exact g.asserted _ _ (program_nodes r.program) η trivial n W h L d r.comp hE (gotoOf_refsOk hsrc hR)

/-- **The main graph at framed returns, from the framed run** (proved,
under `RunSoundFramed`; the draft, `FramedReturnsGuarantee` by
`RunSoundFramed`): a call of the pass over the request's own graph
(`MainCall`) at its bound and stated regions, accepted in the framed mode
at the framed nodes `F` keeping the supports `S`, its codes and the
summaries it leaves sound, its regions meeting their entry conditions,
meets `FramedReturnsGuarantee` at `F`, the returns `framedRet S` and every
throw's return premise. -/
theorem framedReturns_of_main {r : SourceRequest σ ι} {I : InstanceImageCheck (RequestJson.graph r.toRequest)}
    (hrun : Verification.TolerantFrames.RunSoundFramed ι) {c : RunCall (RequestJson.graph r.toRequest) I}
    {codes : CodeEntry ι → Bool} {a after : Answered (RequestJson.graph r.toRequest)} {F : Nat → Bool}
    {S : Nat → List Footprints.Footprint} (RetE : Nat → Env → Heap → Heap → Prop)
    (hm : MainCall r c codes .ordinary a) (hb : c.bound = mainBound r) (hreg : regionOf c.regional = regionalSpec r)
    (hregs : ∀ Φ regions, r.regional = some (Φ, regions) →
      GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions = true)
    (hcodes : ProgramCertificates.CodesSound (RequestJson.graph r.toRequest) codes)
    (hacc : c.AcceptsFramed after (fun _ => True) F S)
    (hsums : ProgramCertificates.SummariesSound (RequestJson.graph r.toRequest) I after.summaries.toList) :
    FramedReturnsGuarantee r F (Verification.TolerantFrames.framedRet S) RetE := by
  obtain ⟨hP, -, hst, hin, hgoal, has, hidx, hc, hchk, -, hens, hsep⟩ := hm
  have hfields : ∀ Φ regions exc, regionOf c.regional = some (Φ, regions, exc) →
      GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) c.inputs regions = true := by
    intro Φ regions exc h
    rw [hreg] at h
    simp only [regionalSpec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨Φ', regions'⟩, hr, rfl, rfl, -⟩ := h
    rw [hin]; exact hregs _ _ hr
  obtain ⟨hsrc, g⟩ := hrun _ I c after (fun _ => True) F S RetE hacc (hchk ▸ .ordinary) (hc ▸ hcodes) hsums hfields
  rw [hP, hst, hin, hgoal, hsep, hidx, has, hens, hb, hreg] at g
  rw [hP] at hsrc
  exact framedReturns_of_guaranteeR hsrc g

end Framed

end Verification.SourceClaimJson.PassUnit
