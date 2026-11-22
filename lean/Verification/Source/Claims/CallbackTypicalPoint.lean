import Verification.Source.Claims.CallbackProducerReturns

namespace Verification.SourceClaimJson.CallbackInferencePlan
open ControlFlow TolerantFrames ProgramTyping GraphCode PositiveGraphs PositiveRules
open HeapObservations TolerantFrames.Target TolerantFrames.ReadOnly

/-- At every reached goto, the producer's ordinary checked context types its slots
in a positive world for this very heap. -/
def GotoContext {ι : Type} (G : NormalGraph ι) (ctx : Nat → List (Ty ι))
    (E : List Tm) (K : List (Continuation × Option ControlFlow.Target)) (h : Heap) (t : Tm) : Prop :=
  ∀ l L d cmp, t = .goto E K l L d cmp →
    ∃ s : IndexedHeap, s.h = h ∧ EnvOk G (ctx l) (envOf L d) s.n s.W

theorem passWalk_gotoContext {ι : Type} [DecidableEq ι] [Hashable ι]
    {G : NormalGraph ι} {E K start goal inputs sep idx asserts bound post regional F Ret RetE w ctx stated}
    (hp : PassWalkSoundR G (program E K) start goal inputs sep idx asserts bound post regional F Ret RetE w ctx stated)
    {n} {W : WorldT n} {h L d cmp} (entry : TolerantFrames.Target.EntryHolds G inputs sep idx (envOf L d) n W h)
    (refs : RefsOk W (.goto E K start L d cmp)) :
    SafeRet (GotoContext G ctx E K) (excOf G) (GoalHolds G goal (goal.argument (envOf L d)))
      (fun _ _ _ _ => True) (fun _ _ _ => True) F Ret RetE n W none h (.goto E K start L d cmp) := by
  obtain ⟨hv, hs, hi, ha, ho⟩ := entry
  have hn := nodesChecked_of_walkR (hp.walk ⟨envOf L d,h⟩ 0) (regionFields regional) h
  refine keeps_postExcR hn passPreU_adminClosed hn.keepsTrue (fun _ _ _ h => h) ?_ n W none h _ _
    .goto ha ho (goto_refs refs).1 (goto_refs refs).2
    (fun hq ha' ho' => hp.start (s := ⟨n,W,h,hq,ha',ho'⟩) hv hs hi (by simp)) trivial
  intro s p ts st sim invariant l L' d' cmp' eq
  subst ts
  cases sim with
  | goto => exact ⟨s,rfl,(invariant s.pos s.adm s.ok).1.1.1.2⟩
  | done hv => simp [isVal] at hv

open CallbackOrigins CallbackEffectInference SinglePass Footprints CertificateProducer PositiveCertificates ProgramCertificates HeapExpressionRules LabelStore

theorem accepted_pointWalk {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}
    {c : TolerantFrames.Target.RunCall G I} {after : Answered G} {admits F S RetE}
    (accepted : c.AcceptsFramed after admits F S) (hscope : CheckerScope G I c.passChecker admits)
    (hcodes : CodesSound G c.codes) (hsums : SummariesSound G I after.summaries.toList)
    (reg : c.regional = none) {η} (hη : admits η) :
    ∃ w stated, PassWalkSoundR (reassign G η) c.P c.start c.goal c.inputs c.entrySeparation c.entryIndices
      c.assertions c.bound c.ensures (regionOf c.regional) F (framedRet S) RetE w (passCtx c) stated := by
  obtain ⟨hacc,hdeliv⟩ := accepted
  have hp : RunPremises G I c after admits := ⟨hacc,hscope,hcodes,hsums,by simp [reg,regionOf]⟩
  have hv := visitsRecord_of (ι := ι) (visitsRest_of (exitsPushOk_of exitsWidth)
    (visitsSettle_of (visitStepPrefix_of_exitStep exitStepPrefix)) visitsImplications) visitExits_answers_prefix
  obtain ⟨r,hchk⟩ := run_traversedC (recordsSound_of setupRecords_of hv) (recordsChecked_of setupRecords_of hv)
    G I c after hacc hsums
  obtain ⟨dead,hd,hgiven,hmerging,hrecord⟩ := hchk
  have hfields := hp.2.2.2.2
  have hnear : LinearNearFuelEq := linearNearFuelEq
  obtain ⟨pc', hpc⟩ := scope_reassign hscope hη
  refine ⟨r.w, r.stated, r.ctx_eq ▸ (show PassWalkSoundR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r.ctx r.stated from
    { walk := fun ε m => ?_
      entered := r.start.entered η
      stable := fun Φ regions exc hr ρ s he =>
        GraphCode.ArgumentPathTracking.checkEntryFields_sound
          ((checkEntryFields_reassign G η c.inputs regions).trans (hfields Φ regions exc hr)) he s.pos s.ok
      footprint := fun Φ Ψ fr hbd => ⟨dead, fun ε h₀ =>
        (footprintKept_of_walk hp (fun l hl => (hd l hl).1) hη hbd ε h₀).toRF F (framedRet S) RetE⟩
      returns := fun hne ε m =>
        (returnsEnsured_of_walk hp (fun l hl => (hd l hl).1) hη hne ε m).toRF F (framedRet S) RetE
      regions := fun Φ regions exc hr => by
        simp [reg,regionOf] at hr
      labelled := assertionsLabelled_of_checked labelsChecked G I c after admits hp r })⟩
  exact nodesChecked_of_walkJR (r.traversed.reassign η)
    (stepEdgesSound_of_yieldsR
      (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl),
        hdeliv hp r ⟨dead, hd, hgiven, hmerging, hrecord⟩ η hη ε m l hl⟩)
      (codesSound_reassign hcodes η))
    (headsEntered_of_recorded r.heads) hnear

theorem AcceptedProducer.safeWithContext {I : ∀ n, WorldT n → Prop} {f i fuel params out} (a : AcceptedProducer f i fuel params out)
    (over : PassUnit.OverStore f) {L d h n} {W : WorldT n} {η}
    (entry : TolerantFrames.Target.EntryHolds (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η)
      a.request.inputs a.request.entrySeparation a.request.entryIndices (envOf L d) n W h)
    (roots : RootsOk W (envOf L d)) (vals : ∀ i, isVal (envOf L d i) = true)
    (initial : I n W)
    (persist : ∀ {k} {U : WorldT (k+1)} {V : WorldT k}, I (k+1) U → WExt (trunc k (Nat.le_succ _) U) V → I k V)
    (supplied : SuppliedDemandsAt (fun label ρ hp => ∃ s : IndexedHeap, s.h = hp ∧
        EnvOk (reassign (StoreView.graph f.F.store) η)
          (((a.request.claims[label]?).map (·.context)).getD []) ρ s.n s.W) I a.request.program a.origins
      (certifiedPrivate a.request.program.toArray a.origins (privateAllocations a.request.program a.origins))
      params out a.request.start (envOf L d) h) :
    SafePostExcW (PositiveRules.excOf (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η))
      (ControlFlow.GoalHolds (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η) a.request.goal
        (a.request.goal.argument (envOf L d))) (fun _ _ _ _ => True) (fun _ _ _ => True) n W h
      (PassUnit.gotoOf a.request.program a.request.start L d a.request.comp) := by
  have store := over.graph a.plan
  have codes := inferCodes_table_sound a.checkedCodes
  have sums := checkReadSummaries_sound (Bool.and_eq_true_iff.mp a.summaries).2
  change CodesSound (StoreView.graph a.request.types) _ at codes
  rw [store] at codes
  change SummariesSound (StoreView.graph a.request.types) (StoreView.images a.request.types) _ at sums
  rw [store] at sums
  have accepted := acceptsFramed_of_acceptedWalk (admits := fun _ => True) a.replayed
  obtain ⟨w,stated,hp⟩ := accepted_pointWalk (RetE := fun _ _ _ _ => True) accepted .ordinary codes sums rfl (η := η) trivial
  have source := (a.framedGuarantee over).1
  obtain ⟨name,pos,request,plan,ordinary,sync,reg,cs,known,before,checked,origins,names,nodes,rfl,rows,rfl,after,replayed,hs⟩ := a
  have nodeEq := SourceElaboration.program_nodes request.program
  have runPoint {P : Program} {goal inp sep idx asserts bound post regional F Ret RetE w ctx st}
      (hp' : PassWalkSoundR (reassign (StoreView.graph f.F.store) η) P request.start goal inp sep idx asserts bound post regional F Ret RetE w ctx st)
      {E K} (eq : program E K = P) := fun he refs => passWalk_gotoContext (eq.symm ▸ hp')
        (n := n) (W := W) (h := h) (L := L) (d := d) (cmp := request.comp) he refs
  have safe := runPoint hp nodeEq entry (PassUnit.gotoOf_refsOk (start := request.start) (comp := request.comp) source roots)
  apply safe_of_normalReturnsAt (Point := fun label ρ hp => ∃ s : IndexedHeap, s.h = hp ∧ EnvOk (reassign (StoreView.graph f.F.store) η) (((request.claims[label]?).map (·.context)).getD []) ρ s.n s.W) (table := origins) initial persist (fun h l L d c checked => checked l L d c rfl) _ vals entry.2.2.2.1 entry.2.2.2.2 safe
  rw [nodeEq]
  exact rows_normalReturnsAt (I := I) (Point := fun label ρ hp => ∃ s : IndexedHeap, s.h = hp ∧ EnvOk (reassign (StoreView.graph f.F.store) η) (((request.claims[label]?).map (·.context)).getD []) ρ s.n s.W) (h₀ := h) rows names source (fun i _ => vals i) supplied

end Verification.SourceClaimJson.CallbackInferencePlan
