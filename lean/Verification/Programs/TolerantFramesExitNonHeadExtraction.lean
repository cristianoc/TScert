import Verification.Programs.TolerantFramesExitsYield
import Verification.Programs.TolerantFramesExitYieldCache

/-! # Non-head checks extracted from successful normal exits -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Local
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- The pair inserted by `pushExit` is present whenever both arrays contain
its target index. -/
theorem pushExit_incoming_mem (env : WalkEnv ι G I) (l : Nat) (t : Target) (target : SinglePass.State)
    (carried : List (PromiseCalls.Implication ι)) (Γe : Thunk (List (Ty ι))) (names : List Nat)
    (pushed vacuous : Bool) (a : ExitsDone ι G)
    (hs : t.label < a.incoming.size) (hi : t.label < a.incomingImpl.size) :
    (target, carried) ∈
      (((pushExit env l t target carried Γe names pushed vacuous a).incoming[t.label]?).getD []).zip
      (((pushExit env l t target carried Γe names pushed vacuous a).incomingImpl[t.label]?).getD []) := by
  obtain ⟨h1, h2, _⟩ := pushExit_fields env l t target carried Γe names pushed vacuous a
  rw [h1, h2]
  simp [Array.getElem?_modify, Array.getElem?_eq_getElem hs, Array.getElem?_eq_getElem hi]

/-- The merge record contains the implications returned by `edgeTransfer`. -/
theorem pushExit_merge_mem (env : WalkEnv ι G I) (l : Nat) (t : Target) (target : SinglePass.State)
    (carried : List (PromiseCalls.Implication ι)) (Γe : Thunk (List (Ty ι))) (names : List Nat)
    (pushed vacuous : Bool) (a : ExitsDone ι G)
    (hs : t.label < a.incomingEdges.size) (hm : env.merging[t.label]! = true) :
    (Γe.get, atSlotsOf names carried, t.mapping) ∈
      ((pushExit env l t target carried Γe names pushed vacuous a).incomingEdges[t.label]?).getD [] := by
  simp [pushExit, hm, atSlotsOf, slotsOfNames, Array.getElem?_modify, Array.getElem?_eq_getElem hs]

/-- A successful normal non-head exit exposes its checked type and assertion,
and the precise incoming pair and merge record it inserts. -/
theorem exitStep_nonHead_checked {env : WalkEnv ι G I} {l i : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ysA : List (PromiseCalls.Yield ι)} {a b : ExitsDone ι G} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    (h : exitStep G I env l en sd (yieldsAtSlots en.entry.names ysA)
      (Thunk.mk fun _ => outAllOf G env.claimed[l]! sd.st.stepOut) a
      (Exit.normal t pushed observed promote, i) = .ok b)
    (hh : env.isHead[t.label]! = false)
    (hs : t.label < b.incoming.size) (hi : t.label < b.incomingImpl.size)
    (he : t.label < b.incomingEdges.size) :
    let c := env.claimed[l]!
    let node := env.nodes[l]!
    let ysE := b.yields.getD []
    let Γr := refinedContext G c node.continuation (yieldsAtSlots en.entry.names ysA)
      (outAllOf G c sd.st.stepOut) (i == 0)
    let carried := en.implies ++ freshImplOf pushed false ysE en.entry.names sd.st.result
    let transfer := edgeTransfer (normalNames en.entry sd.st pushed) t.mapping pushed false sd.outFresh
      en.entry sd.st.result (exitStore G c en.entry sd.st pushed observed promote) carried
    ∃ tc, env.claimed[t.label]? = some tc ∧
      (vacuousOf G en.here c.type (exitCtx c pushed) pushed observed = false →
        ExitTyped G I (exitCtx c pushed) tc.context t observed
          (exitSearchFacts G c en.entry sd.st pushed observed promote tc.context t.mapping)
          (refinedContext G c node.continuation (yieldsAtSlots en.entry.names ysE)
            (outAllOf G c sd.st.stepOut) (i == 0)) (outAllOf G c sd.st.stepOut)) ∧
      (vacuousOf G en.here c.type (exitCtx c pushed) pushed observed = false →
        ∀ req, env.stated[t.label]! = some req →
          KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context)
            (assertionSource G Γr req (exitAssertFacts G c en.entry sd.st pushed observed promote req t.mapping)
              t.mapping observed) req t.mapping = true) ∧
      transfer ∈ ((b.incoming[t.label]?).getD []).zip ((b.incomingImpl[t.label]?).getD []) ∧
      (env.merging[t.label]! = true →
        (Γr, atSlotsOf (normalNames en.entry sd.st pushed) transfer.2, t.mapping) ∈
          (b.incomingEdges[t.label]?).getD []) := by
  unfold exitStep at h
  extract_lets ex first node c width entry st target pushed' observed' handler pushedNames tr a0 Γ names store unsatΓ vacuous Γe read Γr at h
  split at h
  · cases h
  rename_i tc htc
  split at h
  · cases h
  extract_lets diff u a2 typed at h
  generalize ht : typed = T at h
  split at h
  · cases h
  rename_i a1 et
  simp only [typed] at ht
  extract_lets freshImpl record at h
  have hh' : env.isHead[target.label]! = false := hh
  rw [hh'] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  rename_i a3 ha
  let pair := edgeTransfer names target.mapping pushed' handler sd.outFresh entry st.result store
    (en.implies ++ freshImpl)
  cases h
  have hy := assertionExit_yields ha
  have hv : vacuous = vacuousOf G en.here c.type (exitCtx c pushed) pushed observed := rfl
  have htype : vacuous = false →
      ExitTyped G I (exitCtx c pushed) tc.context t observed
        (exitSearchFacts G c en.entry sd.st pushed observed promote tc.context t.mapping)
        (refinedContext G c node.continuation (yieldsAtSlots en.entry.names (a1.yields.getD []))
          (outAllOf G c sd.st.stepOut) (i == 0)) (outAllOf G c sd.st.stepOut) := by
    intro hvf
    rw [hvf] at ht
    simp only [Bool.false_eq_true, ↓reduceIte] at ht
    have hd : diff = differing Γ tc.context t.mapping := by simp only [diff, hvf, Bool.false_eq_true, ↓reduceIte, timedKind]; rfl
    rw [hd] at ht
    obtain ⟨ys, _, hys, hc⟩ := exitTypes_checked ht
    rw [hys] at hc
    exact hc
  refine ⟨tc, htc, ?_, ?_, ?_, ?_⟩
  · intro hvf
    simpa only [pushExit, hy] using htype (hv.trans hvf)
  · intro hvf req hr
    have haf := ha
    rw [hv.trans hvf] at haf
    exact assertionExit_checked haf hr
  · have hm := pushExit_incoming_mem env l target pair.1 pair.2 Γe names pushed' vacuous a3
      (by simpa only [pushExit, Array.size_modify, target, ex, Exit.target] using hs)
      (by simpa only [pushExit, Array.size_modify, target, ex, Exit.target] using hi)
    simp only [pushExit, hy, pair, target, ex, Exit.target, names, handler, Exit.isHandler,
      pushed', Exit.pushed, pushedNames, entry, st, store, Γ, c, width, observed', Exit.observed,
      Exit.promote, freshImpl, freshImplOf, normalNames, exitStore, exitCtx, Prod.eta, Bool.false_eq_true, ↓reduceIte] at hm ⊢
    exact hm
  · intro hm
    have hsize : target.label < a3.incomingEdges.size := by
      simpa only [pushExit, target, ex, Exit.target, hm, ↓reduceIte, Array.size_modify] using he
    have hmem := pushExit_merge_mem env l target pair.1 pair.2 Γe names pushed' vacuous a3 hsize hm
    simp only [pushExit, hy, pair, target, ex, Exit.target, names, handler, Exit.isHandler,
      pushed', Exit.pushed, pushedNames, entry, st, store, Γ, c, width, observed', Exit.observed,
      Exit.promote, freshImpl, freshImplOf, normalNames, exitStore, exitCtx, Γe, node, first, Thunk.get, Bool.false_eq_true, ↓reduceIte] at hmem ⊢
    exact hmem

/-- Each indexed computation has the fold's original allocation and extends
into its final arrays. -/
theorem exitsFold_indexed_arrays {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (Exit × Nat)) (a b : ExitsDone ι G),
      es.foldlM (exitStep G I env l en sd ys out) a = .ok b →
      a.incoming.size = a.incomingImpl.size → ∀ e ∈ es, ∃ a' b',
        exitStep G I env l en sd ys out a' e = .ok b' ∧
        WalkExtends (exitsWalk b') (exitsWalk b) ∧
        b'.incoming.size = a.incoming.size ∧ b'.incomingImpl.size = a.incomingImpl.size ∧
          b'.incomingEdges.size = a.incomingEdges.size ∧
        ExitYieldSource env l en sd a.yields (b'.yields.getD [])
  | [], _, _, _, _, _, he => by cases he
  | e :: es, a, b, h, hs, e', he => by
    rw [List.foldlM_cons] at h
    cases ha : exitStep G I env l en sd ys out a e with
    | error stop => rw [ha] at h; cases h
    | ok a' =>
      rw [ha] at h
      obtain ⟨h1, h2, h3⟩ := exitStep_arraySizes ha
      have hs' : a'.incoming.size = a'.incomingImpl.size := by rw [h1, h2, hs]
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨a, a', ha, exitsFold_extends h hs', h1, h2, h3, exitStep_yields_source ha⟩
      · obtain ⟨a'', b', hb, hx, hs1, hs2, hs3, hsrc⟩ := exitsFold_indexed_arrays es a' b h hs' e' he
        exact ⟨a'', b', hb, hx, hs1.trans h1, hs2.trans h2, hs3.trans h3, (exitStep_yields_source ha).trans hsrc⟩

/-- Every exit of a successful visit has the visit's incoming allocation. -/
theorem visitExits_indexed_arrays {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G}
    (h : visitExits G I env σ l en sd = .ok ex)
    (hs : σ.walk.incoming.size = σ.walk.incomingImpl.size) :
    ∀ e ∈ (Exit.ofNode env.nodes[l]!).zipIdx, ∃ a b,
      exitStep G I env l en sd
        (yieldsAtSlots en.entry.names ((exitsYields G I env l en sd).1.getD []))
        (Thunk.mk fun _ => outAllOf G env.claimed[l]! sd.st.stepOut) a e = .ok b ∧
      WalkExtends (exitsWalk b) (exitsWalk ex) ∧
      b.incoming.size = σ.walk.incoming.size ∧ b.incomingImpl.size = σ.walk.incomingImpl.size ∧
        b.incomingEdges.size = σ.walk.incomingEdges.size ∧
      ExitYieldSource env l en sd sd.yields (b.yields.getD []) := by
  unfold visitExits at h
  extract_lets node c at h
  split at h
  rename_i ys answers heq
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · intro e he
    obtain ⟨a, b, hb, hx, h1, h2, h3, hsrc⟩ := exitsFold_indexed_arrays _ _ _ h hs e he
    refine ⟨a, b, ?_, hx, h1, h2, h3, ?_⟩
    · rw [heq]
      exact hb
    · apply (exitsYields_source env l en sd).trans
      rw [heq]
      exact hsrc

end Local

namespace ExitChecks
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}
    {c : Target.RunCall G I} {r : RunWalkA G I c} {l : Nat} {hl : r.w.visited l}

/-- The execution trace retains the incoming arrays' setup allocation. -/
theorem Site.arrayAllocation (s : Site c r l hl) :
    s.σ.walk.incoming.size = s.env.claimed.size ∧
      s.σ.walk.incomingEdges.size = s.env.claimed.size := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, he, _⟩ := s.facts
  exact ⟨hs, he⟩

/-- The site's merge flags agree with the checked walk's incoming count. -/
theorem Site.mergingOfIncoming (s : Site c r l hl) (checked : WalkChecked c r) :
    ∀ t, r.given t = false → 2 ≤ (r.w.incoming t).length → s.env.merging[t]! = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := s.facts
  rw [hm]
  exact checked.mergingOfIncoming

/-- Non-head extraction from the execution trace. The checked walk and trace supply
allocation, head agreement and merge flags. Cached yield judgments are
an explicit premise. -/
theorem exitChecks_nonHead (s : Site c r l hl) (η : MixedAssignment ι)
    (checked : WalkChecked c r)
    (exitCachesJudged : ∀ ysE, ExitYieldSource s.env l s.en s.sd s.sd.yields ysE →
      ExitYieldsJudged (reassign G η) r.w (List.range c.inputs.length) l
        (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st ysE) : NonHead s η := by
  obtain ⟨hw, hedges, _, hclaims, _, _, hheads, hstated, _, _, hex,
    hnode, hclaim, hentry, hst, _, _, himplies, hsizes, hext, _, _, _, contextAgreement, _⟩ := s.facts
  have arrayAllocation := s.arrayAllocation
  have givenAgreement : r.given = passHeads c := checked.givenAgreement
  intro i t pushed observed promote hi hg
  have indexed : (Exit.normal t pushed observed promote, i) ∈
      (Exit.ofNode s.env.nodes[l]!).zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simpa only [hnode] using hi
  obtain ⟨a, b, hb, hx, hb1, hb2, hb3, hsource⟩ := visitExits_indexed_arrays hex hsizes _ indexed
  have headFlag : s.env.isHead[t.label]! = false := by
    rw [givenAgreement] at hg
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    exact (hheads t.label).trans hg
  have targetBound : t.label < s.env.claimed.size := (exitStep_effect hb).claimed
  have stateBound : t.label < b.incoming.size := by rw [hb1, arrayAllocation.1]; exact targetBound
  have implicationBound : t.label < b.incomingImpl.size := by
    rw [hb2, ← hsizes, arrayAllocation.1]; exact targetBound
  have mergeBound : t.label < b.incomingEdges.size := by rw [hb3, arrayAllocation.2]; exact targetBound
  obtain ⟨tc, htc, ht, ha, hp, hm⟩ := exitStep_nonHead_checked hb headFlag stateBound implicationBound mergeBound
  have targetContext : r.ctx t.label = tc.context := by
    rw [hclaims] at htc
    simp only [List.getElem?_toArray] at htc
    simp only [contextAgreement, passCtx, htc, Option.map_some, Option.getD_some]
  have assertedTable : ∀ req, r.stated t.label = some req → s.env.stated[t.label]! = some req := by
    intro req hr
    rw [hstated, passStated, ← r.stated_eq]
    exact hr
  have extension : WalkExtends (exitsWalk b) s.raw := hx.trans hext
  have typed : vacuousOf G s.en.here (r.node l hl).c.type
      (exitCtx (r.node l hl).c pushed) pushed observed = false →
      ExitTyped G I (exitCtx (r.node l hl).c pushed) (r.ctx t.label) t observed
        (exitSearchFacts G (r.node l hl).c (r.node l hl).entry (r.node l hl).st pushed observed promote
          (r.ctx t.label) t.mapping)
        (refinedContext G (r.node l hl).c (r.node l hl).node.continuation
          (yieldsAtSlots (r.node l hl).entry.names (b.yields.getD []))
          (outAllOf G (r.node l hl).c (r.node l hl).st.stepOut) (i == 0))
        (outAllOf G (r.node l hl).c (r.node l hl).st.stepOut) := by
    simpa only [hclaim, hentry, hst, hnode, targetContext] using ht
  have asserted : vacuousOf G s.en.here (r.node l hl).c.type
      (exitCtx (r.node l hl).c pushed) pushed observed = false → ∀ req, r.stated t.label = some req →
      KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (r.ctx t.label))
        (assertionSource G (refinedContext G (r.node l hl).c (r.node l hl).node.continuation
          (yieldsAtSlots (r.node l hl).entry.names s.ysA)
          (outAllOf G (r.node l hl).c (r.node l hl).st.stepOut) (i == 0)) req
          (exitAssertFacts G (r.node l hl).c (r.node l hl).entry (r.node l hl).st pushed observed promote req t.mapping)
          t.mapping observed) req t.mapping = true := by
    intro hv req hr
    simp only [hclaim, hentry, hst, hnode, targetContext]
    exact ha (by simpa only [hclaim] using hv) req (assertedTable req hr)
  have pushedIn : IncomingRecorded r.w t.label
      (edgeTransfer (normalNames (r.node l hl).entry (r.node l hl).st pushed) t.mapping pushed false s.sd.outFresh
        (r.node l hl).entry (r.node l hl).st.result
        (exitStore G (r.node l hl).c (r.node l hl).entry (r.node l hl).st pushed observed promote)
        (r.w.implies l ++ freshImplOf pushed false (b.yields.getD []) (r.node l hl).entry.names
          (r.node l hl).st.result)) := by
    refine ⟨exitsWalk b, s.raw, passHeads c, hw, ?_, extension, ?_⟩
    · rw [← givenAgreement]; exact hg
    · simpa only [exitsWalk, hclaim, hentry, hst, ← himplies] using hp
  have merged : 2 ≤ (r.w.incoming t.label).length →
      MergeRecorded r.edgesIn t.label
        (refinedContext G (r.node l hl).c (r.node l hl).node.continuation
          (yieldsAtSlots (r.node l hl).entry.names s.ysA)
          (outAllOf G (r.node l hl).c (r.node l hl).st.stepOut) (i == 0),
          atSlotsOf (normalNames (r.node l hl).entry (r.node l hl).st pushed)
            (edgeTransfer (normalNames (r.node l hl).entry (r.node l hl).st pushed) t.mapping pushed false s.sd.outFresh
              (r.node l hl).entry (r.node l hl).st.result
              (exitStore G (r.node l hl).c (r.node l hl).entry (r.node l hl).st pushed observed promote)
              (r.w.implies l ++ freshImplOf pushed false (b.yields.getD []) (r.node l hl).entry.names
                (r.node l hl).st.result)).2, t.mapping) := by
    intro htwo
    have hmem := hm (s.mergingOfIncoming checked t.label hg htwo)
    refine ⟨exitsWalk b, s.raw, hedges, extension, ?_⟩
    simpa only [exitsWalk, hclaim, hentry, hst, hnode, ← himplies, Site.ysA] using hmem
  exact ⟨b.yields.getD [], exitCachesJudged _ hsource,
    (NonHeadExitChecked.mk typed asserted pushedIn merged).reassign η⟩

end ExitChecks
end Verification.TolerantFrames
