import Verification.Programs.ArgumentPathTracking

/-! Whole-graph composition of entry-relative store bounds. Ordinary graph
checking supplies progress and typing; regional node obligations supply effects
and result provenance. This module does not decode or check those obligations. -/
namespace Verification.GraphCode.ArgumentRegionGraph
open ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules Footprints
open PositiveCertificates (InstanceImageCheck)
open CertificateProducer (successors)

def NodeWithin [DecidableEq ι] (G : NormalGraph ι) (Φ : Footprints.Closed)
    (regions : List ArgumentStoreRegion) (c : NodeEvidence ι) (t : Tm)
    (facts : List ArgumentPathTracking.Fact) (origin : Option ArgumentStoreRegion) (thr : Bool) : Prop :=
  ∀ n W h ρ initial entry,
    ArgumentStoreRegionsWithin Φ regions entry initial h → ArgumentPathTracking.Holds facts ρ entry initial →
    EnvOk G (ControlFlow.entry c) ρ n W → PromiseCalls.ImpliesOk G c.implies ρ n W →
    HeapKnowledge.Holds (entryFacts G c) ρ h → WorldAdm W → HeapOk n W h →
    HeapObservations.SafePostExc (excOf G) (meaning G (result c))
      (fun h' v => ArgumentStoreRegionsWithin Φ regions entry initial h' ∧
        ∀ r, origin = some r → HeapKnowledge.readPath initial (entry r.position) r.path = some v)
      (fun h' => thr = true → ArgumentStoreRegionsWithin Φ regions entry initial h')
      n W h (instantiate 0 ρ t)

/-- Existing checked closed-bound nodes also meet an entry-relative bound.
The empty fresh-slot set introduces no assumptions about caller values. -/
theorem nodeWithin_of_closed [DecidableEq ι] {G : NormalGraph ι} {Φ : Footprints.Closed}
    {regions : List ArgumentStoreRegion} {c : NodeEvidence ι} {t : Tm}
    {facts : List ArgumentPathTracking.Fact} {out thr : Bool}
    (hc : GraphCode.NodeWithin G Φ c t [] out thr) :
    NodeWithin G Φ regions c t facts none thr := by
  intro n W h ρ initial entry hb _ he hi hk hw hh
  have hn := hc n W h ρ initial.length hb.1 (by intro i hi; cases hi) he hi hk hw hh
  apply HeapObservations.SafePostExc.weaken _ _ hn
  · intro h' v hp
    exact ⟨hb.trans_on (hp.1.weaken (fun _ hl => hl.1)), by intros r hr; cases hr⟩
  · intro h' hp ht
    exact hb.trans_on ((hp ht).weaken (fun _ hl => hl.1))

/-- A selected receiver-store invocation names a tracked entry region.
The existing expression checker supplies the call's safety and effect. -/
@[nospecialize] def checkReceiverCall [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (facts : List ArgumentPathTracking.Fact) (c : NodeEvidence ι) (thr : Bool) : Bool :=
  (ProgramCertificates.checkTreeUsing G images c.expression (sums := sums) ||
    PromiseCalls.requiresTree G images (entryFacts G c) (fun _ => false) sums c.expression) &&
  ExpressionEffects.selectedOperands c.expression && (!thr || ExpressionEffects.selectedThrows c.expression) &&
  match (ProgramCertificates.claim c.expression).term, ExpressionEffects.selectedEffect c.expression with
  | .invoke _ (.var receiver) _, some eff =>
      eff.footprint.le Φ && eff.receiverStore && !eff.receiverOwn && (!thr || eff.onThrow) &&
        ArgumentPathTracking.checkReceiver facts regions receiver
  | _, _ => false

theorem checkReceiverCall_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion}
    {facts : List ArgumentPathTracking.Fact} {c : NodeEvidence ι} {thr : Bool}
    (hc : checkReceiverCall G images sums Φ regions facts c thr = true)
    (hsums : ProgramCertificates.SummariesSound G images sums) :
    NodeWithin G Φ regions c (ProgramCertificates.claim c.expression).term facts none thr := by
  intro n W h ρ initial entry hb hf he _ hk hw hh
  simp only [checkReceiverCall, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨htree, hops⟩, hthrows⟩, hc⟩ := hc
  split at hc
  · rename_i fn receiver args eff hterm heff
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at hc
    obtain ⟨⟨⟨⟨hle, hstore⟩, hown⟩, hthrow⟩, hreceiver⟩ := hc
    have hs : HeapObservations.SafePostExc (excOf G)
        (meaning G (ProgramCertificates.claim c.expression).type)
        (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term))
          (ExpressionEffects.actualsOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term)) h)
        (fun h' => thr = true → eff.excPost
          (ExpressionEffects.receiverOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term)) h h')
        n W h (instantiate 0 ρ (ProgramCertificates.claim c.expression).term) := by
      rcases Bool.or_eq_true_iff.mp htree with htree | hreq
      · cases ht : thr
        · apply HeapObservations.SafePostExc.of_post (fun _ hf => by cases hf)
          exact ExpressionEffects.selected_sound c.expression htree hops heff
            (ProgramCertificates.codesSound_none _) hsums he hw hh
        · have hx : ExpressionEffects.selectedThrows c.expression = true := by
            simpa [ht] using hthrows
          exact HeapObservations.SafePostExc.weaken (fun _ _ h => h) (fun _ h _ => h)
            (ExpressionEffects.selected_sound_exc c.expression htree hops hx heff
              (ProgramCertificates.codesSound_none _) hsums he hw hh)
      · obtain ⟨eff', heff', hs⟩ := PromiseCalls.requiresTree_sound_exc
          (ProgramCertificates.codesSound_none _) hsums c.expression hreq
        rw [heff] at heff'; cases heff'
        exact HeapObservations.SafePostExc.weaken (fun _ _ h => h) (fun _ h _ => h)
          (hs he hk hw hh)
    have hr : ExpressionEffects.receiverOf
        (instantiate 0 ρ (ProgramCertificates.claim c.expression).term) = ρ receiver := by
      rw [hterm]; simp [ExpressionEffects.receiverOf, instantiate]
    apply HeapObservations.SafePostExc.weaken _ _ hs
    · intro h' v hp
      refine ⟨?_, by intros r hr; cases hr⟩
      have hi := hp.1
      rw [hr] at hi
      exact ArgumentPathTracking.checkReceiver_sound hreceiver hf hb hi hstore hown hle
    · intro h' hp hthr
      have hon : eff.onThrow = true := by
        rcases hthrow with ht | ht
        · rw [hthr] at ht; cases ht
        · exact ht
      have hi := hp hthr hon
      rw [hr] at hi
      exact ArgumentPathTracking.checkReceiver_sound hreceiver hf hb hi hstore hown hle
  · cases hc

def NodesWithin [DecidableEq ι] (G : NormalGraph ι) (Φ : Footprints.Closed)
    (regions : List ArgumentStoreRegion) (P : Program) (C : Certificate ι)
    (table : List (List ArgumentPathTracking.Fact)) (exc : Bool) : Prop :=
  ∀ l node c, P[l]? = some node → C[l]? = some c →
    ∃ origin, NodeWithin G Φ regions c node.expression (ArgumentPathTracking.atLabel table l) origin
        (node.handler.isSome || exc) ∧
      ArgumentPathTracking.checkEdges table (ArgumentPathTracking.atLabel table l) origin node.continuation = true ∧
      ArgumentPathTracking.checkHandler table (ArgumentPathTracking.atLabel table l) node.handler = true

def BoundState (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (exc : Bool) (initial : Heap) (entry : Env)
    (n : Nat) (h : Heap) : State → Prop
  | .at l ρ => ArgumentStoreRegionsWithin Φ regions entry initial h ∧
      ArgumentPathTracking.Holds (ArgumentPathTracking.atLabel table l) ρ entry initial
  | .done _ => ArgumentStoreRegionsWithin Φ regions entry initial h
  | .eval t ρ k handler =>
      ReturnsPost (fun h' v => ArgumentStoreRegionsWithin Φ regions entry initial h' ∧
        ∀ target ∈ successors k, ArgumentPathTracking.Holds (ArgumentPathTracking.atLabel table target.label)
          (mapEnv target.mapping (if pushes k then push v ρ else ρ)) entry initial) n h t ∧
      match handler with
      | none => exc = true → RaisesPost (ArgumentStoreRegionsWithin Φ regions entry initial) n h t
      | some target => RaisesPost (ArgumentStoreRegionsWithin Φ regions entry initial) n h t ∧
          ∀ v, ArgumentPathTracking.Holds (ArgumentPathTracking.atLabel table target.label)
            (mapEnv target.mapping (push v ρ)) entry initial
  | .raised _ => exc = true → ArgumentStoreRegionsWithin Φ regions entry initial h

theorem bounded_step [DecidableEq ι] {G : NormalGraph ι} {Φ : Footprints.Closed}
    {regions : List ArgumentStoreRegion} {Rty : Goal ι} {v0 : Tm} {P : Program}
    {C : Certificate ι} {table : List (List ArgumentPathTracking.Fact)} {exc : Bool}
    (hnodes : NodesWithin G Φ regions P C table exc)
    {initial entry n W h s h' s'} (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hs : StateOk G Rty C v0 (n+1) W h s)
    (hp : BoundState Φ regions table exc initial entry (n+1) h s)
    (st : Transition P h s h' s') :
    BoundState Φ regions table exc initial entry n h' s' := by
  cases st with
  | @enter l node _ ρ hn =>
    obtain ⟨c, hc, he, hi, -, hf⟩ := hs
    obtain ⟨origin, ht, hedge, hhandler⟩ := hnodes l node c hn hc
    have hrun := ht n _ h ρ initial entry hp.1 hp.2
      (he.transfer n (Nat.le_succ n) _ (WExt_refl _))
      (hi.transfer n (Nat.le_succ n) _ (WExt_refl _)) (entryFacts_holds he hf)
      (WorldAdm_trunc _ hw) (HeapOk_trunc n W h hh)
    refine ⟨returnsPost_of_safePost (HeapObservations.weaken
      (fun _ _ post => ⟨post.1, ArgumentPathTracking.checkEdges_sound hedge hp.2 post.2⟩) hrun.post), ?_⟩
    cases hk : node.handler with
    | none =>
      intro hexc k h'' t'' v hb run hr
      exact raisesPost_of_safePostExc hrun k h'' t'' v hb run hr (by simp [hk, hexc])
    | some target =>
      refine ⟨?_, ArgumentPathTracking.checkHandler_sound hhandler hp.2 target hk⟩
      intro k h'' t'' v hb run hr
      exact raisesPost_of_safePostExc hrun k h'' t'' v hb run hr (by simp [hk])
  | @expr _ t _ t' ρ k handler st =>
    refine ⟨hp.1.step st, ?_⟩
    cases handler with
    | none => exact fun he => (hp.2 he).step st
    | some l => exact ⟨hp.2.1.step st, hp.2.2⟩
  | ret hv => exact (hp.1.value hv).1
  | bind hv =>
    have post := hp.1.value hv
    exact ⟨post.1, by simpa [pushes] using post.2 _ (by simp [successors])⟩
  | effect hv =>
    have post := hp.1.value hv
    exact ⟨post.1, by simpa [pushes] using post.2 _ (by simp [successors])⟩
  | yes =>
    have post := hp.1.value rfl
    exact ⟨post.1, by simpa [pushes] using post.2 _ (by simp [successors])⟩
  | no =>
    have post := hp.1.value rfl
    exact ⟨post.1, by simpa [pushes] using post.2 _ (by simp [successors])⟩
  | yesBind =>
    have post := hp.1.value rfl
    exact ⟨post.1, by simpa [pushes] using post.2 _ (by simp [successors])⟩
  | noBind =>
    have post := hp.1.value rfl
    exact ⟨post.1, by simpa [pushes] using post.2 _ (by simp [successors])⟩
  | tagBind hv =>
    have post := hp.1.value hv
    refine ⟨post.1, ?_⟩
    split
    · exact by simpa [pushes] using post.2 _ (by simp [successors])
    · exact by simpa [pushes] using post.2 _ (by simp [successors])
  | handle hr => exact ⟨hp.2.1.raised hr, hp.2.2 _⟩
  | raise hr => exact fun he => (hp.2 he).raised hr

theorem bounded_safe_of_sim [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion} {Rty : Goal ι} {v0 : Tm} {E : List Tm} {K : List (Continuation × Option Target)}
    {C : Certificate ι} {table : List (List ArgumentPathTracking.Fact)} {exc : Bool}
    {codes : CodeEntry ι → Bool} (hg : checkGraphUsing (sums := sums) G images Rty (program E K) C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (hnodes : NodesWithin G Φ regions (program E K) C table exc) (hv0 : isVal v0 = true) :
    ∀ n W h ts s initial entry, Sim E K ts s → WorldAdm W → HeapOk n W h →
      StateOk G Rty C v0 n W h s → BoundState Φ regions table exc initial entry n h s →
      HeapObservations.SafePostExc (excOf G) (GoalHolds G Rty v0)
        (fun h' _ => ArgumentStoreRegionsWithin Φ regions entry initial h')
        (fun h' => exc = true → ArgumentStoreRegionsWithin Φ regions entry initial h') n W h ts := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ts s initial entry sim hw hh hs hp
    rcases state_progress hg hcodes hsums hv0 hw hh hs with
      (⟨v, rfl, hv, ht⟩ | ⟨v, rfl, hsc⟩) | ⟨U, h', s', hx, hu, st, hok, hs'⟩
    · cases sim; exact .inl (.inl ⟨hv, ht, hp⟩)
    · cases sim with
      | raised hv hj => exact .inl (.inr ⟨⟨v, .throwV hv hj, hsc⟩, hp⟩)
    · obtain ⟨ts', step, sim'⟩ := sim_step sim st
      exact .inr ⟨U, h', ts', hx, hu, step, hok,
        ih U h' ts' s' initial entry sim' hu hok hs'
          (bounded_step hnodes hw hh hs hp st)⟩

theorem goto_bounded [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion} {Rty : Goal ι} {E : List Tm} {K : List (Continuation × Option Target)}
    {C : Certificate ι} {start inputs} {table : List (List ArgumentPathTracking.Fact)} {exc : Bool}
    {codes : CodeEntry ι → Bool} {entrySeparation : HeapSeparation.Separation}
    {entryIndices : List HeapKnowledge.IndexAtom}
    (hc : checkEntryUsing (sums := sums) (entrySeparation := entrySeparation) (entryIndices := entryIndices)
      G images Rty (program E K) C start inputs codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (hnodes : NodesWithin G Φ regions (program E K) C table exc)
    (hstart : ArgumentPathTracking.checkEntry (ArgumentPathTracking.atLabel table start) = true)
    (n W h L d) (he : EnvOk G inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W h)
    (hsep : HeapSeparation.Holds entrySeparation (envOf L d) := by exact HeapSeparation.empty_holds _)
    (hidx : HeapKnowledge.IndexHolds entryIndices (envOf L d) h := by exact HeapKnowledge.indexHolds_nil _ _) :
    HeapObservations.SafePostExc (excOf G) (GoalHolds G Rty (Rty.argument (envOf L d)))
      (fun h' _ => ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      (fun h' => exc = true → ArgumentStoreRegionsWithin Φ regions (envOf L d) h h') n W h (.goto E K start L d) := by
  simp only [checkEntryUsing_eq, Bool.and_eq_true] at hc
  have hx := hc.2
  split at hx
  · rename_i c hstart'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨⟨hin, himp, harg⟩, hk⟩, hslot⟩ := hx
    -- The promised argument, where the goal states one, is an input's value.
    have hv0 : isVal (Rty.argument (envOf L d)) = true := by
      unfold Goal.argument
      cases hs : Rty.slot with
      | none => rfl
      | some s =>
        rw [hs] at hslot
        have hlt : s < inputs.length := by simpa using hslot
        exact (meaning_value (he.2 s inputs[s] (List.getElem?_eq_getElem hlt))).1
    apply bounded_safe_of_sim hc.1 hcodes hsums hnodes hv0 n W h _ _ h (envOf L d) .goto hw hh
    · refine ⟨c, hstart', ?_, ?_, ?_, ?_⟩
      · simpa only [hin] using he
      · rw [himp]; exact PromiseCalls.ImpliesOk.nil G _ n W
      · intro p hp
        rw [harg] at hp
        unfold Goal.argument
        cases hs : Rty.slot with
        | none => rw [hs] at hp; cases hp
        | some s =>
          rw [hs] at hp
          cases List.mem_singleton.mp hp
          rfl
      · exact entryKnows_sound hk (by simpa only [hin] using he) hsep hidx
    · exact ⟨(Footprints.Closed.Holds.refl Φ h).on _,
        ArgumentPathTracking.checkEntry_sound hstart _ _⟩
  · contradiction

end Verification.GraphCode.ArgumentRegionGraph
