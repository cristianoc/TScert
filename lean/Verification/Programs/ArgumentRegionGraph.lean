import Verification.Programs.ArgumentRegionFresh

/-! Whole-graph composition of entry-relative store bounds. Ordinary graph
checking supplies progress and typing; regional node obligations supply effects
and result provenance. This module does not decode or check those obligations. -/
namespace Verification.GraphCode.ArgumentRegionGraph
open ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules Footprints
open PositiveCertificates (InstanceImageCheck)
open CertificateProducer (successors)
open ArgumentRegionFresh (FreshValue FreshHold FreshTables FreshWithin)

def NodeWithin [DecidableEq ι] (G : NormalGraph ι) (Φ : Footprints.Closed)
    (regions : List ArgumentStoreRegion) (c : NodeEvidence ι) (t : Tm)
    (facts : List ArgumentPathTracking.Fact) (F : List Nat) (origins : List ArgumentStoreRegion) (thr : Bool) :
    Prop :=
  ∀ n W h ρ initial entry,
    ArgumentStoreRegionsWithin Φ regions entry initial h → ArgumentPathTracking.Holds facts ρ entry initial →
    (∀ i ∈ F, FreshValue initial.length (ρ i)) →
    EnvOk G (ControlFlow.entry c) ρ n W → PromiseCalls.ImpliesOk G c.implies ρ n W →
    HeapKnowledge.Holds (entryFacts G c) ρ h → WorldAdm W → HeapOk n W h →
    (0 < n → ArgumentPathTracking.StableNow (ArgumentPathTracking.stableFields regions) entry initial W) →
    HeapObservations.SafePostExc (excOf G) (meaning G (result c))
      (fun h' v => ArgumentStoreRegionsWithin Φ regions entry initial h' ∧
        ∀ r ∈ origins, HeapKnowledge.readPath initial (entry r.position) r.path = some v)
      (fun h' => thr = true → ArgumentStoreRegionsWithin Φ regions entry initial h')
      n W h (instantiate 0 ρ t)

/-! ## The step-frame rule

Every step of a body has a local effect: a frame read at the step's own
positions in the heap it starts in, on normal return and on a throw. A node
is within the stated frame when its frame, rebased to the invocation's entry
through the tracked slots (`Footprints.rebase`), is included in the stated
frame (`Footprint.le`); `Post.compose_at` composes the two. It is one rule
for every step: a call at its signature's frame (`callStep`), an element
write (`writeStep`), a step within the closed bound (`closedStep`), each
only extracting the step's frame (FOOTPRINTS.md, "Argument-path store
regions"). -/

/-- A step's local effect: its frame on normal return and on a throw, read
at the step's positions, and the node slot each position holds. -/
structure StepEffect where
  slot : Nat → Option Nat
  normal : Footprint
  raised : Footprint

/-- A node's step meets its local effect: from a context ordinary graph
checking established, at positions agreeing with the slots `slot` names, its
normal return, and where `thr` its throw, meets the frame from the heap the
step starts in. -/
def StepOk [DecidableEq ι] (G : NormalGraph ι) (c : NodeEvidence ι) (t : Tm) (se : StepEffect) (thr : Bool) :
    Prop :=
  ∀ n W h ρ, EnvOk G (ControlFlow.entry c) ρ n W → PromiseCalls.ImpliesOk G c.implies ρ n W →
    HeapKnowledge.Holds (entryFacts G c) ρ h → WorldAdm W → HeapOk n W h →
    ∃ σ : Env, (∀ p s, se.slot p = some s → σ p = ρ s) ∧
      HeapObservations.SafePostExc (excOf G) (meaning G (result c))
        (fun h' _ => Post se.normal σ h h') (fun h' => thr = true → Post se.raised σ h h')
        n W h (instantiate 0 ρ t)

/-- The stated frame: the closed bound and the store regions' entries. -/
def statedFrame (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion) : Footprint :=
  Φ.fp ++ regions.map ArgumentStoreRegion.entry

/-- Where a step position's value comes from: the entry path a tracked fact
states of the slot it holds. -/
def nodeLink (facts : List ArgumentPathTracking.Fact) (se : StepEffect) (p : Nat) : Option (Nat × List String) :=
  (se.slot p).bind fun s => (facts.find? (·.slot == s)).map fun f => (f.region.position, f.region.path)

/-- A step position's one-field path read at the entry heap as at the
step's: its value an entry value, and the field one the stated frame
traverses, whose entry witness `StableNow` keeps. -/
def nodeAgree (regions : List ArgumentStoreRegion) (facts : List ArgumentPathTracking.Fact) (se : StepEffect)
    (p : Nat) (q : List String) : Bool :=
  match nodeLink facts se p, q with
  | some (x, []), [f] => (ArgumentPathTracking.stableFields regions).contains (x, f)
  | _, _ => false

/-- A step position holding a node slot whose value is fresh. -/
def nodeFresh (F : List Nat) (se : StepEffect) (p : Nat) : Bool :=
  match se.slot p with
  | some s => F.contains s
  | none => false

def nodeRebase (regions : List ArgumentStoreRegion) (facts : List ArgumentPathTracking.Fact) (F : List Nat)
    (se : StepEffect) : RebaseEvidence :=
  ⟨nodeLink facts se, nodeAgree regions facts se, nodeFresh F se⟩

/-- No class evidence: inclusions read regions alone. -/
def noClasses : ClassEvidence := fun _ _ => none

theorem noClasses_ok (ρ : Env) (h : Heap) : ClassOk noClasses ρ h := fun _ _ _ _ hc => nomatch hc

/-- **The common check**: the step's frames, rebased to the entry, are
included in the stated frame. -/
def stepWithin (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (facts : List ArgumentPathTracking.Fact) (F : List Nat) (se : StepEffect) (thr : Bool) : Bool :=
  Footprint.le noClasses (statedFrame Φ regions ++ rebaseAll (nodeRebase regions facts F se) se.normal)
      (statedFrame Φ regions) &&
    (!thr || Footprint.le noClasses (statedFrame Φ regions ++ rebaseAll (nodeRebase regions facts F se) se.raised)
      (statedFrame Φ regions))

/-- The tracked facts and the entry world's witnesses are rebasing evidence. -/
theorem nodeRebase_ok {regions : List ArgumentStoreRegion} {facts : List ArgumentPathTracking.Fact}
    {F : List Nat} {se : StepEffect} {σ ρ entry : Env} {initial h : Heap} {n : Nat} {W : WorldT n}
    (hσ : ∀ p s, se.slot p = some s → σ p = ρ s) (hf : ArgumentPathTracking.Holds facts ρ entry initial)
    (hF : ∀ i ∈ F, FreshValue initial.length (ρ i))
    (hst : ArgumentPathTracking.StableNow (ArgumentPathTracking.stableFields regions) entry initial W)
    (hn : 0 < n) (hh : HeapOk n W h) :
    RebaseOk (nodeRebase regions facts F se) σ entry initial h := by
  have hlink : ∀ p x q, nodeLink facts se p = some (x, q) →
      HeapKnowledge.readPath initial (entry x) q = some (σ p) := by
    intro p x q hl
    simp only [nodeLink, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hl
    obtain ⟨s, hs, f, hfind, hfq⟩ := hl
    simp only [Prod.mk.injEq] at hfq
    obtain ⟨rfl, rfl⟩ := hfq
    have hslot : f.slot = s := by simpa using List.find?_some hfind
    rw [hσ p s hs, ← hslot]
    exact hf f (List.mem_of_find?_eq_some hfind)
  refine ⟨hlink, fun p q hq v hv => ?_, fun p hp => ?_⟩
  · simp only [nodeRebase] at hq
    unfold nodeAgree at hq
    split at hq
    · rename_i x f hl
      have he : entry x = σ p := by simpa [HeapKnowledge.readPath] using hlink p x [] hl
      rw [← he] at hv ⊢
      exact hst.agree (List.contains_iff_mem.mp hq) hn hh hv
    · cases hq
  · simp only [nodeRebase, nodeFresh] at hp
    split at hp
    · rename_i s hs
      rw [hσ p s hs]
      exact (hF s (List.contains_iff_mem.mp hp)).2
    · cases hp

/-- **The step-frame rule.** A step meeting its local effect, whose frames
the common check includes in the stated frame, keeps the invocation within
it. -/
theorem nodeWithin_of_step [DecidableEq ι] {G : NormalGraph ι} {Φ : Footprints.Closed}
    {regions : List ArgumentStoreRegion} {c : NodeEvidence ι} {t : Tm}
    {facts : List ArgumentPathTracking.Fact} {F : List Nat} {se : StepEffect} {thr : Bool}
    (hs : StepOk G c t se thr) (hc : stepWithin Φ regions facts F se thr = true) :
    NodeWithin G Φ regions c t facts F [] thr := by
  intro n W h ρ initial entry hb hf hF he hi hk hw hh hst
  cases n with
  | zero => trivial
  | succ n =>
    simp only [stepWithin, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨σ, hσ, hrun⟩ := hs (n + 1) W h ρ he hi hk hw hh
    have hp := ArgumentStoreRegionsWithin.iff_post.mp hb
    have hok := nodeRebase_ok (regions := regions) hσ hf hF (hst (Nat.succ_pos n)) (Nat.succ_pos n) hh
    apply HeapObservations.SafePostExc.weaken _ _ hrun
    · intro h' _ hq
      exact ⟨ArgumentStoreRegionsWithin.iff_post.mpr
        (Post.compose_at hp hq hok hc.1 (noClasses_ok _ _)), fun r hr => nomatch hr⟩
    · intro h' hq hthr
      have hle : Footprint.le noClasses (statedFrame Φ regions ++
          rebaseAll (nodeRebase regions facts F se) se.raised) (statedFrame Φ regions) = true := by
        rcases hc.2 with hf | hle
        · rw [hthr] at hf; cases hf
        · exact hle
      exact ArgumentStoreRegionsWithin.iff_post.mpr (Post.compose_at hp (hq hthr) hok hle (noClasses_ok _ _))

/-- What the bounded run reads of each node: its regional obligation, its
freshness obligation, and the transfer of its provenance and fresh facts
along its normal edges and its handler. -/
def NodesWithin [DecidableEq ι] (G : NormalGraph ι) (Φ : Footprints.Closed)
    (regions : List ArgumentStoreRegion) (P : Program) (C : Certificate ι)
    (table : List (List ArgumentPathTracking.Fact)) (ft : FreshTables) (exc : Bool) : Prop :=
  ∀ l node c, P[l]? = some node → C[l]? = some c →
    ∃ origins outF outC,
      NodeWithin G Φ regions c node.expression (ArgumentPathTracking.atLabel table l) (factsAt ft.values l) origins
        (node.handler.isSome || exc) ∧
      ArgumentPathTracking.checkEdges table (ArgumentPathTracking.atLabel table l) origins node.continuation = true ∧
      ArgumentPathTracking.checkHandler table (ArgumentPathTracking.atLabel table l) node.handler = true ∧
      FreshWithin G c node.expression (factsAt ft.values l) (factsAt ft.cells l) outF outC node.handler.isSome ∧
      edgesFresh ft.values (factsAt ft.values l) outF false node.continuation = true ∧
      edgesFresh ft.cells (factsAt ft.cells l) outC false node.continuation = true ∧
      ∀ target, node.handler = some target →
        handlerFresh ft.values (factsAt ft.values l) target = true ∧
        handlerFresh ft.cells (factsAt ft.cells l) target = true

/-- A label's facts: provenance, and fresh values and cells against the
invocation's entry heap. -/
def LabelHolds (table : List (List ArgumentPathTracking.Fact)) (ft : FreshTables) (l : Nat)
    (ρ entry : Env) (initial h : Heap) : Prop :=
  ArgumentPathTracking.Holds (ArgumentPathTracking.atLabel table l) ρ entry initial ∧
    FreshHold (factsAt ft.values l) (factsAt ft.cells l) initial.length ρ h

def BoundState (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (ft : FreshTables) (exc : Bool) (initial : Heap) (entry : Env)
    (n : Nat) (h : Heap) : State → Prop
  | .at l ρ => ArgumentStoreRegionsWithin Φ regions entry initial h ∧ LabelHolds table ft l ρ entry initial h
  | .done _ => ArgumentStoreRegionsWithin Φ regions entry initial h
  | .eval t ρ k handler =>
      ReturnsPost (fun h' v => ArgumentStoreRegionsWithin Φ regions entry initial h' ∧
        ∀ target ∈ successors k, LabelHolds table ft target.label
          (mapEnv target.mapping (if pushes k then push v ρ else ρ)) entry initial h') n h t ∧
      match handler with
      | none => exc = true → RaisesPost (ArgumentStoreRegionsWithin Φ regions entry initial) n h t
      | some target => RaisesPost (fun h' => ArgumentStoreRegionsWithin Φ regions entry initial h' ∧
            ∀ v, FreshHold (factsAt ft.values target.label) (factsAt ft.cells target.label) initial.length
              (mapEnv target.mapping (push v ρ)) h') n h t ∧
          ∀ v, ArgumentPathTracking.Holds (ArgumentPathTracking.atLabel table target.label)
            (mapEnv target.mapping (push v ρ)) entry initial
  | .raised _ => exc = true → ArgumentStoreRegionsWithin Φ regions entry initial h

theorem bounded_step [DecidableEq ι] {G : NormalGraph ι} {Φ : Footprints.Closed}
    {regions : List ArgumentStoreRegion} {Rty : Goal ι} {v0 : Tm} {P : Program}
    {C : Certificate ι} {table : List (List ArgumentPathTracking.Fact)} {ft : FreshTables} {exc : Bool}
    (hnodes : NodesWithin G Φ regions P C table ft exc)
    {initial entry n W h s h' s'} (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hst : 0 < n + 1 → ArgumentPathTracking.StableNow (ArgumentPathTracking.stableFields regions) entry initial W)
    (hs : StateOk G Rty C v0 (n+1) W h s)
    (hp : BoundState Φ regions table ft exc initial entry (n+1) h s)
    (st : Transition P h s h' s') :
    BoundState Φ regions table ft exc initial entry n h' s' := by
  cases st with
  | @enter l node _ ρ hn =>
    obtain ⟨c, hc, he, hi, -, hf⟩ := hs
    obtain ⟨origins, outF, outC, ht, hedge, hhandler, hfr, hef, hec, hhf⟩ := hnodes l node c hn hc
    have he' := he.transfer n (Nat.le_succ n) _ (WExt_refl _)
    have hi' := hi.transfer n (Nat.le_succ n) _ (WExt_refl _)
    have hk := entryFacts_holds he hf
    have hh' := HeapOk_trunc n W h hh
    have hrun := ht n _ h ρ initial entry hp.1 hp.2.1 hp.2.2.values he' hi' hk
      (WorldAdm_trunc _ hw) hh'
      (fun _ => (hst (Nat.succ_pos n)).transfer (Nat.le_succ n) (WExt_refl _))
    have hfresh := hfr n _ h ρ initial.length (ArgumentStoreRegionsWithin.iff_post.mp hp.1).1 hp.2.2 he' hi' hk
      (WorldAdm_trunc _ hw) hh'
    have hboth := HeapObservations.SafePostExc.cross_upto n (fun _ _ _ _ _ _ _ _ hu _ => hu) _ _ h _ hh' hh'
      hrun hfresh
    refine ⟨returnsPost_of_safePost (HeapObservations.weaken
      (fun _ _ post => ⟨post.1.1, fun target htarget =>
        ⟨ArgumentPathTracking.checkEdges_sound hedge hp.2.1 post.1.2 target htarget,
          ⟨edgesFresh_holds hef hp.2.2.values post.2.1 target htarget,
            edgesFresh_holds hec post.2.2.2 post.2.2.1 target htarget⟩⟩⟩) hboth.post), ?_⟩
    cases hk : node.handler with
    | none =>
      intro hexc k h'' t'' v hb run hr
      exact (raisesPost_of_safePostExc hboth k h'' t'' v hb run hr).1 (by simp [hk, hexc])
    | some target =>
      refine ⟨?_, ArgumentPathTracking.checkHandler_sound hhandler hp.2.1 target hk⟩
      intro k h'' t'' v hb run hr
      have hr' := raisesPost_of_safePostExc hboth k h'' t'' v hb run hr
      have hcells := hr'.2 (by simp [hk])
      obtain ⟨hhv, hhc⟩ := hhf target hk
      exact ⟨hr'.1 (by simp [hk]), fun u => ⟨handlerFresh_holds hhv hp.2.2.values u,
        handlerFresh_holds hhc hcells u⟩⟩
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
  | handle hr =>
    have hq := hp.2.1.raised hr
    exact ⟨hq.1, hp.2.2 _, hq.2 _⟩
  | raise hr => exact fun he => (hp.2 he).raised hr

theorem bounded_safe_of_sim [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion} {Rty : Goal ι} {v0 : Tm} {E : List Tm} {K : List (Continuation × Option Target)}
    {C : Certificate ι} {table : List (List ArgumentPathTracking.Fact)} {ft : FreshTables} {exc : Bool}
    {codes : CodeEntry ι → Bool} (hg : checkGraphUsing (sums := sums) G images Rty (program E K) C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (hnodes : NodesWithin G Φ regions (program E K) C table ft exc) (hv0 : isVal v0 = true) :
    ∀ n W h ts s initial entry, Sim E K ts s → WorldAdm W → HeapOk n W h →
      (0 < n → ArgumentPathTracking.StableNow (ArgumentPathTracking.stableFields regions) entry initial W) →
      StateOk G Rty C v0 n W h s → BoundState Φ regions table ft exc initial entry n h s →
      HeapObservations.SafePostExc (excOf G) (GoalHolds G Rty v0)
        (fun h' _ => ArgumentStoreRegionsWithin Φ regions entry initial h')
        (fun h' => exc = true → ArgumentStoreRegionsWithin Φ regions entry initial h') n W h ts := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ts s initial entry sim hw hh hst hs hp
    rcases state_progress hg hcodes hsums hv0 hw hh hs with
      (⟨v, rfl, hv, ht⟩ | ⟨v, rfl, hsc⟩) | ⟨U, h', s', hx, hu, st, hok, hs'⟩
    · cases sim; exact .inl (.inl ⟨hv, ht, hp⟩)
    · cases sim with
      | raised hv hj => exact .inl (.inr ⟨⟨v, .throwV hv hj, hsc⟩, hp⟩)
    · obtain ⟨ts', step, sim'⟩ := sim_step sim st
      exact .inr ⟨U, h', ts', hx, hu, step, hok,
        ih U h' ts' s' initial entry sim' hu hok
          (fun _ => (hst (Nat.succ_pos n)).transfer (Nat.le_succ n) hx) hs'
          (bounded_step hnodes hw hh hst hs hp st)⟩

theorem goto_bounded [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion} {Rty : Goal ι} {E : List Tm} {K : List (Continuation × Option Target)}
    {C : Certificate ι} {start inputs} {table : List (List ArgumentPathTracking.Fact)} {exc : Bool}
    {codes : CodeEntry ι → Bool} {entrySeparation : HeapSeparation.Separation}
    {entryIndices : List HeapKnowledge.IndexAtom}
    (hc : checkEntryUsing (sums := sums) (entrySeparation := entrySeparation) (entryIndices := entryIndices)
      G images Rty (program E K) C start inputs codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (hnodes : NodesWithin G Φ regions (program E K) C table ft exc)
    (hstart : ArgumentPathTracking.checkEntry (ArgumentPathTracking.atLabel table start) = true)
    (hfresh : ((factsAt ft.values start).isEmpty && (factsAt ft.cells start).isEmpty) = true)
    (hfields : ArgumentPathTracking.checkEntryFields G inputs regions = true)
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
      (fun hn => ArgumentPathTracking.checkEntryFields_sound hfields (by simpa only [hin] using he) hn hh)
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
    · simp only [Bool.and_eq_true, List.isEmpty_iff] at hfresh
      refine ⟨(Footprints.Closed.Holds.refl Φ h).on _,
        ArgumentPathTracking.checkEntry_sound hstart _ _, ?_, ?_⟩
      · intro i hi; rw [hfresh.1] at hi; cases hi
      · intro i hi; rw [hfresh.2] at hi; cases hi
  · contradiction

end Verification.GraphCode.ArgumentRegionGraph
