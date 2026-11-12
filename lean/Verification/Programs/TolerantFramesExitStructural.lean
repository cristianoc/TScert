import Verification.Programs.TolerantFramesExitHeadExtraction
import Verification.Programs.TolerantFramesExitNonHeadExtraction
import Verification.Programs.TolerantFramesDriverEntry
import Verification.Programs.TolerantFramesDriverSetup
import Verification.Programs.TolerantFramesExitStart

/-! # Structural facts for head and handler exit extraction -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Structural
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- A handler pushes the transferred pair and records its transferred
implications at source slots when the target is marked as a merge. -/
theorem exitStep_handler_arrays {env : WalkEnv ι G I} {l i : Nat} {en : Entered ι}
    {sd : StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    {a b : ExitsDone ι G} {t : Target}
    (h : exitStep G I env l en sd ys out a (.handler t, i) = .ok b)
    (hh : env.isHead[t.label]! = false) :
    let pair := edgeTransfer (sd.thrown :: en.entry.names) t.mapping true true sd.outFresh en.entry sd.st.result
      (handlerStore G env.claimed[l]! (sd.thrownTy.getD []) en.entry sd.st sd.thrown) en.implies
    b.incoming = a.incoming.modify t.label (pair.1 :: ·) ∧
    b.incomingImpl = a.incomingImpl.modify t.label (pair.2 :: ·) ∧
    b.incomingEdges = if env.merging[t.label]! then a.incomingEdges.modify t.label
      ((handlerCtx env.claimed[l]! (sd.thrownTy.getD []), atSlotsOf (sd.thrown :: en.entry.names) pair.2, t.mapping) :: ·)
      else a.incomingEdges := by
  unfold exitStep at h
  extract_lets ex first node c width entry st target push obs handler pushedNames tr a0 Γ names store unsatΓ vacuous Γe read Γr at h
  split at h
  · cases h
  split at h
  · cases h
  extract_lets diff u a2 typed at h
  generalize ht : typed = T at h
  split at h
  · cases h
  rename_i a1 et
  simp only [typed] at ht
  have hp : SameCore a a2 ∧ a2.edges = a.edges :=
    sameCore_unsat (sameCore_trace _ _ _) _ _
  have hp1 : SameCore a a1 := by
    split at ht
    · cases ht; exact hp.1
    · exact hp.1.trans (exitTypes_core ht).1
  extract_lets freshImpl record at h
  have hh' : env.isHead[target.label]! = false := hh
  simp only [hh', Bool.false_eq_true, if_false] at h
  split at h
  · cases h
  rename_i a3 ha
  have hp3 := hp1.trans (assertionExit_core ha).1
  cases h
  dsimp only [pushExit]
  rw [hp3.incoming, hp3.incomingImpl, hp3.incomingEdges]
  simp only [freshImpl, handler, ex, Exit.isHandler, Bool.or_true, if_true, List.append_nil]
  exact ⟨rfl, rfl, rfl⟩

/-- The entry and implications of a head with a non-initial entry. -/
theorem visitEntry_head_pair {env : WalkEnv ι G I} {σ : WalkState ι G} {t : Nat}
    {en : Entered ι} {req : HeapKnowledge.Knowledge}
    (h : visitEntry G I env σ t = .ok en) (hh : env.isHead[t]! = true)
    (hg : env.given[t]! = some req) (initial : (t == env.start && !env.startEntered) = false) :
    (en.entry, en.implies) =
      ((headEntry req false (env.claimed[t]!).context.length σ.fresh env.startNames env.argName
        ((env.givenArgs[t]?).getD []) ((env.givenInputs[t]?).getD []) ((env.givenImplies[t]?).getD [])).1,
       (headEntry req false (env.claimed[t]!).context.length σ.fresh env.startNames env.argName
        ((env.givenArgs[t]?).getD []) ((env.givenInputs[t]?).getD []) ((env.givenImplies[t]?).getD [])).2.1) := by
  obtain ⟨_, _, he, hi⟩ := visitEntry_merge h
  rw [he, hi]
  simp [withStated, hh, entryStart, hg, initial]

/-- Setup records whether any source edge targets the start. -/
theorem setup_startEntered {c : Target.RunCall G I} {env : WalkEnv ι G I} {σ0 : WalkState ι G}
    (h : RunCall.setup c = .ok (env, σ0)) :
    env.startEntered = c.P.toArray.any (fun node =>
      (successors node.continuation ++ node.handler.toList).any (·.label == c.start)) := by
  unfold RunCall.setup SinglePass.setup at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | (cases h; rfl) | cases h

/-- Exit enumeration retains every successor's target label. -/
theorem exit_target_labels (node : Node) :
    (Exit.ofNode node).map (·.target.label) =
      (successors node.continuation ++ node.handler.toList).map (·.label) := by
  unfold Exit.ofNode
  cases node.continuation <;> cases node.handler <;> simp [Exit.target, successors]

namespace ExitChecks
variable {c : Target.RunCall G I} {r : RunWalkA G I c} {l : Nat} {hl : r.w.visited l}

/-- The run record identifies its head flags with setup's flags. -/
theorem givenCorrespondence : r.given = passHeads c := r.given_eq

/-- The run record identifies its contexts with the claims read by the pass. -/
theorem contextCorrespondence : r.ctx = passCtx c := r.ctx_eq

/-- The successful computation belonging to the handler's indexed record. -/
theorem Site.handler_record (s : Site c r l hl) {t : Target}
    (ht : (r.node l hl).node.handler = some t) :
    ∃ i record, record ∈ s.ex.exits.toList ∧ record.index = i ∧ record.target = t ∧
      ∃ a b, exitStep G I s.env l s.en s.sd (yieldsAtSlots s.en.entry.names s.ysA)
        (Thunk.mk fun _ => outAllOf G s.env.claimed[l]! s.sd.st.stepOut) a (.handler t, i) = .ok b ∧
        b.exits = a.exits.push record ∧ WalkExtends (exitsWalk b) s.raw := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hn, _, _, _, _, _, _, _, hext, _, _, hrecords, _⟩ := s.facts
  have member : Exit.handler t ∈ Exit.ofNode s.env.nodes[l]! := by
    rw [hn] at ht
    simp only [Exit.ofNode, ht, Option.toList_some, List.map_cons, List.map_nil,
      List.mem_append, List.mem_singleton]
    exact .inr trivial
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨record, hr, hidx, htarget, a, b, hb, hpush, hg⟩ :=
    hrecords (.handler t, i) (List.mem_zipIdx_iff_getElem?.mpr hi)
  exact ⟨i, record, hr, hidx, htarget, a, b, hb, hpush, hg.trans hext⟩

/-- A handler's transferred pair and implications persist in the final walk. -/
theorem handlerRecords_of_checked (s : Site c r l hl) (checked : WalkChecked c r) {t : Target}
    (ht : (r.node l hl).node.handler = some t) : HandlerRecords s t := by
  obtain ⟨hw, hedge, _, _, _, _, _, _, _, _, hex, hn, hc, he, hs, _, _, hi,
    hsizes, hext, _⟩ := s.facts
  have member : Exit.handler t ∈ Exit.ofNode s.env.nodes[l]! := by
    rw [hn] at ht
    simp only [Exit.ofNode, ht, Option.toList_some, List.map_cons, List.map_nil,
      List.mem_append, List.mem_singleton]
    exact .inr trivial
  obtain ⟨i, hidx⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨a, b, hb, hx, hb1, hb2, hb3, _⟩ :=
    visitExits_indexed_arrays hex hsizes (.handler t, i) (List.mem_zipIdx_iff_getElem?.mpr hidx)
  have growth := exitStep_arraySizes hb
  have targetBound : t.label < s.env.claimed.size := (exitStep_effect hb).claimed
  have b1 : t.label < a.incoming.size := by
    rw [← growth.1, hb1, s.arrayAllocation.1]; exact targetBound
  have b2 : t.label < a.incomingImpl.size := by
    rw [← growth.2.1, hb2, ← hsizes, s.arrayAllocation.1]; exact targetBound
  have b3 : t.label < a.incomingEdges.size := by
    rw [← growth.2.2, hb3, s.arrayAllocation.2]; exact targetBound
  have flag : s.env.isHead[t.label]! = r.given t.label := by rw [s.headFlag, r.given_eq]
  change (_ → IncomingRecorded _ _ _) ∧ (_ → _ → MergeRecorded _ _ _)
  constructor
  · intro hg
    obtain ⟨h1, h2, _⟩ := exitStep_handler_arrays hb (flag.trans hg)
    refine ⟨exitsWalk b, s.raw, passHeads c, hw, r.given_eq ▸ hg, hx.trans hext, ?_⟩
    change _ ∈ ((b.incoming[t.label]?).getD []).zip ((b.incomingImpl[t.label]?).getD [])
    rw [hc, he, hs, ← hi, h1, h2]
    simp [b1, b2, Array.getElem_modify_self]
  · intro hg hm
    obtain ⟨_, _, h3⟩ := exitStep_handler_arrays hb (flag.trans hg)
    refine ⟨exitsWalk b, s.raw, hedge, hx.trans hext, ?_⟩
    change _ ∈ (b.incomingEdges[t.label]?).getD []
    rw [h3, s.mergingOfIncoming checked t.label hg hm, if_pos rfl, hc, he, hs, ← hi]
    simp only [Array.getElem?_modify, ↓reduceIte, Array.getElem?_eq_getElem b3,
      Option.map_some, Option.getD_some]
    exact List.mem_cons_self

/-- Every site retains the setup which produced its environment. -/
theorem Site.setup (s : Site c r l hl) : ∃ σ0, RunCall.setup c = .ok (s.env, σ0) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsetup, _⟩ := s.facts
  exact hsetup

/-- Every site's input names precede its entry counter. -/
theorem Site.startBelow (s : Site c r l hl) : ∀ x ∈ s.env.startNames, x < s.σ.fresh := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := s.facts
  exact hb

/-- Setup is deterministic, so sites at different visited labels share an environment. -/
theorem Site.env_eq (s : Site c r l hl) {t : Nat} {ht : r.w.visited t} (q : Site c r t ht) :
    s.env = q.env := by
  obtain ⟨σ0, hs⟩ := s.setup
  obtain ⟨σ1, hq⟩ := q.setup
  exact (Prod.mk.inj (Except.ok.inj (hs.symm.trans hq))).1

/-- At a head other than the start, setup adds only the supplied index facts. -/
theorem Site.head_written (s : Site c r l hl) {t : Nat} {req : HeapKnowledge.Knowledge}
    (hg : s.env.given[t]! = some req) (ht : t ≠ c.start) :
    ∃ cf, req = { (r.stated t).getD {} with indices := ((r.stated t).getD {}).indices ++ cf } := by
  obtain ⟨σ0, hsetup⟩ := s.setup
  have h := setup_ok hsetup
  obtain ⟨counts, hgiven⟩ := h.given
  rw [hgiven, setupGiven_get] at hg
  split at hg
  · simp only [beq_iff_eq, ht, if_false, Option.some.injEq] at hg
    refine ⟨((byLabel c.P.toArray.size c.candidates)[t]!).getD [], ?_⟩
    rw [← hg]
    have hst : s.env.stated[t]! = r.stated t := by
      rw [h.stated, r.stated_eq]
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      rfl
    rw [hst]
  · cases hg

/-- A checked exit into a head puts the final head entry among its incoming pairs. -/
theorem Site.head_incoming (s : Site c r l hl) {e : Exit}
    (hm : e ∈ Exit.ofNode (r.node l hl).node) (hh : r.given e.target.label = true) :
    (r.w.entry e.target.label, r.w.implies e.target.label) ∈ r.w.incoming e.target.label := by
  obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, hn, _, _, _, _, _, _, _, _, hsteps, _⟩ := s.facts
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hn ▸ hm)
  obtain ⟨a, b, hb, hext⟩ := hsteps (e, i) (List.mem_zipIdx_iff_getElem?.mpr hi)
  obtain ⟨edge, hedges, htarget⟩ := (exitStep_effect hb).edges
  have hmem : edge ∈ s.raw.edges.toList := hext.edge_mem (by
    change edge ∈ b.edges.toList
    rw [hedges, Array.toList_push]
    simp)
  have hany : s.raw.edges.toList.any (·.target.label == e.target.label) = true :=
    List.any_eq_true.mpr ⟨edge, hmem, by simp [htarget]⟩
  rw [hw]
  simp only [ofPass, ← r.given_eq, hh, if_true, hany, List.mem_singleton]


/-- An edge into the start uses its ordinary fresh head entry. -/
theorem Site.exit_noninitial (s : Site c r l hl) {e : Exit}
    (hm : e ∈ Exit.ofNode (r.node l hl).node) :
    (e.target.label == s.env.start && !s.env.startEntered) = false := by
  obtain ⟨σ0, hs⟩ := s.setup
  rw [(setup_ok hs).start]
  by_cases ht : e.target.label = c.start
  · have hm' : e.target.label ∈
        (successors (r.node l hl).node.continuation ++ (r.node l hl).node.handler.toList).map (·.label) := by
      rw [← exit_target_labels]
      exact List.mem_map.mpr ⟨e, hm, rfl⟩
    obtain ⟨t, htm, heq⟩ := List.mem_map.mp hm'
    have entered : s.env.startEntered = true := by
      rw [setup_startEntered hs, ← Array.any_toList, List.toList_toArray, List.any_eq_true]
      refine ⟨(r.node l hl).node, ?_, List.any_eq_true.mpr ⟨t, htm, ?_⟩⟩
      · simpa using List.mem_of_getElem? (r.node l hl).hP
      · simp [heq, ht]
    simp [entered]
  · simp [ht]
/-- Head entry construction at the final walk. The checked target visit
supplies its entry and name bound even when it follows the source visit. -/
theorem headEntryContract_of_checked (s : Site c r l hl) (checked : WalkChecked c r) {e : Exit}
    (hm : e ∈ Exit.ofNode (r.node l hl).node) (hh : r.given e.target.label = true)
    {req : HeapKnowledge.Knowledge} (hg : s.env.given[e.target.label]! = some req)
    (writtenCoherent : ∃ written cf,
      (∀ ρ h, HeapKnowledge.Holds written ρ h →
        HeapKnowledge.Holds ((r.stated e.target.label).getD {}) ρ h) ∧
      req = { written with indices := written.indices ++ cf }) :
    HeadEntryContract s e.target.label req := by
  have hin := s.head_incoming hm hh
  have hne : r.w.incoming e.target.label ≠ [] := List.ne_nil_of_mem hin
  obtain ⟨base, traversed, _⟩ := r.traversed
  have visited : r.w.visited e.target.label := traversed.visited _ hne
  obtain ⟨dead, hnodes, _⟩ := checked
  obtain ⟨q⟩ := site_of_trace (hnodes e.target.label visited).2
  have henv := s.env_eq q
  obtain ⟨_, _, _, _, _, _, _, _, hentry, _, _, _, _, he, _, _, _, hi, _, _, _, _, _, hnames, _⟩ := q.facts
  have hflag : q.env.isHead[e.target.label]! = true := by
    rw [q.headFlag, ← r.given_eq]; exact hh
  have hpair := visitEntry_head_pair hentry hflag (henv ▸ hg) (henv ▸ s.exit_noninitial hm)
  have hrecord : (q.en.entry, q.en.implies) = (r.w.entry e.target.label, r.w.implies e.target.label) := by
    rw [← he, (r.node e.target.label visited).hentry, hi]
  obtain ⟨written, cf, hwritten, hcf⟩ := writtenCoherent
  refine ⟨written, cf, (q.env.claimed[e.target.label]!).context.length,
    q.σ.fresh, ?_, ⟨hwritten, hcf⟩, ?_⟩
  · rw [henv, ← hnames, ← hpair, hrecord]
    exact hin
  · rw [← hnames]
    exact q.startBelow

/-- Heads other than the start have the written coherence required by delivery. -/
theorem headEntryContract_nonstart (s : Site c r l hl) (checked : WalkChecked c r) {e : Exit}
    (hm : e ∈ Exit.ofNode (r.node l hl).node) (hh : r.given e.target.label = true)
    {req : HeapKnowledge.Knowledge} (hg : s.env.given[e.target.label]! = some req)
    (notStart : e.target.label ≠ c.start) : HeadEntryContract s e.target.label req := by
  obtain ⟨cf, hcf⟩ := s.head_written hg notStart
  exact headEntryContract_of_checked s checked hm hh hg ⟨_, cf, fun _ _ h => h, hcf⟩

/-- The semantic projection needed when an exit targets the start.
The pass's separation union does not establish this implication for arbitrary proposals. -/
@[nospecialize] def StartWrittenImpliesStated (r : RunWalkA G I c) : Prop :=
  ∀ ρ h, HeapKnowledge.Holds (startWritten (r.stated c.start) c.entryIndices c.entrySeparation) ρ h →
    HeapKnowledge.Holds ((r.stated c.start).getD {}) ρ h

/-- The start's given contract is `startWritten` with the supplied index facts. -/
theorem Site.start_given (s : Site c r l hl) {req : HeapKnowledge.Knowledge}
    (hg : s.env.given[c.start]! = some req) :
    req = { startWritten (r.stated c.start) c.entryIndices c.entrySeparation with
      indices := (startWritten (r.stated c.start) c.entryIndices c.entrySeparation).indices ++
        ((byLabel c.P.toArray.size c.candidates)[c.start]!).getD [] } := by
  obtain ⟨σ0, hs⟩ := s.setup
  have h := setup_ok hs
  obtain ⟨counts, hgiven⟩ := h.given
  rw [hgiven, setupGiven_get] at hg
  split at hg
  · simp only [BEq.rfl, if_true, Option.some.injEq] at hg
    have hst : s.env.stated[c.start]! = r.stated c.start := by
      rw [h.stated, r.stated_eq]
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      rfl
    rw [← hg, hst]; rfl
  · cases hg

/-- Setup's given head contract contains a base implying the written assertion.
At the start the base is `startWritten`, including the entry facts. -/
theorem Site.head_written_coherent (s : Site c r l hl) {t : Nat}
    {req : HeapKnowledge.Knowledge} (hg : s.env.given[t]! = some req)
    (startWrittenSound : StartWrittenImpliesStated r) :
    ∃ written cf,
      (∀ ρ h, HeapKnowledge.Holds written ρ h → HeapKnowledge.Holds ((r.stated t).getD {}) ρ h) ∧
      req = { written with indices := written.indices ++ cf } := by
  by_cases ht : t = c.start
  · subst t
    exact ⟨startWritten (r.stated c.start) c.entryIndices c.entrySeparation,
      ((byLabel c.P.toArray.size c.candidates)[c.start]!).getD [], startWrittenSound, s.start_given hg⟩
  · obtain ⟨cf, hcf⟩ := s.head_written hg ht
    exact ⟨_, cf, fun _ _ h => h, hcf⟩

/-- All targeted heads have their contract at the final walk. -/
theorem headEntries_of_checked (s : Site c r l hl) (checked : WalkChecked c r)
    (startWrittenSound : StartWrittenImpliesStated r) :
    ∀ t, (∃ e ∈ Exit.ofNode (r.node l hl).node, e.target.label = t) → r.given t = true →
      ∀ req, s.env.given[t]! = some req → HeadEntryContract s t req := by
  intro t htarget hh req hg
  obtain ⟨e, hm, rfl⟩ := htarget
  exact headEntryContract_of_checked s checked hm hh hg (s.head_written_coherent hg startWrittenSound)

/-- Normal head extraction under the yield-source judgment. -/
theorem exitChecks_head_structural (s : Site c r l hl) (checked : WalkChecked c r) (η : MixedAssignment ι)
    (startWrittenSound : StartWrittenImpliesStated r)
    (yieldSourcesJudged : ∀ ys, ExitYieldSource s.env l s.en s.sd s.sd.yields ys →
      ExitYieldsJudged (reassign G η) r.w (List.range c.inputs.length) l
        (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st ys) : Head s η :=
  exitChecks_head s η (headEntries_of_checked s checked startWrittenSound) yieldSourcesJudged

/-- Handler extraction from checked records. -/
theorem exitChecks_handler_structural (s : Site c r l hl) (checked : WalkChecked c r) (η : MixedAssignment ι)
    (startWrittenSound : StartWrittenImpliesStated r) : Handler s η :=
  exitChecks_handler_of_records s η (headEntries_of_checked s checked startWrittenSound)
    (fun _ ht => handlerRecords_of_checked s checked ht)

end ExitChecks
/-- Checked exit execution delivers under yield judgments and final-world realization. -/
theorem exitsYield_of_yields
    (startWrittenSound : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
      after admits, RunPremises G I c after admits → ∀ r : RunWalkA G I c,
        WalkChecked c r → ExitChecks.StartWrittenImpliesStated r)
    (yieldSourcesJudged : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
      after admits, RunPremises G I c after admits → ∀ r : RunWalkA G I c,
        WalkChecked c r → ∀ η, admits η → ∀ l (hl : r.w.visited l) (s : ExitChecks.Site c r l hl),
        ∀ ys, ExitYieldSource s.env l s.en s.sd s.sd.yields ys →
          ExitYieldsJudged (reassign G η) r.w (List.range c.inputs.length) l
            (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st ys)
    (initialYieldsJudged : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
      after admits, RunPremises G I c after admits → ∀ r : RunWalkA G I c,
        WalkChecked c r → ∀ η, admits η → ∀ l (hl : r.w.visited l) (s : ExitChecks.Site c r l hl),
          ExitYieldsJudged (reassign G η) r.w (List.range c.inputs.length) l
            (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st s.ysA)
    (realization : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
      after admits, RunPremises G I c after admits → ∀ r : RunWalkA G I c,
        WalkChecked c r → ∀ η, admits η → ∀ l (hl : r.w.visited l) (s : ExitChecks.Site c r l hl),
          ExitChecks.Realization s η) : ExitsYield ι := by
  apply exitsYield_of_checks
  intro G I c after admits hp r checked η ha l hl s
  have startSound := startWrittenSound G I c after admits hp r checked
  have sources := yieldSourcesJudged G I c after admits hp r checked η ha l hl s
  exact ExitChecks.assemble s η
    (ExitChecks.exitChecks_here s η (initialYieldsJudged G I c after admits hp r checked η ha l hl s))
    (ExitChecks.exitChecks_widths s η)
    (ExitChecks.exitChecks_nonHead s η checked sources)
    (ExitChecks.exitChecks_head_structural s checked η startSound sources)
    (ExitChecks.exitChecks_handler_structural s checked η startSound)
    (ExitChecks.exitChecks_fresh s)
    (realization G I c after admits hp r checked η ha l hl s)

end Structural
end Verification.TolerantFrames
