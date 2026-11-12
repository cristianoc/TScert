import Verification.Programs.TolerantFramesExitsYield
import Verification.Programs.TolerantFramesExitHeadChecks
import Verification.Programs.TolerantFramesExitYieldCache

/-! # Head contracts extracted from successful exit computations -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Extraction
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- The parts of a head contract checked by `headExit`. -/
structure HeadChecks (env : WalkEnv ι G I) (l : Nat) (t : Target) (tc : PointClaim ι)
    (Γ : List (Ty ι)) (names : List Nat) (store : Store) (pushed vacuous : Bool)
    (carried : List (PromiseCalls.Implication ι)) (req : HeapKnowledge.Knowledge) : Prop where
  given : env.given[t.label]! = some req
  implied : vacuous = false → ∀ x ∈ (env.givenImplies[t.label]?).getD [], ∃ y ∈ carried,
    names[PointClaims.slot t.mapping x.test]? = some y.test ∧
    names[PointClaims.slot t.mapping x.target]? = some y.target ∧
    (y.type = x.type ∨ ∃ a, ((subtypeUsing G I y.type x.type a).1).value.isSome = true)
  inputs : vacuous = false → ∀ p ∈ (env.givenInputs[t.label]?).getD [],
    names[PointClaims.slot t.mapping p.1]? = env.startNames[p.2]?
  args : vacuous = false → ∀ j ∈ (env.givenArgs[t.label]?).getD [],
    names[PointClaims.slot t.mapping j]? = env.argName
  query : vacuous = false → KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context)
    (HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req t.mapping
      (materialize { names, store }
        (if pushed then (env.claimed[l]!).context.length + 1 else (env.claimed[l]!).context.length)
        (((atomsOf req).flatMap Atom.names).map (PointClaims.slot t.mapping)) true).1)) req t.mapping = true

/-- The given contract exists even when the edge is vacuous. -/
theorem headExit_contract {env : WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γ : List (Ty ι)} {names : List Nat} {store : Store} {pushed vacuous : Bool}
    {carried : List (PromiseCalls.Implication ι)} {a b : ExitsDone ι G}
    (h : headExit G I env l t tc Γ names store pushed vacuous carried a = .ok b) :
    ∃ req, HeadChecks env l t tc Γ names store pushed vacuous carried req := by
  have hg : ∃ req, env.given[t.label]! = some req := by
    unfold headExit at h
    repeat' (first | split at h | extract_lets at h)
    all_goals first | cases h | skip
    all_goals exact ⟨_, by assumption⟩
  obtain ⟨req, hr⟩ := hg
  have checked := fun (hv : vacuous = false) => headExit_checked (hv ▸ h)
  refine ⟨req, hr, fun hv => (checked hv).1, fun hv => (checked hv).2.1,
    fun hv => (checked hv).2.2.1, fun hv => ?_⟩
  obtain ⟨req', hr', hq⟩ := (checked hv).2.2.2
  have he : req' = req := Option.some.inj (hr'.symm.trans hr)
  exact he ▸ hq

/-- A successful normal head exit exposes its type checks and the head
checks at the very same output yield cache. -/
theorem exitStep_head_checks {env : WalkEnv ι G I} {l i : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ysAll : List (PromiseCalls.Yield ι)} {a b : ExitsDone ι G}
    {t : Target} {pushed : Bool} {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    (h : exitStep G I env l en sd ysAll (Thunk.mk fun _ => outAllOf G env.claimed[l]! sd.st.stepOut)
      a (.normal t pushed observed promote, i) = .ok b)
    (hh : env.isHead[t.label]! = true) :
    ∃ tc req, env.claimed[t.label]? = some tc ∧
      (vacuousOf G en.here (env.claimed[l]!).type (exitCtx env.claimed[l]! pushed) pushed observed = false →
        ExitTyped G I (exitCtx env.claimed[l]! pushed) tc.context t observed
          (exitSearchFacts G env.claimed[l]! en.entry sd.st pushed observed promote tc.context t.mapping)
          (refinedContext G env.claimed[l]! (env.nodes[l]!).continuation
            (yieldsAtSlots en.entry.names (b.yields.getD [])) (outAllOf G env.claimed[l]! sd.st.stepOut) (i == 0))
          (outAllOf G env.claimed[l]! sd.st.stepOut)) ∧
      HeadChecks env l t tc (exitCtx env.claimed[l]! pushed) (normalNames en.entry sd.st pushed)
        (exitStore G env.claimed[l]! en.entry sd.st pushed observed promote) pushed
        (vacuousOf G en.here (env.claimed[l]!).type (exitCtx env.claimed[l]! pushed) pushed observed)
        (en.implies ++ freshImplOf pushed false (b.yields.getD []) en.entry.names sd.st.result) req := by
  unfold exitStep at h
  extract_lets ex first node c width entry st target push obs handler pushedNames tr a0 Γ names store unsatΓ vacuous Γe read Γr at h
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
  have hh' : env.isHead[target.label]! = true := hh
  simp only [hh', if_true] at h
  simp only [Except.map] at h
  split at h
  · cases h
  rename_i a3 hc
  cases h
  have hy : a3.yields = a1.yields := headExit_yields hc
  obtain ⟨req, hreq⟩ := headExit_contract hc
  refine ⟨tc, req, htc, ?_, ?_⟩
  · intro hv
    have hv' : vacuous = false := hv
    simp only [hv', Bool.false_eq_true, if_false] at ht
    have hd : diff = differing Γ tc.context target.mapping := by simp only [diff, hv', Bool.false_eq_true, if_false, timedKind]
    rw [hd] at ht
    obtain ⟨ys, _, heq, hty⟩ := exitTypes_checked ht
    rw [heq] at hty
    cases pushed <;> cases observed <;> simpa [hy, Γ, handler, ex, Exit.isHandler, Bool.false_eq_true, if_false, push, Exit.pushed, c,
      target, Exit.target, obs, Exit.observed, store, names, pushedNames, entry, st, width, Exit.promote,
      first, exitCtx, exitSearchFacts, exitStore, normalNames, exitWidth, Thunk.get] using hty
  · cases pushed <;> cases observed <;> simpa [hy, Γ, handler, ex, Exit.isHandler, Bool.false_eq_true, if_false, push, Exit.pushed, c,
      target, Exit.target, obs, Exit.observed, store, names, pushedNames, entry, st, width, Exit.promote,
      vacuous, unsatΓ, freshImpl, freshImplOf, exitCtx, exitStore, normalNames, vacuousOf] using hreq

/-- Handler type, assertion, and head checks exposed by execution. -/
theorem exitStep_handler_checks {env : WalkEnv ι G I} {l i : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ysAll : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    {a b : ExitsDone ι G} {t : Target}
    (h : exitStep G I env l en sd ysAll out a (.handler t, i) = .ok b) :
    ∃ tc, env.claimed[t.label]? = some tc ∧
      ((en.here || ControlFlow.unsatisfiable G [sd.thrownTy.getD []]) = false →
        SubtypesPass G I (handlerCtx env.claimed[l]! (sd.thrownTy.getD [])) tc.context
          (differing (handlerCtx env.claimed[l]! (sd.thrownTy.getD [])) tc.context t.mapping) ∨
        EdgeFound G I tc.context (handlerCtx env.claimed[l]! (sd.thrownTy.getD [])) t none
          (handlerSearchFacts G env.claimed[l]! (sd.thrownTy.getD []) en.entry sd.st sd.thrown tc.context t.mapping)) ∧
      (env.isHead[t.label]! = true → ∃ req,
        HeadChecks env l t tc (handlerCtx env.claimed[l]! (sd.thrownTy.getD [])) (sd.thrown :: en.entry.names)
          (handlerStore G env.claimed[l]! (sd.thrownTy.getD []) en.entry sd.st sd.thrown) true
          (en.here || ControlFlow.unsatisfiable G [sd.thrownTy.getD []]) en.implies req) ∧
      (env.isHead[t.label]! = false →
        (en.here || ControlFlow.unsatisfiable G [sd.thrownTy.getD []]) = false → ∀ req,
        env.stated[t.label]! = some req →
        KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context)
          (assertionSource G (handlerCtx env.claimed[l]! (sd.thrownTy.getD [])) req
            (handlerAssertFacts G env.claimed[l]! (sd.thrownTy.getD []) en.entry sd.st sd.thrown req t.mapping)
            t.mapping none) req t.mapping = true) := by
  unfold exitStep at h
  extract_lets ex first node c width entry st target push obs handler pushedNames tr a0 Γ names store unsatΓ vacuous Γe read Γr at h
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
  have htcheck : (en.here || ControlFlow.unsatisfiable G [sd.thrownTy.getD []]) = false →
      SubtypesPass G I (handlerCtx env.claimed[l]! (sd.thrownTy.getD [])) tc.context
        (differing (handlerCtx env.claimed[l]! (sd.thrownTy.getD [])) tc.context t.mapping) ∨
      EdgeFound G I tc.context (handlerCtx env.claimed[l]! (sd.thrownTy.getD [])) t none
        (handlerSearchFacts G env.claimed[l]! (sd.thrownTy.getD []) en.entry sd.st sd.thrown tc.context t.mapping) := by
    intro hv
    have hv' : vacuous = false := hv
    simp only [hv', Bool.false_eq_true, if_false] at ht
    have hd : diff = differing Γ tc.context target.mapping := by simp only [diff, hv', Bool.false_eq_true, if_false, timedKind]
    rw [hd] at ht
    simpa only [Γ, handler, ex, Exit.isHandler, if_true, names, entry, target, Exit.target, obs, Exit.observed,
      store, st, pushedNames, width, c, push, Exit.pushed, Exit.promote, handlerCtx, handlerSearchFacts, handlerStore]
      using exitTypes_handler_checked ht
  refine ⟨tc, htc, htcheck, ?_⟩
  extract_lets freshImpl record at h
  split at h
  · rename_i hh
    simp only [Except.map] at h
    split at h
    · cases h
    rename_i a3 hc
    obtain ⟨req, hreq⟩ := headExit_contract hc
    refine ⟨fun _ => ⟨req, ?_⟩, fun hn => ?_⟩
    · simpa only [freshImpl, handler, ex, Exit.isHandler, Bool.or_true, if_true, List.append_nil,
        Γ, c, names, entry, target, Exit.target, store, st, pushedNames, width, push, Exit.pushed, obs,
        Exit.observed, Exit.promote, vacuous, unsatΓ, handlerCtx, handlerStore] using hreq
    · exact Bool.noConfusion (hh.symm.trans hn)
  · rename_i hh
    split at h
    · cases h
    rename_i a3 ha
    refine ⟨fun ht => (hh ht).elim, fun _ hv req hr => ?_⟩
    have hv' : vacuous = false := hv
    rw [hv'] at ha
    simpa only [Γe, Thunk.get, handler, ex, Exit.isHandler, if_true, Γ, c, names, entry, target, Exit.target,
      store, st, pushedNames, width, push, Exit.pushed, obs, Exit.observed, Exit.promote, handlerCtx,
      handlerAssertFacts, handlerStore] using assertionExit_checked ha hr

/-- The selected handler type admits every exception value. -/
theorem thrownTyOf_admits {env : WalkEnv ι G I} {node : Node} {T : Ty ι}
    (h : thrownTyOf env node = some T) : ControlFlow.admitsAll G T = true := by
  unfold thrownTyOf at h
  cases hn : node.handler with
  | none => simp [hn] at h
  | some t =>
    simp only [hn, Option.bind_some] at h
    cases hc : env.claimed[t.label]? with
    | none => simp [hc] at h
    | some tc =>
      simp only [hc, bind, Option.bind_some] at h
      exact List.find?_some h

/-- A successful step with a handler retains a type admitting every exception. -/
theorem visitStep_handler_admits {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G}
    (h : visitStep G I env σ l en = .ok sd) (hh : (env.nodes[l]!).handler.isSome = true) :
    ControlFlow.admitsAll G (sd.thrownTy.getD []) = true := by
  have ht : ∀ T : Option (Ty ι), T = thrownTyOf env env.nodes[l]! →
      ¬ ((env.nodes[l]!).handler.isSome && T.isNone) = true →
      ControlFlow.admitsAll G (T.getD []) = true := by
    intro T he hn
    cases T with
    | none => simp [hh] at hn
    | some T => exact thrownTyOf_admits he.symm
  unfold visitStep at h
  split at h
  · cases h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals apply ht _ rfl; assumption

namespace ExitChecks
variable {c : Target.RunCall G I} {r : RunWalkA G I c} {l : Nat} {hl : r.w.visited l}

/-- The structural part of a head's entry, separate from its edge checks. -/
@[nospecialize] def HeadEntryContract (s : Site c r l hl) (t : Nat)
    (req : HeapKnowledge.Knowledge) : Prop :=
  ∃ (written : HeapKnowledge.Knowledge) (cf : List HeapKnowledge.IndexAtom) (width fresh : Nat),
    ((headEntry req false width fresh (List.range c.inputs.length) s.env.argName
      ((s.env.givenArgs[t]?).getD []) ((s.env.givenInputs[t]?).getD [])
      ((s.env.givenImplies[t]?).getD [])).1,
     (headEntry req false width fresh (List.range c.inputs.length) s.env.argName
      ((s.env.givenArgs[t]?).getD []) ((s.env.givenInputs[t]?).getD [])
      ((s.env.givenImplies[t]?).getD [])).2.1) ∈ r.w.incoming t ∧
    ((r.stated t).getD {} = written ∧ req = { written with indices := written.indices ++ cf }) ∧
    ∀ y ∈ List.range c.inputs.length, y < fresh

/-- The trace identifies the head flag with the pass's flag. -/
theorem Site.headFlag (s : Site c r l hl) (t : Nat) :
    s.env.isHead[t]! = passHeads c t := by
  obtain ⟨_, _, _, _, _, _, hh, _⟩ := s.facts
  simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] using hh t

/-- A target claim read by execution supplies the pass context. -/
theorem Site.targetContext (s : Site c r l hl) {t : Nat} {tc : PointClaim ι}
    (h : s.env.claimed[t]? = some tc) : tc.context = passCtx c t := by
  obtain ⟨_, _, _, hc, _⟩ := s.facts
  rw [hc, List.getElem?_toArray] at h
  simp only [passCtx, h, Option.map_some, Option.getD_some]

/-- The setup's promised argument is one of its input names. -/
theorem Site.argumentInput (s : Site c r l hl) :
    ∀ a, s.env.argName = some a → ∃ q : Nat, (List.range c.inputs.length)[q]? = some a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ha⟩ := s.facts
  intro a he
  rw [ha] at he
  cases hslot : c.goal.slot with
  | none => simp [hslot] at he
  | some q => exact ⟨q, by simpa only [hslot, Option.bind_some] using he⟩

/-- Normal head extraction. The structural entry and judged yield sources
are explicit leaves; every edge check comes from the successful visit. -/
theorem exitChecks_head (s : Site c r l hl) (η : MixedAssignment ι)
    (givenCorrespondence : r.given = passHeads c)
    (contextCorrespondence : r.ctx = passCtx c)
    (headEntries : ∀ t, r.given t = true → ∀ req, s.env.given[t]! = some req → HeadEntryContract s t req)
    (yieldSourcesJudged : ∀ ys, ExitYieldSource s.env l s.en s.sd s.sd.yields ys →
      ExitYieldsJudged (reassign G η) r.w (List.range c.inputs.length) l
        (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st ys) : Head s η := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hv, hn, hc, he, hs, _, _, hi, _, _, _, _, _, hnames, _⟩ := s.facts
  intro i t pushed observed promote hm hg
  have headFlag : s.env.isHead[t.label]! = true := by
    rw [s.headFlag, ← givenCorrespondence]; exact hg
  have member : (Exit.normal t pushed observed promote, i) ∈ (Exit.ofNode s.env.nodes[l]!).zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simpa only [hn] using hm
  obtain ⟨record, _, _, _, a, b, hb, _, _, hy⟩ := visitExits_records_yields hv _ member
  obtain ⟨tc, req, htc, typed, checks⟩ := exitStep_head_checks hb headFlag
  have targetContext : tc.context = r.ctx t.label := by
    rw [contextCorrespondence]; exact s.targetContext htc
  have constructedHead : HeadEntryContract s t.label req := headEntries _ hg _ checks.given
  obtain ⟨written, cf, width, fresh, entered, coherent, below⟩ := constructedHead
  have argumentInput : ∀ a, s.env.argName = some a → ∃ q : Nat, (List.range c.inputs.length)[q]? = some a :=
    s.argumentInput
  have checked : HeadExitChecked G I r.w (List.range c.inputs.length) r.ctx r.stated l
      (r.node l hl).node (r.node l hl).c (r.node l hl).entry (r.node l hl).st
      (r.node l hl).ys (b.yields.getD []) s.en.here i t pushed observed promote req written cf
      ((s.env.givenImplies[t.label]?).getD []) s.env.argName ((s.env.givenArgs[t.label]?).getD [])
      ((s.env.givenInputs[t.label]?).getD []) width fresh := by
    refine ⟨?_, ?_, ?_, ?_, ?_, entered, coherent⟩
    · simpa only [hn, hc, he, hs, ← targetContext] using typed
    · simpa only [hc, he, hs, ← hi] using checks.implied
    · simpa only [hc, he, hs, ← hnames] using checks.inputs
    · simpa only [hc, he, hs] using checks.args
    · simpa only [hc, he, hs, ← targetContext, exitWidth] using checks.query
  exact ⟨b.yields.getD [], yieldSourcesJudged _ hy, req, written, cf,
    (s.env.givenImplies[t.label]?).getD [], s.env.argName, (s.env.givenArgs[t.label]?).getD [],
    (s.env.givenInputs[t.label]?).getD [], width, fresh, checked.reassign η, below, argumentInput⟩

/-- Handler records at the final walk. The merge record states the
source implications required by the semantic interface. -/
@[nospecialize] def HandlerRecords (s : Site c r l hl) (t : Target) : Prop :=
  let n := r.node l hl
  (r.given t.label = false → IncomingRecorded r.w t.label
    (edgeTransfer (s.sd.thrown :: n.entry.names) t.mapping true true s.sd.outFresh n.entry n.st.result
      (handlerStore G n.c (s.sd.thrownTy.getD []) n.entry n.st s.sd.thrown) (r.w.implies l))) ∧
  (r.given t.label = false → 2 ≤ (r.w.incoming t.label).length →
    MergeRecorded r.edgesIn t.label (handlerCtx n.c (s.sd.thrownTy.getD []),
      atSlotsOf (s.sd.thrown :: n.entry.names) (r.w.implies l), t.mapping))

/-- Handler edge checks from the trace, under the structural head-entry
and incoming-record leaves. Type admission, type checks, head queries,
and written assertions are extracted from execution. -/
theorem exitChecks_handler_edges (s : Site c r l hl) (η : MixedAssignment ι)
    (givenCorrespondence : r.given = passHeads c)
    (contextCorrespondence : r.ctx = passCtx c)
    (headEntries : ∀ t, r.given t = true → ∀ req, s.env.given[t]! = some req → HeadEntryContract s t req)
    (handlerRecords : ∀ t, (r.node l hl).node.handler = some t → HandlerRecords s t) :
    ∀ t, (r.node l hl).node.handler = some t →
      HandlerExitChecked (reassign G η) (I.reassign η) r.w (List.range c.inputs.length)
        r.ctx r.stated r.given r.edgesIn l (r.node l hl).c (r.node l hl).entry (r.node l hl).st
        s.en.here s.sd.outFresh (s.sd.thrownTy.getD []) s.sd.thrown t := by
  obtain ⟨_, _, _, _, _, _, _, hstated, _, hstep, _, hn, hc, he, hs, _, _, hi, _, _, hsteps, _, _, hnames, _⟩ := s.facts
  intro t ht
  have member : Exit.handler t ∈ Exit.ofNode s.env.nodes[l]! := by
    rw [hn] at ht
    simp only [Exit.ofNode, ht, Option.toList_some, List.map_cons, List.map_nil,
      List.mem_append, List.mem_singleton]
    exact .inr trivial
  obtain ⟨i, hm⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨a, b, hb, _⟩ := hsteps (.handler t, i) (List.mem_zipIdx_iff_getElem?.mpr hm)
  obtain ⟨tc, htc, typed, head, asserted⟩ := exitStep_handler_checks hb
  have targetContext : tc.context = r.ctx t.label := by
    rw [contextCorrespondence]; exact s.targetContext htc
  have headFlag : s.env.isHead[t.label]! = r.given t.label := by
    rw [s.headFlag, givenCorrespondence]
  have writtenContext : s.env.stated[t.label]! = r.stated t.label := by
    rw [hstated, r.stated_eq]; rfl
  have admits : ControlFlow.admitsAll G (s.sd.thrownTy.getD []) = true :=
    visitStep_handler_admits hstep (by rw [← hn, ht]; rfl)
  have checked : HandlerExitChecked G I r.w (List.range c.inputs.length) r.ctx r.stated r.given r.edgesIn l
      (r.node l hl).c (r.node l hl).entry (r.node l hl).st s.en.here s.sd.outFresh
      (s.sd.thrownTy.getD []) s.sd.thrown t := by
    refine ⟨admits, ?_, ?_, (handlerRecords t ht).1, (handlerRecords t ht).2, ?_⟩
    · simpa only [hc, he, hs, ← targetContext] using typed
    · simpa only [hc, he, hs, ← targetContext, headFlag, writtenContext] using asserted
    · intro hg
      obtain ⟨req, checks⟩ := head (headFlag.trans hg)
      obtain ⟨written, cf, width, fresh, entered, coherent, below⟩ := headEntries _ hg _ checks.given
      refine ⟨req, written, cf, (s.env.givenImplies[t.label]?).getD [], s.env.argName,
        (s.env.givenArgs[t.label]?).getD [], (s.env.givenInputs[t.label]?).getD [], width, fresh,
        ?_, ?_, ?_, ?_, entered, coherent, below, s.argumentInput⟩
      · simpa only [he, ← hi] using checks.implied
      · simpa only [he, ← hnames] using checks.inputs
      · simpa only [he] using checks.args
      · simpa only [hc, he, hs, ← targetContext, if_true] using checks.query
  exact checked.reassign η

/-- The extracted handler checks and the step's fresh-name bound give
all of the handler field group. -/
theorem exitChecks_handler_of_records (s : Site c r l hl) (η : MixedAssignment ι)
    (givenCorrespondence : r.given = passHeads c)
    (contextCorrespondence : r.ctx = passCtx c)
    (headEntries : ∀ t, r.given t = true → ∀ req, s.env.given[t]! = some req → HeadEntryContract s t req)
    (handlerRecords : ∀ t, (r.node l hl).node.handler = some t → HandlerRecords s t) : Handler s η :=
  exitChecks_handler s η (exitChecks_handler_edges s η givenCorrespondence contextCorrespondence headEntries handlerRecords)

end ExitChecks

end Extraction
end Verification.TolerantFrames
