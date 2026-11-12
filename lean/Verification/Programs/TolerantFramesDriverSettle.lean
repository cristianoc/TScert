import Verification.Programs.TolerantFramesExitRecords
import Verification.Programs.TolerantFramesDriverExitTrace
import Verification.Programs.TolerantFramesDriverSettleEntry

/-! # Tolerant frames: checks retained by a successful visit -/
namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore ProgramCertificates ProgramTyping

/-- A check whose negation does not pass is true. -/
theorem visitCheck_true {b : Bool} (h : ¬(!b) = true) : b = true := by
  cases b <;> simp_all

section Checks
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- A successful step run passes the node's shape check. -/
theorem stepRun_shape {env : SinglePass.WalkEnv ι G I} {l : Nat} {entry : SinglePass.State} {fresh : Nat}
    {answers : Answered G} {counts : SinglePass.Counts} {trace : SinglePass.Trace} {ms : List Nat}
    {st : SinglePass.Stepped ι} {stats : SinglePass.StepStats} {a : Answered G}
    (h : SinglePass.stepRun G I env l entry fresh answers counts trace = .ok (ms, st, stats, a)) :
    SinglePass.passShapeCheck' G (env.claimed[l]!).type (env.nodes[l]!).continuation = true := by
  unfold SinglePass.stepRun at h
  extract_lets node c at h
  split at h
  · cases h
  · rename_i hs
    exact visitCheck_true hs

/-- The footprint check in the pass is the check read by the soundness theorem. -/
theorem boundOk_eq (codes : CodeEntry ι → Bool) (bound : Option (Footprints.Closed × Bool × Bool))
    (dead : Array Bool) (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State)
    (sums : List (ReadSummary ι)) (k : HeapKnowledge.Knowledge) (d : ProgramCertificates.Evidence ι) :
    SinglePass.boundOk G I codes bound dead l node c entry sums k d =
      passBounded G I codes bound dead l node c entry sums k d := rfl

/-- A successful visit step retains its passing bound and return checks
and the yields computed at the answers after the checked step. -/
theorem visitStep_checks {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G}
    (h : SinglePass.visitStep G I env σ l en = .ok sd) :
    passBounded G I env.codes env.bound env.deadArr l env.nodes[l]! env.claimed[l]! en.entry
        sd.steppedAnswers.summaries.toList sd.st.stepK (passDerivOf env.claimed[l]! env.nodes[l]! sd.st) = true ∧
      SinglePass.returnOk G I env l en.entry sd.st (sd.yields.getD []) sd.yieldAnswers = true ∧
      SinglePass.stepYields G I env l en.entry en.implies sd.st sd.steppedAnswers =
        (sd.yields, sd.yieldAnswers) := by
  unfold SinglePass.visitStep at h
  split at h
  · cases h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (apply visitCheck_true; assumption)
    | (unfold SinglePass.returnOk; simp_all (config := { zetaDelta := true }) only; try rfl)
    | assumption

/-- A passing return check exposes the successful `returnCheck` at a return. -/
theorem returnOk_check {env : SinglePass.WalkEnv ι G I} {l : Nat} {entry : SinglePass.State}
    {st : SinglePass.Stepped ι} {ys : List (PromiseCalls.Yield ι)} {a : Answered G}
    (h : SinglePass.returnOk G I env l entry st ys a = true)
    (hr : (env.nodes[l]!).continuation = .ret) :
    (SinglePass.returnCheck G I env.goal env.ensures env.claimed[l]! l entry st.store st.result env.start
      env.startNames env.argName ys env.debugNode a).1 = none := by
  unfold SinglePass.returnOk SinglePass.returnRun at h
  rw [hr] at h
  exact Option.isNone_iff_eq_none.mp h

/-- A computed yield list is empty or checked against a subset of the
entry's implications, over the checked step's summary table. -/
theorem stepYields_kept {env : SinglePass.WalkEnv ι G I} {l : Nat} {entry : SinglePass.State}
    {imp : List (PromiseCalls.Implication ι)} {st : SinglePass.Stepped ι} {a a' : Answered G}
    {ys : Option (List (PromiseCalls.Yield ι))}
    (h : SinglePass.stepYields G I env l entry imp st a = (ys, a')) :
    ys.getD [] = [] ∨ ∃ xs ys0,
      (∀ x ∈ xs, x ∈ imp) ∧
      ys.getD [] = SinglePass.checkYsAt G I env.codes a env.claimed[l]! env.nodes[l]! st
        (SinglePass.slotImplOf entry.names xs) ys0 := by
  unfold SinglePass.stepYields at h
  split at h
  · rename_i ys' hr
    cases h
    unfold SinglePass.readYields at hr
    repeat' (first | split at hr | extract_lets at hr)
    all_goals first | cases hr | skip
    all_goals exact .inr ⟨_, _, fun x hx => (List.mem_filter.mp hx).1, rfl⟩
  · extract_lets at h
    split at h
    · split at h
      cases h
      exact .inr ⟨imp, _, fun _ hx => hx, rfl⟩
    · cases h
      exact .inl rfl

/-- The yield and return checks retained by a successful visit step. -/
theorem visitStep_yields {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G} {w : Walk ι}
    (h : SinglePass.visitStep G I env σ l en = .ok sd)
    (himp : w.implies l = en.implies)
    (harg : env.argName = env.goal.slot.bind (env.startNames[·]?)) :
    NodeYieldChecks G I env.codes sd.steppedAnswers.summaries.toList w env.startNames env.goal env.ensures
      l env.nodes[l]! env.claimed[l]! en.entry sd.st (sd.yields.getD []) := by
  obtain ⟨-, hr, hy⟩ := visitStep_checks h
  refine ⟨?_, fun hk => ⟨env.start, env.argName, env.debugNode, sd.yieldAnswers, returnOk_check hr hk, harg⟩⟩
  rcases stepYields_kept hy with h0 | ⟨xs, ys0, hx, hy⟩
  · exact .inl h0
  · exact .inr ⟨xs, SinglePass.derivOf env.claimed[l]! env.nodes[l]! sd.st, ys0,
      sd.steppedAnswers.summaries.toList, fun x h => himp.symm ▸ hx x h, fun _ h => h, hy⟩

/-- A checked step preserves soundness of its summary table. -/
theorem StepChecked.summaries {pc : SinglePass.PassChecker G I} {codes : CodeEntry ι → Bool}
    {c : PointClaim ι} {node : Node} {entry : SinglePass.State} {ms : List Nat} {fresh : Nat}
    {a b : Answered G} {st : SinglePass.Stepped ι}
    (h : StepChecked G I pc codes c node entry ms fresh a b st)
    (ha : SummariesSound G I a.summaries.toList) : SummariesSound G I b.summaries.toList := by
  rcases h with ⟨_, _, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, hs⟩
  · exact ha
  · exact (hs ha).2

/-- A successful visit's step supplies the checked node and all its pass
checks, where the entry's names and implications are below its counter. -/
theorem visitStep_node {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    {σ : SinglePass.WalkState ι G} {l : Nat} {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G}
    {w : Walk ι} (hE : EnvFacts c env) (hl : l < env.n)
    (h : SinglePass.visitStep G I env σ l en = .ok sd)
    (hdir : DirectKeepsSummaries G I env.undefTy)
    (hsrch : SearchKeepsSummaries G I env.pool env.fuel env.suggestions env.index env.codes env.aliases
      env.passChecker.checker)
    (hw : StoreWF en.entry.store)
    (hb : NamesBelow en.entry en.implies (List.range c.inputs.length) en.fresh)
    (hwidth : en.entry.names.length ≤ (env.claimed[l]!).context.length)
    (hentry : en.entry = w.entry l) (himp : w.implies l = en.implies)
    (hsums : SummariesSound G I σ.answers.summaries.toList) :
    ∃ r : NodeChecked G I c.codes c.passChecker c.P w (List.range c.inputs.length) (passCtx c) l,
      NodePassChecked c env.deadArr.toList r ∧ r.node = env.nodes[l]! ∧ r.c = env.claimed[l]! ∧
      r.entry = en.entry ∧ r.st = sd.st ∧ r.ans = sd.steppedAnswers ∧ r.ys = sd.yields.getD [] := by
  obtain ⟨⟨ms, stats, hr⟩, -, -⟩ := visitStep_ok h
  have hc := stepChecked_of_step (stepRun_ok hr) hdir hsrch
  have ha := hc.summaries hsums
  have hn : c.P[l]? = some env.nodes[l]! := by
    rw [hE.nodes]
    have hpl : l < c.P.length := hE.nodeCount ▸ hl
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem hpl]
  have hc' := hc
  rw [hE.codes, hE.checker] at hc'
  let r : NodeChecked G I c.codes c.passChecker c.P w (List.range c.inputs.length) (passCtx c) l :=
    ⟨env.nodes[l]!, hn, env.claimed[l]!, (hE.context hl).symm, en.entry, ms, en.fresh, σ.answers,
      sd.st, sd.steppedAnswers, hc', hw, himp.symm ▸ hb, hwidth, hsums, hentry, stepRun_shape hr,
      sd.yields.getD []⟩
  obtain ⟨hbound, hret, -⟩ := visitStep_checks h
  have hy := visitStep_yields h himp (by rw [hE.goal, hE.startNames]; exact hE.argName)
  rw [hE.codes, hE.startNames, hE.goal, hE.ensures] at hy
  refine ⟨r, nodePassChecked_of r ?_ (fun _ hk => ?_) ⟨sd.steppedAnswers.summaries.toList, ha, hy⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  · change passBounded G I c.codes c.bound env.deadArr l _ _ _ _ _ _ = true
    rw [hE.codes, hE.bound] at hbound
    exact hbound
  · obtain ⟨start, arg, debug, answers, hr, -⟩ := hy.ret hk
    exact ⟨start, arg, sd.yields.getD [], debug, answers, hr⟩

/-- A visit settles its label under the direct-call and search summary
soundness premises. Setup equations are fields of `EnvFacts`; incoming
implications are bounded by `RecInv.impBelow`. -/
theorem visitsSettle_of
    (hdir : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G I),
      DirectKeepsSummaries G I env.undefTy)
    (hsrch : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (env : SinglePass.WalkEnv ι G I),
      SearchKeepsSummaries G I env.pool env.fuel env.suggestions env.index env.codes env.aliases
        env.passChecker.checker) : VisitsSettle ι := by
  intro G I c env σ l rest en sd ex hP hself
  have hl := (hP.inv.queue l (by rw [hP.queue]; exact List.mem_cons_self ..)).1
  have hlabel := visitResult_record (σ := { σ with queue := rest }) (en := en) (sd := sd) (ex := ex)
    (hP.inv.size ▸ hl)
  refine ⟨?_, ?_, visitEntry_settled hP hself⟩
  · intro w a hw hext hk ha
    obtain ⟨he, hi, -⟩ := ofPass_visitRecord (heads := envHead env) (hw.trans hlabel)
    obtain ⟨wf, hb, hwidth⟩ := hP.entryNames
    have hp : SumsPrefix σ.answers a := (keep_prefix σ.answers ex.answers).trans hk
    obtain ⟨r, hchecked, hn, hc, heq, hst, hans, hys⟩ :=
      visitStep_node hP.facts hl hP.step (hdir G I env) (hsrch G I env) wf hb hwidth he.symm hi
        (fun s hs => ha s (hp.mem s hs))
    refine ⟨r, hchecked, w, env, { σ with queue := rest }, en, sd, ex, ?_, rfl,
      hP.facts.nodes, hP.facts.claims, hP.facts.codes, hP.facts.checker, ?_, hP.facts.stated,
      hP.entry, hP.step, hP.exits, hn, hc, heq, hst, hans, hys, hi.symm, hP.inv.inSizes, ?_, ?_, ?_, ?_⟩
    · rw [hP.facts.heads]
    · exact congrFun hP.facts.heads
    · exact ⟨hext.incoming, hext.incomingEdges, hext.edges⟩
    · exact visitExits_checked hP.exits hP.inv.inSizes ⟨hext.incoming, hext.incomingEdges, hext.edges⟩
    · exact visitEntry_hereEmpty hP.inv.vacuity hP.entry
    · exact visitExits_records hP.exits hP.inv.inSizes
  · intro hs w hw
    exact visitStart_entered hP hs (hw.trans hlabel)

end Checks
end Verification.TolerantFrames
