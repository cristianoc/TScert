import Verification.Programs.TolerantFramesDriverEntry

/-! # Names in a visit's implications -/
namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore ProgramTyping

section Names
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

omit [Labels ι] in
/-- Renaming both slots of an implication uses names in the renaming list. -/
theorem renamedImplication_names {names : List Nat} {xs : List (PromiseCalls.Implication ι)}
    {y : PromiseCalls.Implication ι}
    (h : y ∈ xs.filterMap (fun x => do
      pure (⟨← names[x.test]?, ← names[x.target]?, x.type⟩ : PromiseCalls.Implication ι))) :
    y.test ∈ names ∧ y.target ∈ names := by
  obtain ⟨x, -, hx⟩ := List.mem_filterMap.mp h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨List.mem_of_getElem? ha, List.mem_of_getElem? hb⟩

omit [Labels ι] in
/-- A head's implications refer to its entry's names. -/
theorem headEntry_impNames {g : HeapKnowledge.Knowledge} {isStart : Bool} {width fresh : Nat}
    {startNames : List Nat} {argName : Option Nat} {args : List Nat} {inputs : List (Nat × Nat)}
    {xs : List (PromiseCalls.Implication ι)} {y : PromiseCalls.Implication ι}
    (h : y ∈ (SinglePass.headEntry g isStart width fresh startNames argName args inputs xs).2.1) :
    y.test ∈ (SinglePass.headEntry g isStart width fresh startNames argName args inputs xs).1.names ∧
    y.target ∈ (SinglePass.headEntry g isStart width fresh startNames argName args inputs xs).1.names :=
  renamedImplication_names h

/-- A merge's implications refer to its merged names. -/
theorem mergeState_impNames {ctx : List (Ty ι)} {preds : List SinglePass.State}
    {edges : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)} {fresh : Nat}
    {y : PromiseCalls.Implication ι} (h : y ∈ (SinglePass.mergeState G ctx preds edges fresh).implies) :
    y.test ∈ (SinglePass.mergeState G ctx preds edges fresh).state.names ∧
    y.target ∈ (SinglePass.mergeState G ctx preds edges fresh).state.names := by
  rw [mergeState_implies] at h
  unfold mergeImplies at h
  extract_lets at h
  split at h
  · cases h
  · exact renamedImplication_names (keepFirst_mem h)

/-- The entry's implications are below its counter, where incoming
implications are below the walk's counter. -/
theorem entryStart_impBelow {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    (hb : StateBelow (SinglePass.entryStart G env σ l).base (SinglePass.entryStart G env σ l).fresh)
    (hi : IncomingBelow σ.walk σ.fresh) :
    ∀ y ∈ (SinglePass.entryStart G env σ l).implies,
      y.test < (SinglePass.entryStart G env σ l).fresh ∧
      y.target < (SinglePass.entryStart G env σ l).fresh := by
  unfold SinglePass.entryStart at hb ⊢
  split at *
  · intro y hy
    obtain ⟨ht, hu⟩ := headEntry_impNames hy
    exact ⟨hb.1 _ ht, hb.1 _ hu⟩
  · split at *
    · intro y hy
      change y ∈ (σ.walk.incomingImpl[l]!).headD [] at hy
      apply hi l ((σ.walk.incomingImpl[l]!).headD []) ?_ y hy
      change (σ.walk.incomingImpl[l]!).headD [] ∈ (σ.walk.incomingImpl[l]?).getD []
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at hy ⊢
      change y ∈ ((σ.walk.incomingImpl[l]?).getD []).headD [] at hy
      cases hh : (σ.walk.incomingImpl[l]?).getD [] with
      | nil => rw [hh] at hy; cases hy
      | cons a rest => exact List.mem_cons_self ..
    · intro y hy; cases hy
    · intro y hy
      obtain ⟨ht, hu⟩ := mergeState_impNames hy
      exact ⟨hb.1 _ ht, hb.1 _ hu⟩

/-- A successful entry supplies `NamesBelow`, including the implications
and the call's start names. -/
theorem visitEntry_names {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {start : List Nat}
    (h : SinglePass.visitEntry G I env σ l = .ok en)
    (hp : ∀ q ∈ σ.walk.incoming[l]!, q.names.length = (env.claimed[l]!).context.length ∧
      StoreWF q.store ∧ StateBelow q σ.fresh)
    (hs : StartBelow env σ.fresh) (hi : IncomingBelow σ.walk σ.fresh)
    (hst : ∀ x ∈ start, x < σ.fresh) :
    StoreWF en.entry.store ∧ NamesBelow en.entry en.implies start en.fresh ∧
      en.entry.names.length ≤ (env.claimed[l]!).context.length := by
  obtain ⟨hw, hb, hf, hwidth⟩ := visitEntry_ok h hp hs
  obtain ⟨-, hfr, -, himp⟩ := visitEntry_merge h
  have hbi := entryStart_impBelow (entryStart_ok hp hs).2.1 hi
  rw [← hfr, ← himp] at hbi
  exact ⟨hw, ⟨hb.1, hb.2.1, hb.2.2, fun x hx => Nat.lt_of_lt_of_le (hst x hx) hf, hbi⟩, hwidth⟩

/-- A list of carried implications is below a counter. -/
@[nospecialize] def ImpliesBelow (xs : List (PromiseCalls.Implication ι)) (N : Nat) : Prop :=
  ∀ y ∈ xs, y.test < N ∧ y.target < N

/-- Every list in an incoming-implication array is below the counter. -/
@[nospecialize] def ImplArrayBelow (a : Array (List (List (PromiseCalls.Implication ι)))) (N : Nat) : Prop :=
  ∀ (t : Nat) xs, xs ∈ (a[t]?).getD [] → ImpliesBelow xs N

omit [Labels ι] in
/-- Prepending a bounded implication list preserves the array's bound. -/
theorem implArrayBelow_modify {a : Array (List (List (PromiseCalls.Implication ι)))} {N t : Nat}
    {xs : List (PromiseCalls.Implication ι)} (h : ImplArrayBelow a N) (hx : ImpliesBelow xs N) :
    ImplArrayBelow (a.modify t (xs :: ·)) N := by
  intro u ys hy
  rw [Array.getElem?_modify] at hy
  split at hy
  · subst u
    cases he : a[t]? with
    | none => rw [he] at hy; cases hy
    | some old =>
      rw [he] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact h t ys (by rw [he]; exact hy)
  · exact h u ys hy

/-- An edge only filters and deduplicates its incoming implications. -/
theorem edgeTransfer_impBelow {names : List Nat} {m : PointClaims.Mapping} {pushed handler outFresh : Bool}
    {entry : SinglePass.State} {result : Nat} {store : SinglePass.Store}
    {xs : List (PromiseCalls.Implication ι)} {N : Nat} (h : ImpliesBelow xs N) :
    ImpliesBelow (SinglePass.edgeTransfer names m pushed handler outFresh entry result store xs).2 N := by
  intro y hy
  exact h y (List.mem_filter.mp (keepFirst_mem hy)).1

omit [Labels ι] in
/-- A result's conditional yields name the result and an entry name. -/
theorem freshImpl_below {ys : List (PromiseCalls.Yield ι)} {names : List Nat} {result N : Nat}
    (hr : result < N) (hn : ∀ x ∈ names, x < N) :
    ImpliesBelow (ys.filterMap fun y => if y.conditional && !y.onFalse then
      (names[y.target]?).map fun tgt => ⟨result, tgt, y.type⟩ else none) N := by
  intro y hy
  obtain ⟨z, -, hz⟩ := List.mem_filterMap.mp hy
  split at hz
  · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hz
    exact ⟨hr, hn t (List.mem_of_getElem? ht)⟩
  · cases hz

/-- A successful exit preserves the bound on the incoming implications. -/
theorem exitStep_impBelow {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ysAll : List (PromiseCalls.Yield ι)} {outAll : Thunk HeapKnowledge.Knowledge}
    {acc acc' : SinglePass.ExitsDone ι G} {exi : SinglePass.Exit × Nat} {N : Nat}
    (h : SinglePass.exitStep G I env l en sd ysAll outAll acc exi = .ok acc')
    (hi : ImpliesBelow en.implies N) (hn : ∀ x ∈ en.entry.names, x < N) (hr : sd.st.result < N)
    (ha : ImplArrayBelow acc.incomingImpl N) : ImplArrayBelow acc'.incomingImpl N := by
  unfold SinglePass.exitStep at h
  extract_lets at h
  split at h
  · cases h
  rename_i tc htc
  split at h
  · cases h
  extract_lets diff u acc2 typed at h
  generalize ht : typed = T at h
  split at h
  · cases h
  rename_i acc1 et
  simp only [typed] at ht
  have hp : SameCore acc acc2 ∧ acc2.edges = acc.edges := by
    exact sameCore_unsat (sameCore_trace _ _ _) _ _
  have hc1 : SameCore acc acc1 ∧ acc1.edges = acc.edges := by
    split at ht
    · cases ht; exact hp
    · obtain ⟨h1, h2⟩ := exitTypes_core ht
      exact ⟨hp.1.trans h1, h2.trans hp.2⟩
  extract_lets freshImpl record at h
  have hf : ImpliesBelow freshImpl N := by
    unfold freshImpl
    split
    · intro y hy; cases hy
    · exact freshImpl_below hr hn
  have hj : ImpliesBelow (en.implies ++ freshImpl) N := fun y hy => by
    rcases List.mem_append.mp hy with hy | hy
    · exact hi y hy
    · exact hf y hy
  split at h
  · simp only [Except.map] at h
    split at h
    · cases h
    · rename_i a hh
      cases h
      obtain ⟨hc2, -⟩ := headExit_core hh
      change ImplArrayBelow a.incomingImpl N
      rw [hc2.incomingImpl, hc1.1.incomingImpl]
      exact ha
  · split at h
    · cases h
    rename_i acc3 hA
    obtain ⟨hc3, -⟩ := assertionExit_core hA
    split at h
    rename_i target carried hT
    cases h
    have hcar : ImpliesBelow carried N := by
      have hh : _ = carried := congrArg Prod.snd hT
      rw [← hh]
      exact edgeTransfer_impBelow hj
    apply implArrayBelow_modify _ hcar
    rw [hc3.incomingImpl, hc1.1.incomingImpl]
    exact ha

/-- Folding the exits preserves the incoming implications' bound. -/
theorem exitsFold_impBelow {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ysAll : List (PromiseCalls.Yield ι)} {outAll : Thunk HeapKnowledge.Knowledge}
    {N : Nat} (hi : ImpliesBelow en.implies N) (hn : ∀ x ∈ en.entry.names, x < N) (hr : sd.st.result < N) :
    ∀ (es : List (SinglePass.Exit × Nat)) (acc r : SinglePass.ExitsDone ι G),
      es.foldlM (SinglePass.exitStep G I env l en sd ysAll outAll) acc = .ok r →
      ImplArrayBelow acc.incomingImpl N → ImplArrayBelow r.incomingImpl N
  | [], acc, r, h, ha => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ha
  | e :: es, acc, r, h, ha => by
    rw [List.foldlM_cons] at h
    cases he : SinglePass.exitStep G I env l en sd ysAll outAll acc e with
    | error stop => rw [he] at h; cases h
    | ok a =>
      rw [he] at h
      exact exitsFold_impBelow hi hn hr es a r h (exitStep_impBelow he hi hn hr ha)

/-- The exits preserve the incoming implications' bound. -/
theorem visitExits_impBelow {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G} {ex : SinglePass.ExitsDone ι G} {N : Nat}
    (h : SinglePass.visitExits G I env σ l en sd = .ok ex)
    (hi : ImpliesBelow en.implies N) (hn : ∀ x ∈ en.entry.names, x < N) (hr : sd.st.result < N)
    (ha : IncomingBelow σ.walk N) : ImplArrayBelow ex.incomingImpl N := by
  unfold SinglePass.visitExits at h
  extract_lets node c at h
  split at h
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · exact exitsFold_impBelow hi hn hr _ _ _ h ha

/-- The claim at a label below the environment's bound gives its pass context. -/
theorem EnvFacts.context {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    (hE : EnvFacts c env) {l : Nat} (hl : l < env.n) : (env.claimed[l]!).context = passCtx c l := by
  unfold passCtx
  rw [hE.claims, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  have hc : l < c.claims.toArray.size := by rw [← hE.claims, hE.claimed]; exact hl
  rw [Array.getElem?_eq_getElem hc, List.getElem?_eq_getElem (by simpa using hc)]
  simp

/-- The invariant supplies every premise of the entry's name-bound theorem. -/
theorem VisitParts.entryNames {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    {σ : SinglePass.WalkState ι G} {l : Nat} {rest : List Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ex : SinglePass.ExitsDone ι G}
    (hP : VisitParts c env σ l rest en sd ex) :
    StoreWF en.entry.store ∧ NamesBelow en.entry en.implies (List.range c.inputs.length) en.fresh ∧
      en.entry.names.length ≤ (env.claimed[l]!).context.length := by
  have hl := (hP.inv.queue l (by rw [hP.queue]; exact List.mem_cons_self ..)).1
  apply visitEntry_names hP.entry _ hP.inv.startBelow hP.inv.impBelow hP.inv.startFresh
  intro q hq
  have hp := hP.inv.push l q (by
    unfold incS
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at hq
    exact hq)
  exact ⟨(hP.facts.context hl).symm ▸ hp.1, hp.2⟩

/-- A visit preserves the invariant's incoming implication bound. -/
theorem visitsImplications (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I)
    (env : SinglePass.WalkEnv ι G I) (σ : SinglePass.WalkState ι G) (l : Nat) (rest : List Nat)
    (en : SinglePass.Entered ι) (sd : SinglePass.StepDone ι G) (ex : SinglePass.ExitsDone ι G)
    (hP : VisitParts c env σ l rest en sd ex) :
    IncomingBelow (visitResult { σ with queue := rest } l en sd ex).walk sd.fresh := by
  obtain ⟨hw, hb, -⟩ := hP.entryNames
  obtain ⟨⟨ms, stats, hs⟩, -, hf⟩ := visitStep_ok hP.step
  obtain ⟨-, -, hr, hle⟩ := checkedStep_store (stepRun_ok hs) hw hb.1 hb.2.1
  have hsd : sd.st.fresh ≤ sd.fresh := by rw [hf]; split <;> omega
  have hfr := stepFresh hP
  exact visitExits_impBelow hP.exits
    (fun y hy => ⟨Nat.lt_of_lt_of_le (hb.2.2.2.2 y hy).1 (by omega),
      Nat.lt_of_lt_of_le (hb.2.2.2.2 y hy).2 (by omega)⟩)
    (fun x hx => Nat.lt_of_lt_of_le (hb.1 x hx) (by omega)) (by omega)
    (fun t xs hx y hy => ⟨Nat.lt_of_lt_of_le (hP.inv.impBelow t xs hx y hy).1 hfr,
      Nat.lt_of_lt_of_le (hP.inv.impBelow t xs hx y hy).2 hfr⟩)

end Names
end Verification.TolerantFrames
