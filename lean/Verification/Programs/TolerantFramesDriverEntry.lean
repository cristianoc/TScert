import Verification.Programs.TolerantFramesDriverVisitRest

/-! # Tolerant frames: a visit's entry and step states, well-formed and below the counter

A visit's entry (`visitEntry`: `entryStart`, then `withStated`) has a
well-formed store, is below its fresh counter and has at most its
context's width, where the states that came in meet `PushOk` and the
start's names and the promised input's name are below the walk's counter
(`entryStart_ok`, `visitEntry_ok`). A checked step keeps its store
well-formed and below its own counter, with its result below it
(`checkedStep_store`). So every state an exit pushes is well-formed and
below the step's fresh counter, and meets `PushOk` where the exit's
mapping has the target's width (`exitsPushOk_of`, under `ExitsWidth`). -/

namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore

section Stores
variable {ι : Type}

/-- **The written facts keep the facts below the counter** where the
state's names are below it: each added fact names the state's names. -/
theorem withWritten_below {req : Option HeapKnowledge.Knowledge} {e : SinglePass.State} {N : Nat}
    (hn : ∀ x ∈ e.names, x < N) (hs : FactsBelow e.store N) : FactsBelow (withWritten req e).store N := by
  cases req with
  | none => exact hs
  | some k =>
    refine foldl_inv (fun s => FactsBelow s N) _ _ _ hs fun a _ st hst => ?_
    split
    · rename_i b hb
      refine add_below hst fun y hy => ?_
      obtain ⟨x, -, hx⟩ := atom_rename_names hb y hy
      exact hn y (List.mem_of_getElem? hx)
    · exact hst

/-- **A head's given state is well-formed**: facts added to the empty
store (`add_wf`). -/
theorem headEntry_wf {g : HeapKnowledge.Knowledge} {isStart : Bool} {width fresh : Nat} {startNames : List Nat}
    {argName : Option Nat} {argSlots : List Nat} {inputSlots : List (Nat × Nat)}
    {implies : List (PromiseCalls.Implication ι)} :
    StoreWF (SinglePass.headEntry g isStart width fresh startNames argName argSlots inputSlots implies).1.store := by
  simp only [SinglePass.headEntry, SinglePass.timedKind]
  refine foldl_inv StoreWF _ _ _ storeWF_empty fun a _ st hst => ?_
  split
  · exact add_wf hst _
  · exact hst

theorem headEntry_names_length {g : HeapKnowledge.Knowledge} {isStart : Bool} {width fresh : Nat}
    {startNames : List Nat} {argName : Option Nat} {argSlots : List Nat} {inputSlots : List (Nat × Nat)}
    {implies : List (PromiseCalls.Implication ι)} :
    (SinglePass.headEntry g isStart width fresh startNames argName argSlots inputSlots implies).1.names.length =
      width := by
  simp [SinglePass.headEntry]

theorem factsBelow_mono {s : SinglePass.Store} {a b : Nat} (h : FactsBelow s a) (hab : a ≤ b) : FactsBelow s b :=
  fun x hx y hy => Nat.lt_of_lt_of_le (h x hx y hy) hab

theorem stateBelow_mono {s : SinglePass.State} {a b : Nat} (h : StateBelow s a) (hab : a ≤ b) : StateBelow s b :=
  ⟨fun x hx => Nat.lt_of_lt_of_le (h.1 x hx) hab, fun x hx y hy => Nat.lt_of_lt_of_le (h.2.1 x hx y hy) hab,
    fun x hx => Nat.lt_of_lt_of_le (h.2.2 x hx) hab⟩

end Stores

section Step
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- **A checked step's store well-formed and below its counter**, its
result below it: a copy keeps the entry's store and names a slot's name;
a step applies its delta (`applyDelta_wf`, `applyDelta_below`, renaming
by `passBack` into the entry's names and the result) to the entry's store
or to its heap-free part (`dropHeap_cover`, `dropHeap_below`). -/
theorem checkedStep_store {pool fuel suggestions index codes aliases pc undefTy l} {node : Node}
    {c : PointClaim ι} {entry : SinglePass.State} {ms : List Nat} {fresh : Nat} {answers : Answered G}
    {st : SinglePass.Stepped ι} {stats : SinglePass.StepStats} {ans : Answered G}
    (h : SinglePass.checkedStep G I pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh
      answers = (.ok st, stats, ans))
    (w : StoreWF entry.store) (hn : ∀ x ∈ entry.names, x < fresh) (hs : FactsBelow entry.store fresh) :
    StoreWF st.store ∧ FactsBelow st.store st.fresh ∧ st.result < st.fresh ∧ fresh ≤ st.fresh := by
  have hle := checkedStep_fresh h
  rcases checkedStep_ok h with ⟨x, hc, hr, hstore, hfr, -⟩ | ⟨-, effect, a0, a1, -, -, hacc, -⟩
  · obtain ⟨i, -, -, hx⟩ := copiedOf_some hc
    rw [hstore, hfr, hr]
    exact ⟨w, hs, hn x (List.mem_of_getElem? hx), Nat.le_refl _⟩
  · obtain ⟨out, pre, -, -, hres, hfresh, -, -, hpres, hwrit⟩ := hacc
    have hrl : st.result < st.fresh := by
      rw [hres, hfresh]
      rcases resultOf_cases node.expression entry.names fresh with ⟨_, -, hx, hf⟩ | ⟨hr, hf⟩
      · rw [hf]; exact hn _ (List.mem_of_getElem? hx)
      · rw [hr, hf]; exact Nat.lt_succ_self _
    have hn' : ∀ x ∈ entry.names, x < st.fresh := fun x hx => Nat.lt_of_lt_of_le (hn x hx) hle
    have hs' := factsBelow_mono hs hle
    refine ⟨?_, ?_, hrl, hle⟩ <;> cases hp : passPreserving G I (jOf c node) (kOf G c entry ms (wholeOf node.expression))
      effect codes a0.summaries.toList
    · obtain ⟨out', -, -, hst, -⟩ := hwrit hp
      rw [hst]
      exact applyDelta_wf (dropHeap_cover w _).1 _ _ _ _
    · obtain ⟨hst, -⟩ := hpres hp
      rw [hst]
      exact applyDelta_wf w _ _ _ _
    · obtain ⟨out', -, -, hst, -⟩ := hwrit hp
      rw [hst]
      exact applyDelta_below (dropHeap_below w hs' _) _ _ _
        (passBack_below hn' hrl (materialize_table_keys _ _ _ _ _))
    · obtain ⟨hst, -⟩ := hpres hp
      rw [hst]
      exact applyDelta_below hs' _ _ _ (passBack_below hn' hrl (materialize_table_keys _ _ _ _ _))

end Step

section Entry
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- `withStated` is the written facts at a node other than a head. -/
theorem withStated_eq (env : SinglePass.WalkEnv ι G I) (l : Nat) (e : SinglePass.State) :
    SinglePass.withStated env l e = if env.isHead[l]! then e else withWritten env.stated[l]! e := by
  unfold SinglePass.withStated
  cases env.isHead[l]! <;> simp only [Bool.not_false, Bool.not_true, ite_true, ite_false, Bool.false_eq_true]
  cases env.stated[l]! <;> rfl

/-- **The entry with its written facts**: well-formed, below the counter
and of the same names where the state is. -/
theorem withStated_ok {env : SinglePass.WalkEnv ι G I} {l : Nat} {e : SinglePass.State} {N : Nat}
    (w : StoreWF e.store) (hb : StateBelow e N) :
    StoreWF (SinglePass.withStated env l e).store ∧ StateBelow (SinglePass.withStated env l e) N ∧
      (SinglePass.withStated env l e).names = e.names := by
  rw [withStated_eq]
  split
  · exact ⟨w, hb, rfl⟩
  · refine ⟨withWritten_wf w, ⟨?_, withWritten_below hb.1 hb.2.1, ?_⟩, withWritten_names _ _⟩
    · rw [withWritten_names]; exact hb.1
    · rw [withWritten_fresh]; exact hb.2.2

/-- `entryStart`'s cases: a head's given state, one state that came in, none,
or the merge of those that came in. -/
theorem entryStart_cases (env : SinglePass.WalkEnv ι G I) (σ : SinglePass.WalkState ι G) (l : Nat) :
    (∃ g, env.given[l]! = some g ∧
      (SinglePass.entryStart G env σ l).base = (SinglePass.headEntry g (l == env.start && !env.startEntered)
        (env.claimed[l]!).context.length σ.fresh env.startNames env.argName ((env.givenArgs[l]?).getD [])
        ((env.givenInputs[l]?).getD []) ((env.givenImplies[l]?).getD [])).1 ∧
      (SinglePass.entryStart G env σ l).fresh = (SinglePass.headEntry g (l == env.start && !env.startEntered)
        (env.claimed[l]!).context.length σ.fresh env.startNames env.argName ((env.givenArgs[l]?).getD [])
        ((env.givenInputs[l]?).getD []) ((env.givenImplies[l]?).getD [])).2.2) ∨
    ((∃ q, σ.walk.incoming[l]! = [q] ∧ (SinglePass.entryStart G env σ l).base = q ∧
        (SinglePass.entryStart G env σ l).fresh = σ.fresh) ∨
      ((SinglePass.entryStart G env σ l).base = { names := [] } ∧ (SinglePass.entryStart G env σ l).fresh = σ.fresh) ∨
      (∃ q rest, σ.walk.incoming[l]! = q :: rest ∧
        (SinglePass.entryStart G env σ l).base =
          (SinglePass.mergeState G (env.claimed[l]!).context (q :: rest) σ.walk.incomingEdges[l]! σ.fresh).state ∧
        (SinglePass.entryStart G env σ l).fresh =
          (SinglePass.mergeState G (env.claimed[l]!).context (q :: rest) σ.walk.incomingEdges[l]! σ.fresh).fresh)) := by
  unfold SinglePass.entryStart
  split
  · rename_i g hg
    exact .inl ⟨g, hg, rfl, rfl⟩
  · refine .inr ?_
    split
    · rename_i q hq
      exact .inl ⟨q, hq, rfl, rfl⟩
    · exact .inr (.inl ⟨rfl, rfl⟩)
    · rename_i q rest _ hq
      exact .inr (.inr ⟨q, rest, hq, rfl, rfl⟩)

/-- **A node's entry before its written facts** (`entryStart`): its store
well-formed, below its counter, the counter not below the walk's, at most
the node's width of names, where the states that came in have the node's
width, well-formed stores and are below the walk's counter and the start's
names are (`headEntry_below`, `mergeState_below`, `mergeState_wf`). -/
theorem entryStart_ok {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    (hpreds : ∀ q ∈ σ.walk.incoming[l]!, q.names.length = (env.claimed[l]!).context.length ∧ StoreWF q.store ∧
      StateBelow q σ.fresh)
    (hstart : StartBelow env σ.fresh) :
    StoreWF (SinglePass.entryStart G env σ l).base.store ∧
      StateBelow (SinglePass.entryStart G env σ l).base (SinglePass.entryStart G env σ l).fresh ∧
      σ.fresh ≤ (SinglePass.entryStart G env σ l).fresh ∧
      (SinglePass.entryStart G env σ l).base.names.length ≤ (env.claimed[l]!).context.length := by
  have hfr := entryStart_fresh hpreds
  refine ⟨?_, ?_, hfr, ?_⟩ <;>
    rcases entryStart_cases env σ l with ⟨g, -, hb, hf⟩ | ⟨q, hq, hb, hf⟩ | ⟨hb, hf⟩ | ⟨q, rest, hq, hb, hf⟩ <;>
    rw [hb] <;> (try rw [hf]) <;> (try rw [hf] at hfr)
  · exact headEntry_wf
  · exact (hpreds q (by rw [hq]; exact List.mem_singleton_self _)).2.1
  · exact storeWF_empty
  · exact (mergeState_wf (G := G) (List.cons_ne_nil _ _) (fun q' hq' => (hpreds q' (hq ▸ hq')).1)
      (fun q' hq' => (hpreds q' (hq ▸ hq')).2.1) (fun q' hq' => (hpreds q' (hq ▸ hq')).2.2)).1
  · refine headEntry_below rfl (fun x hx => Nat.lt_of_lt_of_le (hstart.1 x hx) hfr)
      (fun a ha => Nat.lt_of_lt_of_le (hstart.2.1 a ha) hfr) fun i hi => ?_
    unfold SinglePass.headEntry
    dsimp only
    split
    · rename_i hs
      have hl : l = env.start := by simp only [Bool.and_eq_true, beq_iff_eq] at hs; exact hs.1
      subst hl
      exact hstart.2.2 i hi
    · omega
  · exact (hpreds q (by rw [hq]; exact List.mem_singleton_self _)).2.2
  · exact ⟨fun x hx => by simp at hx, fun a ha => by simp [storeAll, SinglePass.Store.toList, valsOf] at ha,
      fun x hx => by simp at hx⟩
  · exact mergeState_below (List.cons_ne_nil _ _) (fun q' hq' => (hpreds q' (hq ▸ hq')).1)
      (fun q' hq' => (hpreds q' (hq ▸ hq')).2.1) (fun q' hq' => (hpreds q' (hq ▸ hq')).2.2)
  · exact Nat.le_of_eq headEntry_names_length
  · exact Nat.le_of_eq (hpreds q (by rw [hq]; exact List.mem_singleton_self _)).1
  · exact Nat.zero_le _
  · rw [mergeState_state]
    exact Nat.le_of_eq (by rw [Array.length_toList]; exact (mergeSlots_inv _ _ _).size)

/-- **A node's entry that returns** (`visitEntry`): well-formed, below its
counter, the counter not below the walk's, at most the node's width of
names (`entryStart_ok`, `withStated_ok`). -/
theorem visitEntry_ok {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} (h : SinglePass.visitEntry G I env σ l = .ok en)
    (hpreds : ∀ q ∈ σ.walk.incoming[l]!, q.names.length = (env.claimed[l]!).context.length ∧ StoreWF q.store ∧
      StateBelow q σ.fresh)
    (hstart : StartBelow env σ.fresh) :
    StoreWF en.entry.store ∧ StateBelow en.entry en.fresh ∧ σ.fresh ≤ en.fresh ∧
      en.entry.names.length ≤ (env.claimed[l]!).context.length := by
  obtain ⟨-, hf, he, -⟩ := visitEntry_merge h
  obtain ⟨w, hb, hfr, hw⟩ := entryStart_ok (G := G) (l := l) hpreds hstart
  obtain ⟨w', hb', hn⟩ := withStated_ok (env := env) (l := l) w hb
  rw [he, hf]
  exact ⟨w', hb', hfr, hn ▸ hw⟩

end Entry

section Exits
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- **A step that returns names its throw by the step's counter**
(`visitStep`), the visit's counter one past it at a node with a handler. -/
theorem visitStep_thrown {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G} (h : SinglePass.visitStep G I env σ l en = .ok sd) :
    sd.thrown = sd.st.fresh := by
  unfold SinglePass.visitStep at h
  split at h
  · cases h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | (cases h; rfl) | cases h

/-- A node's handler exit is there only where the node has a handler. -/
theorem ofNode_handler {node : Node} {e : SinglePass.Exit} (hm : e ∈ SinglePass.Exit.ofNode node)
    (hh : e.isHandler = true) : node.handler.isSome = true := by
  unfold SinglePass.Exit.ofNode at hm
  rcases List.mem_append.mp hm with hm | hm
  · split at hm <;> simp at hm <;>
      first | (subst hm; cases hh) | (rcases hm with rfl | rfl <;> cases hh)
  · cases hn : node.handler with
    | none => rw [hn] at hm; simp at hm
    | some _ => rfl

/-- The names an exit carries from (`exitStep`): the throw's name and the
entry's at a handler, the result and the entry's where it pushes, the
entry's otherwise. -/
def exitNames (en : SinglePass.Entered ι) (sd : SinglePass.StepDone ι G) (e : SinglePass.Exit) : List Nat :=
  if e.isHandler then sd.thrown :: en.entry.names else if e.pushed then sd.st.result :: en.entry.names
  else en.entry.names

variable (ι) in
/-- **(Named hypothesis, pass change W9) Each exit's mapping has its
target's width**: no mapping, the source's names as many as the target's
context; a mapping, as many slots as the target's context, each a source
slot. -/
def ExitsWidth : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) env σ l rest en sd ex,
    VisitParts c env σ l rest en sd ex → ∀ e ∈ SinglePass.Exit.ofNode env.nodes[l]!,
      match e.target.mapping with
      | none => (exitNames en sd e).length = (passCtx c e.target.label).length
      | some slots => slots.length = (passCtx c e.target.label).length ∧ ∀ j ∈ slots, j < (exitNames en sd e).length

/-- **(`exitsPushOk_of`) Each state an exit pushes meets `PushOk`** where
its mapping has the target's width: the entry well-formed and below its
counter (`visitEntry_ok`, the states that came in meeting `PushOk` and the
start's names below the walk's counter by the invariant), the step's store
well-formed and below the step's counter with its result
(`checkedStep_store`), the throw's name the step's counter, below the
visit's (`visitStep_thrown`), so `pushOk_of_exit`. -/
theorem exitsPushOk_of (hw : ExitsWidth ι) : ExitsPushOk ι := by
  intro G I c env σ l rest en sd ex hP e he imp
  have hln : l < env.n := (hP.inv.queue l (by rw [hP.queue]; exact List.mem_cons_self ..)).1
  have hctx : (env.claimed[l]!).context = passCtx c l := by
    unfold passCtx
    rw [hP.facts.claims, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    have hl : l < c.claims.toArray.size := by rw [← hP.facts.claims, hP.facts.claimed]; exact hln
    rw [Array.getElem?_eq_getElem hl, List.getElem?_eq_getElem (by simpa using hl)]
    simp
  obtain ⟨wE, bE, -, -⟩ := visitEntry_ok (σ := { σ with queue := rest }) hP.entry (fun q hq => by
      have hp := hP.inv.push l q (by
        unfold incS
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at hq
        exact hq)
      exact ⟨hctx ▸ hp.1, hp.2.1, hp.2.2⟩) hP.inv.startBelow
  obtain ⟨⟨ms, stats, hrun⟩, -, hsf⟩ := visitStep_ok hP.step
  obtain ⟨wS, bS, hr, hle⟩ := checkedStep_store (stepRun_ok hrun) wE bE.1 bE.2.1
  have hth := visitStep_thrown hP.step
  have hsd : sd.st.fresh ≤ sd.fresh := by rw [hsf]; split <;> omega
  have hlt : ∀ x, x < en.fresh → x < sd.fresh := fun x hx => by omega
  have hnames : ∀ x ∈ exitNames en sd e, x < sd.fresh := by
    intro x hx
    unfold exitNames at hx
    split at hx
    · rename_i hh
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hth, hsf, if_pos (ofNode_handler he hh)]; exact Nat.lt_succ_self _
      · exact hlt x (bE.1 x hx)
    · split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact hlt x (bE.1 x hx)
      · exact hlt x (bE.1 x hx)
  unfold exitPushed
  exact pushOk_of_exit (hw G I c env σ l rest en sd ex hP e he) wE wS
    (factsBelow_mono bE.2.1 (by omega)) (factsBelow_mono bS hsd) (by omega) hnames
    (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact hlt x (bE.1 x hx))
    (fun x hx => hlt x (bE.2.2 x hx)) (by omega)

end Exits

end Verification.TolerantFrames
