import Verification.Programs.TolerantFramesStepLink

/-! # Tolerant frames: the step theorem about `checkedStep`

`checkedStep_ok` reads an accepted `SinglePass.checkedStep` as its
conditions; this module composes those conditions with the selected output,
the preserving and writing judgments, the materialization and the delta into
one statement of the step at a node, in the form `NodesChecked` consumes: a
local judgment of the node's term, and on each exit the action of the step's
effect, the residual budget, the value's type, the rule's output and the
state after the step (`checkedStep_sound`).

Named hypotheses, stated as definitions: the search keeps its table of read
summaries checked (`DirectKeepsSummaries`, `SearchKeepsSummaries`), and the
pass's next fresh name is above every name of the entry state
(`NamesBelow`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section StepSound
variable {ι : Type}

/-! ## Named hypotheses -/

/-- Every name the state, the start names and the implications mention is
below `next` (the part of `StateWF.below` a result name needs, with the start
names and the implications). -/
def NamesBelow (st : SinglePass.State) (I : List (PromiseCalls.Implication ι)) (start : List Nat) (next : Nat) :
    Prop :=
  (∀ x ∈ st.names, x < next) ∧ (∀ a ∈ storeAll st.store, ∀ x ∈ a.names, x < next) ∧ (∀ x ∈ st.fresh, x < next) ∧
    (∀ x ∈ start, x < next) ∧ ∀ y ∈ I, y.test < next ∧ y.target < next

variable [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- **(Hypothesis) The direct call keeps the summary table checked**: every
summary of the answers after `directCall` passes `checkReadSummary` where
every one before did. `summaryUsing` checks a summary before appending it
(`CertificateProducer.lean` 625–651); no theorem states it of the search. -/
def DirectKeepsSummaries (G : NormalGraph ι) (images : InstanceImageCheck G) (undefTy : Option (Ty ι)) : Prop :=
  ∀ Γ t A adm (a : Answered G), SummariesSound G images a.summaries.toList →
    SummariesSound G images (directCall G images Γ t A adm undefTy a).2.summaries.toList

variable [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- **(Hypothesis) The search keeps the summary table checked**, as
`DirectKeepsSummaries` for `expressionEffectUsing`. -/
def SearchKeepsSummaries (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (suggestions : List (Sequent ι)) (index : KnownIndex ι) (codes : CodeEntry ι → Bool) (aliases : List (ι × ι))
    (checker : HeapExpressionRules.Checker G images) : Prop :=
  ∀ j k own adm (a : Answered G), SummariesSound G images a.summaries.toList →
    SummariesSound G images
      (expressionEffectUsing G images pool fuel j k suggestions index codes aliases checker own adm a).2.summaries.toList

/-! ## The valuation after a step -/

theorem set_keeps {η : Env} {r x : Nat} {v : Tm} (h : x < r ∨ η r = v) : Env.set η r v x = η x := by
  unfold Env.set
  split
  · rename_i hx
    subst hx
    rcases h with h | h
    · exact absurd h (Nat.lt_irrefl _)
    · exact h.symm
  · rfl

/-- Where the result's name is new or already holds the value, setting it
keeps every name the state mentions. -/
theorem set_agree {st : SinglePass.State} {I : List (PromiseCalls.Implication ι)} {start : List Nat} {η : Env}
    {r : Nat} {v : Tm} (hk : NamesBelow st I start r ∨ η r = v) :
    (∀ x ∈ st.names, Env.set η r v x = η x) ∧
    (∀ a ∈ storeAll st.store, ∀ x ∈ a.names, Env.set η r v x = η x) ∧
    (∀ x ∈ st.fresh, Env.set η r v x = η x) ∧ (∀ x ∈ start, Env.set η r v x = η x) ∧
    ∀ y ∈ I, Env.set η r v y.test = η y.test ∧ Env.set η r v y.target = η y.target := by
  rcases hk with ⟨h1, h2, h3, h4, h5⟩ | hv
  · exact ⟨fun x hx => set_keeps (.inl (h1 x hx)), fun a ha x hx => set_keeps (.inl (h2 a ha x hx)),
      fun x hx => set_keeps (.inl (h3 x hx)), fun x hx => set_keeps (.inl (h4 x hx)),
      fun y hy => ⟨set_keeps (.inl (h5 y hy).1), set_keeps (.inl (h5 y hy).2)⟩⟩
  · exact ⟨fun _ _ => set_keeps (.inr hv), fun _ _ _ _ => set_keeps (.inr hv), fun _ _ => set_keeps (.inr hv),
      fun _ _ => set_keeps (.inr hv), fun _ _ => ⟨set_keeps (.inr hv), set_keeps (.inr hv)⟩⟩

/-- **The state after a step**, from any store whose facts hold at the
valuation naming the result: the pushed slots named, the implications, fresh
and start names carried along an admissible transition. -/
theorem stateHolds_pushed {G : NormalGraph ι} {st : SinglePass.State} {I : List (PromiseCalls.Implication ι)}
    {start : List Nat} {E ρ η : Env} {m : Nat} {s s' : IndexedHeap} {r : Nat} {v : Tm} {store : Store}
    (hn : SlotsNamed st.names ρ η) (hI : PromiseCalls.ImpliesOk G I η s.n s.W)
    (hF : ∀ x ∈ st.fresh, FreshAt m (η x)) (hst : ∀ q x, start[q]? = some x → η x = E q)
    (ha : Admissible s s') (hk : NamesBelow st I start r ∨ η r = v)
    (hstore : StoreOk store (Env.set η r v) s'.h) :
    StateHolds G ⟨r :: st.names, store, st.fresh⟩ I start E (push v ρ) m s' := by
  obtain ⟨g1, -, g3, g4, g5⟩ := set_agree hk
  refine ⟨Env.set η r v, fun i x hx => ?_, hstore, ?_, ?_, ?_⟩
  · cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx; simp [Env.set, push]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hx
      rw [g1 x (List.mem_of_getElem? hx)]; exact hn j x hx
  · intro y hy ht
    obtain ⟨e1, e2⟩ := g5 y hy
    rw [e2]; rw [e1] at ht
    exact impliesOk_admissible ha hI y hy ht
  · intro x hx; rw [g3 x hx]; exact hF x hx
  · intro q x hq; rw [g4 x (List.mem_of_getElem? hq)]; exact hst q x hq

/-- **The state on a throw**: the entry's names and its facts reading no heap
(`Store.dropHeap` keeping nothing, the store the handler edge starts from), at
the entry environment, after an admissible transition. -/
theorem stateHolds_throw {G : NormalGraph ι} {st : SinglePass.State} {I : List (PromiseCalls.Implication ι)}
    {start : List Nat} {E ρ : Env} {m : Nat} {s s' : IndexedHeap} (hS : StateHolds G st I start E ρ m s)
    (w : StoreWF st.store) (ha : Admissible s s') :
    StateHolds G ⟨st.names, st.store.dropHeap (fun _ => false), st.fresh⟩ I start E ρ m s' := by
  obtain ⟨η, hn, hst, hI, hF, hs⟩ := hS
  refine ⟨η, hn, fun a ha' => ?_, impliesOk_admissible ha hI, hF, hs⟩
  obtain ⟨-, hcov⟩ := dropHeap_cover w (fun _ => false)
  obtain ⟨hx, hk | hfr⟩ := hcov a ha'
  · cases hk
  · exact atomHolds_heapFree hfr (hst a hx) s'.h

/-- The table `materialize` returns is a slot table of the state's names. -/
theorem materialize_table (st : SinglePass.State) (d : Nat) (ms : List Nat) (whole : Bool) :
    ∃ want, (materialize st d ms whole).2.2 = SinglePass.slotTable st.names want whole := by
  rw [materialize_eq]; exact materializeFrom_table

/-- **A preserving step's store holds after the step**: every fact of the
entry's store holds after an action keeping the heap, at the valuation naming
the result; the delta adds the rule's output read back to names. -/
theorem preserving_store {st : SinglePass.State} {I : List (PromiseCalls.Implication ι)} {start : List Nat}
    {ρ η : Env} {h' : Heap} {r : Nat} {v : Tm} {d : Nat} {ms : List Nat} {whole : Bool}
    {out : HeapKnowledge.Knowledge} (hn : SlotsNamed st.names ρ η) (hk : NamesBelow st I start r ∨ η r = v)
    (hS : StoreOk st.store η h') (hout : HeapKnowledge.Holds out (push v ρ) h') :
    StoreOk (applyDelta st.store (materialize st d ms whole).2.1 out true
      (passBack (materialize st d ms whole).2.2 st.names r)) (Env.set η r v) h' := by
  obtain ⟨g1, g2, -⟩ := set_agree hk
  obtain ⟨want, hT⟩ := materialize_table st d ms whole
  rw [hT]
  refine applyDelta_preserving (fun a ha => ?_) hout
    (passBack_ok hn (by simp [Env.set]) g1)
  exact (atomHolds_congr fun x hx => (g2 a ha x hx).symm).mp (hS a ha)

/-- **A writing step's store holds after the step**: the entry's heap-free
facts hold in every heap, the handed facts by the rule's output over every
fact (`applyDelta_dropHeap`). -/
theorem writing_store {st : SinglePass.State} {I : List (PromiseCalls.Implication ι)} {start : List Nat}
    {ρ η : Env} {h h' : Heap} {r : Nat} {v : Tm} {d : Nat} {ms : List Nat}
    {out : HeapKnowledge.Knowledge} (w : StoreWF st.store) (hn : SlotsNamed st.names ρ η)
    (hk : NamesBelow st I start r ∨ η r = v)
    (hS : StoreOk st.store η h) (hout : HeapKnowledge.Holds out (push v ρ) h') :
    StoreOk (applyDelta (st.store.dropHeap (handedSet (materialize st d ms true).2.1).contains)
      (materialize st d ms true).2.1 out true
      (passBack (materialize st d ms true).2.2 st.names r)) (Env.set η r v) h' := by
  obtain ⟨g1, g2, -⟩ := set_agree hk
  have hn' : SlotsNamed st.names ρ (Env.set η r v) := fun i x hx => by rw [g1 x (List.mem_of_getElem? hx)]; exact hn i x hx
  obtain ⟨want, hT⟩ := materialize_table st d ms true
  refine applyDelta_dropHeap (f := fun n => (materialize st d ms true).2.2.get? n) w
    (fun x hx hfr => (atomHolds_congr fun y hy => (g2 x hx y hy).symm).mp (atomHolds_heapFree hfr (hS x hx) h'))
    (fun x b hp => (materializeFrom_pairs hp).2) (fun x i hx => ?_) hout ?_
  · rw [hT] at hx; exact table_named hn' x i hx
  · rw [hT]; exact passBack_ok hn (by simp [Env.set]) g1

/-! ## The judgments at the pass's two sums -/

variable [DecidableEq ι]

/-- **A preserving step keeps the heap** with the call layers' test read at
the summaries `sums₀` (`SinglePass.lean` 1251) and the selection at `sums`. -/
theorem passPreserving_keeps_two {G : NormalGraph ι} {images : InstanceImageCheck G} {pc : PassChecker G images}
    {j : Sequent ι} {kE out : HeapKnowledge.Knowledge} {e : HeapExpressionRules.StepEvidence ι}
    {codes : CodeEntry ι → Bool} {sums₀ sums : List (ReadSummary ι)}
    (hpres : passPreserving G images j kE e codes sums₀ = true)
    (hok : pc.selectChecks = false → passTreeOk G images kE codes sums e = true)
    (hsel : (pc.checker.select j kE e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums₀ : SummariesSound G images sums₀) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) : KeepsPost G j ρ n W h := by
  simp only [passPreserving, Bool.or_eq_true] at hpres
  rcases hpres with hc | hp
  · exact callKeepsHeap_keeps hc hcodes hsums₀ he hk hw hh
  · exact passPreserving_keeps_pass (by simp [passPreserving, hp]) hok hsel hcodes hsums he hk hw hh

/-- **A preserving step's judgment** at the pass's two sums: normal exit
keeping the heap with the selected output, throw within `top`. -/
theorem preserving_judgment_two {G : NormalGraph ι} {images : InstanceImageCheck G} {pc : PassChecker G images}
    {j : Sequent ι} {kE out : HeapKnowledge.Knowledge} {e : HeapExpressionRules.StepEvidence ι}
    {codes : CodeEntry ι → Bool} {sums₀ sums : List (ReadSummary ι)}
    (hpres : passPreserving G images j kE e codes sums₀ = true)
    (hok : pc.selectChecks = false → passTreeOk G images kE codes sums e = true)
    (hsel : (pc.checker.select j kE e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums₀ : SummariesSound G images sums₀) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G j.type)
      (fun h' v => Footprints.Closed.empty.Holds h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => Footprints.Closed.top.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) := by
  have hboth := cross_upto n (fun _ _ _ _ _ _ _ _ hb _ => hb) W W h _ hh hh
    (passPreserving_keeps_two hpres hok hsel hcodes hsums₀ hsums he hk hw hh)
    (pass_select_sound hok hsel hcodes hsums he hk hw hh)
  exact SafePostExc.weaken (fun _ _ hq => ⟨hq.2.1.1, hq.2.2⟩)
    (fun _ hq => ⟨Footprints.Closed.holds_top.mpr hq, trivial⟩) (safePost_grow h.length (Nat.le_refl _) hboth)

/-! ## The copy -/

theorem copiedOf_some {G : NormalGraph ι} {c : PointClaim ι} {entry : SinglePass.State} {t : Tm} {x : Nat}
    (h : copiedOf G c entry t = some x) :
    ∃ i, t = .var i ∧ c.context[i]? = some c.type ∧ entry.names[i]? = some x := by
  unfold copiedOf at h
  split at h
  · rename_i i
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Option.any_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨A, hA, rfl⟩, -⟩ := hc
      exact ⟨i, rfl, hA, h⟩
    · cases h
  · cases h

theorem holds_empty {ρ : Env} {h : Heap} : HeapKnowledge.Holds {} ρ h := by
  refine ⟨?_, ?_, ?_, ?_, HeapKnowledge.elemsHolds_nil _ _, HeapKnowledge.indexHolds_nil _ _⟩ <;>
    simp [HeapFacts.Holds, HeapKnowledge.ValueHolds, HeapLinks.Holds, HeapSeparation.Holds]

theorem resultOf_cases (t : Tm) (names : List Nat) (fresh : Nat) :
    (∃ i, t = .var i ∧ names[i]? = some (resultOf t names fresh).1 ∧ (resultOf t names fresh).2 = fresh) ∨
      ((resultOf t names fresh).1 = fresh ∧ (resultOf t names fresh).2 = fresh + 1) := by
  unfold resultOf
  split
  · rename_i i
    split
    · rename_i x hx; exact .inl ⟨i, rfl, hx, rfl⟩
    · exact .inr ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-! ## The step's exits -/

/-- **A step's exits**: a local judgment of the node's term `t` at the
step's effects `cn`, `ce` with the rule's output `out` at the pushed slots,
and, on each run with budget left, the normal exit an action of `cn` with the
residual budget, the value's type, `out` and the assertion `Fn` at the pushed
environment, the throw an action of `ce` with the raised value closed and of
the exception family and `Fe` at the node's environment. -/
def StepExits (G : NormalGraph ι) (A : Ty ι) (cn ce : Footprints.Closed) (t : Tm) (out : HeapKnowledge.Knowledge)
    (Fn Fe : Assertion) (ρ : Env) (m : Nat) (s : IndexedHeap) : Prop :=
  SafePostExc (excOf G) (meaning G A) (fun h' v => cn.Holds s.h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => ce.Holds s.h h' ∧ True) s.n s.W s.h (instantiate 0 ρ t) ∧
    ∀ k h' t', Steps k s.h (instantiate 0 ρ t) h' t' → k < s.n →
      (isVal t' = true → ∃ s' : IndexedHeap, Action cn.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        meaning G A s'.n s'.W t' ∧ HeapKnowledge.Holds out (push t' ρ) h' ∧ Fn (push t' ρ) m s') ∧
      (∀ x, Raises t' x → ∃ s' : IndexedHeap, Action ce.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        Scoped 0 x ∧ excOf G s'.n s'.W x ∧ Fe ρ m s')

/-- **A step's exits in parts**: the local judgment, the assertion `Fn` at
the pushed environment after every run to a value whose endpoint is an action
of `cn` with the rule's output, and `Fe` at the node's environment after every
action of `ce`. -/
def StepParts (G : NormalGraph ι) (A : Ty ι) (cn ce : Footprints.Closed) (t : Tm) (out : HeapKnowledge.Knowledge)
    (Fn Fe : Assertion) (ρ : Env) (m : Nat) (s : IndexedHeap) : Prop :=
  SafePostExc (excOf G) (meaning G A) (fun h' v => cn.Holds s.h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => ce.Holds s.h h' ∧ True) s.n s.W s.h (instantiate 0 ρ t) ∧
    (∀ k h' v (s' : IndexedHeap), Steps k s.h (instantiate 0 ρ t) h' v → isVal v = true →
      Action cn.fp ρ s s' → s'.h = h' → HeapKnowledge.Holds out (push v ρ) h' → Fn (push v ρ) m s') ∧
    ∀ s' : IndexedHeap, Action ce.fp ρ s s' → Fe ρ m s'

omit [DecidableEq ι] in
theorem stepExits_of {G : NormalGraph ι} {A : Ty ι} {cn ce : Footprints.Closed} {t : Tm}
    {out : HeapKnowledge.Knowledge} {Fn Fe : Assertion} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hj : SafePostExc (excOf G) (meaning G A) (fun h' v => cn.Holds s.h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => ce.Holds s.h h' ∧ True) s.n s.W s.h (instantiate 0 ρ t))
    (hn : ∀ k h' v (s' : IndexedHeap), Steps k s.h (instantiate 0 ρ t) h' v → isVal v = true →
      Action cn.fp ρ s s' → s'.h = h' → HeapKnowledge.Holds out (push v ρ) h' → Fn (push v ρ) m s')
    (he : ∀ s' : IndexedHeap, Action ce.fp ρ s s' → Fe ρ m s') :
    StepExits G A cn ce t out Fn Fe ρ m s := by
  refine ⟨hj, fun k h' t' hst hk => ⟨fun hv => ?_, fun x hx => ?_⟩⟩
  · obtain ⟨s', ha, hh, hnk, hT, hq⟩ := action_normal (ρ := ρ) hj hst hv hk
    exact ⟨s', ha, hh, hnk, hT, hq, hn k h' t' s' hst hv ha hh hq⟩
  · obtain ⟨s', ha, hh, hnk, hsc, hΞ, -⟩ := action_throw (ρ := ρ) hj hst hx hk
    exact ⟨s', ha, hh, hnk, hsc, hΞ, he s' ha⟩

end StepSound

/-! ## The step theorem -/

section StepTheorem
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **THE STEP THEOREM, in parts** (`StepParts`: each exit's assertion
stated for every run to a value and every action of the effect, the form a
node's obligations read). Where `checkedStep` accepts node `l` (its claim
`c`, its term `node.expression`) from the entry state `entry` with result
`st`, and `entry`'s state holds at the node's environment `ρ` (typed by
`c.context`) with its store well-formed and every name it mentions below the
next fresh name: the summary table stays checked; the step's knowledge
`st.stepK` holds; the result is a name of the entry or the fresh one; and
there are closed effects `cn`, `ce` (`{values: keep, stores: keep}` and
`top` for a preserving step, `top` for both at a writing step) with the
node's local judgment and, on the normal exit with value `v`, the action of
`cn`, the residual budget, `v`'s type, the rule's output `st.stepOut` at
`push v ρ` and the state after the step (`st.result` pushed on the entry's
names, `st.store`) at `push v ρ`; on a throw, the action of `ce`, the raised
value closed and of the exception family, and the entry's heap-free state at
`ρ` (the store a handler edge starts from). -/
theorem checkedStep_parts {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool}
    {aliases : List (ι × ι)} {pc : PassChecker G images} {undefTy : Option (Ty ι)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {ms : List Nat} {fresh : Nat}
    {answers : Answered G} {st : Stepped ι} {stats : StepStats} {ans : Answered G}
    (h : checkedStep G images pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh
      answers = (Except.ok st, stats, ans))
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G entry I start E ρ m s) (w : StoreWF entry.store) (hnb : NamesBelow entry I start fresh)
    (hwidth : entry.names.length ≤ c.context.length)
    (he : EnvOk G c.context ρ s.n s.W) (hcodes : CodesSound G codes)
    (hsum : SummariesSound G images answers.summaries.toList)
    (hdir : DirectKeepsSummaries G images undefTy)
    (hsrch : SearchKeepsSummaries G images pool fuel suggestions index codes aliases pc.checker) :
    SummariesSound G images ans.summaries.toList ∧ HeapKnowledge.Holds st.stepK ρ s.h ∧
    ((st.result ∈ entry.names ∧ st.fresh = fresh) ∨ (st.result = fresh ∧ st.fresh = fresh + 1)) ∧
    ∃ cn ce : Footprints.Closed, StepParts G c.type cn ce node.expression st.stepOut
      (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ I start E)
      (StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ I start E) ρ m s := by
  have hS' := hS
  obtain ⟨η, hn, hst, hI, hF, hstart⟩ := hS'
  have hk := stateHolds_stepKnowledge hS he c.context.length ms (wholeOf node.expression)
  rcases checkedStep_ok h with ⟨x, hc, hr, hstore, hfr, -, hK, hO, rfl⟩ |
      ⟨-, effect, a0, a1, ha0, ha1, ⟨out, pre, hsel, htree, hres, hfresh, -, -, hpres, hwrit⟩, hans⟩
  · -- A copy of slot `i`: the term is the slot's value.
    obtain ⟨i, hi, hty, hx⟩ := copiedOf_some hc
    have hval : instantiate 0 ρ node.expression = ρ i := by rw [hi]; simp [instantiate]
    have hv : isVal (ρ i) = true := (meaning_value (he.2 i _ hty)).1
    refine ⟨hsum, by rw [hK]; exact holds_empty, .inl ⟨hr ▸ List.mem_of_getElem? hx, hfr⟩,
      Footprints.Closed.empty, Footprints.Closed.empty, ⟨?_, ?_, ?_⟩⟩
    · rw [hval, hO]
      exact SafePostExc.value hv (he.2 i _ hty) ⟨Footprints.Closed.holds_empty.mpr (List.prefix_refl _), holds_empty⟩
    · intro k h' v s' hsteps _ ha _ _
      rw [hval] at hsteps
      have hvv := PromiseCalls.steps_value hv hsteps
      subst hvv
      have hηx : η x = ρ i := (hn i x hx).symm
      obtain ⟨-, g2, -⟩ := set_agree (st := entry) (I := I) (start := start) (r := x) (.inr hηx)
      rw [hr, hstore]
      refine stateHolds_pushed hn hI hF hstart ha.1 (.inr hηx) fun a ha' => ?_
      exact (atomHolds_congr fun y hy => (g2 a ha' y hy).symm).mp
        (named_keep_box (Footprints.Closed.empty_le _) hst s' ha a ha')
    · intro s' ha; exact stateHolds_throw hS w ha.1
  · subst hans
    have hs0 : SummariesSound G images a0.summaries.toList := by
      rcases ha0 with rfl | ⟨adm, rfl⟩
      · exact hsum
      · exact hdir _ _ _ _ _ hsum
    have hs1 : SummariesSound G images ans.summaries.toList := by
      rcases ha1 with rfl | ⟨k, own, adm, rfl⟩
      · exact hs0
      · exact hsrch _ _ _ _ _ hs0
    -- The result's name: a slot's name its value holds, or the fresh one.
    have hkv : ∀ k h' v, Steps k s.h (instantiate 0 ρ node.expression) h' v →
        NamesBelow entry I start st.result ∨ η st.result = v := by
      intro k h' v hsteps
      rcases resultOf_cases node.expression entry.names fresh with ⟨i, hi, hx, -⟩ | ⟨hr1, -⟩
      · right
        rw [hres]
        have hval : instantiate 0 ρ node.expression = ρ i := by rw [hi]; simp [instantiate]
        rw [hval] at hsteps
        have hi' : i < c.context.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hx).1 hwidth
        obtain ⟨A, hA⟩ : ∃ A, c.context[i]? = some A := ⟨_, List.getElem?_eq_getElem hi'⟩
        have hv : isVal (ρ i) = true := (meaning_value (he.2 i A hA)).1
        rw [PromiseCalls.steps_value hv hsteps]
        exact (hn i _ hx).symm
      · left; rw [hres, hr1]; exact hnb
    have hres' : (st.result ∈ entry.names ∧ st.fresh = fresh) ∨ (st.result = fresh ∧ st.fresh = fresh + 1) := by
      rcases resultOf_cases node.expression entry.names fresh with ⟨i, -, hx, hf⟩ | ⟨hr1, hf⟩
      · exact .inl ⟨hres ▸ List.mem_of_getElem? hx, hfresh.trans hf⟩
      · exact .inr ⟨hres.trans hr1, hfresh.trans hf⟩
    have hok : pc.selectChecks = false → passTreeOk G images (kOf G c entry ms (wholeOf node.expression)) codes
        ans.summaries.toList effect = true := fun hs => passTreeCheck_ok htree hs
    by_cases hp : passPreserving G images (jOf c node) (kOf G c entry ms (wholeOf node.expression)) effect codes
        a0.summaries.toList = true
    · obtain ⟨hstore, hK, hO⟩ := hpres hp
      refine ⟨hs1, by rw [hK]; exact hk.1, hres', Footprints.Closed.empty, Footprints.Closed.top,
        ⟨?_, ?_, ?_⟩⟩
      · rw [hO]; exact preserving_judgment_two hp hok hsel hcodes hs0 hs1 he hk.1 s.adm s.ok
      · intro k h' v s' hsteps _ ha hh hout
        rw [hstore]
        refine stateHolds_pushed hn hI hF hstart ha.1 (hkv k h' v hsteps) ?_
        rw [hO] at hout
        exact preserving_store hn (hkv k h' v hsteps)
          (fun a ha' => named_keep_box (Footprints.Closed.empty_le _) hst s' ha a ha') (hh ▸ hout)
      · intro s' ha; exact stateHolds_throw hS w ha.1
    · have hpf : passPreserving G images (jOf c node) (kOf G c entry ms (wholeOf node.expression)) effect codes
          a0.summaries.toList = false := by simpa using hp
      obtain ⟨out', hwc, hsel', hstore, hK, hO⟩ := hwrit hpf
      have hrun := pass_select_whole htree hwc hsel'
      refine ⟨hs1, by rw [hK]; exact hk.2, hres', Footprints.Closed.top, Footprints.Closed.top,
        ⟨?_, ?_, ?_⟩⟩
      · rw [hO]; exact top_judgment (passRunChecker pc) hrun hcodes hs1 he hk.2 s.adm s.ok
      · intro k h' v s' hsteps _ ha hh hout
        rw [hstore]
        refine stateHolds_pushed hn hI hF hstart ha.1 (hkv k h' v hsteps) ?_
        rw [hO] at hout
        exact writing_store w hn (hkv k h' v hsteps) hst (hh ▸ hout)
      · intro s' ha; exact stateHolds_throw hS w ha.1

/-- **THE STEP THEOREM.** Where `checkedStep` accepts node `l` (its claim
`c`, its term `node.expression`) from the entry state `entry` with result
`st`, and `entry`'s state holds at the node's environment `ρ` (typed by
`c.context`) with its store well-formed and every name it mentions below the
next fresh name: the summary table stays checked; the step's knowledge
`st.stepK` holds; the result is a name of the entry or the fresh one; and
there are closed effects `cn`, `ce` with the node's local judgment and the
exits' endpoints (`StepExits`), from `checkedStep_parts`. -/
theorem checkedStep_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool}
    {aliases : List (ι × ι)} {pc : PassChecker G images} {undefTy : Option (Ty ι)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {ms : List Nat} {fresh : Nat}
    {answers : Answered G} {st : Stepped ι} {stats : StepStats} {ans : Answered G}
    (h : checkedStep G images pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh
      answers = (Except.ok st, stats, ans))
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G entry I start E ρ m s) (w : StoreWF entry.store) (hnb : NamesBelow entry I start fresh)
    (hwidth : entry.names.length ≤ c.context.length)
    (he : EnvOk G c.context ρ s.n s.W) (hcodes : CodesSound G codes)
    (hsum : SummariesSound G images answers.summaries.toList)
    (hdir : DirectKeepsSummaries G images undefTy)
    (hsrch : SearchKeepsSummaries G images pool fuel suggestions index codes aliases pc.checker) :
    SummariesSound G images ans.summaries.toList ∧ HeapKnowledge.Holds st.stepK ρ s.h ∧
    ((st.result ∈ entry.names ∧ st.fresh = fresh) ∨ (st.result = fresh ∧ st.fresh = fresh + 1)) ∧
    ∃ cn ce : Footprints.Closed, StepExits G c.type cn ce node.expression st.stepOut
      (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ I start E)
      (StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ I start E) ρ m s := by
  obtain ⟨h1, h2, h3, cn, ce, hj, hn, hx⟩ := checkedStep_parts h hS w hnb hwidth he hcodes hsum hdir hsrch
  exact ⟨h1, h2, h3, cn, ce, stepExits_of hj hn hx⟩

end StepTheorem

end Verification.TolerantFrames
