import Verification.Programs.TolerantFramesInvocation
import Verification.Programs.GraphCode
import Verification.Semantics.SafeRet

/-! # Tolerant frames: run properties beside the graph invariant

A graph's guarantees beyond safety (a footprint, a postcondition, a regional
bound) are properties of the heap and value at the run's exits. They are
carried beside the graph invariant by a property of the graph machine's
states (`StateKeeps`): at a node entry a per-label property `X` of the
environment and heap, inside a node every run of its term reaching an exit
with that exit's obligation (`EvalKeeps`), and at the run's ends the exit
posts `Q` and `R`. A node keeps it (`NodesKeep`) when, from its entry
assertion and `X`, every run of its term with budget left meets the
obligation of the exit it takes: `X` at the target's environment, `Q` at a
return, `R` at an escaping throw. Then the term running the graph code meets
`Q` and `R` at its exits (`keeps_postExc`), and every node entry a run
reaches satisfies the node assertion (`reached_pre`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations ControlFlow PointClaims

section Keeps

/-- The obligation of the exit continuation `k` takes with the value `v` in
the heap `h`: `X` at the target's environment, `Q` at a return. -/
def ContKeeps (X : Nat → Env → Heap → Prop) (Q : Heap → Tm → Prop) (ρ : Env) (v : Tm) (h : Heap) :
    Continuation → Prop
  | .ret => Q h v
  | .bind l => X l.label (mapEnv l.mapping (push v ρ)) h
  | .effect l => X l.label (mapEnv l.mapping ρ) h
  | .branch y n => (v = .tru → X y.label (mapEnv y.mapping ρ) h) ∧ (v = .fls → X n.label (mapEnv n.mapping ρ) h)
  | .branchBind y n => (v = .tru → X y.label (mapEnv y.mapping (push .tru ρ)) h) ∧
      (v = .fls → X n.label (mapEnv n.mapping (push .fls ρ)) h)
  | .tagBind tag y n => X (if tagHoldsIn h tag v then y else n).label
      (mapEnv (if tagHoldsIn h tag v then y else n).mapping (push v ρ)) h

/-- The obligation of a throw of `e` in the heap `h`: `X` at the handler's
environment with `e` bound, `R` where it escapes. -/
def HandlerKeeps (X : Nat → Env → Heap → Prop) (R : Heap → Prop) (ρ : Env) (e : Tm) (h : Heap) :
    Option Target → Prop
  | some l => X l.label (mapEnv l.mapping (push e ρ)) h
  | none => R h

/-- Every run of `t` from `h` with fewer than `n` steps meets the obligation
of the exit it reaches. -/
def EvalKeeps (X : Nat → Env → Heap → Prop) (Q : Heap → Tm → Prop) (R : Heap → Prop) (n : Nat) (h : Heap)
    (t : Tm) (ρ : Env) (k : Continuation) (x : Option Target) : Prop :=
  ∀ j h' t', Steps j h t h' t' → j < n →
    (isVal t' = true → ContKeeps X Q ρ t' h' k) ∧ (∀ e, Raises t' e → HandlerKeeps X R ρ e h' x)

/-- The run property at a state of the graph machine. -/
def StateKeeps (X : Nat → Env → Heap → Prop) (Q : Heap → Tm → Prop) (R : Heap → Prop) (n : Nat) (h : Heap) :
    State → Prop
  | .at l ρ => X l ρ h
  | .eval t ρ k x => EvalKeeps X Q R n h t ρ k x
  | .done v => Q h v
  | .raised _ => R h

/-- **Each node keeps the run property**: from a state where its assertion
and `X` hold, every run of its term with budget left meets its exit's
obligation. -/
def NodesKeep (P : Program) (pre : Nat → Assertion) (X : Nat → Env → Heap → Prop) (Q : Heap → Tm → Prop)
    (R : Heap → Prop) (m : Nat) : Prop :=
  ∀ l ρ (s : IndexedHeap), pre l ρ m s → X l ρ s.h → ∃ node, P[l]? = some node ∧
    (RefsOk s.W (instantiate 0 ρ node.expression) → RootsOk s.W ρ →
      EvalKeeps X Q R s.n s.h (instantiate 0 ρ node.expression) ρ node.continuation node.handler)

/-- **Each node keeps the run property at framed returns**: `NodesKeep`,
a framed node's exit obligations required where the exit meets its returns
from the heap it is entered at (`EvalKeepsR`). -/
def EvalKeepsR (Rn Re : Heap → Prop) (X : Nat → Env → Heap → Prop) (Q : Heap → Tm → Prop) (R : Heap → Prop)
    (n : Nat) (h : Heap) (t : Tm) (ρ : Env) (k : Continuation) (x : Option Target) : Prop :=
  ∀ j h' t', Steps j h t h' t' → j < n →
    (isVal t' = true → Rn h' → ContKeeps X Q ρ t' h' k) ∧ (∀ e, Raises t' e → Re h' → HandlerKeeps X R ρ e h' x)

/-- The run property at a state of the graph machine under the pending
evaluation `p`. -/
def StateKeepsR (Ret RetE : Nat → Env → Heap → Heap → Prop) (X : Nat → Env → Heap → Prop) (Q : Heap → Tm → Prop)
    (R : Heap → Prop) (n : Nat) (p : Option (Nat × Heap)) (h : Heap) : State → Prop
  | .at l ρ => X l ρ h
  | .eval t ρ k x => EvalKeepsR (RetP Ret p ρ) (RetP RetE p ρ) X Q R n h t ρ k x
  | .done v => Q h v
  | .raised _ => R h

/-- **Each node keeps the run property at framed returns.** -/
def NodesKeepR (P : Program) (pre : Nat → Assertion) (F : Nat → Bool) (Ret RetE : Nat → Env → Heap → Heap → Prop)
    (X : Nat → Env → Heap → Prop) (Q : Heap → Tm → Prop) (R : Heap → Prop) (m : Nat) : Prop :=
  ∀ l ρ (s : IndexedHeap), pre l ρ m s → X l ρ s.h → ∃ node, P[l]? = some node ∧
    (RefsOk s.W (instantiate 0 ρ node.expression) → RootsOk s.W ρ →
      EvalKeepsR (RetP Ret (enterPend F l s.h) ρ) (RetP RetE (enterPend F l s.h) ρ) X Q R s.n s.h
        (instantiate 0 ρ node.expression) ρ node.continuation node.handler)

section
variable {P : Program} {pre : Nat → Assertion} {X : Nat → Env → Heap → Prop} {Q : Heap → Tm → Prop}
  {R : Heap → Prop} {m : Nat} {Ret RetE : Nat → Env → Heap → Heap → Prop}

/-- Nodes keeping the run property keep it at framed returns with no framed
node. -/
theorem NodesKeep.toR (hk : NodesKeep P pre X Q R m) : NodesKeepR P pre (fun _ => false) Ret RetE X Q R m :=
  fun l ρ s hp hx => by
    obtain ⟨node, hP, hk⟩ := hk l ρ s hp hx
    exact ⟨node, hP, fun hr hρ j h' t' hs hj =>
      ⟨fun hv _ => (hk hr hρ j h' t' hs hj).1 hv, fun e he _ => (hk hr hρ j h' t' hs hj).2 e he⟩⟩

theorem StateKeeps.toR {n : Nat} {h : Heap} {st : State} (hb : StateKeeps X Q R n h st) :
    StateKeepsR Ret RetE X Q R n none h st := by
  cases st with
  | eval => exact fun j h' t' hs hj => ⟨fun hv _ => (hb j h' t' hs hj).1 hv, fun e he _ => (hb j h' t' hs hj).2 e he⟩
  | _ => exact hb

theorem StateKeepsR.toPlain {n : Nat} {h : Heap} {st : State} (hb : StateKeepsR Ret RetE X Q R n none h st) :
    StateKeeps X Q R n h st := by
  cases st with
  | eval => exact fun j h' t' hs hj => ⟨fun hv => (hb j h' t' hs hj).1 hv trivial,
      fun e he => (hb j h' t' hs hj).2 e he trivial⟩
  | _ => exact hb
end

/-- **One transition keeps the run property at framed returns**: where the
transition meets the returns, the state after it keeps the run property
under the pending evaluation after it. -/
theorem keeps_stepR {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    {F : Nat → Bool} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    {X : Nat → Env → Heap → Prop} {Q : Heap → Tm → Prop} {R : Heap → Prop}
    (hdown : AdminClosed pre m) (hkeep : NodesKeepR P pre F Ret RetE X Q R m) {n : Nat} {W : WorldT (n + 1)}
    {h h' : Heap} {st st' : State} {p : Option (Nat × Heap)} (ha : WorldAdm W) (ho : HeapOk (n + 1) W h)
    (hPr : ∀ node ∈ P, RefsOk W node.expression) (hsr : StateRefs W st)
    (hinv : GraphInvR pre Ξres Tres Qres Rres Ret RetE m (n + 1) W p h st)
    (hb : StateKeepsR Ret RetE X Q R (n + 1) p h st)
    (tr : Transition P h st h' st') (hR : RetAtG Ret RetE p h' st st') :
    StateKeepsR Ret RetE X Q R n (pendG F p h st st') h' st' := by
  cases tr with
  | @enter l node _ ρ hn =>
    cases n with
    | zero => intro j _ _ _ hj; omega
    | succ n =>
      have hpre := hinv (Nat.zero_lt_succ _) ha ho
      let s₀ : IndexedHeap := ⟨n + 1, trunc (n + 1) (Nat.le_succ _) W, h, Nat.zero_lt_succ _,
        WorldAdm_trunc _ ha, HeapOk_trunc _ W h ho⟩
      have hpre₀ := hdown l ρ ⟨n + 2, W, h, Nat.zero_lt_succ _, ha, ho⟩ s₀ ⟨Nat.le_succ _, WExt_refl _⟩ rfl hpre
      obtain ⟨node', hP, hk⟩ := hkeep l ρ s₀ hpre₀ hb
      rw [hn] at hP; cases hP
      exact hk (RefsOk_trunc _ (node_refs (hPr _ (List.mem_of_getElem? hn)) hsr)) (fun i => RefsOk_trunc _ (hsr i))
  | expr st => exact fun j h'' t'' hs hj => hb (j + 1) h'' t'' (.next st hs) (by omega)
  | ret hv => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 hv (hR.1 hv)
  | bind hv => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 hv (hR.1 hv)
  | effect hv => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 hv (hR.1 hv)
  | yes => exact ((hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 rfl (hR.1 rfl)).1 rfl
  | no => exact ((hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 rfl (hR.1 rfl)).2 rfl
  | yesBind => exact ((hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 rfl (hR.1 rfl)).1 rfl
  | noBind => exact ((hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 rfl (hR.1 rfl)).2 rfl
  | tagBind hv => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 hv (hR.1 hv)
  | handle hr => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).2 _ hr (hR.2 (raises_not_val hr))
  | raise hr => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).2 _ hr (hR.2 (raises_not_val hr))

/-- **One transition keeps the run property** (`keeps_stepR` with no framed
node). -/
theorem keeps_step {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    {X : Nat → Env → Heap → Prop} {Q : Heap → Tm → Prop} {R : Heap → Prop}
    (hdown : AdminClosed pre m) (hkeep : NodesKeep P pre X Q R m) {n : Nat} {W : WorldT (n + 1)}
    {h h' : Heap} {st st' : State} (ha : WorldAdm W) (ho : HeapOk (n + 1) W h)
    (hPr : ∀ node ∈ P, RefsOk W node.expression) (hsr : StateRefs W st)
    (hinv : GraphInv pre Ξres Tres Qres Rres m (n + 1) W h st) (hb : StateKeeps X Q R (n + 1) h st)
    (tr : Transition P h st h' st') : StateKeeps X Q R n h' st' := by
  have := keeps_stepR (Ret := fun _ _ _ _ => True) (RetE := fun _ _ _ _ => True) hdown hkeep.toR ha ho hPr hsr
    hinv.toR hb.toR tr (retAtG_none h' st st')
  rw [pendG_false] at this
  exact this.toPlain

/-! ### The term that runs graph code, at framed returns -/

/-- **A step of the term running graph code leaves the pending evaluation
its transition leaves** (`framedPend` of the steps, `pendG` of the
transitions). -/
theorem sim_pend {E : List Tm} {K : List (Continuation × Option Target)} {F : Nat → Bool}
    {p : Option (Nat × Heap)} {h h' : Heap} {ts ts' : Tm} {s s' : State} (hs : GraphCode.Sim E K ts s)
    (tr : Transition (GraphCode.program E K) h s h' s') (hs' : GraphCode.Sim E K ts' s') :
    framedPend F p h ts ts' = pendG F p h s s' := by
  have hval : ∀ {v : Tm}, isVal v = true → isFrame v = false := fun {v} hv => by
    cases v <;> simp_all [isVal, isFrame]
  cases hs with
  | goto =>
    cases hs' with
    | frame =>
      simp only [framedPend, pendG, enterPend, isFrame, Bool.true_and]
      cases F _ <;> rfl
    | goto => cases tr
    | done => cases tr
    | raised => cases tr
  | frame =>
    cases hs' with
    | frame => rfl
    | goto => rfl
    | done hv => simp only [framedPend, pendG, hval hv]; rfl
    | raised => rfl
  | done hv => cases tr
  | raised => cases tr

/-- **A step meeting the framed returns is a transition meeting them.** -/
theorem sim_retAt {E : List Tm} {K : List (Continuation × Option Target)}
    {Ret RetE : Nat → Env → Heap → Heap → Prop} {p : Option (Nat × Heap)} {h' : Heap} {ts ts' : Tm} {s s' : State}
    (hs : GraphCode.Sim E K ts s) (hs' : GraphCode.Sim E K ts' s') (hR : RetAt Ret RetE p h' ts ts') :
    RetAtG Ret RetE p h' s s' := by
  cases hs with
  | goto => trivial
  | done => trivial
  | raised => trivial
  | frame =>
    rename_i t L d k x comp
    have key : isFrame ts' = false → (isVal t = true → RetP Ret p (envOf L d) h') ∧
        (isVal t = false → RetP RetE p (envOf L d) h') := fun hf => by
      cases p with
      | none => exact ⟨fun _ => trivial, fun _ => trivial⟩
      | some q =>
        obtain ⟨l, h₀⟩ := q
        simp only [RetAt] at hR
        rcases hR with hR | ⟨hv, hR⟩ | ⟨hv, hR⟩
        · rw [hf] at hR; cases hR
        · exact ⟨fun _ => hR, fun h => (by rw [hv] at h; cases h)⟩
        · exact ⟨fun h => (by rw [hv] at h; cases h), fun _ => hR⟩
    cases hs' with
    | frame => trivial
    | goto => exact key rfl
    | done hv => cases ts' <;> first | exact key rfl | simp [isVal] at hv
    | raised => exact key rfl

/-- **The term running graph code is safe at framed returns as the graph
is** (`GraphCode.safe_of_sim` at framed returns). -/
theorem safeRet_of_sim {E : List Tm} {K : List (Continuation × Option Target)} {Ξ T : Fam} {F : Nat → Bool}
    {Ret RetE : Nat → Env → Heap → Heap → Prop} :
    ∀ (n : Nat) (W : WorldT n) (p : Option (Nat × Heap)) (h : Heap) {ts s}, GraphCode.Sim E K ts s →
      (∀ e ∈ E, RefsOk W e) → SafeGraphRet Ξ (GraphCode.program E K) T F Ret RetE n W p h s →
      SafeRet (fun _ _ => True) Ξ T (fun _ _ _ _ => True) (fun _ _ _ => True) F Ret RetE n W p h ts := by
  intro n
  induction n with
  | zero => intro W p h ts s hs hE hg; exact GraphCode.sim_refs hs hE hg
  | succ n ih =>
    intro W p h ts s hs hE hg
    obtain ⟨hr, hg⟩ := hg
    refine ⟨GraphCode.sim_refs hs hE hr, trivial, ?_⟩
    rcases hg with (⟨v, rfl, hv, hT⟩ | ⟨v, rfl, hsc, hΞ⟩) | ⟨U, h', s', hx, hu, tr, hh, hg⟩
    · cases hs; exact .inl (.inl ⟨hv, hT, trivial⟩)
    · cases hs with
      | raised hv hj => exact .inl (.inr ⟨⟨v, .throwV hv hj, hsc, hΞ⟩, trivial⟩)
    · obtain ⟨ts', st, hs'⟩ := GraphCode.sim_step hs tr
      exact .inr ⟨U, h', ts', hx, hu, st, hh, fun hR => by
        rw [sim_pend hs tr hs']
        exact ih U _ h' hs' (fun e he => RefsOk_mono hx (RefsOk_trunc _ (hE e he))) (hg (sim_retAt hs hs' hR))⟩

/-- **The term running graph code meets the run property's posts at framed
returns.** Where the nodes are checked and keep the run property at framed
returns, a term simulating a state the invariant and the run property
describe under a pending evaluation is safe at framed returns with `Q` at
its normal exit and `R` at a throw. -/
theorem keeps_postExcR {E : List Tm} {K : List (Continuation × Option Target)} {pre : Nat → Assertion}
    {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat} {X : Nat → Env → Heap → Prop}
    {Q : Heap → Tm → Prop} {R : Heap → Prop} {T : Fam} {F : Nat → Bool} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    (hnodes : NodesCheckedR (GraphCode.program E K) pre F Ret RetE Ξres Tres Qres Rres m) (hdown : AdminClosed pre m)
    (hkeep : NodesKeepR (GraphCode.program E K) pre F Ret RetE X Q R m) (hT : ∀ n W v, Tres n W v → T n W v) :
    ∀ n (W : WorldT n) p h ts st, GraphCode.Sim E K ts st → WorldAdm W → HeapOk n W h →
      (∀ e ∈ E, RefsOk W e) → StateRefs W st →
      GraphInvR pre Ξres Tres Qres Rres Ret RetE m n W p h st → StateKeepsR Ret RetE X Q R n p h st →
      SafeRet (fun _ _ => True) Ξres T (WPost.lift Q) (WExc.lift R) F Ret RetE n W p h ts := by
  intro n
  induction n with
  | zero => intro W p h ts st sim _ _ hE hr _ _; exact GraphCode.sim_refs sim hE hr
  | succ n ih =>
    intro W p h ts st sim ha ho hE hr hinv hb
    refine ⟨GraphCode.sim_refs sim hE hr, trivial, ?_⟩
    rcases graph_stepR hnodes hdown ha ho (GraphCode.program_refs hE) hr hinv with
        (⟨v, rfl, hv, hTv⟩ | ⟨v, rfl, hsc, hΞ⟩) | ⟨U, h', st', hx, hu, tr, hh, hrs, hi⟩
    · cases sim; exact .inl (.inl ⟨hv, hT _ _ _ hTv, hb⟩)
    · cases sim with
      | raised hv hj => exact .inl (.inr ⟨⟨v, .throwV hv hj, hsc, hΞ⟩, hb⟩)
    · obtain ⟨ts', step, sim'⟩ := GraphCode.sim_step sim tr
      exact .inr ⟨U, h', ts', hx, hu, step, hh, fun hR => by
        have hRG := sim_retAt sim sim' hR
        rw [sim_pend sim tr sim']
        exact ih U _ h' ts' st' sim' hu hh (fun e he => RefsOk_mono hx (RefsOk_trunc _ (hE e he))) hrs (hi hRG)
          (keeps_stepR hdown hkeep ha ho (GraphCode.program_refs hE) hr hinv hb tr hRG)⟩

/-- **The term running graph code meets the run property's posts**
(`keeps_postExcR` with no framed node). Where the nodes are checked for
safety and keep the run property, a term simulating a state the graph
invariant and the run property describe is safe with `Q` at its normal exit
and `R` at a throw. -/
theorem keeps_postExc {E : List Tm} {K : List (Continuation × Option Target)} {pre : Nat → Assertion}
    {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat} {X : Nat → Env → Heap → Prop}
    {Q : Heap → Tm → Prop} {R : Heap → Prop} {T : Fam}
    (hnodes : NodesChecked (GraphCode.program E K) pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m)
    (hkeep : NodesKeep (GraphCode.program E K) pre X Q R m) (hT : ∀ n W v, Tres n W v → T n W v) :
    ∀ n (W : WorldT n) h ts st, GraphCode.Sim E K ts st → WorldAdm W → HeapOk n W h →
      (∀ e ∈ E, RefsOk W e) → StateRefs W st →
      GraphInv pre Ξres Tres Qres Rres m n W h st → StateKeeps X Q R n h st →
      SafePostExc Ξres T Q R n W h ts :=
  fun n W h ts st sim ha ho hE hr hinv hb =>
    SafeRet.erase (fun _ => rfl)
      (keeps_postExcR (Ret := fun _ _ _ _ => True) (RetE := fun _ _ _ _ => True) hnodes.toR hdown hkeep.toR hT
        n W none h ts st sim ha ho hE hr hinv.toR hb.toR)

/-- **Every node entry a run reaches satisfies its assertion**: a graph run
from a node entry whose assertion holds, with budget left, to the entry of
node `l'` ends in a state where `l'`'s assertion holds. -/
theorem reached_pre {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat} {ρ : Env}
    {s : IndexedHeap} (hpre : pre l ρ m s) (hPr : ∀ node ∈ P, RefsOk s.W node.expression)
    (hρ : ∀ i, RefsOk s.W (ρ i)) {k : Nat} {h' : Heap} {l' : Nat} {ρ' : Env}
    (hrun : Transitions P k s.h (.at l ρ) h' (.at l' ρ')) (hk : k < s.n) :
    ∃ s' : IndexedHeap, s'.h = h' ∧ pre l' ρ' m s' := by
  obtain ⟨s', -, he, -, hinv⟩ := graph_inv_run hnodes hdown hrun s rfl hk hPr hρ fun _ _ _ => hpre
  exact ⟨s', he, hinv s'.pos s'.adm s'.ok⟩

end Keeps

end Verification.TolerantFrames
