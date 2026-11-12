import Verification.Programs.TolerantFramesInvocation
import Verification.Programs.GraphCode

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
    EvalKeeps X Q R s.n s.h (instantiate 0 ρ node.expression) ρ node.continuation node.handler

/-- **One transition keeps the run property.** -/
theorem keeps_step {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    {X : Nat → Env → Heap → Prop} {Q : Heap → Tm → Prop} {R : Heap → Prop}
    (hdown : AdminClosed pre m) (hkeep : NodesKeep P pre X Q R m) {n : Nat} {W : WorldT (n + 1)}
    {h h' : Heap} {st st' : State} (ha : WorldAdm W) (ho : HeapOk (n + 1) W h)
    (hinv : GraphInv pre Ξres Tres Qres Rres m (n + 1) W h st) (hb : StateKeeps X Q R (n + 1) h st)
    (tr : Transition P h st h' st') : StateKeeps X Q R n h' st' := by
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
      exact hk
  | expr st => exact fun j h'' t'' hs hj => hb (j + 1) h'' t'' (.next st hs) (by omega)
  | ret hv => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 hv
  | bind hv => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 hv
  | effect hv => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 hv
  | yes => exact ((hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 rfl).1 rfl
  | no => exact ((hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 rfl).2 rfl
  | yesBind => exact ((hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 rfl).1 rfl
  | noBind => exact ((hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 rfl).2 rfl
  | tagBind hv => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).1 hv
  | handle hr => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).2 _ hr
  | raise hr => exact (hb 0 _ _ .refl (Nat.zero_lt_succ _)).2 _ hr

/-- **The term running graph code meets the run property's posts.** Where
the nodes are checked for safety and keep the run property, a term
simulating a state the graph invariant and the run property describe is
safe with `Q` at its normal exit and `R` at a throw. -/
theorem keeps_postExc {E : List Tm} {K : List (Continuation × Option Target)} {pre : Nat → Assertion}
    {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat} {X : Nat → Env → Heap → Prop}
    {Q : Heap → Tm → Prop} {R : Heap → Prop} {T : Fam}
    (hnodes : NodesChecked (GraphCode.program E K) pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m)
    (hkeep : NodesKeep (GraphCode.program E K) pre X Q R m) (hT : ∀ n W v, Tres n W v → T n W v) :
    ∀ n (W : WorldT n) h ts st, GraphCode.Sim E K ts st → WorldAdm W → HeapOk n W h →
      GraphInv pre Ξres Tres Qres Rres m n W h st → StateKeeps X Q R n h st →
      SafePostExc Ξres T Q R n W h ts := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ts st sim ha ho hinv hb
    rcases graph_step hnodes hdown ha ho hinv with (⟨v, rfl, hv, hTv⟩ | ⟨v, rfl, hsc, hΞ⟩) |
        ⟨U, h', st', hx, hu, tr, hh, hi⟩
    · cases sim; exact .inl (.inl ⟨hv, hT _ _ _ hTv, hb⟩)
    · cases sim with
      | raised hv hj => exact .inl (.inr ⟨⟨v, .throwV hv hj, hsc, hΞ⟩, hb⟩)
    · obtain ⟨ts', step, sim'⟩ := GraphCode.sim_step sim tr
      exact .inr ⟨U, h', ts', hx, hu, step, hh,
        ih U h' ts' st' sim' hu hh hi (keeps_step hdown hkeep ha ho hinv hb tr)⟩

/-- **Every node entry a run reaches satisfies its assertion**: a graph run
from a node entry whose assertion holds, with budget left, to the entry of
node `l'` ends in a state where `l'`'s assertion holds. -/
theorem reached_pre {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat} {ρ : Env}
    {s : IndexedHeap} (hpre : pre l ρ m s) {k : Nat} {h' : Heap} {l' : Nat} {ρ' : Env}
    (hrun : Transitions P k s.h (.at l ρ) h' (.at l' ρ')) (hk : k < s.n) :
    ∃ s' : IndexedHeap, s'.h = h' ∧ pre l' ρ' m s' := by
  obtain ⟨s', -, he, -, hinv⟩ := graph_inv_run hnodes hdown hrun s rfl hk fun _ _ _ => hpre
  exact ⟨s', he, hinv s'.pos s'.adm s'.ok⟩

end Keeps

end Verification.TolerantFrames
