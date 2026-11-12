import Verification.Programs.TolerantFramesRuns
import Verification.Semantics.FootprintRebase

/-! # Tolerant frames: one action per graph invocation

A graph invocation's run from its entry state follows the graph invariant
(`graph_inv_run`), by determinism of the graph machine; at its exits it meets
the graph's exit posts `Qres` and `Rres` (`invocation_done`,
`invocation_raised`). With those posts the invocation's stated effect, a run
of the invocation is one action of that effect from its entry state
(`invocation_action`, `invocation_throw_action`): what a caller's `transfer`
consumes for the call.

The node assertions carry the bound so far, from the fixed invocation entry
heap `h₀`, and each node's exit composes its own effect onto it: a closed
node effect within the bound (`bound_step`), a node effect within the bound
on the entry's locations only, fresh stores exempt (`bound_step_fresh`), and a
regional node effect rebased to the entry (`action_compose_at`, the lift of
`Post.compose_at`), its class evidence read at the entry heap and its paths
resolved through stable paths (`rebaseOk_stable`). The administrative
transitions keep the heap, so the bound survives them (`adminClosed_bound`).
Effects are required at the invocation's exits only. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations ControlFlow PointClaims

/-! ## Runs follow the invariant -/

/-- **A graph run from a state the invariant describes, with budget left,
ends in a state the invariant describes**, reached by an admissible
transition. Each transition is the one `graph_step` supplies, by
determinism. -/
theorem graph_inv_run {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) :
    ∀ {k h st h' st'}, Transitions P k h st h' st' → ∀ (s : IndexedHeap), s.h = h → k < s.n →
      GraphInv pre Ξres Tres Qres Rres m s.n s.W s.h st →
      ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        GraphInv pre Ξres Tres Qres Rres m s'.n s'.W s'.h st' := by
  intro k h st h' st' hst
  induction hst with
  | refl => intro s hs _ hinv; exact ⟨s, Admissible.refl s, hs, rfl, hinv⟩
  | next tr _ ih =>
    intro s hs hk hinv
    obtain ⟨n, W, h₀, pos, adm, ok⟩ := s
    simp only at hs hk hinv ⊢
    subst hs
    cases n with
    | zero => omega
    | succ j =>
      rcases graph_step hnodes hdown adm ok hinv with (⟨v, rfl, -⟩ | ⟨v, rfl, -⟩) | ⟨U, h₁, st₁, hx, hu, tr', hh, hi⟩
      · cases tr
      · cases tr
      · obtain ⟨rfl, rfl⟩ := transition_det tr tr'
        obtain ⟨s', ha, he, hn, hinv'⟩ := ih ⟨j, U, _, by omega, hu, hh⟩ rfl (by simp only; omega) hi
        exact ⟨s', Admissible.trans ⟨Nat.le_succ j, hx⟩ ha, he, by simp only at hn; omega, hinv'⟩

/-- **An invocation's normal exit**: a run from a node entry whose assertion
holds to `.done v`, with budget left, ends in an admissible state where `v`
meets the result type and the heap the normal exit post. -/
theorem invocation_done {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop}
    {m : Nat} (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat}
    {ρ : Env} {s : IndexedHeap} (hpre : pre l ρ m s) {k : Nat} {h' : Heap} {v : Tm}
    (hrun : Transitions P k s.h (.at l ρ) h' (.done v)) (hk : k < s.n) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ isVal v = true ∧ Tres s'.n s'.W v ∧
      Qres h' := by
  obtain ⟨s', ha, he, hn, hinv⟩ := graph_inv_run hnodes hdown hrun s rfl hk fun _ _ _ => hpre
  obtain ⟨hv, hT, hQ⟩ := hinv s'.pos
  exact ⟨s', ha, he, hn, hv, hT, he ▸ hQ⟩

/-- **An invocation's exceptional exit**: a run to `.raised e`, with budget
left, ends in an admissible state where `e` is closed and of the exception
family and the heap meets the exceptional exit post. -/
theorem invocation_raised {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop}
    {m : Nat} (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat}
    {ρ : Env} {s : IndexedHeap} (hpre : pre l ρ m s) {k : Nat} {h' : Heap} {e : Tm}
    (hrun : Transitions P k s.h (.at l ρ) h' (.raised e)) (hk : k < s.n) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ Scoped 0 e ∧ Ξres s'.n s'.W e ∧
      Rres h' := by
  obtain ⟨s', ha, he, hn, hinv⟩ := graph_inv_run hnodes hdown hrun s rfl hk fun _ _ _ => hpre
  obtain ⟨hsc, hΞ, hR⟩ := hinv s'.pos
  exact ⟨s', ha, he, hn, hsc, hΞ, he ▸ hR⟩

/-- **A graph invocation is one action of its stated effect.** Where the
normal exit post bounds the heap by `cn` from the entry heap, a run to a
value is an action of `cn` from the entry state, at every name valuation;
every fact under `□_{cn}` at the entry holds at the exit. -/
theorem invocation_action {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop}
    {m : Nat} (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat}
    {ρ : Env} {s : IndexedHeap} (hpre : pre l ρ m s) {cn : Footprints.Closed}
    (hQ : ∀ h, Qres h → cn.Holds s.h h) {k : Nat} {h' : Heap} {v : Tm}
    (hrun : Transitions P k s.h (.at l ρ) h' (.done v)) (hk : k < s.n) (σ : Env) :
    ∃ s' : IndexedHeap, Action cn.fp σ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ isVal v = true ∧
      Tres s'.n s'.W v := by
  obtain ⟨s', ha, he, hn, hv, hT, hq⟩ := invocation_done hnodes hdown hpre hrun hk
  refine ⟨s', ⟨ha, ?_⟩, he, hn, hv, hT⟩
  rw [he]
  exact Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp (hQ h' hq))

/-- **A fact under the invocation's effect at its entry holds at its normal
exit**: the caller's frame across the call. -/
theorem invocation_box {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop}
    {m : Nat} (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat}
    {ρ : Env} {s : IndexedHeap} (hpre : pre l ρ m s) {cn : Footprints.Closed}
    (hQ : ∀ h, Qres h → cn.Holds s.h h) {k : Nat} {h' : Heap} {v : Tm}
    (hrun : Transitions P k s.h (.at l ρ) h' (.done v)) (hk : k < s.n) {F : Assertion} {σ : Env} {m' : Nat}
    (hb : Box cn.fp F σ m' s) : ∃ s' : IndexedHeap, s'.h = h' ∧ F σ m' s' := by
  obtain ⟨s', ha, he, -⟩ := invocation_action hnodes hdown hpre hQ hrun hk σ
  exact ⟨s', he, hb s' ha⟩

/-- The exceptional exit of an invocation is one action of its exceptional
effect. -/
theorem invocation_throw_action {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam}
    {Qres Rres : Heap → Prop} {m : Nat} (hnodes : NodesChecked P pre Ξres Tres Qres Rres m)
    (hdown : AdminClosed pre m) {l : Nat} {ρ : Env} {s : IndexedHeap} (hpre : pre l ρ m s)
    {ce : Footprints.Closed} (hR : ∀ h, Rres h → ce.Holds s.h h) {k : Nat} {h' : Heap} {e : Tm}
    (hrun : Transitions P k s.h (.at l ρ) h' (.raised e)) (hk : k < s.n) (σ : Env) :
    ∃ s' : IndexedHeap, Action ce.fp σ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ Scoped 0 e ∧
      Ξres s'.n s'.W e := by
  obtain ⟨s', ha, he, hn, hsc, hΞ, hr⟩ := invocation_raised hnodes hdown hpre hrun hk
  refine ⟨s', ⟨ha, ?_⟩, he, hn, hsc, hΞ⟩
  rw [he]
  exact Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp (hR h' hr))

/-! ## Composing node effects from the invocation entry -/

/-- **A closed node effect within the bound composes onto the bound so far.** -/
theorem bound_step {c cn : Footprints.Closed} {h₀ : Heap} {σ : Env} {s₀ s : IndexedHeap}
    (hI : c.Holds h₀ s₀.h) (ha : Action cn.fp σ s₀ s) (hle : cn.le c = true) : c.Holds h₀ s.h :=
  hI.trans_on ((Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp ha.2)).mono hle |>.on _)

/-- **The fresh-store exemption**: a node effect within the bound on the
locations the invocation's entry heap has composes onto the bound so far;
what the node does to a location allocated during the invocation is
unbounded. -/
theorem bound_step_fresh {c : Footprints.Closed} {h₀ h h' : Heap} (hI : c.Holds h₀ h)
    (hn : c.HoldsOn (· < h₀.length) h h') : c.Holds h₀ h' :=
  hI.trans_on hn

/-- The bound so far survives the administrative transitions, which keep the
heap: conjoined to node assertions they keep, it keeps `AdminClosed`. -/
theorem adminClosed_bound {pre : Nat → Assertion} {m : Nat} (hdown : AdminClosed pre m) (c : Footprints.Closed)
    (h₀ : Heap) : AdminClosed (fun l ρ m s => pre l ρ m s ∧ c.Holds h₀ s.h) m :=
  fun l ρ s s' ha he ⟨hp, hc⟩ => ⟨hdown l ρ s s' ha he hp, he ▸ hc⟩

/-- **A regional node effect composes from the invocation entry**: the bound
so far `Φp` at the entry values `ρ₀` from the entry state, a node's action of
`Ψ` at its own positions `σ`, the rebasing evidence holding at the node's
entry, and an inclusion whose class evidence holds at the invocation's entry
heap give an action of `Φq` from the invocation's entry (`Post.compose_at`). -/
theorem action_compose_at {Φp Ψ Φq : Footprint} {cl : ClassEvidence} {ρ₀ σ : Env} {ev : RebaseEvidence}
    {sI s₀ s : IndexedHeap} (hp : Action Φp ρ₀ sI s₀) (hn : Action Ψ σ s₀ s) (hk : RebaseOk ev σ ρ₀ sI.h s₀.h)
    (hle : Footprint.le cl (Φp ++ rebaseAll ev Ψ) Φq = true) (hc : ClassOk cl ρ₀ sI.h) :
    Action Φq ρ₀ sI s :=
  ⟨hp.1.trans hn.1, Post.compose_at hp.2 hn.2 hk hle hc⟩

/-- **Rebasing through stable paths**: evidence that links each step position
to an entry position and path along which the entry world fixes the
position's value, and states no agreement or freshness, holds at every heap
the invocation reaches. -/
theorem rebaseOk_stable {ev : RebaseEvidence} {σ ρ₀ : Env} {sI : IndexedHeap} {h : Heap}
    (hlink : ∀ s x q, ev.link s = some (x, q) → StablePath sI.W (ρ₀ x) q (σ s))
    (hagree : ∀ s p, ev.agree s p = false) (hfresh : ∀ s, ev.fresh s = false)
    (hfield : ∀ s f, ev.freshField s f = false) : RebaseOk ev σ ρ₀ sI.h h where
  link s x q he := (hlink s x q he).read sI.pos sI.ok
  agree s p he := by rw [hagree s p] at he; cases he
  fresh s he := by rw [hfresh s] at he; cases he
  freshField s f he := by rw [hfield s f] at he; cases he

end Verification.TolerantFrames
