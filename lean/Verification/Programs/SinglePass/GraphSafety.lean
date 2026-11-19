import Verification.Semantics.IndexedStates
import Verification.Programs.ExpressionEffects
import Verification.Programs.ControlFlow

/-! # Graph safety from node obligations

A graph run that `SafeGraph` covers, with budget left, ends in a state an
admissible transition reaches, by determinism of the graph machine's
transitions (`graph_run`). A graph whose every node meets its obligations
from the states its entry assertion admits, with the administrative nodes'
assertions closed downward, is safe from every node entry whose assertion
holds (`graph_safe`, `graph_safe_at`). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations

/-! ## Graph runs -/

open ControlFlow in
/-- Finite closure of the graph machine's transitions, with its count. -/
inductive Transitions (P : Program) : Nat → Heap → State → Heap → State → Prop where
  | refl : Transitions P 0 h s h s
  | next : Transition P h s h' s' → Transitions P k h' s' h'' s'' → Transitions P (k + 1) h s h'' s''

open ControlFlow in
/-- **The graph machine is deterministic**: one state in one heap has at most
one next state. -/
theorem transition_det {P : Program} {h h₁ h₂ : Heap} {s s₁ s₂ : State}
    (t₁ : Transition P h s h₁ s₁) (t₂ : Transition P h s h₂ s₂) : h₁ = h₂ ∧ s₁ = s₂ := by
  cases t₁ with
  | enter hn =>
    cases t₂ with
    | enter hn' => rw [hn] at hn'; cases hn'; exact ⟨rfl, rfl⟩
  | expr st =>
    cases t₂ <;> first
      | (rename_i st'; obtain ⟨rfl, rfl⟩ := Step_det st st'; exact ⟨rfl, rfl⟩)
      | exact absurd st (value_no_step (by assumption))
      | exact absurd st (value_no_step rfl)
      | exact absurd st (raises_no_step (by assumption))
  | handle hr =>
    cases t₂ <;> first
      | (rename_i hr'; cases Raises_det hr hr'; exact ⟨rfl, rfl⟩)
      | exact absurd ‹Step _ _ _ _› (raises_no_step hr)
      | (exfalso; have hv := raises_not_val hr; simp_all [isVal])
  | raise hr =>
    cases t₂ <;> first
      | (rename_i hr'; cases Raises_det hr hr'; exact ⟨rfl, rfl⟩)
      | exact absurd ‹Step _ _ _ _› (raises_no_step hr)
      | (exfalso; have hv := raises_not_val hr; simp_all [isVal])
  | ret _ | bind _ | effect _ | tagBind _ | yes | no | yesBind | noBind =>
    cases t₂ <;> first
      | exact ⟨rfl, rfl⟩
      | exact absurd ‹Step _ _ _ _› (value_no_step (by assumption))
      | exact absurd ‹Step _ _ _ _› (value_no_step rfl)
      | (exfalso; have hv := raises_not_val ‹Raises _ _›; simp_all [isVal])

open ControlFlow in
/-- **A graph run that `SafeGraph` covers, with budget left, ends in a state
an admissible transition reaches**, the graph's safety continuing there. -/
theorem graph_run {Ξ T : Fam} {P : Program} :
    ∀ {k h st h' st'}, Transitions P k h st h' st' → ∀ (s : IndexedHeap), s.h = h → k < s.n →
      SafeGraph Ξ P T s.n s.W s.h st →
      ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        SafeGraph Ξ P T s'.n s'.W s'.h st' := by
  intro k h st h' st' hst
  induction hst with
  | refl => intro s hs _ hsafe; exact ⟨s, Admissible.refl s, hs, rfl, hsafe⟩
  | next tr _ ih =>
    intro s hs hk hsafe
    obtain ⟨n, W, h₀, pos, adm, ok⟩ := s
    simp only at hs hk hsafe ⊢
    subst hs
    cases n with
    | zero => omega
    | succ m =>
      rcases hsafe.2 with (⟨v, rfl, -⟩ | ⟨v, rfl, -⟩) | ⟨U, h₁, st₁, hx, hu, tr', hh, hs'⟩
      · cases tr
      · cases tr
      · obtain ⟨rfl, rfl⟩ := transition_det tr tr'
        obtain ⟨s', ha, he, hn, hsafe'⟩ :=
          ih ⟨m, U, _, by omega, hu, hh⟩ rfl (by simp only; omega) hs'
        exact ⟨s', Admissible.trans ⟨Nat.le_succ m, hx⟩ ha, he, by simp only at hn; omega, hsafe'⟩

/-! ## Graph safety from node obligations

`SafeGraph` is established, not assumed: an invariant over `.at`, partially
evaluated `.eval`, `.done` and `.raised` states gives a successor at every
positive budget. Observations are made only at positive states; at budget zero
the invariant states the state's reference validity alone (`StateRefs`). Entering a node and leaving it by a
continuation or a handler each spend one level, as in `Transition`. -/

open ControlFlow PointClaims

/-- `(n, W)` is reached from `s₀`: a budget at most `s₀`'s and a world
extending `s₀`'s, truncated. -/
def Reach (s₀ : IndexedHeap) (n : Nat) (W : WorldT n) : Prop :=
  ∃ hle : n ≤ s₀.n, WExt (trunc n hle s₀.W) W

/-- `v` is of `T` one level above `s`, at a world truncating to `s`'s: the
type a value or a throw has at the step before the transition that leaves the
node. -/
def Above (T : Fam) (s : IndexedHeap) (v : Tm) : Prop :=
  ∃ U : WorldT (s.n + 1), trunc s.n (Nat.le_succ _) U = s.W ∧ T (s.n + 1) U v

/-- What a continuation needs of a node's value to take a transition: a
branch and a `branchBind` a Boolean; a `tagBind` any value. -/
def ShapeOk (v : Tm) : Continuation → Prop
  | .ret | .bind _ | .effect _ => True
  | .branch _ _ => v = .tru ∨ v = .fls
  | .branchBind _ _ => v = .tru ∨ v = .fls
  | .tagBind _ _ _ => True

/-- The obligation a normal exit with value `v` meets at the state `s` its
continuation's transition reaches: the target's assertion at its environment
(at a `branchBind`, the arm of the Boolean with the value pushed; at a
`tagBind`, the arm of the tag's answer in `s`'s heap with the value pushed),
or the result type and the graph's normal exit post `Qres`. -/
def NormalTarget (pre : Nat → Assertion) (Tres : Fam) (Qres : Heap → Prop) (ρ : Env) (m : Nat) (s : IndexedHeap)
    (v : Tm) : Continuation → Prop
  | .ret => Tres s.n s.W v ∧ Qres s.h
  | .bind l => pre l.label (mapEnv l.mapping (push v ρ)) m s
  | .effect l => pre l.label (mapEnv l.mapping ρ) m s
  | .branch y n => (v = .tru ∧ pre y.label (mapEnv y.mapping ρ) m s) ∨
      (v = .fls ∧ pre n.label (mapEnv n.mapping ρ) m s)
  | .branchBind y n => (v = .tru ∧ pre y.label (mapEnv y.mapping (push v ρ)) m s) ∨
      (v = .fls ∧ pre n.label (mapEnv n.mapping (push v ρ)) m s)
  | .tagBind tag y n => (tagHoldsIn s.h tag v = true ∧ pre y.label (mapEnv y.mapping (push v ρ)) m s) ∨
      (tagHoldsIn s.h tag v = false ∧ pre n.label (mapEnv n.mapping (push v ρ)) m s)

/-- The obligation a throw of `e` meets at the state the handler's transition
reaches: the handler's assertion with `e` bound, or, escaping, the graph's
exception family and its exceptional exit post `Rres`. -/
def RaiseTarget (pre : Nat → Assertion) (Ξres : Fam) (Rres : Heap → Prop) (ρ : Env) (m : Nat) (s : IndexedHeap)
    (e : Tm) : Option Target → Prop
  | some l => pre l.label (mapEnv l.mapping (push e ρ)) m s
  | none => Ξres s.n s.W e ∧ Rres s.h

/-- A node's exit obligations from its entry state `s₀`, exit by exit: the
normal exit within `cn` with post `Qn`, the exceptional one within `ce` with
post `Qe`. The shape is required at every budget, the targets at positive
states only. -/
structure NodeObligations (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (Ξ T : Fam)
    (cn ce : Footprints.Closed)
    (Qn : Post) (Qe : Heap → Prop) (ρ : Env) (m : Nat) (s₀ : IndexedHeap) (k : Continuation)
    (x : Option Target) : Prop where
  shape : ∀ (j : Nat) (U : WorldT (j + 1)) (h : Heap) (v : Tm), isVal v = true → T (j + 1) U v →
    cn.Holds s₀.h h → Qn h v → ShapeOk v k
  normal : ∀ (s : IndexedHeap) (v : Tm), Action cn.fp ρ s₀ s → isVal v = true → Above T s v → Qn s.h v →
    NormalTarget pre Tres Qres ρ m s v k
  raise : ∀ (s : IndexedHeap) (e : Tm), Action ce.fp ρ s₀ s → Scoped 0 e → Above Ξ s e → Qe s.h →
    RaiseTarget pre Ξres Rres ρ m s e x

/-- The entry mark lies within the current heap. -/
def marked (pre : Nat → Assertion) : Nat → Assertion :=
  fun l ρ m s => pre l ρ m s ∧ m ≤ s.h.length

/-- A partially evaluated node: its local safety from its entry state `s₀`,
the current world reached from `s₀`, and its exit obligations. -/
def EvalOk (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (m n : Nat) (W : WorldT n) (h : Heap) (t : Tm)
    (ρ : Env) (k : Continuation) (x : Option Target) : Prop :=
  ∃ (s₀ : IndexedHeap) (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
    Reach s₀ n W ∧
    SafePostExc Ξ T (fun h' v => cn.Holds s₀.h h' ∧ Qn h' v) (fun h' => ce.Holds s₀.h h' ∧ Qe h') n W h t ∧
    NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x

/-- The graph invariant: a node's assertion at `.at`, a partially evaluated
node at `.eval`, the result type at `.done`, the exception family at
`.raised`, with the exits' posts `Qres` and `Rres` of the heap; each only at
positive budget. -/
def GraphInv (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (m n : Nat) (W : WorldT n)
    (h : Heap) : State → Prop
  | .at l ρ => ∀ (hp : 0 < n) (ha : WorldAdm W) (ho : HeapOk n W h), pre l ρ m ⟨n, W, h, hp, ha, ho⟩
  | .eval t ρ k x => 0 < n → EvalOk pre Ξres Tres Qres Rres m n W h t ρ k x
  | .done v => 0 < n → isVal v = true ∧ Tres n W v ∧ Qres h
  | .raised v => 0 < n → Scoped 0 v ∧ Ξres n W v ∧ Rres h

/-- Every node a label's assertion reaches exists and meets its local safety
and exit obligations from every state where the assertion holds. -/
def NodesChecked (P : Program) (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (m : Nat) :
    Prop :=
  ∀ l ρ (s : IndexedHeap), pre l ρ m s → ∃ node, P[l]? = some node ∧
    (RefsOk s.W (instantiate 0 ρ node.expression) → RootsOk s.W ρ →
    ∃ (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
      SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
        s.n s.W s.h (instantiate 0 ρ node.expression) ∧
      NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s node.continuation node.handler)

/-- The node assertions survive the administrative steps: a truncation of
the world with the heap unchanged. -/
def AdminClosed (pre : Nat → Assertion) (m : Nat) : Prop :=
  ∀ l ρ (s s' : IndexedHeap), Admissible s s' → s'.h = s.h → pre l ρ m s → pre l ρ m s'

theorem Reach.step {s₀ : IndexedHeap} {j : Nat} {U : WorldT (j + 1)} {U' : WorldT j}
    (hr : Reach s₀ (j + 1) U) (hx : WExt (trunc j (Nat.le_succ j) U) U') : Reach s₀ j U' := by
  obtain ⟨hle, hx₀⟩ := hr
  refine ⟨Nat.le_trans (Nat.le_succ j) hle, ?_⟩
  simpa only [trunc_trunc] using WExt_trans (WExt_trunc (Nat.le_succ j) hx₀) hx

/-- The state one level below `(j+1, U, h)`, its world truncated. -/
def below (j : Nat) (U : WorldT (j + 1)) (h : Heap) (hp : 0 < j) (ha : WorldAdm U)
    (ho : HeapOk (j + 1) U h) : IndexedHeap :=
  ⟨j, trunc j (Nat.le_succ j) U, h, hp, WorldAdm_trunc _ ha, HeapOk_trunc j U h ho⟩

theorem below_action {s₀ : IndexedHeap} {c : Footprints.Closed} {ρ : Env} {j : Nat} {U : WorldT (j + 1)}
    {h : Heap} {hp ha ho} (hr : Reach s₀ (j + 1) U) (hc : c.Holds s₀.h h) :
    Action c.fp ρ s₀ (below j U h hp ha ho) :=
  ⟨hr.step (WExt_refl _), Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp hc)⟩

/-! ## Framed returns

A run whose framed nodes `F` are trusted to return within `Ret` (normal
exit) and `RetE` (throw), as `HeapObservations.SafeRet` states it of the
term that runs the graph: entering a framed node `l` at the heap `h₀`
records `(l, h₀)` as the pending evaluation (`enterPend`), its term's steps
keep it, and the transition leaving it meets `Ret l ρ h₀` at the heap it
leaves where the term is a value and `RetE l ρ h₀` where it throws
(`RetAtG`). With no framed node every transition meets the returns, and the
statements below are the ones above (`graph_step`, `graph_safe`). -/

/-- **The return premise of a pending evaluation** at the heap a node
leaves: `R` at the node, its environment and the heap it was entered at;
`True` where none is pending. -/
def RetP (R : Nat → Env → Heap → Heap → Prop) : Option (Nat × Heap) → Env → Heap → Prop
  | some (l, h₀), ρ, h' => R l ρ h₀ h'
  | none, _, _ => True

/-- The pending evaluation an entry of node `l` at the heap `h` starts:
`(l, h)` where `l` is framed. -/
def enterPend (F : Nat → Bool) (l : Nat) (h : Heap) : Option (Nat × Heap) :=
  cond (F l) (some (l, h)) none

/-- **The pending evaluation after a transition** from `st` at the heap `h`
to `st'`: an entry starts one (`enterPend`), a step of the node's term
keeps it, any other transition clears it. -/
def pendG (F : Nat → Bool) (p : Option (Nat × Heap)) (h : Heap) : State → State → Option (Nat × Heap)
  | .at l _, _ => enterPend F l h
  | .eval .., .eval .. => p
  | _, _ => none

/-- **A transition meets the framed returns**: one leaving a node's
evaluation, at the heap `h'`, meets the pending evaluation's `Ret` where the
term is a value and its `RetE` where it is not (a throw); every other
transition meets them. -/
def RetAtG (Ret RetE : Nat → Env → Heap → Heap → Prop) (p : Option (Nat × Heap)) (h' : Heap) :
    State → State → Prop
  | .eval _ _ _ _, .eval _ _ _ _ => True
  | .eval t ρ _ _, _ => (isVal t = true → RetP Ret p ρ h') ∧ (isVal t = false → RetP RetE p ρ h')
  | _, _ => True

/-- **The graph machine is safe at framed returns** (`SafeGraph` with the
run followed past a transition only where it meets the framed returns,
`RetAtG`, the pending evaluation after it `pendG`'s). -/
def SafeGraphRet (Ξ : Fam) (P : Program) (T : Fam) (F : Nat → Bool) (Ret RetE : Nat → Env → Heap → Heap → Prop) :
    (n : Nat) → WorldT n → Option (Nat × Heap) → Heap → State → Prop
  | 0, W, _, _, s => StateRefs W s
  | n+1, W, p, h, s => StateRefs W s ∧
    (((∃ v, s = .done v ∧ isVal v = true ∧ T (n+1) W v) ∨ (∃ v, s = .raised v ∧ Scoped 0 v ∧ Ξ (n+1) W v)) ∨
    ∃ U : WorldT n, ∃ h' s', WExt (trunc n (Nat.le_succ n) W) U ∧
      WorldAdm U ∧ Transition P h s h' s' ∧ HeapOk n U h' ∧
        (RetAtG Ret RetE p h' s s' → SafeGraphRet Ξ P T F Ret RetE n U (pendG F p h s s') h' s'))

/-- With nothing pending every transition meets the returns. -/
theorem retAtG_none {Ret RetE : Nat → Env → Heap → Heap → Prop} (h' : Heap) (s s' : State) :
    RetAtG Ret RetE none h' s s' := by
  cases s <;> cases s' <;> simp [RetAtG, RetP]

/-- With no framed node nothing is pending after a transition from a state
with nothing pending. -/
theorem pendG_false (h : Heap) (s s' : State) : pendG (fun _ => false) none h s s' = none := by
  cases s <;> cases s' <;> rfl

/-- **With no framed node, safety at framed returns is `SafeGraph`.** -/
theorem SafeGraphRet.erase {Ξ T : Fam} {P : Program} {Ret RetE : Nat → Env → Heap → Heap → Prop} :
    ∀ {n : Nat} {W : WorldT n} {h : Heap} {s : State},
      SafeGraphRet Ξ P T (fun _ => false) Ret RetE n W none h s → SafeGraph Ξ P T n W h s := by
  intro n
  induction n with
  | zero => intro _ _ _ hs; exact hs
  | succ n ih =>
    intro W h s hs
    obtain ⟨hr, hs⟩ := hs
    refine ⟨hr, ?_⟩
    rcases hs with ht | ⟨U, h', s', hx, hu, tr, hh, hs⟩
    · exact .inl ht
    · have hs' := hs (retAtG_none h' s s')
      rw [pendG_false] at hs'
      exact .inr ⟨U, h', s', hx, hu, tr, hh, ih hs'⟩

/-- **A node's exit obligations under return premises**: `NodeObligations`
with each exit's target required where the exit's heap meets `Rn` (normal)
or `Re` (throw). -/
structure NodeObligationsR (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (Ξ T : Fam)
    (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop) (Rn Re : Heap → Prop) (ρ : Env) (m : Nat)
    (s₀ : IndexedHeap) (k : Continuation) (x : Option Target) : Prop where
  shape : ∀ (j : Nat) (U : WorldT (j + 1)) (h : Heap) (v : Tm), isVal v = true → T (j + 1) U v →
    cn.Holds s₀.h h → Qn h v → ShapeOk v k
  normal : ∀ (s : IndexedHeap) (v : Tm), Action cn.fp ρ s₀ s → isVal v = true → Above T s v → Qn s.h v →
    Rn s.h → NormalTarget pre Tres Qres ρ m s v k
  raise : ∀ (s : IndexedHeap) (e : Tm), Action ce.fp ρ s₀ s → Scoped 0 e → Above Ξ s e → Qe s.h →
    Re s.h → RaiseTarget pre Ξres Rres ρ m s e x

section
variable {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop} {cn ce : Footprints.Closed}
  {Qn : Post} {Qe : Heap → Prop} {ρ : Env} {m : Nat} {s₀ : IndexedHeap} {k : Continuation} {x : Option Target}

/-- Obligations hold under any return premises. -/
theorem NodeObligations.toR (ho : NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x)
    (Rn Re : Heap → Prop) : NodeObligationsR pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe Rn Re ρ m s₀ k x :=
  ⟨ho.shape, fun s v ha hv hT hq _ => ho.normal s v ha hv hT hq, fun s e ha hsc hΞ hq _ => ho.raise s e ha hsc hΞ hq⟩

/-- Obligations under return premises every heap meets are obligations. -/
theorem NodeObligationsR.toPlain {Rn Re : Heap → Prop}
    (ho : NodeObligationsR pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe Rn Re ρ m s₀ k x)
    (hn : ∀ h, Rn h) (he : ∀ h, Re h) : NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x :=
  ⟨ho.shape, fun s v ha hv hT hq => ho.normal s v ha hv hT hq (hn _),
    fun s e ha hsc hΞ hq => ho.raise s e ha hsc hΞ hq (he _)⟩
end

/-- Every admissible exit preserves a bound on the entry mark, under return
premises. -/
theorem nodeObligationsR_marked {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop}
    {cn ce : Footprints.Closed} {Qn : Post} {Qe : Heap → Prop} {Rn Re : Heap → Prop} {ρ : Env} {m : Nat}
    {s : IndexedHeap} {k : Continuation} {x : Option Target} (hm : m ≤ s.h.length)
    (ho : NodeObligationsR pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe Rn Re ρ m s k x) :
    NodeObligationsR (marked pre) Ξres Tres Qres Rres Ξ T cn ce Qn Qe Rn Re ρ m s k x where
  shape := ho.shape
  normal s' v ha hv hT hq hR := by
    have ht := ho.normal s' v ha hv hT hq hR
    have hm' := (Nat.le_trans hm ha.1.length_le)
    cases k with
    | ret => exact ht
    | effect t => exact ⟨ht, hm'⟩
    | bind t => exact ⟨ht, hm'⟩
    | _ => exact ht.imp (fun h => ⟨h.1, h.2, hm'⟩) (fun h => ⟨h.1, h.2, hm'⟩)
  raise s' e ha hsc hΞ hq hR := by
    have ht := ho.raise s' e ha hsc hΞ hq hR
    cases x with
    | none => exact ht
    | some t => exact ⟨ht, (Nat.le_trans hm ha.1.length_le)⟩

/-- Every admissible exit preserves a bound on the entry mark
(`nodeObligationsR_marked` with no return premise). -/
theorem nodeObligations_marked {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop}
    {cn ce : Footprints.Closed} {Qn : Post} {Qe : Heap → Prop} {ρ : Env} {m : Nat} {s : IndexedHeap}
    {k : Continuation} {x : Option Target} (hm : m ≤ s.h.length)
    (ho : NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s k x) :
    NodeObligations (marked pre) Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s k x :=
  (nodeObligationsR_marked hm (ho.toR (fun _ => True) (fun _ => True))).toPlain (fun _ => trivial) (fun _ => trivial)

/-- A partially evaluated node under the pending evaluation `p`: `EvalOk`
with its exits' targets required where they meet `p`'s returns. -/
def EvalOkR (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop)
    (Ret RetE : Nat → Env → Heap → Heap → Prop) (p : Option (Nat × Heap)) (m n : Nat) (W : WorldT n) (h : Heap)
    (t : Tm) (ρ : Env) (k : Continuation) (x : Option Target) : Prop :=
  ∃ (s₀ : IndexedHeap) (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
    Reach s₀ n W ∧
    SafePostExc Ξ T (fun h' v => cn.Holds s₀.h h' ∧ Qn h' v) (fun h' => ce.Holds s₀.h h' ∧ Qe h') n W h t ∧
    NodeObligationsR pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe (RetP Ret p ρ) (RetP RetE p ρ) ρ m s₀ k x

/-- The graph invariant under the pending evaluation `p` (`GraphInv`, its
partially evaluated node `EvalOkR`'s). -/
def GraphInvR (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop)
    (Ret RetE : Nat → Env → Heap → Heap → Prop) (m n : Nat) (W : WorldT n) (p : Option (Nat × Heap))
    (h : Heap) : State → Prop
  | .at l ρ => ∀ (hp : 0 < n) (ha : WorldAdm W) (ho : HeapOk n W h), pre l ρ m ⟨n, W, h, hp, ha, ho⟩
  | .eval t ρ k x => 0 < n → EvalOkR pre Ξres Tres Qres Rres Ret RetE p m n W h t ρ k x
  | .done v => 0 < n → isVal v = true ∧ Tres n W v ∧ Qres h
  | .raised v => 0 < n → Scoped 0 v ∧ Ξres n W v ∧ Rres h

/-- **Every node meets its obligations at framed returns**: `NodesChecked`
with a framed node's exits' targets required where they meet its returns
from the heap it is entered at. -/
def NodesCheckedR (P : Program) (pre : Nat → Assertion) (F : Nat → Bool) (Ret RetE : Nat → Env → Heap → Heap → Prop)
    (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (m : Nat) : Prop :=
  ∀ l ρ (s : IndexedHeap), pre l ρ m s → ∃ node, P[l]? = some node ∧
    (RefsOk s.W (instantiate 0 ρ node.expression) → RootsOk s.W ρ →
    ∃ (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
      SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
        s.n s.W s.h (instantiate 0 ρ node.expression) ∧
      NodeObligationsR pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe (RetP Ret (enterPend F l s.h) ρ)
        (RetP RetE (enterPend F l s.h) ρ) ρ m s node.continuation node.handler)

section
variable {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
  {Ret RetE : Nat → Env → Heap → Heap → Prop}

/-- Nodes checked are checked at framed returns with no framed node. -/
theorem NodesChecked.toR (hn : NodesChecked P pre Ξres Tres Qres Rres m) :
    NodesCheckedR P pre (fun _ => false) Ret RetE Ξres Tres Qres Rres m := by
  intro l ρ s hp
  obtain ⟨node, hP, hck⟩ := hn l ρ s hp
  refine ⟨node, hP, fun hr hρ => ?_⟩
  obtain ⟨Ξ, T, cn, ce, Qn, Qe, hs, ho⟩ := hck hr hρ
  exact ⟨Ξ, T, cn, ce, Qn, Qe, hs, ho.toR _ _⟩

/-- Nodes checked at framed returns with no framed node are checked. -/
theorem NodesCheckedR.toPlain (hn : NodesCheckedR P pre (fun _ => false) Ret RetE Ξres Tres Qres Rres m) :
    NodesChecked P pre Ξres Tres Qres Rres m := by
  intro l ρ s hp
  obtain ⟨node, hP, hck⟩ := hn l ρ s hp
  refine ⟨node, hP, fun hr hρ => ?_⟩
  obtain ⟨Ξ, T, cn, ce, Qn, Qe, hs, ho⟩ := hck hr hρ
  exact ⟨Ξ, T, cn, ce, Qn, Qe, hs, ho.toPlain (fun _ => trivial) (fun _ => trivial)⟩

/-- The graph invariant is the invariant with nothing pending. -/
theorem GraphInv.toR {n : Nat} {W : WorldT n} {h : Heap} {st : State}
    (hi : GraphInv pre Ξres Tres Qres Rres m n W h st) : GraphInvR pre Ξres Tres Qres Rres Ret RetE m n W none h st := by
  cases st with
  | «at» => exact hi
  | eval t ρ k x =>
    intro hp
    obtain ⟨s₀, Ξ, T, cn, ce, Qn, Qe, hr, hs, ho⟩ := hi hp
    exact ⟨s₀, Ξ, T, cn, ce, Qn, Qe, hr, hs, ho.toR _ _⟩
  | done => exact hi
  | raised => exact hi

/-- The invariant with nothing pending is the graph invariant. -/
theorem GraphInvR.toPlain {n : Nat} {W : WorldT n} {h : Heap} {st : State}
    (hi : GraphInvR pre Ξres Tres Qres Rres Ret RetE m n W none h st) : GraphInv pre Ξres Tres Qres Rres m n W h st := by
  cases st with
  | «at» => exact hi
  | eval t ρ k x =>
    intro hp
    obtain ⟨s₀, Ξ, T, cn, ce, Qn, Qe, hr, hs, ho⟩ := hi hp
    exact ⟨s₀, Ξ, T, cn, ce, Qn, Qe, hr, hs, ho.toPlain (fun _ => trivial) (fun _ => trivial)⟩
  | done => exact hi
  | raised => exact hi
end

/-- **One transition from the graph invariant, at framed returns.** At a
positive budget a state the invariant describes under the pending
evaluation `p` is terminal, with its result, or takes a transition, its
world extending the truncated one, to a state the invariant describes one
level down under the pending evaluation after it, where the transition
meets the framed returns. -/
theorem graph_stepR {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    {F : Nat → Bool} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    (hnodes : NodesCheckedR P pre F Ret RetE Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {n : Nat}
    {W : WorldT (n + 1)} {h : Heap} {st : State} {p : Option (Nat × Heap)} (ha : WorldAdm W) (ho : HeapOk (n + 1) W h)
    (hPr : ∀ node ∈ P, RefsOk W node.expression) (hr : StateRefs W st)
    (hinv : GraphInvR pre Ξres Tres Qres Rres Ret RetE m (n + 1) W p h st) :
    ((∃ v, st = .done v ∧ isVal v = true ∧ Tres (n + 1) W v) ∨
      (∃ v, st = .raised v ∧ Scoped 0 v ∧ Ξres (n + 1) W v)) ∨
    ∃ (U : WorldT n) (h' : Heap) (st' : State), WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧
      Transition P h st h' st' ∧ HeapOk n U h' ∧ StateRefs U st' ∧
        (RetAtG Ret RetE p h' st st' → GraphInvR pre Ξres Tres Qres Rres Ret RetE m n U (pendG F p h st st') h' st') := by
  have ha' := WorldAdm_trunc (Nat.le_succ n) ha
  have ho' := HeapOk_trunc n W h ho
  have next : ∀ {h' st'} (U : WorldT n), WExt (trunc n (Nat.le_succ n) W) U → WorldAdm U →
      Transition P h st h' st' → HeapOk n U h' → StateRefs U st' →
      (RetAtG Ret RetE p h' st st' → GraphInvR pre Ξres Tres Qres Rres Ret RetE m n U (pendG F p h st st') h' st') →
      ((∃ v, st = .done v ∧ isVal v = true ∧ Tres (n + 1) W v) ∨
        (∃ v, st = .raised v ∧ Scoped 0 v ∧ Ξres (n + 1) W v)) ∨
      ∃ (U : WorldT n) (h' : Heap) (st' : State), WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧
        Transition P h st h' st' ∧ HeapOk n U h' ∧ StateRefs U st' ∧
          (RetAtG Ret RetE p h' st st' →
            GraphInvR pre Ξres Tres Qres Rres Ret RetE m n U (pendG F p h st st') h' st') :=
    fun U hx hu tr hh hrs hi => .inr ⟨U, _, _, hx, hu, tr, hh, hrs, hi⟩
  cases st with
  | «at» l ρ =>
    have hpre := hinv (Nat.zero_lt_succ n) ha ho
    obtain ⟨node, hP, -⟩ := hnodes l ρ _ hpre
    have hnr : RefsOk (trunc n (Nat.le_succ n) W) (instantiate 0 ρ node.expression) :=
      RefsOk_trunc _ (node_refs (hPr node (List.mem_of_getElem? hP)) hr)
    refine next _ (WExt_refl _) ha' (.enter hP) ho' ⟨hnr, fun i => RefsOk_trunc _ (hr i)⟩ fun _ hp => ?_
    let s₀ : IndexedHeap := ⟨n, trunc n (Nat.le_succ n) W, h, hp, ha', ho'⟩
    have hpre₀ := hdown l ρ ⟨n + 1, W, h, Nat.zero_lt_succ n, ha, ho⟩ s₀ ⟨Nat.le_succ n, WExt_refl _⟩ rfl hpre
    obtain ⟨node', hP', hck⟩ := hnodes l ρ s₀ hpre₀
    rw [hP] at hP'; cases hP'
    obtain ⟨Ξ, T, cn, ce, Qn, Qe, hsafe, hobl⟩ := hck hnr (fun i => RefsOk_trunc _ (hr i))
    exact ⟨s₀, Ξ, T, cn, ce, Qn, Qe, ⟨Nat.le_refl _, by rw [trunc_id]; exact WExt_refl _⟩, hsafe, hobl⟩
  | eval t ρ k x =>
    obtain ⟨htr, hρr⟩ := hr
    have htU : RefsOk (trunc n (Nat.le_succ n) W) t := RefsOk_trunc _ htr
    have hρU : ∀ i, RefsOk (trunc n (Nat.le_succ n) W) (ρ i) := fun i => RefsOk_trunc _ (hρr i)
    obtain ⟨s₀, Ξ, T, cn, ce, Qn, Qe, hr, hsafe, hobl⟩ := hinv (Nat.zero_lt_succ n)
    rcases hsafe.2 with (⟨hv, hT, hc, hq⟩ | ⟨⟨e, hre, hsc, hΞ⟩, hc, hq⟩) | ⟨U, h', t', hx, hu, st, hh, hs'⟩
    · -- a value: the continuation's transition, its target where the return meets `Ret`
      have hshape := hobl.shape n W h t hv hT hc hq
      have tgt : ∀ st', (∀ t' ρ' k' x', st' ≠ .eval t' ρ' k' x') → RetAtG Ret RetE p h (.eval t ρ k x) st' →
          ∀ (hp : 0 < n), NormalTarget pre Tres Qres ρ m (below n W h hp ha ho) t k := fun st' hne hR hp => by
        have hR' : RetP Ret p ρ h := by
          cases st' with
          | eval => exact absurd rfl (hne _ _ _ _)
          | _ => exact hR.1 hv
        exact hobl.normal _ t (below_action hr hc) hv ⟨W, rfl, hT⟩ hq hR'
      cases k with
      | ret =>
        exact next _ (WExt_refl _) ha' (.ret hv) ho' htU fun hR hp =>
          ⟨hv, tgt _ (fun _ _ _ _ h => by cases h) hR hp⟩
      | bind l =>
        exact next _ (WExt_refl _) ha' (.bind hv) ho' (mapEnv_refs _ (push_refs htU hρU))
          fun hR hp _ _ => tgt _ (fun _ _ _ _ h => by cases h) hR hp
      | effect l =>
        exact next _ (WExt_refl _) ha' (.effect hv) ho' (mapEnv_refs _ hρU)
          fun hR hp _ _ => tgt _ (fun _ _ _ _ h => by cases h) hR hp
      | branch y no =>
        rcases hshape with rfl | rfl
        · refine next _ (WExt_refl _) ha' .yes ho' (mapEnv_refs _ hρU) fun hR hp _ _ => ?_
          rcases tgt _ (fun _ _ _ _ h => by cases h) hR hp with ⟨-, hy⟩ | ⟨he, -⟩
          · exact hy
          · cases he
        · refine next _ (WExt_refl _) ha' .no ho' (mapEnv_refs _ hρU) fun hR hp _ _ => ?_
          rcases tgt _ (fun _ _ _ _ h => by cases h) hR hp with ⟨he, -⟩ | ⟨-, hn⟩
          · cases he
          · exact hn
      | branchBind y no =>
        rcases hshape with rfl | rfl
        · refine next _ (WExt_refl _) ha' .yesBind ho' (mapEnv_refs _ (push_refs (RefsOk_of_nil rfl) hρU))
            fun hR hp _ _ => ?_
          rcases tgt _ (fun _ _ _ _ h => by cases h) hR hp with ⟨-, hy⟩ | ⟨he, -⟩
          · exact hy
          · cases he
        · refine next _ (WExt_refl _) ha' .noBind ho' (mapEnv_refs _ (push_refs (RefsOk_of_nil rfl) hρU))
            fun hR hp _ _ => ?_
          rcases tgt _ (fun _ _ _ _ h => by cases h) hR hp with ⟨he, -⟩ | ⟨-, hn⟩
          · cases he
          · exact hn
      | tagBind tag y no =>
        refine next _ (WExt_refl _) ha' (.tagBind hv) ho' (mapEnv_refs _ (push_refs htU hρU)) fun hR hp _ _ => ?_
        rcases tgt _ (fun _ _ _ _ h => by cases h) hR hp with ⟨hq, hy⟩ | ⟨hq, hn⟩
        · simp only [below] at hq
          simp only [hq, if_true]
          exact hy
        · simp only [below] at hq
          simp only [hq, Bool.false_eq_true, if_false]
          exact hn
    · -- a throw: the handler's transition, or the run ends raised, where it meets `RetE`
      have tgt : ∀ st', (∀ t' ρ' k' x', st' ≠ .eval t' ρ' k' x') → RetAtG Ret RetE p h (.eval t ρ k x) st' →
          ∀ (hp : 0 < n), RaiseTarget pre Ξres Rres ρ m (below n W h hp ha ho) e x := fun st' hne hR hp => by
        have hR' : RetP RetE p ρ h := by
          cases st' with
          | eval => exact absurd rfl (hne _ _ _ _)
          | _ => exact hR.2 (raises_not_val hre)
        exact hobl.raise _ e (below_action hr hc) hsc ⟨W, rfl, hΞ⟩ hq hR'
      have heU : RefsOk (trunc n (Nat.le_succ n) W) e := fun r' hr' => htU r' (Kinds.raises_refs hre r' hr')
      cases x with
      | some l =>
        exact next _ (WExt_refl _) ha' (.handle hre) ho' (mapEnv_refs _ (push_refs heU hρU))
          fun hR hp _ _ => tgt _ (fun _ _ _ _ h => by cases h) hR hp
      | none =>
        exact next _ (WExt_refl _) ha' (.raise hre) ho' heU
          fun hR hp => ⟨hsc, tgt _ (fun _ _ _ _ h => by cases h) hR hp⟩
    · -- an expression step: the pending evaluation kept
      exact next U hx hu (.expr st) hh ⟨SafePostExcW.refs hs', fun i => RefsOk_mono hx (hρU i)⟩
        fun _ _ => ⟨s₀, Ξ, T, cn, ce, Qn, Qe, hr.step hx, hs', hobl⟩
  | done v =>
    obtain ⟨hv, hT, -⟩ := hinv (Nat.zero_lt_succ n)
    exact .inl (.inl ⟨v, rfl, hv, hT⟩)
  | raised v =>
    obtain ⟨hsc, hΞ, -⟩ := hinv (Nat.zero_lt_succ n)
    exact .inl (.inr ⟨v, rfl, hsc, hΞ⟩)

/-- **One transition from the graph invariant** (`graph_stepR` with no
framed node). At a positive budget a state the invariant describes is
terminal, with its result, or takes a transition to a state the invariant
describes one level down, its world extending the truncated one. -/
theorem graph_step {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {n : Nat}
    {W : WorldT (n + 1)} {h : Heap} {st : State} (ha : WorldAdm W) (ho : HeapOk (n + 1) W h)
    (hPr : ∀ node ∈ P, RefsOk W node.expression) (hr : StateRefs W st)
    (hinv : GraphInv pre Ξres Tres Qres Rres m (n + 1) W h st) :
    ((∃ v, st = .done v ∧ isVal v = true ∧ Tres (n + 1) W v) ∨
      (∃ v, st = .raised v ∧ Scoped 0 v ∧ Ξres (n + 1) W v)) ∨
    ∃ (U : WorldT n) (h' : Heap) (st' : State), WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧
      Transition P h st h' st' ∧ HeapOk n U h' ∧ StateRefs U st' ∧
        GraphInv pre Ξres Tres Qres Rres m n U h' st' := by
  rcases graph_stepR (Ret := fun _ _ _ _ => True) (RetE := fun _ _ _ _ => True) hnodes.toR hdown ha ho hPr hr
      hinv.toR with ht | ⟨U, h', st', hx, hu, tr, hh, hrs, hi⟩
  · exact .inl ht
  · have hi' := hi (retAtG_none h' st st')
    rw [pendG_false] at hi'
    exact .inr ⟨U, h', st', hx, hu, tr, hh, hrs, hi'.toPlain⟩

/-- **Graph safety at framed returns from node obligations.** Every state
the invariant describes under a pending evaluation is safe at framed returns
for the graph machine, at every budget. -/
theorem graph_safeR {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    {F : Nat → Bool} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    (hnodes : NodesCheckedR P pre F Ret RetE Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) :
    ∀ n (W : WorldT n) p h st, WorldAdm W → HeapOk n W h → (∀ node ∈ P, RefsOk W node.expression) →
      StateRefs W st → GraphInvR pre Ξres Tres Qres Rres Ret RetE m n W p h st →
      SafeGraphRet Ξres P Tres F Ret RetE n W p h st := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ hr _; exact hr
  | succ n ih =>
    intro W p h st ha ho hPr hr hinv
    refine ⟨hr, ?_⟩
    rcases graph_stepR hnodes hdown ha ho hPr hr hinv with (h1 | h2) | ⟨U, h', st', hx, hu, tr, hh, hrs, hi⟩
    · exact .inl (.inl h1)
    · exact .inl (.inr h2)
    · exact .inr ⟨U, h', st', hx, hu, tr, hh, fun hR =>
        ih U _ h' st' hu hh (fun node hm => RefsOk_mono hx (RefsOk_trunc _ (hPr node hm))) hrs (hi hR)⟩

/-- **Graph safety from node obligations** (`graph_safeR` with no framed
node). Every state the invariant describes is safe for the graph machine,
at every budget. -/
theorem graph_safe {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) :
    ∀ n (W : WorldT n) h st, WorldAdm W → HeapOk n W h → (∀ node ∈ P, RefsOk W node.expression) →
      StateRefs W st → GraphInv pre Ξres Tres Qres Rres m n W h st → SafeGraph Ξres P Tres n W h st :=
  fun n W h st ha ho hPr hr hinv =>
    (graph_safeR (Ret := fun _ _ _ _ => True) (RetE := fun _ _ _ _ => True) hnodes.toR hdown n W none h st ha ho
      hPr hr hinv.toR).erase

/-- The graph is safe at framed returns from every node entry whose
assertion holds. -/
theorem graph_safe_atR {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    {F : Nat → Bool} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    (hnodes : NodesCheckedR P pre F Ret RetE Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat} {ρ : Env}
    {s : IndexedHeap} (hpre : pre l ρ m s) (hPr : ∀ node ∈ P, RefsOk s.W node.expression)
    (hρ : ∀ i, RefsOk s.W (ρ i)) (p : Option (Nat × Heap)) :
    SafeGraphRet Ξres P Tres F Ret RetE s.n s.W p s.h (.at l ρ) :=
  graph_safeR hnodes hdown _ _ p _ _ s.adm s.ok hPr hρ fun _ _ _ => hpre

/-- The graph is safe from every node entry whose assertion holds. -/
theorem graph_safe_at {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat} {ρ : Env}
    {s : IndexedHeap} (hpre : pre l ρ m s) (hPr : ∀ node ∈ P, RefsOk s.W node.expression)
    (hρ : ∀ i, RefsOk s.W (ρ i)) : SafeGraph Ξres P Tres s.n s.W s.h (.at l ρ) :=
  graph_safe hnodes hdown _ _ _ _ s.adm s.ok hPr hρ fun _ _ _ => hpre
end Verification.TolerantFrames
