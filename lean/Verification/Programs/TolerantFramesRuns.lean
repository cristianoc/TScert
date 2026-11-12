import Verification.Semantics.TolerantFrames
import Verification.Programs.ExpressionEffects
import Verification.Programs.ControlFlow

/-! # Tolerant frames: graph runs and an expression's action

A graph run that `SafeGraph` covers, with budget left, ends in a state an
admissible transition reaches, by determinism of the graph machine's
transitions. A typed field write's effect judgment
(`ExpressionEffects.field_write_within_exc`) yields, on each exit of a run
with budget left, an action of `{values: any, stores: keep}`, and every length
lower bound survives it by antitonicity and (Grow). -/
namespace Verification.TolerantFrames
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
      rcases hsafe with (⟨v, rfl, -⟩ | ⟨v, rfl, -⟩) | ⟨U, h₁, st₁, hx, hu, tr', hh, hs'⟩
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
the invariant states nothing. Entering a node and leaving it by a
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
    ∃ (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
      SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
        s.n s.W s.h (instantiate 0 ρ node.expression) ∧
      NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s node.continuation node.handler

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

/-- **One transition from the graph invariant.** At a positive budget a state
the invariant describes is terminal, with its result, or takes a transition to
a state the invariant describes one level down, its world extending the
truncated one. -/
theorem graph_step {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {n : Nat}
    {W : WorldT (n + 1)} {h : Heap} {st : State} (ha : WorldAdm W) (ho : HeapOk (n + 1) W h)
    (hinv : GraphInv pre Ξres Tres Qres Rres m (n + 1) W h st) :
    ((∃ v, st = .done v ∧ isVal v = true ∧ Tres (n + 1) W v) ∨
      (∃ v, st = .raised v ∧ Scoped 0 v ∧ Ξres (n + 1) W v)) ∨
    ∃ (U : WorldT n) (h' : Heap) (st' : State), WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧
      Transition P h st h' st' ∧ HeapOk n U h' ∧ GraphInv pre Ξres Tres Qres Rres m n U h' st' := by
  have ha' := WorldAdm_trunc (Nat.le_succ n) ha
  have ho' := HeapOk_trunc n W h ho
  have next : ∀ {h' st'} (U : WorldT n), WExt (trunc n (Nat.le_succ n) W) U → WorldAdm U →
      Transition P h st h' st' → HeapOk n U h' → GraphInv pre Ξres Tres Qres Rres m n U h' st' →
      ((∃ v, st = .done v ∧ isVal v = true ∧ Tres (n + 1) W v) ∨
        (∃ v, st = .raised v ∧ Scoped 0 v ∧ Ξres (n + 1) W v)) ∨
      ∃ (U : WorldT n) (h' : Heap) (st' : State), WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧
        Transition P h st h' st' ∧ HeapOk n U h' ∧ GraphInv pre Ξres Tres Qres Rres m n U h' st' :=
    fun U hx hu tr hh hi => .inr ⟨U, _, _, hx, hu, tr, hh, hi⟩
  cases st with
  | «at» l ρ =>
    have hpre := hinv (Nat.zero_lt_succ n) ha ho
    obtain ⟨node, hP, -⟩ := hnodes l ρ _ hpre
    refine next _ (WExt_refl _) ha' (.enter hP) ho' fun hp => ?_
    let s₀ : IndexedHeap := ⟨n, trunc n (Nat.le_succ n) W, h, hp, ha', ho'⟩
    have hpre₀ := hdown l ρ ⟨n + 1, W, h, Nat.zero_lt_succ n, ha, ho⟩ s₀ ⟨Nat.le_succ n, WExt_refl _⟩ rfl hpre
    obtain ⟨node', hP', Ξ, T, cn, ce, Qn, Qe, hsafe, hobl⟩ := hnodes l ρ s₀ hpre₀
    rw [hP] at hP'; cases hP'
    exact ⟨s₀, Ξ, T, cn, ce, Qn, Qe, ⟨Nat.le_refl _, by rw [trunc_id]; exact WExt_refl _⟩, hsafe, hobl⟩
  | eval t ρ k x =>
    obtain ⟨s₀, Ξ, T, cn, ce, Qn, Qe, hr, hsafe, hobl⟩ := hinv (Nat.zero_lt_succ n)
    rcases hsafe with (⟨hv, hT, hc, hq⟩ | ⟨⟨e, hre, hsc, hΞ⟩, hc, hq⟩) | ⟨U, h', t', hx, hu, st, hh, hs'⟩
    · -- a value: the continuation's transition
      have hshape := hobl.shape n W h t hv hT hc hq
      have tgt : ∀ (hp : 0 < n), NormalTarget pre Tres Qres ρ m (below n W h hp ha ho) t k := fun hp =>
        hobl.normal _ t (below_action hr hc) hv ⟨W, rfl, hT⟩ hq
      cases k with
      | ret => exact next _ (WExt_refl _) ha' (.ret hv) ho' fun hp => ⟨hv, tgt hp⟩
      | bind l => exact next _ (WExt_refl _) ha' (.bind hv) ho' fun hp _ _ => tgt hp
      | effect l => exact next _ (WExt_refl _) ha' (.effect hv) ho' fun hp _ _ => tgt hp
      | branch y no =>
        rcases hshape with rfl | rfl
        · refine next _ (WExt_refl _) ha' .yes ho' fun hp _ _ => ?_
          rcases tgt hp with ⟨-, hy⟩ | ⟨he, -⟩
          · exact hy
          · cases he
        · refine next _ (WExt_refl _) ha' .no ho' fun hp _ _ => ?_
          rcases tgt hp with ⟨he, -⟩ | ⟨-, hn⟩
          · cases he
          · exact hn
      | branchBind y no =>
        rcases hshape with rfl | rfl
        · refine next _ (WExt_refl _) ha' .yesBind ho' fun hp _ _ => ?_
          rcases tgt hp with ⟨-, hy⟩ | ⟨he, -⟩
          · exact hy
          · cases he
        · refine next _ (WExt_refl _) ha' .noBind ho' fun hp _ _ => ?_
          rcases tgt hp with ⟨he, -⟩ | ⟨-, hn⟩
          · cases he
          · exact hn
      | tagBind tag y no =>
        refine next _ (WExt_refl _) ha' (.tagBind hv) ho' fun hp _ _ => ?_
        rcases tgt hp with ⟨hq, hy⟩ | ⟨hq, hn⟩
        · simp only [below] at hq
          simp only [hq, if_true]
          exact hy
        · simp only [below] at hq
          simp only [hq, Bool.false_eq_true, if_false]
          exact hn
    · -- a throw: the handler's transition, or the run ends raised
      have tgt : ∀ (hp : 0 < n), RaiseTarget pre Ξres Rres ρ m (below n W h hp ha ho) e x := fun hp =>
        hobl.raise _ e (below_action hr hc) hsc ⟨W, rfl, hΞ⟩ hq
      cases x with
      | some l => exact next _ (WExt_refl _) ha' (.handle hre) ho' fun hp _ _ => tgt hp
      | none => exact next _ (WExt_refl _) ha' (.raise hre) ho' fun hp => ⟨hsc, tgt hp⟩
    · -- an expression step
      exact next U hx hu (.expr st) hh fun _ => ⟨s₀, Ξ, T, cn, ce, Qn, Qe, hr.step hx, hs', hobl⟩
  | done v =>
    obtain ⟨hv, hT, -⟩ := hinv (Nat.zero_lt_succ n)
    exact .inl (.inl ⟨v, rfl, hv, hT⟩)
  | raised v =>
    obtain ⟨hsc, hΞ, -⟩ := hinv (Nat.zero_lt_succ n)
    exact .inl (.inr ⟨v, rfl, hsc, hΞ⟩)

/-- **Graph safety from node obligations.** Every state the invariant
describes is safe for the graph machine, at every budget. -/
theorem graph_safe {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) :
    ∀ n (W : WorldT n) h st, WorldAdm W → HeapOk n W h → GraphInv pre Ξres Tres Qres Rres m n W h st →
      SafeGraph Ξres P Tres n W h st := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h st ha ho hinv
    rcases graph_step hnodes hdown ha ho hinv with (h1 | h2) | ⟨U, h', st', hx, hu, tr, hh, hi⟩
    · exact .inl (.inl h1)
    · exact .inl (.inr h2)
    · exact .inr ⟨U, h', st', hx, hu, tr, hh, ih U h' st' hu hh hi⟩

/-- The graph is safe from every node entry whose assertion holds. -/
theorem graph_safe_at {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat} {ρ : Env}
    {s : IndexedHeap} (hpre : pre l ρ m s) : SafeGraph Ξres P Tres s.n s.W s.h (.at l ρ) :=
  graph_safe hnodes hdown _ _ _ _ s.adm s.ok fun _ _ _ => hpre

/-! ## Transfer along an exit -/

open HeapKnowledge in
/-- The retained index facts `K`, read at `ρ`, hold at every target
environment `ρ'` under every renaming `g` that maps each slot they name to a
slot of `ρ'` holding the same value. -/
def Transported (K : List IndexFact) (ρ ρ' : Env) (h : Heap) : Prop :=
  ∀ F ∈ K, ∀ (g : Nat → Option Nat) (F' : IndexFact), F.mapM g = some F' →
    (∀ i ∈ F.slots, ∀ j, g i = some j → ρ' j = ρ i) → F'.HoldsAt ρ' h

open HeapKnowledge in
theorem transported_of {K : List IndexFact} {ρ : Env} {h : Heap} (hK : ∀ F ∈ K, F.HoldsAt ρ h)
    (ρ' : Env) : Transported K ρ ρ' h :=
  fun F hF _ _ hm hg => (IndexFact.holdsAt_mapM hm hg).mpr (hK F hF)

/-- A target slot mapped to a source slot reads that slot. -/
theorem mapEnv_slot {θ : Mapping} {ρ : Env} {i j : Nat} (hs : slot θ j = i) : mapEnv θ ρ j = ρ i := by
  simp [mapEnv, hs]

/-- With the exit's value bound, a target slot mapped to source slot `i + 1`
reads the node's slot `i`. -/
theorem mapEnv_push_slot {θ : Mapping} {v : Tm} {ρ : Env} {i j : Nat} (hs : slot θ j = i + 1) :
    mapEnv θ (push v ρ) j = ρ i := by
  simp [mapEnv, hs, push]

open HeapKnowledge in
/-- **TRANSFER.** A node's local safety from `s₀`, its exit-specific footprints
`cn`, `ce` and posts `Qn`, `Qe`; the retained facts `Kn`, `Ke` under the
modality of the exit's footprint; and, per exit, the target obligation from
the exit's value, its type above, its post and the retained facts transported
to every target environment: then the node meets its exit obligations, which
`graph_safe` composes into `SafeGraph`. -/
theorem transfer {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop} {cn ce : Footprints.Closed}
    {Qn : Post}
    {Qe : Heap → Prop} {ρ : Env} {m : Nat} {s₀ : IndexedHeap} {k : Continuation} {x : Option Target}
    {Kn Ke : List IndexFact}
    (hshape : ∀ (j : Nat) (U : WorldT (j + 1)) (h : Heap) (v : Tm), isVal v = true → T (j + 1) U v →
      cn.Holds s₀.h h → Qn h v → ShapeOk v k)
    (hkeepN : ∀ F ∈ Kn, Box cn.fp (fun ρ _ s => F.HoldsAt ρ s.h) ρ m s₀)
    (hkeepE : ∀ F ∈ Ke, Box ce.fp (fun ρ _ s => F.HoldsAt ρ s.h) ρ m s₀)
    (hentN : ∀ (s : IndexedHeap) (v : Tm), Action cn.fp ρ s₀ s → isVal v = true → Above T s v → Qn s.h v →
      (∀ ρ', Transported Kn ρ ρ' s.h) → NormalTarget pre Tres Qres ρ m s v k)
    (hentE : ∀ (s : IndexedHeap) (e : Tm), Action ce.fp ρ s₀ s → Scoped 0 e → Above Ξ s e → Qe s.h →
      (∀ ρ', Transported Ke ρ ρ' s.h) → RaiseTarget pre Ξres Rres ρ m s e x) :
    NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x :=
  ⟨hshape,
    fun s v ha hv hT hq => hentN s v ha hv hT hq (transported_of fun F hF => hkeepN F hF s ha),
    fun s e ha hsc hΞ hq => hentE s e ha hsc hΞ hq (transported_of fun F hF => hkeepE F hF s ha)⟩

/-! ## A typed field write -/

/-- `{values: any, stores: keep}`: the effect of a typed field write. -/
def fieldWriteEffect : Footprints.Closed := ⟨.any, .keep⟩

/-- **A typed field write keeps every length lower bound, on both exits**,
exposing each exit's endpoint: the action of `{values: any, stores: keep}`, the
residual budget, the result's type or the raised value's family, and the
bound. -/
theorem field_write_keeps_bound {ι : Type} [DecidableEq ι] {G : PositiveGraphs.NormalGraph ι}
    {Γ} {t : Tm} {Ξ T : Fam} {ρ : Env} {s : IndexedHeap} {y x m k : Nat}
    {h' : Heap} {t' : Tm}
    (hc : ExpressionEffects.fieldWriteWithin G Γ fieldWriteEffect t = true)
    (he : ProgramTyping.EnvOk G Γ ρ s.n s.W) (hs : Safe Ξ T s.n s.W s.h (instantiate 0 ρ t))
    (hst : Steps k s.h (instantiate 0 ρ t) h' t') (hk : k < s.n) (hb : LowerBound y x ρ m s) :
    (isVal t' = true → ∃ s' : IndexedHeap, Action fieldWriteEffect.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ T s'.n s'.W t' ∧ LowerBound y x ρ m s') ∧
      (∀ e, Raises t' e → ∃ s' : IndexedHeap, Action fieldWriteEffect.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ Scoped 0 e ∧ Ξ s'.n s'.W e ∧ LowerBound y x ρ m s') := by
  have hp := HeapObservations.SafePostExc.weaken (Q' := fun h' _ => fieldWriteEffect.Holds s.h h' ∧ True)
    (R' := fun h' => fieldWriteEffect.Holds s.h h' ∧ True) (fun _ _ h => ⟨h, trivial⟩) (fun _ h => ⟨h, trivial⟩)
    (ExpressionEffects.field_write_within_exc hc he s.ok hs)
  have hgrow : ∀ s', Action fieldWriteEffect.fp ρ s s' → LowerBound y x ρ m s' :=
    fun s' ha => grow hb s' (action_le_closed (by decide) ha)
  refine ⟨fun hv => ?_, fun e hr => ?_⟩
  · obtain ⟨s', ha, he', hn, hT, -⟩ := action_normal (ρ := ρ) hp hst hv hk
    exact ⟨s', ha, he', hn, hT, hgrow s' ha⟩
  · obtain ⟨s', ha, he', hn, hsc, hΞ, -⟩ := action_throw (ρ := ρ) hp hst hr hk
    exact ⟨s', ha, he', hn, hsc, hΞ, hgrow s' ha⟩

/-! ## The loop of `out[j] = xs[j]`: the aliasing write and the back edge

The note's loop `for (j = from; j < to; j++) out[j] = xs[j]`, its head
holding `0 ≤ j` and `to ≤ |xs|`. The write node's environment is
`v, j, to, xs, out` (slots 0 to 4); the increment binds `j' = j + 1` and the
back edge maps `j', to, xs, out` (slots 0, 3, 4, 5 after the push) to the
head's `j, to, xs, out`. `out` may be `xs`. -/

/-- Slot `j` holds a non-negative integer. It reads no heap. -/
def NonNeg (j : Nat) : Assertion := fun ρ _ _ => ∃ a, HeapKnowledge.intValue (ρ j) = some a ∧ 0 ≤ a

/-- **The aliasing element write keeps the head's facts** for the increment:
an element write at a run-time index, checked within
`{values: any, stores: grow}` whichever array it writes, and `to ≤ |xs|`
retained under that effect; `0 ≤ j` reads no heap. The escaping throw meets
the graph's exception family where the node's family does one level up. -/
theorem loop_write_obligations {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop} {ρ : Env}
    {m : Nat}
    {s₀ : IndexedHeap} {l : Nat}
    (hinc : ∀ s, NonNeg 1 ρ m s → LowerBound 2 3 ρ m s → pre l ρ m s)
    (hΞ : ∀ s e, Above Ξ s e → Ξres s.n s.W e ∧ Rres s.h)
    (hj : NonNeg 1 ρ m s₀) (hb : LowerBound 2 3 ρ m s₀) :
    NodeObligations pre Ξres Tres Qres Rres Ξ T growEffect growEffect (fun _ _ => True) (fun _ => True) ρ m s₀
      (.effect ⟨l, none⟩) none :=
  transfer (Kn := [lowerBoundFact 2 3]) (Ke := [])
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun F hF => by simp only [List.mem_singleton] at hF; subst hF; exact grow hb)
    (fun F hF => by simp at hF)
    (fun s _ _ _ _ _ htr => by
      have hb' : LowerBound 2 3 ρ m s :=
        htr ρ _ (List.mem_singleton_self _) some _ rfl (fun _ _ _ hg => by cases hg; rfl)
      exact hinc s hj hb')
    (fun s e _ _ hab _ _ => hΞ s e hab)

/-- The write node's local judgment: a typed write checked within
`{values: any, stores: grow}` (`ExpressionEffects.write_within_exc`), in the
form `NodesChecked` takes, with both posts `True`. -/
theorem grow_write_judgment {ι : Type} [DecidableEq ι] {G : PositiveGraphs.NormalGraph ι} {Γ} {t : Tm}
    {Ξ T : Fam} {ρ : Env} {s : IndexedHeap}
    (hc : ExpressionEffects.writeWithin G Γ growEffect t = true) (he : ProgramTyping.EnvOk G Γ ρ s.n s.W)
    (hs : Safe Ξ T s.n s.W s.h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => growEffect.Holds s.h h' ∧ True) (fun h' => growEffect.Holds s.h h' ∧ True)
      s.n s.W s.h (instantiate 0 ρ t) :=
  HeapObservations.SafePostExc.weaken (fun _ _ h => ⟨h, trivial⟩) (fun _ h => ⟨h, trivial⟩)
    (ExpressionEffects.write_within_exc hc he s.ok hs)

/-- **The back edge with a changed head valuation**: after `j' = j + 1`, the
head holds `0 ≤ j` and `to ≤ |xs|` at its new environment, the head's slot 0
now `j'`. The bound is retained under the increment's empty effect and
renamed (`to, xs` from slots 2, 3 to 1, 2); `0 ≤ j'` follows from `0 ≤ j` and
the increment's post. -/
theorem loop_back_edge {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop} {ce : Footprints.Closed}
    {Qe : Heap → Prop}
    {ρ : Env} {m : Nat} {s₀ : IndexedHeap} {hd : Nat}
    (hhead : ∀ ρ' s, NonNeg 0 ρ' m s → LowerBound 1 2 ρ' m s → pre hd ρ' m s)
    (hΞ : ∀ s e, Above Ξ s e → Ξres s.n s.W e ∧ Rres s.h)
    (hj : NonNeg 1 ρ m s₀) (hb : LowerBound 2 3 ρ m s₀) :
    NodeObligations pre Ξres Tres Qres Rres Ξ T Footprints.Closed.empty ce
      (fun _ v => ∃ a, HeapKnowledge.intValue (ρ 1) = some a ∧ HeapKnowledge.intValue v = some (a + 1)) Qe
      ρ m s₀ (.bind ⟨hd, some [0, 3, 4, 5]⟩) none :=
  transfer (Kn := [lowerBoundFact 2 3]) (Ke := [])
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun F hF s ha => by
      simp only [List.mem_singleton] at hF; subst hF
      exact grow hb s (action_le_closed (by decide) ha))
    (fun F hF => by simp at hF)
    (fun s v _ _ _ hq htr => by
      obtain ⟨a, ha, hv⟩ := hq
      obtain ⟨a', ha', hle⟩ := hj
      rw [ha] at ha'; cases ha'
      refine hhead _ s ⟨a + 1, ?_, by omega⟩ ?_
      · simpa [mapEnv, slot, push] using hv
      · refine htr _ _ (List.mem_singleton_self _)
          (fun i => if i = 2 then some 1 else if i = 3 then some 2 else none) (lowerBoundFact 1 2) rfl ?_
        intro i hi j hg
        simp only [lowerBoundFact, HeapKnowledge.IndexFact.slots] at hi
        by_cases h2 : i = 2
        · subst h2; simp at hg; subst hg; simp [mapEnv, slot, push]
        · by_cases h3 : i = 3
          · subst h3; simp at hg; subst hg; simp [mapEnv, slot, push]
          · simp [h2, h3] at hg)
    (fun s e _ _ hab _ _ => hΞ s e hab)

end Verification.TolerantFrames
