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

/-- What a continuation needs of a node's value to take a transition at all:
a branch needs a Boolean; `branchBind` and `tagBind` are outside this
statement. -/
def ShapeOk (v : Tm) : Continuation → Prop
  | .ret | .bind _ | .effect _ => True
  | .branch _ _ => v = .tru ∨ v = .fls
  | _ => False

/-- The obligation a normal exit with value `v` meets at the state `s` its
continuation's transition reaches: the target's assertion at its environment,
or the result type. -/
def NormalTarget (pre : Nat → Assertion) (Tres : Fam) (ρ : Env) (m : Nat) (s : IndexedHeap) (v : Tm) :
    Continuation → Prop
  | .ret => Tres s.n s.W v
  | .bind l => pre l.label (mapEnv l.mapping (push v ρ)) m s
  | .effect l => pre l.label (mapEnv l.mapping ρ) m s
  | .branch y n => (v = .tru ∧ pre y.label (mapEnv y.mapping ρ) m s) ∨
      (v = .fls ∧ pre n.label (mapEnv n.mapping ρ) m s)
  | _ => False

/-- The obligation a throw of `e` meets at the state the handler's transition
reaches: the handler's assertion with `e` bound, or, escaping, the graph's
exception family. -/
def RaiseTarget (pre : Nat → Assertion) (Ξres : Fam) (ρ : Env) (m : Nat) (s : IndexedHeap) (e : Tm) :
    Option Target → Prop
  | some l => pre l.label (mapEnv l.mapping (push e ρ)) m s
  | none => Ξres s.n s.W e

/-- A node's exit obligations from its entry state `s₀`, exit by exit: the
normal exit within `cn` with post `Qn`, the exceptional one within `ce` with
post `Qe`. The shape is required at every budget, the targets at positive
states only. -/
structure NodeObligations (pre : Nat → Assertion) (Ξres Tres Ξ T : Fam) (cn ce : Footprints.Closed)
    (Qn : Post) (Qe : Heap → Prop) (ρ : Env) (m : Nat) (s₀ : IndexedHeap) (k : Continuation)
    (x : Option Target) : Prop where
  shape : ∀ (j : Nat) (U : WorldT (j + 1)) (h : Heap) (v : Tm), isVal v = true → T (j + 1) U v →
    cn.Holds s₀.h h → Qn h v → ShapeOk v k
  normal : ∀ (s : IndexedHeap) (v : Tm), Action cn.fp ρ s₀ s → isVal v = true → Above T s v → Qn s.h v →
    NormalTarget pre Tres ρ m s v k
  raise : ∀ (s : IndexedHeap) (e : Tm), Action ce.fp ρ s₀ s → Scoped 0 e → Above Ξ s e → Qe s.h →
    RaiseTarget pre Ξres ρ m s e x

/-- A partially evaluated node: its local safety from its entry state `s₀`,
the current world reached from `s₀`, and its exit obligations. -/
def EvalOk (pre : Nat → Assertion) (Ξres Tres : Fam) (m n : Nat) (W : WorldT n) (h : Heap) (t : Tm)
    (ρ : Env) (k : Continuation) (x : Option Target) : Prop :=
  ∃ (s₀ : IndexedHeap) (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
    Reach s₀ n W ∧
    SafePostExc Ξ T (fun h' v => cn.Holds s₀.h h' ∧ Qn h' v) (fun h' => ce.Holds s₀.h h' ∧ Qe h') n W h t ∧
    NodeObligations pre Ξres Tres Ξ T cn ce Qn Qe ρ m s₀ k x

/-- The graph invariant: a node's assertion at `.at`, a partially evaluated
node at `.eval`, the result type at `.done`, the exception family at
`.raised`; each only at positive budget. -/
def GraphInv (pre : Nat → Assertion) (Ξres Tres : Fam) (m n : Nat) (W : WorldT n) (h : Heap) : State → Prop
  | .at l ρ => ∀ (hp : 0 < n) (ha : WorldAdm W) (ho : HeapOk n W h), pre l ρ m ⟨n, W, h, hp, ha, ho⟩
  | .eval t ρ k x => 0 < n → EvalOk pre Ξres Tres m n W h t ρ k x
  | .done v => 0 < n → isVal v = true ∧ Tres n W v
  | .raised v => 0 < n → Scoped 0 v ∧ Ξres n W v

/-- Every node a label's assertion reaches exists and meets its local safety
and exit obligations from every state where the assertion holds. -/
def NodesChecked (P : Program) (pre : Nat → Assertion) (Ξres Tres : Fam) (m : Nat) : Prop :=
  ∀ l ρ (s : IndexedHeap), pre l ρ m s → ∃ node, P[l]? = some node ∧
    ∃ (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
      SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
        s.n s.W s.h (instantiate 0 ρ node.expression) ∧
      NodeObligations pre Ξres Tres Ξ T cn ce Qn Qe ρ m s node.continuation node.handler

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

/-- **Graph safety from node obligations.** Every state the invariant
describes is safe for the graph machine, at every budget. -/
theorem graph_safe {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres m) (hdown : AdminClosed pre m) :
    ∀ n (W : WorldT n) h st, WorldAdm W → HeapOk n W h → GraphInv pre Ξres Tres m n W h st →
      SafeGraph Ξres P Tres n W h st := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h st ha ho hinv
    have ha' := WorldAdm_trunc (Nat.le_succ n) ha
    have ho' := HeapOk_trunc n W h ho
    -- one administrative or expression transition, to the next state
    have next : ∀ {h' st'} (U : WorldT n), WExt (trunc n (Nat.le_succ n) W) U → WorldAdm U →
        Transition P h st h' st' → HeapOk n U h' → GraphInv pre Ξres Tres m n U h' st' →
        SafeGraph Ξres P Tres (n + 1) W h st :=
      fun U hx hu tr hh hi => .inr ⟨U, _, _, hx, hu, tr, hh, ih U _ _ hu hh hi⟩
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
        have tgt : ∀ (hp : 0 < n), NormalTarget pre Tres ρ m (below n W h hp ha ho) t k := fun hp =>
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
        | branchBind _ _ => exact hshape.elim
        | tagBind _ _ _ => exact hshape.elim
      · -- a throw: the handler's transition, or the run ends raised
        have tgt : ∀ (hp : 0 < n), RaiseTarget pre Ξres ρ m (below n W h hp ha ho) e x := fun hp =>
          hobl.raise _ e (below_action hr hc) hsc ⟨W, rfl, hΞ⟩ hq
        cases x with
        | some l => exact next _ (WExt_refl _) ha' (.handle hre) ho' fun hp _ _ => tgt hp
        | none => exact next _ (WExt_refl _) ha' (.raise hre) ho' fun hp => ⟨hsc, tgt hp⟩
      · -- an expression step
        exact next U hx hu (.expr st) hh fun _ => ⟨s₀, Ξ, T, cn, ce, Qn, Qe, hr.step hx, hs', hobl⟩
    | done v =>
      obtain ⟨hv, hT⟩ := hinv (Nat.zero_lt_succ n)
      exact .inl (.inl ⟨v, rfl, hv, hT⟩)
    | raised v =>
      obtain ⟨hsc, hΞ⟩ := hinv (Nat.zero_lt_succ n)
      exact .inl (.inr ⟨v, rfl, hsc, hΞ⟩)

/-- The graph is safe from every node entry whose assertion holds. -/
theorem graph_safe_at {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres m) (hdown : AdminClosed pre m) {l : Nat} {ρ : Env}
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
theorem transfer {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {cn ce : Footprints.Closed} {Qn : Post}
    {Qe : Heap → Prop} {ρ : Env} {m : Nat} {s₀ : IndexedHeap} {k : Continuation} {x : Option Target}
    {Kn Ke : List IndexFact}
    (hshape : ∀ (j : Nat) (U : WorldT (j + 1)) (h : Heap) (v : Tm), isVal v = true → T (j + 1) U v →
      cn.Holds s₀.h h → Qn h v → ShapeOk v k)
    (hkeepN : ∀ F ∈ Kn, Box cn.fp (fun ρ _ s => F.HoldsAt ρ s.h) ρ m s₀)
    (hkeepE : ∀ F ∈ Ke, Box ce.fp (fun ρ _ s => F.HoldsAt ρ s.h) ρ m s₀)
    (hentN : ∀ (s : IndexedHeap) (v : Tm), Action cn.fp ρ s₀ s → isVal v = true → Above T s v → Qn s.h v →
      (∀ ρ', Transported Kn ρ ρ' s.h) → NormalTarget pre Tres ρ m s v k)
    (hentE : ∀ (s : IndexedHeap) (e : Tm), Action ce.fp ρ s₀ s → Scoped 0 e → Above Ξ s e → Qe s.h →
      (∀ ρ', Transported Ke ρ ρ' s.h) → RaiseTarget pre Ξres ρ m s e x) :
    NodeObligations pre Ξres Tres Ξ T cn ce Qn Qe ρ m s₀ k x :=
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

end Verification.TolerantFrames
