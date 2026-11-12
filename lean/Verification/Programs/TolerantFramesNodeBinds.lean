import Verification.Programs.TolerantFramesRuns

/-! # Tolerant frames: node obligations at every continuation

`NodeObligations` (`TolerantFramesRuns`) states a node's exits at a return,
a bind, an effect and a branch; at `branchBind` and `tagBind` its shape and
normal target are `False`, so `graph_safe` covers no graph with such a node.
This module states the obligations at every continuation: `branchBind`
pushes its Boolean and takes the arm its value selects, `tagBind` pushes its
value and takes the arm the tag's answer in the heap selects
(`ControlFlow.Transition.yesBind`, `noBind`, `tagBind`). On the other four
continuations the statements are the existing ones (`shapeOk'_eq`,
`normalTarget'_eq`), and every `NodeObligations` is a `NodeObligations'`
(`nodeObligations'_of`). Graph safety follows as before (`graph_safe'`,
`graph_inv_run'`, `reached_pre'`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations ControlFlow PointClaims

/-- What a continuation needs of a node's value to take a transition: a
branch and a `branchBind` a Boolean; a `tagBind` any value. -/
def ShapeOk' (v : Tm) : Continuation → Prop
  | .branchBind _ _ => v = .tru ∨ v = .fls
  | .tagBind _ _ _ => True
  | k => ShapeOk v k

/-- The obligation a normal exit with value `v` meets at the state `s` its
continuation's transition reaches: at a `branchBind`, the arm of the
Boolean with the value pushed; at a `tagBind`, the arm of the tag's answer
in `s`'s heap with the value pushed; elsewhere `NormalTarget`. -/
def NormalTarget' (pre : Nat → Assertion) (Tres : Fam) (Qres : Heap → Prop) (ρ : Env) (m : Nat) (s : IndexedHeap)
    (v : Tm) : Continuation → Prop
  | .branchBind y n => (v = .tru ∧ pre y.label (mapEnv y.mapping (push v ρ)) m s) ∨
      (v = .fls ∧ pre n.label (mapEnv n.mapping (push v ρ)) m s)
  | .tagBind tag y n => (tagHoldsIn s.h tag v = true ∧ pre y.label (mapEnv y.mapping (push v ρ)) m s) ∨
      (tagHoldsIn s.h tag v = false ∧ pre n.label (mapEnv n.mapping (push v ρ)) m s)
  | k => NormalTarget pre Tres Qres ρ m s v k

theorem shapeOk'_eq {v : Tm} {k : Continuation}
    (hk : ∀ y n, k ≠ .branchBind y n) (ht : ∀ tg y n, k ≠ .tagBind tg y n) : ShapeOk' v k = ShapeOk v k := by
  cases k with
  | branchBind y n => exact absurd rfl (hk y n)
  | tagBind tg y n => exact absurd rfl (ht tg y n)
  | _ => rfl

theorem normalTarget'_eq {pre : Nat → Assertion} {Tres : Fam} {Qres : Heap → Prop} {ρ : Env} {m : Nat}
    {s : IndexedHeap} {v : Tm} {k : Continuation}
    (hk : ∀ y n, k ≠ .branchBind y n) (ht : ∀ tg y n, k ≠ .tagBind tg y n) :
    NormalTarget' pre Tres Qres ρ m s v k = NormalTarget pre Tres Qres ρ m s v k := by
  cases k with
  | branchBind y n => exact absurd rfl (hk y n)
  | tagBind tg y n => exact absurd rfl (ht tg y n)
  | _ => rfl

/-- A node's exit obligations at every continuation: `NodeObligations` with
`ShapeOk'` and `NormalTarget'`. -/
structure NodeObligations' (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (Ξ T : Fam)
    (cn ce : Footprints.Closed)
    (Qn : Post) (Qe : Heap → Prop) (ρ : Env) (m : Nat) (s₀ : IndexedHeap) (k : Continuation)
    (x : Option Target) : Prop where
  shape : ∀ (j : Nat) (U : WorldT (j + 1)) (h : Heap) (v : Tm), isVal v = true → T (j + 1) U v →
    cn.Holds s₀.h h → Qn h v → ShapeOk' v k
  normal : ∀ (s : IndexedHeap) (v : Tm), Action cn.fp ρ s₀ s → isVal v = true → Above T s v → Qn s.h v →
    NormalTarget' pre Tres Qres ρ m s v k
  raise : ∀ (s : IndexedHeap) (e : Tm), Action ce.fp ρ s₀ s → Scoped 0 e → Above Ξ s e → Qe s.h →
    RaiseTarget pre Ξres Rres ρ m s e x

/-- A partially evaluated node, with `NodeObligations'`. -/
def EvalOk' (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (m n : Nat) (W : WorldT n) (h : Heap)
    (t : Tm) (ρ : Env) (k : Continuation) (x : Option Target) : Prop :=
  ∃ (s₀ : IndexedHeap) (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
    Reach s₀ n W ∧
    SafePostExc Ξ T (fun h' v => cn.Holds s₀.h h' ∧ Qn h' v) (fun h' => ce.Holds s₀.h h' ∧ Qe h') n W h t ∧
    NodeObligations' pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x

/-- The graph invariant `GraphInv`, its partially evaluated nodes meeting
`NodeObligations'`. -/
def GraphInv' (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (m n : Nat) (W : WorldT n)
    (h : Heap) : State → Prop
  | .at l ρ => ∀ (hp : 0 < n) (ha : WorldAdm W) (ho : HeapOk n W h), pre l ρ m ⟨n, W, h, hp, ha, ho⟩
  | .eval t ρ k x => 0 < n → EvalOk' pre Ξres Tres Qres Rres m n W h t ρ k x
  | .done v => 0 < n → isVal v = true ∧ Tres n W v ∧ Qres h
  | .raised v => 0 < n → Scoped 0 v ∧ Ξres n W v ∧ Rres h

/-- Every node a label's assertion reaches exists and meets its local safety
and `NodeObligations'` from every state where the assertion holds. -/
def NodesChecked' (P : Program) (pre : Nat → Assertion) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (m : Nat) :
    Prop :=
  ∀ l ρ (s : IndexedHeap), pre l ρ m s → ∃ node, P[l]? = some node ∧
    ∃ (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
      SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
        s.n s.W s.h (instantiate 0 ρ node.expression) ∧
      NodeObligations' pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s node.continuation node.handler

/-! ## The existing obligations are among these -/

/-- **Every `NodeObligations` is a `NodeObligations'`**: on the four
continuations it covers they say the same; at `branchBind` and `tagBind`
its shape is `False`, so no value reaches a normal exit there. -/
theorem nodeObligations'_of {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop}
    {cn ce : Footprints.Closed} {Qn : Post} {Qe : Heap → Prop} {ρ : Env} {m : Nat} {s₀ : IndexedHeap}
    {k : Continuation} {x : Option Target}
    (ho : NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x) :
    NodeObligations' pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x := by
  refine ⟨fun j U h v hv hT hc hq => ?_, fun s v ha hv hT hq => ?_, ho.raise⟩
  · have := ho.shape j U h v hv hT hc hq
    cases k <;> first | exact this | exact this.elim
  · have := ho.normal s v ha hv hT hq
    cases k <;> first | exact this | exact this.elim

theorem nodesChecked'_of {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop}
    {m : Nat} (hn : NodesChecked P pre Ξres Tres Qres Rres m) : NodesChecked' P pre Ξres Tres Qres Rres m := by
  intro l ρ s hp
  obtain ⟨node, hP, Ξ, T, cn, ce, Qn, Qe, hs, ho⟩ := hn l ρ s hp
  exact ⟨node, hP, Ξ, T, cn, ce, Qn, Qe, hs, nodeObligations'_of ho⟩

/-- `NodeObligations'` is monotone in the targets' assertions. -/
theorem nodeObligations'_mono {pre pre' : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop}
    {cn ce : Footprints.Closed} {Qn : Post} {Qe : Heap → Prop} {ρ : Env} {m : Nat} {s₀ : IndexedHeap}
    {k : Continuation} {x : Option Target}
    (hle : ∀ t ρ s, pre t ρ m s → pre' t ρ m s)
    (ho : NodeObligations' pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x) :
    NodeObligations' pre' Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x where
  shape := ho.shape
  normal s v ha hv hT hq := by
    have := ho.normal s v ha hv hT hq
    cases k with
    | ret => exact this
    | bind l => exact hle _ _ _ this
    | effect l => exact hle _ _ _ this
    | branch y n => exact this.imp (fun h => ⟨h.1, hle _ _ _ h.2⟩) (fun h => ⟨h.1, hle _ _ _ h.2⟩)
    | branchBind y n => exact this.imp (fun h => ⟨h.1, hle _ _ _ h.2⟩) (fun h => ⟨h.1, hle _ _ _ h.2⟩)
    | tagBind tg y n => exact this.imp (fun h => ⟨h.1, hle _ _ _ h.2⟩) (fun h => ⟨h.1, hle _ _ _ h.2⟩)
  raise s e ha hsc hΞ hq := by
    have := ho.raise s e ha hsc hΞ hq
    cases x with
    | some l => exact hle _ _ _ this
    | none => exact this

/-! ## Graph safety from the obligations at every continuation -/

/-- **One transition from the graph invariant**, `graph_step` at every
continuation: a `branchBind` takes the arm of its Boolean, a `tagBind` the
arm of the tag's answer in the current heap. -/
theorem graph_step' {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked' P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {n : Nat}
    {W : WorldT (n + 1)} {h : Heap} {st : State} (ha : WorldAdm W) (ho : HeapOk (n + 1) W h)
    (hinv : GraphInv' pre Ξres Tres Qres Rres m (n + 1) W h st) :
    ((∃ v, st = .done v ∧ isVal v = true ∧ Tres (n + 1) W v) ∨
      (∃ v, st = .raised v ∧ Scoped 0 v ∧ Ξres (n + 1) W v)) ∨
    ∃ (U : WorldT n) (h' : Heap) (st' : State), WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧
      Transition P h st h' st' ∧ HeapOk n U h' ∧ GraphInv' pre Ξres Tres Qres Rres m n U h' st' := by
  have ha' := WorldAdm_trunc (Nat.le_succ n) ha
  have ho' := HeapOk_trunc n W h ho
  have next : ∀ {h' st'} (U : WorldT n), WExt (trunc n (Nat.le_succ n) W) U → WorldAdm U →
      Transition P h st h' st' → HeapOk n U h' → GraphInv' pre Ξres Tres Qres Rres m n U h' st' →
      ((∃ v, st = .done v ∧ isVal v = true ∧ Tres (n + 1) W v) ∨
        (∃ v, st = .raised v ∧ Scoped 0 v ∧ Ξres (n + 1) W v)) ∨
      ∃ (U : WorldT n) (h' : Heap) (st' : State), WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧
        Transition P h st h' st' ∧ HeapOk n U h' ∧ GraphInv' pre Ξres Tres Qres Rres m n U h' st' :=
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
      have tgt : ∀ (hp : 0 < n), NormalTarget' pre Tres Qres ρ m (below n W h hp ha ho) t k := fun hp =>
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

/-- **Graph safety from the node obligations at every continuation.** -/
theorem graph_safe' {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked' P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) :
    ∀ n (W : WorldT n) h st, WorldAdm W → HeapOk n W h → GraphInv' pre Ξres Tres Qres Rres m n W h st →
      SafeGraph Ξres P Tres n W h st := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h st ha ho hinv
    rcases graph_step' hnodes hdown ha ho hinv with (h1 | h2) | ⟨U, h', st', hx, hu, tr, hh, hi⟩
    · exact .inl (.inl h1)
    · exact .inl (.inr h2)
    · exact .inr ⟨U, h', st', hx, hu, tr, hh, ih U h' st' hu hh hi⟩

/-- The graph is safe from every node entry whose assertion holds, at every
continuation. -/
theorem graph_safe_at' {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked' P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat} {ρ : Env}
    {s : IndexedHeap} (hpre : pre l ρ m s) : SafeGraph Ξres P Tres s.n s.W s.h (.at l ρ) :=
  graph_safe' hnodes hdown _ _ _ _ s.adm s.ok fun _ _ _ => hpre

/-- **A graph run from a state the invariant describes ends in one it
describes**, at every continuation (`graph_inv_run` over `graph_step'`). -/
theorem graph_inv_run' {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked' P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) :
    ∀ {k h st h' st'}, Transitions P k h st h' st' → ∀ (s : IndexedHeap), s.h = h → k < s.n →
      GraphInv' pre Ξres Tres Qres Rres m s.n s.W s.h st →
      ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        GraphInv' pre Ξres Tres Qres Rres m s'.n s'.W s'.h st' := by
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
      rcases graph_step' hnodes hdown adm ok hinv with (⟨v, rfl, -⟩ | ⟨v, rfl, -⟩) | ⟨U, h₁, st₁, hx, hu, tr', hh, hi⟩
      · cases tr
      · cases tr
      · obtain ⟨rfl, rfl⟩ := transition_det tr tr'
        obtain ⟨s', ha, he, hn, hinv'⟩ := ih ⟨j, U, _, by omega, hu, hh⟩ rfl (by simp only; omega) hi
        exact ⟨s', Admissible.trans ⟨Nat.le_succ j, hx⟩ ha, he, by simp only at hn; omega, hinv'⟩

/-- **Every node entry a run reaches satisfies its assertion**, at every
continuation. -/
theorem reached_pre' {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked' P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat} {ρ : Env}
    {s : IndexedHeap} (hpre : pre l ρ m s) {k : Nat} {h' : Heap} {l' : Nat} {ρ' : Env}
    (hrun : Transitions P k s.h (.at l ρ) h' (.at l' ρ')) (hk : k < s.n) :
    ∃ s' : IndexedHeap, s'.h = h' ∧ pre l' ρ' m s' := by
  obtain ⟨s', -, he, -, hinv⟩ := graph_inv_run' hnodes hdown hrun s rfl hk fun _ _ _ => hpre
  exact ⟨s', he, hinv s'.pos s'.adm s'.ok⟩

open HeapKnowledge in
/-- **TRANSFER** at every continuation: `transfer` with `ShapeOk'` and
`NormalTarget'`. -/
theorem transfer' {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop} {cn ce : Footprints.Closed}
    {Qn : Post} {Qe : Heap → Prop} {ρ : Env} {m : Nat} {s₀ : IndexedHeap} {k : Continuation} {x : Option Target}
    {Kn Ke : List IndexFact}
    (hshape : ∀ (j : Nat) (U : WorldT (j + 1)) (h : Heap) (v : Tm), isVal v = true → T (j + 1) U v →
      cn.Holds s₀.h h → Qn h v → ShapeOk' v k)
    (hkeepN : ∀ F ∈ Kn, Box cn.fp (fun ρ _ s => F.HoldsAt ρ s.h) ρ m s₀)
    (hkeepE : ∀ F ∈ Ke, Box ce.fp (fun ρ _ s => F.HoldsAt ρ s.h) ρ m s₀)
    (hentN : ∀ (s : IndexedHeap) (v : Tm), Action cn.fp ρ s₀ s → isVal v = true → Above T s v → Qn s.h v →
      (∀ ρ', Transported Kn ρ ρ' s.h) → NormalTarget' pre Tres Qres ρ m s v k)
    (hentE : ∀ (s : IndexedHeap) (e : Tm), Action ce.fp ρ s₀ s → Scoped 0 e → Above Ξ s e → Qe s.h →
      (∀ ρ', Transported Ke ρ ρ' s.h) → RaiseTarget pre Ξres Rres ρ m s e x) :
    NodeObligations' pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x :=
  ⟨hshape,
    fun s v ha hv hT hq => hentN s v ha hv hT hq (transported_of fun F hF => hkeepN F hF s ha),
    fun s e ha hsc hΞ hq => hentE s e ha hsc hΞ hq (transported_of fun F hF => hkeepE F hF s ha)⟩

end Verification.TolerantFrames
