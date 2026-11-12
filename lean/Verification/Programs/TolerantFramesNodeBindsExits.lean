import Verification.Programs.TolerantFramesNodeBinds
import Verification.Programs.TolerantFramesComposeShape

/-! # Tolerant frames: a node's exits at every continuation

The per-node obligations of the pass (`StepEdgesSoundT`, `NodeAccepted`,
`stepEdgesSound_of`) at every continuation, over `NodeObligations'`: a
`branchBind`'s two exits push the Boolean and observe it, a `tagBind`'s push
the value and observe the tag's answer (`Exit.ofNode`). Each exit delivers
by the edge lemmas as they stand (`exitDelivers_of_edge`,
`exitDelivers_head`): an observing exit is a pushed one with no promotion
(`ofNode_flags`), the premises `hpo` and `hpp` of those lemmas. A
`branchBind`'s claim type is Boolean where the shape check accepts it
(`passShapeCheck'`, the proved checker's `onlyBoolean`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Shape
variable {ι : Type} [DecidableEq ι]

/-- The shape check of a continuation at every kind: `passShapeCheck`, and
at a `branchBind` the proved checker's test (`ControlFlow.checkNodeResult`
at `.branchBind`, `onlyBoolean`); a `tagBind` needs none. -/
def passShapeCheck' (G : NormalGraph ι) (A : Ty ι) : Continuation → Bool
  | .branchBind _ _ => BranchRefinement.onlyBoolean G A
  | .tagBind _ _ _ => true
  | k => passShapeCheck G A k

/-- **The shape check gives every value its continuation's shape**, at
every continuation. -/
theorem nodeShape'_of {G : NormalGraph ι} {A : Ty ι} {k : Continuation} (hs : passShapeCheck' G A k = true)
    {n : Nat} {W : WorldT n} {v : Tm} (hv : meaning G A n W v) : ShapeOk' v k := by
  cases k with
  | ret | bind _ | effect _ => trivial
  | branch y no => exact nodeShape_of (k := .branch y no) hs hv
  | branchBind _ _ => exact BranchRefinement.onlyBoolean_sound hs hv
  | tagBind _ _ _ => trivial

end Shape

section Exits
variable {ι : Type}

/-- **A node's normal exits observe only where they push and promote only
where they do not** (`Exit.ofNode`): the premises `hpo`, `hpp` of the edge
lemmas, at every exit. -/
theorem ofNode_flags {node : Node} {t : Target} {pushed : Bool} {observed : Option BranchRefinement.Observation}
    {promote : Option Bool} (hm : Exit.normal t pushed observed promote ∈ Exit.ofNode node) :
    (observed.isSome = true → pushed = true) ∧ (promote.isSome = true → pushed = false) := by
  unfold Exit.ofNode at hm
  rcases List.mem_append.mp hm with hm | hm
  · split at hm <;> simp at hm <;>
      first
        | (rcases hm with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ <;> simp; done)
        | (obtain ⟨-, rfl, rfl, rfl⟩ := hm; simp)
  · simp at hm

/-- **A continuation's normal target from its exits, at every
continuation**: `normalTarget_of_exits`, and at a `branchBind` the arm of
the Boolean, at a `tagBind` the arm of the tag's answer in the heap, each
exit observing what its arm's transition tests. -/
theorem normalTarget'_of_exits {pre : Nat → Assertion} {G : NormalGraph ι} {A : Ty ι} {Γ : List (Ty ι)}
    {Fn : Assertion} {ρ : Env} {m : Nat} {node : Node} {Tres : Fam} {Qres : Heap → Prop}
    (hex : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node →
      ExitDelivers pre G A Γ Fn ρ m t pushed observed promote)
    (hret : node.continuation = .ret → ∀ n (W : WorldT n) v, meaning G A n W v → Tres n W v)
    (hQ : ∀ h, Qres h)
    (s' : IndexedHeap) (v : Tm) (hv : isVal v = true) (hF : Fn (push v ρ) m s')
    (he : EnvOk G (A :: Γ) (push v ρ) s'.n s'.W) (hshape : ShapeOk' v node.continuation) :
    NormalTarget' pre Tres Qres ρ m s' v node.continuation := by
  have mem : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node →
      ObservedOk observed promote v →
      pre t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) m s' :=
    fun t p o q hm ho => hex t p o q hm s' v hv hF he ho
  have old : ShapeOk v node.continuation → NormalTarget pre Tres Qres ρ m s' v node.continuation :=
    normalTarget_of_exits hex hret hQ s' v hv hF he
  unfold Exit.ofNode at mem
  cases hk : node.continuation with
  | ret => rw [hk] at old hshape; exact old hshape
  | bind t => rw [hk] at old hshape; exact old hshape
  | effect t => rw [hk] at old hshape; exact old hshape
  | branch y n => rw [hk] at old hshape; exact old hshape
  | branchBind y n =>
    rw [hk] at mem hshape
    rcases hshape with rfl | rfl
    · have := mem y true (some (.boolean true)) none (by simp)
        (by simp [ObservedOk, BranchRefinement.Observation.holds])
      exact .inl ⟨rfl, by simpa using this⟩
    · have := mem n true (some (.boolean false)) none (by simp)
        (by simp [ObservedOk, BranchRefinement.Observation.holds])
      exact .inr ⟨rfl, by simpa using this⟩
  | tagBind tg y n =>
    rw [hk] at mem
    cases hq : tagHoldsIn s'.h tg v with
    | true =>
      have := mem y true (some (.tag tg true)) none (by simp)
        (by simpa [ObservedOk, BranchRefinement.Observation.holds] using tagHolds_of_heap hq)
      exact .inl ⟨hq, by simpa using this⟩
    | false =>
      have := mem n true (some (.tag tg false)) none (by simp)
        (by simpa [ObservedOk, BranchRefinement.Observation.holds] using tagHolds_of_heap hq)
      exact .inr ⟨hq, by simpa using this⟩

end Exits

section Typed
variable {ι : Type}

/-- **Each visited node's step and edges deliver, typed, at every
continuation**: `StepEdgesSoundT` over `NodeObligations'`. -/
def StepEdgesSoundT' (P : ControlFlow.Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (ctx : Nat → List (Ty ι)) (Ξres Tres : Fam) (Qres Rres : Heap → Prop) (m : Nat) : Prop :=
  ∀ l ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s → ∃ node, P[l]? = some node ∧
    ∃ (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
      SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
        s.n s.W s.h (instantiate 0 ρ node.expression) ∧
      NodeObligations' (edgePreT G w startNames ρ0 ctx) Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s
        node.continuation node.handler

theorem stepEdgesSoundT'_of {P : ControlFlow.Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ρ0 : Env} {ctx : Nat → List (Ty ι)} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (h : StepEdgesSoundT P G w startNames ρ0 ctx Ξres Tres Qres Rres m) :
    StepEdgesSoundT' P G w startNames ρ0 ctx Ξres Tres Qres Rres m := by
  intro l ρ s hp
  obtain ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hs, ho⟩ := h l ρ s hp
  exact ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hs, nodeObligations'_of ho⟩

variable [DecidableEq ι] [Hashable ι] in
/-- **The pass's graph is safe from the start's typed entry, at every
continuation**: `run_sound_of_walk_typed` over `StepEdgesSoundT'`. -/
theorem run_sound_of_walk_typed' {P : ControlFlow.Program} {G : NormalGraph ι} {w : Walk ι}
    {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {Ξres Tres : Fam} {Qres Rres : Heap → Prop}
    {m : Nat} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} (hT : Traversed G w startNames given ctx edgesIn fresh)
    (hstep : StepEdgesSoundT' P G w startNames ρ0 ctx Ξres Tres Qres Rres m)
    (hheads : HeadsEntered G w startNames ρ0 given m) (hmerges : MergesSound G w given ctx edgesIn)
    {start : Nat} {s : IndexedHeap} (hpre : passPreT G w startNames ρ0 ctx start ρ0 m s) :
    ControlFlow.SafeGraph Ξres P Tres s.n s.W s.h (.at start ρ0) := by
  have hentries := entries_of_traversed (ρ0 := ρ0) (m := m) hT hheads hmerges
  refine graph_safe_at' (pre := passPreT G w startNames ρ0 ctx) (Qres := Qres) (Rres := Rres) ?_
    passPreT_adminClosed hpre
  intro l ρ s hp
  obtain ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hsafe, ho⟩ := hstep l ρ s hp
  exact ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hsafe,
    nodeObligations'_mono (fun t ρ s h => ⟨hentries t ρ s h.1, h.2⟩) ho⟩

/-- **A node's obligations from its step's parts, at every continuation**:
`nodeObligations_of_parts` with `ShapeOk'` and `NormalTarget'`. -/
theorem nodeObligations'_of_parts {G : NormalGraph ι} {A : Ty ι} {Γ : List (Ty ι)} {cn ce : Footprints.Closed}
    {t : Tm} {out : HeapKnowledge.Knowledge} {Fn Fe : Assertion} {ρ : Env} {m : Nat} {s : IndexedHeap}
    {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {k : Continuation} {x : Option Target}
    (hp : StepParts G A cn ce t out Fn Fe ρ m s) (he : EnvOk G Γ ρ s.n s.W)
    (hshape : ∀ j (U : WorldT (j + 1)) v, meaning G A (j + 1) U v → ShapeOk' v k)
    (hnormal : ∀ (s' : IndexedHeap) v, Admissible s s' → isVal v = true → Fn (push v ρ) m s' →
      EnvOk G (A :: Γ) (push v ρ) s'.n s'.W → HeapKnowledge.Holds out (push v ρ) s'.h →
      NormalTarget' pre Tres Qres ρ m s' v k)
    (hraise : ∀ (s' : IndexedHeap) e, Admissible s s' → Fe ρ m s' → EnvOk G Γ ρ s'.n s'.W → Scoped 0 e →
      excOf G s'.n s'.W e → RaiseTarget pre Ξres Rres ρ m s' e x) :
    SafePostExc (excOf G) (meaning G A)
      (fun h' v => cn.Holds s.h h' ∧ (HeapKnowledge.Holds out (push v ρ) h' ∧
        ∃ k, Steps k s.h (instantiate 0 ρ t) h' v))
      (fun h' => ce.Holds s.h h' ∧ True) s.n s.W s.h (instantiate 0 ρ t) ∧
    NodeObligations' pre Ξres Tres Qres Rres (excOf G) (meaning G A) cn ce
      (fun h' v => HeapKnowledge.Holds out (push v ρ) h' ∧ ∃ k, Steps k s.h (instantiate 0 ρ t) h' v)
      (fun _ => True) ρ m s k x := by
  obtain ⟨hj, hn, hx⟩ := hp
  refine ⟨SafePostExc.weaken (fun _ _ ⟨⟨hc, ho⟩, hk⟩ => ⟨hc, ho, hk⟩) (fun _ h => h) (safePostExc_trace hj),
    ⟨fun j U h v _ hT _ _ => hshape j U v hT, ?_, ?_⟩⟩
  · intro s' v ha hv ⟨U, hU, hT⟩ ⟨ho, k', hk⟩
    have hT' : meaning G A s'.n s'.W v := by
      have := (meaning_adm G A).down_le (s'.n + 1) s'.n (Nat.le_succ _) U v hT
      rwa [hU] at this
    exact hnormal s' v ha.1 hv (hn k' s'.h v s' hk hv ha rfl ho) ((envOk_admissible ha.1 he).push hT') ho
  · intro s' e ha hsc ⟨U, hU, hΞ⟩ _
    have hΞ' : excOf G s'.n s'.W e := by
      have := (builtinExc_adm G _).down_le (s'.n + 1) s'.n (Nat.le_succ _) U e hΞ
      rwa [hU] at this
    exact hraise s' e ha.1 (hx s' ha) (envOk_admissible ha.1 he) hsc hΞ'

end Typed

section Nodes
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **What the pass accepted at a visited node, at every continuation**:
`NodeAccepted` with the shape `ShapeOk'`, which `nodeShape'_of` gives from
`passShapeCheck'`. -/
structure NodeAccepted' (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (suggestions : List (Sequent ι)) (index : KnownIndex ι) (codes : CodeEntry ι → Bool) (aliases : List (ι × ι))
    (pc : PassChecker G images) (undefTy : Option (Ty ι)) (P : ControlFlow.Program) (w : Walk ι)
    (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι)) (Tres : Fam) (m : Nat) (l : Nat) where
  node : Node
  hP : P[l]? = some node
  c : PointClaim ι
  hctx : ctx l = c.context
  entry : SinglePass.State
  stated : ∀ ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s →
    StateHolds G entry (w.implies l) startNames ρ0 ρ m s
  ms : List Nat
  fresh : Nat
  answers : Answered G
  st : Stepped ι
  stats : StepStats
  ans : Answered G
  hstep : checkedStep G images pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh answers =
    (Except.ok st, stats, ans)
  wf : StoreWF entry.store
  below : NamesBelow entry (w.implies l) startNames fresh
  width : entry.names.length ≤ c.context.length
  sums : SummariesSound G images answers.summaries.toList
  shape : ∀ n (W : WorldT n) v, meaning G c.type n W v → ShapeOk' v node.continuation
  ret : node.continuation = .ret → ∀ n (W : WorldT n) v, meaning G c.type n W v → Tres n W v
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ,
    ExitDelivers (edgePreT G w startNames ρ0 ctx) G c.type c.context
      (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ρ0) ρ m t pushed
      observed promote
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ρ0 ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    edgePreT G w startNames ρ0 ctx t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s'

/-- A `NodeAccepted` is a `NodeAccepted'`: its shape, `ShapeOk`, is
`ShapeOk'` on the continuations it admits. -/
def NodeAccepted.toPrime {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool}
    {aliases : List (ι × ι)} {pc : PassChecker G images} {undefTy : Option (Ty ι)} {P : ControlFlow.Program}
    {w : Walk ι} {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {Tres : Fam} {m l : Nat}
    (na : NodeAccepted G images pool fuel suggestions index codes aliases pc undefTy P w startNames ρ0 ctx Tres m l) :
    NodeAccepted' G images pool fuel suggestions index codes aliases pc undefTy P w startNames ρ0 ctx Tres m l :=
  { na with
    shape := fun n W v hv => by
      have := na.shape n W v hv
      cases hk : na.node.continuation <;> rw [hk] at this <;> first | exact this | exact this.elim }

/-- **Every node of the pass delivers, at every continuation**
(`StepEdgesSoundT'`): `stepEdgesSound_of` over `NodeAccepted'`. -/
theorem stepEdgesSound'_of {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool}
    {aliases : List (ι × ι)} {pc : PassChecker G images} {undefTy : Option (Ty ι)} {P : ControlFlow.Program}
    {w : Walk ι} {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {Tres : Fam} {m : Nat}
    (hacc : ∀ l, w.visited l →
      Nonempty (NodeAccepted' G images pool fuel suggestions index codes aliases pc undefTy P w startNames ρ0 ctx Tres m l))
    (hcodes : CodesSound G codes) (hdir : DirectKeepsSummaries G images undefTy)
    (hsrch : SearchKeepsSummaries G images pool fuel suggestions index codes aliases pc.checker) :
    StepEdgesSoundT' P G w startNames ρ0 ctx (excOf G) Tres (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp
  obtain ⟨na⟩ := hacc l hp.1.1
  have hS := na.stated ρ s hp
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  obtain ⟨-, -, -, cn, ce, hparts⟩ :=
    checkedStep_parts na.hstep hS na.wf na.below na.width he hcodes na.sums hdir hsrch
  obtain ⟨hj, ho⟩ := nodeObligations'_of_parts (pre := edgePreT G w startNames ρ0 ctx) (Ξres := excOf G)
    (Tres := Tres) (Qres := fun _ => True) (Rres := fun _ => True) (x := na.node.handler) hparts he
    (fun j U v hv => na.shape (j + 1) U v hv)
    (fun s' v _ hv hF he' _ => normalTarget'_of_exits (fun t p o q hm => na.exits t p o q hm ρ) na.ret
      (fun _ => trivial) s' v hv hF he' (na.shape _ _ v (he'.2 0 _ rfl)))
    (fun s' e _ hFe he' hsc hx => by
      cases hh : na.node.handler with
      | none => exact ⟨hx, trivial⟩
      | some t => exact na.handler t hh ρ s' e hFe he' hsc hx)
  exact ⟨na.node, na.hP, _, _, cn, ce, _, _, hj, ho⟩

end Nodes

end Verification.TolerantFrames
