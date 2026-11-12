import Verification.Programs.TolerantFramesNodeJoined

/-! # Tolerant frames: a step's kept yields hold of the values it returns

`run` keeps a step's yields only where the checker's yield check accepts
them (`SinglePass.checkedYields`, pass change D2): outside a call at a
promise signature, the yields `PromiseCalls.yieldFollows` accepts of the
node's term. Proved:

- `SafePostExc.conj_post`: a run safe with a normal and a throw
  postcondition, and safe with another value property, is safe with that
  property and both postconditions (the two runs are the same run,
  `Step_det`; heaps are world-free);
- `checkedYields_follows`: outside a promise call, every kept yield is one
  `yieldFollows` accepts;
- `stepYields_judgment`: the step's local judgment (`StepParts`) with the
  claim's type strengthened by `YieldsOk` of the accepted yields, where the
  context types the environment, the implications the yields read hold and
  the step's facts' links hold (`yieldFollows_sound`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Yields
variable {ι : Type} [DecidableEq ι] [Hashable ι]

omit [DecidableEq ι] [Hashable ι] in
/-- **Two safety statements of one run combine**: the value property of the
second, the normal and throw postconditions of the first, at the second's
worlds. -/
theorem SafePostExc.conj_post {Ξ T T' : Fam} {Q Q' : Post} {R : Heap → Prop} :
    ∀ {n} {W W' : WorldT n} {h t}, SafePostExc Ξ T Q R n W h t → SafePost Ξ T' Q' n W' h t →
      SafePostExc Ξ T' Q R n W' h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ p ih =>
    intro W W' h t h1 h2
    rcases h1 with ((⟨hv1, -, hQ⟩ | ⟨hr1, hR⟩) | ⟨Z, h1, t1, -, -, hst1, -, hc1⟩)
    · rcases h2 with ((⟨-, hT', -⟩ | hr2) | ⟨_, _, _, _, _, hst2, _, _⟩)
      · exact .inl (.inl ⟨hv1, hT', hQ⟩)
      · rw [hr2.not_val] at hv1; contradiction
      · exact absurd hst2 (value_no_step hv1)
    · rcases h2 with ((⟨hv2, -, -⟩ | hr2) | ⟨_, _, _, _, _, hst2, _, _⟩)
      · rw [hr1.not_val] at hv2; contradiction
      · exact .inl (.inr ⟨hr2, hR⟩)
      · exact absurd hst2 hr1.no_step
    · rcases h2 with ((⟨hv2, -, -⟩ | hr2) | ⟨Z', h2, t2, hz, huz, hst2, hok2, hc2⟩)
      · exact absurd hst1 (value_no_step hv2)
      · exact absurd hst1 hr2.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det hst1 hst2
        exact .inr ⟨Z', h1, t1, hz, huz, hst2, hok2, ih hc1 hc2⟩

omit [Hashable ι] in
/-- **Outside a promise call, a kept yield follows from the term**
(`checkedYields`' filter by `yieldFollows`). -/
theorem checkedYields_follows {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ : List (Ty ι)} {A : Ty ι}
    {xs : List (PromiseCalls.Implication ι)} {k out : HeapKnowledge.Knowledge} {e : ProgramCertificates.Evidence ι}
    {t : Tm} {ys : List (PromiseCalls.Yield ι)} (hp : PromiseCalls.promiseOf G e = none) :
    (checkedYields G images Γ A xs k out e t ys).all (PromiseCalls.yieldFollows G images Γ xs k.links t) = true := by
  unfold checkedYields
  split
  · rfl
  · rw [hp]
    exact List.all_eq_true.mpr fun _ hy => (List.mem_filter.mp hy).2

omit [Hashable ι] in
/-- **The step's judgment with its accepted yields**: where every yield
`ys` is one `yieldFollows` accepts of the node's term at the implications
`xs` and the links `links`, the context types `ρ`, `xs` and `links` hold,
the step's local judgment holds with each returned value meeting the
claim's type and `YieldsOk ys`. -/
theorem stepYields_judgment {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ : List (Ty ι)} {A : Ty ι}
    {xs : List (PromiseCalls.Implication ι)} {links : HeapLinks.Links} {t : Tm} {ys : List (PromiseCalls.Yield ι)}
    {Q : Post} {R : Heap → Prop} {ρ : Env} {s : IndexedHeap}
    (hc : ys.all (PromiseCalls.yieldFollows G images Γ xs links t) = true)
    (he : EnvOk G Γ ρ s.n s.W) (hx : PromiseCalls.ImpliesOk G xs ρ s.n s.W) (hl : HeapLinks.Holds links ρ s.h)
    (hj : SafePostExc (excOf G) (meaning G A) Q R s.n s.W s.h (instantiate 0 ρ t)) :
    SafePostExc (excOf G) (fun k U u => meaning G A k U u ∧ PromiseCalls.YieldsOk G ys ρ k U u) Q R
      s.n s.W s.h (instantiate 0 ρ t) :=
  SafePostExc.conj_post hj (PromiseCalls.yieldFollows_sound hc he hx s.ok hl hj.post)

end Yields

section Edge
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **A normal exit into a node other than a loop head delivers, its yields
at the step's value** (`exitDelivers_of_edge` with the step's yields read
from the state after the step at the returned value, and the target's
types from the edge's check where the yields hold: the context the yields
refine). -/
theorem exitDeliversY_of_edge {G : NormalGraph ι} {w : Walk ι} {ctx : Nat → List (Ty ι)} {A : Ty ι}
    {Γ : List (Ty ι)} {entry : SinglePass.State} {store : Store} {result width : Nat} {pushed outFresh : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool} {t : Target}
    {I : List (PromiseCalls.Implication ι)} {ys : List (PromiseCalls.Yield ι)} {start : List Nat} {E : Env}
    {m : Nat}
    (hpo : observed.isSome = true → pushed = true) (hpp : promote.isSome = true → pushed = false)
    (hmap : MapNamesSound (if pushed then result :: entry.names else entry.names) t.mapping)
    (hrec : (edgeTransfer (if pushed then result :: entry.names else entry.names) t.mapping pushed false outFresh
      entry result (edgeStoreOf G (if pushed then A :: Γ else Γ) entry.store store
        (if pushed then result :: entry.names else entry.names) (result :: entry.names) width pushed false observed
        promote) (I ++ freshImplOf pushed false ys entry.names result)) ∈ w.incoming t.label)
    (hfo : ∀ v, pushed = true → outFresh = true → result ∉ entry.fresh → FreshAt m v)
    (ρ : Env)
    (htc : ∀ (s' : IndexedHeap) v, EnvOk G (A :: Γ) (push v ρ) s'.n s'.W → ObservedOk observed promote v →
      PromiseCalls.YieldsOk G ys ρ s'.n s'.W v →
      EnvOk G (ctx t.label) (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) s'.n s'.W) :
    ExitDelivers (edgePreT G w start E ctx) G A Γ
      (fun ρ' m' s' => StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I start E ρ' m' s' ∧
        PromiseCalls.YieldsOk G ys ρ s'.n s'.W (ρ' 0)) ρ m t pushed observed promote := by
  intro s' v _ hF he ho
  obtain ⟨hF, hy⟩ := hF
  refine normal_edge_delivers hF ho hpo hpp (fun hs => ?_) (fun _ => hy) hmap (hfo v) hrec (htc s' v he ho hy)
  rw [hpo hs]; simpa using he

end Edge

section Obligations
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- **A node's obligations from its step's parts, with its yields**:
`nodeObligations_of_parts` with the judgment's values also meeting
`YieldsOk ys` (`hjY`), which each normal exit's target obligation receives
at the state after the step (`hnormal`). -/
theorem nodeObligations_of_partsY {G : NormalGraph ι} {A : Ty ι} {Γ : List (Ty ι)} {cn ce : Footprints.Closed}
    {t : Tm} {out : HeapKnowledge.Knowledge} {Fn Fe : Assertion} {ρ : Env} {m : Nat} {s : IndexedHeap}
    {ys : List (PromiseCalls.Yield ι)}
    {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {k : Continuation} {x : Option Target}
    (hp : StepParts G A cn ce t out Fn Fe ρ m s) (he : EnvOk G Γ ρ s.n s.W)
    (hjY : SafePostExc (excOf G) (fun j U u => meaning G A j U u ∧ PromiseCalls.YieldsOk G ys ρ j U u)
      (fun h' v => cn.Holds s.h h' ∧ HeapKnowledge.Holds out (push v ρ) h') (fun h' => ce.Holds s.h h' ∧ True)
      s.n s.W s.h (instantiate 0 ρ t))
    (hshape : ∀ j (U : WorldT (j + 1)) v, meaning G A (j + 1) U v → ShapeOk v k)
    (hnormal : ∀ (s' : IndexedHeap) v, Admissible s s' → isVal v = true → Fn (push v ρ) m s' →
      PromiseCalls.YieldsOk G ys ρ s'.n s'.W v →
      EnvOk G (A :: Γ) (push v ρ) s'.n s'.W → HeapKnowledge.Holds out (push v ρ) s'.h →
      NormalTarget pre Tres Qres ρ m s' v k)
    (hraise : ∀ (s' : IndexedHeap) e, Admissible s s' → Fe ρ m s' → EnvOk G Γ ρ s'.n s'.W → Scoped 0 e →
      excOf G s'.n s'.W e → RaiseTarget pre Ξres Rres ρ m s' e x) :
    SafePostExc (excOf G) (fun j U u => meaning G A j U u ∧ PromiseCalls.YieldsOk G ys ρ j U u)
      (fun h' v => cn.Holds s.h h' ∧ (HeapKnowledge.Holds out (push v ρ) h' ∧
        ∃ k, Steps k s.h (instantiate 0 ρ t) h' v))
      (fun h' => ce.Holds s.h h' ∧ True) s.n s.W s.h (instantiate 0 ρ t) ∧
    NodeObligations pre Ξres Tres Qres Rres (excOf G)
      (fun j U u => meaning G A j U u ∧ PromiseCalls.YieldsOk G ys ρ j U u) cn ce
      (fun h' v => HeapKnowledge.Holds out (push v ρ) h' ∧ ∃ k, Steps k s.h (instantiate 0 ρ t) h' v)
      (fun _ => True) ρ m s k x := by
  obtain ⟨-, hn, hx⟩ := hp
  refine ⟨SafePostExc.weaken (fun _ _ ⟨⟨hc, ho⟩, hk⟩ => ⟨hc, ho, hk⟩) (fun _ h => h) (safePostExc_trace hjY),
    ⟨fun j U h v _ hT _ _ => hshape j U v hT.1, ?_, ?_⟩⟩
  · intro s' v ha hv ⟨U, hU, hT, hY⟩ ⟨ho, k', hk⟩
    have hT' : meaning G A s'.n s'.W v := by
      have := (meaning_adm G A).down_le (s'.n + 1) s'.n (Nat.le_succ _) U v hT
      rwa [hU] at this
    have hY' : PromiseCalls.YieldsOk G ys ρ s'.n s'.W v :=
      hY.transfer s'.n (Nat.le_succ _) s'.W (by rw [hU]; exact WExt_refl _)
    exact hnormal s' v ha.1 hv (hn k' s'.h v s' hk hv ha rfl ho) hY' ((envOk_admissible ha.1 he).push hT') ho
  · intro s' e ha hsc ⟨U, hU, hΞ⟩ _
    have hΞ' : excOf G s'.n s'.W e := by
      have := (builtinExc_adm G _).down_le (s'.n + 1) s'.n (Nat.le_succ _) U e hΞ
      rwa [hU] at this
    exact hraise s' e ha.1 (hx s' ha) (envOk_admissible ha.1 he) hsc hΞ'

/-- **A step's judgment carries its kept yields** `ys`: at every state
where the entry state `entry` holds, the context types the environment and
the step's facts `stepK` hold, the step's judgment at the claim's type `A`
holds with each value also meeting `YieldsOk ys`. -/
def YieldsJudged (G : NormalGraph ι) (A : Ty ι) (Γ : List (Ty ι)) (t : Tm) (entry : SinglePass.State)
    (I : List (PromiseCalls.Implication ι)) (startNames : List Nat) (ρ0 : Env) (m : Nat)
    (stepK : HeapKnowledge.Knowledge) (ys : List (PromiseCalls.Yield ι)) : Prop :=
  ∀ ρ (s : IndexedHeap) (Q : Post) (R : Heap → Prop), StateHolds G entry I startNames ρ0 ρ m s →
    EnvOk G Γ ρ s.n s.W → HeapKnowledge.Holds stepK ρ s.h →
    SafePostExc (excOf G) (meaning G A) Q R s.n s.W s.h (instantiate 0 ρ t) →
    SafePostExc (excOf G) (fun k U u => meaning G A k U u ∧ PromiseCalls.YieldsOk G ys ρ k U u) Q R
      s.n s.W s.h (instantiate 0 ρ t)

omit [Hashable ι] [Instantiates ι] in
/-- **Yields `yieldFollows` accepts are judged** (`stepYields_judgment`):
where every yield passes `yieldFollows` at the implications `xs` and the
step's links, and `xs` holds wherever the entry state does. -/
theorem yieldsJudged_of_follows {G : NormalGraph ι} {images : InstanceImageCheck G} {A : Ty ι}
    {Γ : List (Ty ι)} {t : Tm} {entry : SinglePass.State} {I : List (PromiseCalls.Implication ι)}
    {startNames : List Nat} {ρ0 : Env} {m : Nat} {stepK : HeapKnowledge.Knowledge}
    {xs : List (PromiseCalls.Implication ι)} {ys : List (PromiseCalls.Yield ι)}
    (hc : ys.all (PromiseCalls.yieldFollows G images Γ xs stepK.links t) = true)
    (hx : ∀ ρ (s : IndexedHeap), StateHolds G entry I startNames ρ0 ρ m s → PromiseCalls.ImpliesOk G xs ρ s.n s.W) :
    YieldsJudged G A Γ t entry I startNames ρ0 m stepK ys :=
  fun ρ s _ _ hS he hk hj => stepYields_judgment hc he (hx ρ s hS) hk.2.2.1 hj

/-- **What a node's step means with its kept yields** `ys`: the step's
judgment carrying them (`YieldsJudged`), a return's goal from the state after the step,
the claim's type and the yields (`ret`, the premises of
`goalHolds_of_return`), each normal exit delivering from the state after the step
and the yields at the pushed value (`exits`). `NodeMeaning`'s `ret` and
`exits`, stated for every value of the claim's type, restated at the values
the step returns. -/
structure NodeYielded (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat)
    (ρ0 : Env) (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge) (given : Nat → Bool)
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (Tres : Fam) (m : Nat) (l : Nat) (node : Node) (c : PointClaim ι) (entry : SinglePass.State) (st : Stepped ι)
    (ys : List (PromiseCalls.Yield ι)) : Prop where
  judged : YieldsJudged G c.type c.context node.expression entry (w.implies l) startNames ρ0 m st.stepK ys
  ret : node.continuation = .ret → ∀ ρ (s' : IndexedHeap) v, isVal v = true →
    StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ρ0 (push v ρ) m s' →
    EnvOk G (c.type :: c.context) (push v ρ) s'.n s'.W → PromiseCalls.YieldsOk G ys ρ s'.n s'.W v →
    Tres s'.n s'.W v
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ,
    ExitDelivers (edgePreAJ G w startNames ρ0 ctx stated given edgesIn) G c.type c.context
      (fun ρ' m' s' => StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ρ0
        ρ' m' s' ∧ PromiseCalls.YieldsOk G ys ρ s'.n s'.W (ρ' 0)) ρ m t pushed observed promote

omit [Instantiates ι] in
/-- **Every checked node delivers, its exits and return reading its kept
yields** (`StepEdgesSoundJ`): `stepEdgesSoundJ_of_checked` with the
judgment strengthened by the yields (`stepYields_judgment`), the return's
goal and the exits from `NodeYielded`, the entry state, the shapes and the
handler from `NodeMeaning`, the handler's joined implications from
`NodeJoined`. -/
theorem stepEdgesSoundJ_of_yields {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G images} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {given : Nat → Bool}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {Tres : Fam} {m : Nat}
    (hacc : ∀ l, w.visited l → ∃ r : NodeChecked G images codes pc P w startNames ctx l,
      ∃ ys, NodeMeaning G w startNames ρ0 ctx stated Tres m l r.node r.c r.entry r.st ∧
      NodeJoined G w startNames ρ0 ctx given edgesIn m l r.node r.c r.entry r.st ∧
      NodeYielded G w startNames ρ0 ctx stated given edgesIn Tres m l r.node r.c r.entry r.st ys)
    (hcodes : CodesSound G codes) :
    StepEdgesSoundJ P G w startNames ρ0 ctx stated given edgesIn (excOf G) Tres (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp
  obtain ⟨na, ys, hm, hJ, hY⟩ := hacc l hp.1.1
  have hS := hm.entered ρ s hp
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  obtain ⟨-, hkS, -, cn, ce, hparts⟩ := stepChecked_parts na.hstep hS na.wf na.below na.width he hcodes na.sums
  have hjY := hY.judged ρ s _ _ hS he hkS hparts.1
  obtain ⟨hj, ho⟩ := nodeObligations_of_partsY (pre := edgePreAJ G w startNames ρ0 ctx stated given edgesIn)
    (Ξres := excOf G) (Tres := Tres) (Qres := fun _ => True) (Rres := fun _ => True) (x := na.node.handler)
    hparts he hjY
    (fun j U v hv => hm.shape (j + 1) U v hv)
    (fun s' v _ hv hF hy he' _ => by
      have hshape := hm.shape _ _ v (he'.2 0 _ rfl)
      by_cases hk : na.node.continuation = .ret
      · rw [hk]
        exact ⟨hY.ret hk ρ s' v hv hF he' hy, trivial⟩
      · exact normalTarget_of_exits (Fn := fun ρ' m' s'' => StateHolds G
            ⟨na.st.result :: na.entry.names, na.st.store, na.entry.fresh⟩ (w.implies l) startNames ρ0 ρ' m' s'' ∧
            PromiseCalls.YieldsOk G ys ρ s''.n s''.W (ρ' 0))
          (fun t p o q hmem => hY.exits t p o q hmem ρ) (fun h => absurd h hk)
          (fun _ => trivial) s' v hv ⟨hF, hy⟩ he' hshape)
    (fun s' e _ hFe he' hsc hx => by
      cases hh : na.node.handler with
      | none => exact ⟨hx, trivial⟩
      | some t =>
        exact ⟨hm.handler t hh ρ s' e hFe he' hsc hx, hJ.handler t hh ρ s' e hFe he' hsc hx⟩)
  exact ⟨na.node, na.hP, _, _, cn, ce, _, _, hj, ho⟩

end Obligations

end Verification.TolerantFrames
