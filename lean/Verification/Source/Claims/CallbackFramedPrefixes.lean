import Verification.Source.Claims.CallbackProducerGuarantee
import Verification.Source.Claims.CallbackGraphDispatch

namespace Verification.SourceClaimJson.CallbackInferencePlan
open ControlFlow GraphCode HeapObservations TolerantFrames TolerantFrames.ReadOnly PointClaims

private def AllValues (ρ : Env) := ∀ i, isVal (ρ i) = true
private def StateValues : State → Prop
  | .at _ ρ | .eval _ ρ .. => AllValues ρ
  | _ => True

private theorem pushValues {ρ v} (vars : AllValues ρ) (val : isVal v = true) : AllValues (push v ρ) := by
  intro i
  cases i with | zero => exact val | succ i => exact vars i

private theorem stateValues_step {P h s h' s'} (tr : Transition P h s h' s') (old : StateValues s) :
    StateValues s' := by
  have mapped {ρ : Env} (m : PointClaims.Mapping) (hv : AllValues ρ) : AllValues (mapEnv m ρ) := fun _ => hv _
  cases tr <;> first | trivial | exact old | exact mapped _ old | exact mapped _ (pushValues old (by assumption)) |
    exact mapped _ (pushValues old rfl) | exact mapped _ (pushValues old (raises_val (by assumption)))

private theorem execution_snoc {P k h s h' s' h'' s''} (r : Execution P k h s h' s') (t : Transition P h' s' h'' s'') :
    Execution P (k+1) h s h'' s'' := by
  induction r with | refl => exact .next t .refl | next tr _ ih => exact .next tr (ih t)

private theorem deterministic {P k h s h' s' h'' s''} (a : Execution P k h s h' s') (b : Execution P k h s h'' s'') :
    h' = h'' ∧ s' = s'' := by
  induction a with
  | refl => cases b; exact ⟨rfl,rfl⟩
  | next tr _ ih =>
    cases b with
    | next tr' tail =>
      obtain ⟨rfl,rfl⟩ := transition_det tr tr'
      exact ih tail

private theorem stepsSnoc {j h e h' e' h'' e''} (r : Steps j h e h' e') (t : Step h' e' h'' e'') :
    Steps (j+1) h e h'' e'' := by
  induction r with | refl => exact .next t .refl | next tr _ ih => exact .next tr (ih t)

private theorem valSnoc {h t h' t' h'' t''} (r : ValRun h t h' t')
    (values : ∀ (l : Nat) (v : Tm), h'[l]? = some v → isVal v = true) (step : Step h' t' h'' t'') :
    ValRun h t h'' t'' := by
  induction r with
  | refl => exact .step values step .refl
  | step hv s _ ih => exact .step hv s (ih values step)

private def PastMoments (P : Program) (table : CallbackOrigins.Table) (start : Nat) (entry : Env) (h₀ : Heap) (n : Nat) :=
  ∀ j h st, j < n → Execution P j h₀ (.at start entry) h st → GraphMoment table h st

private theorem extendMoments {P table start entry h₀ k h st} (past : PastMoments P table start entry h₀ k)
    (reached : Execution P k h₀ (.at start entry) h st) (current : GraphMoment table h st) :
    PastMoments P table start entry h₀ (k+1) := by
  intro j h' st' prior run
  by_cases same : j = k
  · subst j
    obtain ⟨rfl,rfl⟩ := deterministic reached run
    exact current
  · exact past _ _ _ (by omega) run

private theorem currentMoment {k} {W : WorldT (k+1)} {h st} {table : CallbackOrigins.Table} (adm : WorldAdm W)
    (ok : HeapOk (k+1) W h) (refs : StateRefs W st) (vals : StateValues st) : GraphMoment table h st := by
  refine ⟨⟨k+1,W,h,by omega,adm,ok⟩,rfl,?_⟩
  cases st with
  | «at» => exact ⟨refs,fun i _ => vals i⟩
  | eval => exact refs.1
  | done | raised => trivial

/-- The current framed evaluation stores its reached node and the heap
values along its own expression reductions, all from the same execution. -/
private inductive Pending (Point : Nat → Env → Heap → Prop) (I : ∀ n, WorldT n → Prop) (P : Program) (table : CallbackOrigins.Table) (start : Nat) (entry : Env) (h₀ : Heap) :
    Nat → Option (Nat × Heap) → Heap → State → Prop where
  | none : Pending Point I P table start entry h₀ budget none h state
  | eval {label node ρ j ticks h t cont handler budget} (s : IndexedHeap) (inherited : I s.n s.W) (point : Point label ρ s.h) (reached : Execution P j h₀ (.at start entry) s.h (.at label ρ))
      (past : PastMoments P table start entry h₀ j) (vals : AllValues ρ) (roots : RootsOk s.W ρ)
      (location : P[label]? = some node) (steps : Steps ticks s.h (instantiate 0 ρ node.expression) h t)
      (run : ValRun s.h (instantiate 0 ρ node.expression) h t) (room : ticks + budget < s.n) :
      Pending Point I P table start entry h₀ budget (some (label,s.h)) h (.eval t ρ cont handler)

/-- Exactly what a framed normal return must establish. Every graph prefix
and operand prefix supplied here precedes the return currently being proved. -/
def NormalReturns (P : Program) (table : CallbackOrigins.Table) (start : Nat) (entry : Env) (h₀ : Heap)
    (Ret : Nat → Env → Heap → Heap → Prop) :=
  ∀ {label node ρ j ticks after t} (s : IndexedHeap), Execution P j h₀ (.at start entry) s.h (.at label ρ) →
    (∀ i < j, ∀ h st, Execution P i h₀ (.at start entry) h st → GraphMoment table h st) →
    (∀ i, isVal (ρ i) = true) → RootsOk s.W ρ → P[label]? = some node →
    Steps ticks s.h (instantiate 0 ρ node.expression) after t → ValRun s.h (instantiate 0 ρ node.expression) after t →
    ticks < s.n → isVal t = true → Ret label ρ s.h after

def NormalReturnsWith (I : ∀ n, WorldT n → Prop) (P : Program) (table : CallbackOrigins.Table) (start : Nat) (entry : Env) (h₀ : Heap)
    (Ret : Nat → Env → Heap → Heap → Prop) :=
  ∀ {label node ρ j ticks after t} (s : IndexedHeap), I s.n s.W → Execution P j h₀ (.at start entry) s.h (.at label ρ) →
    (∀ i < j, ∀ h st, Execution P i h₀ (.at start entry) h st → GraphMoment table h st) →
    (∀ i, isVal (ρ i) = true) → RootsOk s.W ρ → P[label]? = some node →
    Steps ticks s.h (instantiate 0 ρ node.expression) after t → ValRun s.h (instantiate 0 ρ node.expression) after t →
    ticks < s.n → isVal t = true → Ret label ρ s.h after

def NormalReturnsAt (Point : Nat → Env → Heap → Prop) (I : ∀ n, WorldT n → Prop) (P : Program) (table : CallbackOrigins.Table) (start : Nat) (entry : Env) (h₀ : Heap)
    (Ret : Nat → Env → Heap → Heap → Prop) :=
  ∀ {label node ρ j ticks after t} (s : IndexedHeap), I s.n s.W → Point label ρ s.h → Execution P j h₀ (.at start entry) s.h (.at label ρ) →
    (∀ i < j, ∀ h st, Execution P i h₀ (.at start entry) h st → GraphMoment table h st) →
    (∀ i, isVal (ρ i) = true) → RootsOk s.W ρ → P[label]? = some node →
    Steps ticks s.h (instantiate 0 ρ node.expression) after t → ValRun s.h (instantiate 0 ρ node.expression) after t →
    ticks < s.n → isVal t = true → Ret label ρ s.h after

private theorem advance {P table start entry h₀ p h st h' st' F k} {W : WorldT (k+1)} {Ret}
    {I : ∀ n, WorldT n → Prop} {Point : Nat → Env → Heap → Prop} (current : I (k+1) W)
    (atPoint : ∀ l ρ, st = .at l ρ → Point l ρ h) (returns : NormalReturnsAt Point I P table start entry h₀ Ret) (pend : Pending Point I P table start entry h₀ (k+1) p h st)
    {j} (reached : Execution P j h₀ (.at start entry) h st) (past : PastMoments P table start entry h₀ j)
    (vars : StateValues st) (refs : StateRefs W st) (adm : WorldAdm W) (heap : HeapOk (k+1) W h)
    (tr : Transition P h st h' st') :
    RetAtG Ret (fun _ _ _ _ => True) p h' st st' ∧ Pending Point I P table start entry h₀ k (pendG F p h st st') h' st' := by
  cases tr with
  | enter atNode =>
    refine ⟨trivial,?_⟩
    simp only [pendG,enterPend]
    rename_i l node ρ
    cases F l <;> first | exact .none | exact .eval ⟨k+1,W,_,by omega,adm,heap⟩ current (atPoint _ _ rfl) reached past vars refs atNode .refl .refl (by simp)
  | expr step =>
    refine ⟨trivial,?_⟩
    cases pend with
    | none => exact .none
    | eval s prior point r past vals roots loc steps run room =>
      exact .eval s prior point r past vals roots loc (stepsSnoc steps step)
        (valSnoc run (HeapExpressionRules.heap_values adm heap) step) (by omega)
  | _ =>
    refine ⟨?_,.none⟩
    cases pend with
    | none => exact retAtG_none _ _ _
    | eval s prior point r earlier vals roots loc steps run room =>
      exact ⟨fun value => returns s prior point r (fun i hi h st run => earlier i h st hi run) vals roots loc steps run (by omega) value,fun _ => trivial⟩

private theorem retAt_of_graph {E K h' t t' st st' p Ret} (sim : Sim E K t st) (sim' : Sim E K t' st')
    (ret : RetAtG Ret (fun _ _ _ _ => True) p h' st st') :
    RetAt Ret (fun _ _ _ _ => True) p h' t t' := by
  cases p with
  | none => trivial
  | some pair =>
    obtain ⟨l,h⟩ := pair
    cases sim with
    | goto | raised => trivial
    | done val =>
      cases t <;> first | trivial | contradiction
    | frame =>
      rename_i u L d k x comp
      by_cases val : isVal u = true
      · cases sim' with
        | frame => exact Or.inl rfl
        | goto | raised | done => exact Or.inr (.inl ⟨val,ret.1 val⟩)
      · exact Or.inr (.inr ⟨Bool.eq_false_iff.mpr val,trivial⟩)

/-- Discharge framed returns only after the corresponding expression has
completed. The induction supplies typed heaps and valid references at all
strictly earlier graph moments from the framed guarantee itself. -/
theorem safe_of_normalReturnsAt {E K table start L d comp h₀ n} {W : WorldT n} {F Ret J Ξ T Q R}
    {I : ∀ n, WorldT n → Prop} (initial : I n W)
    (persist : ∀ {k} {U : WorldT (k+1)} {V : WorldT k}, I (k+1) U → WExt (trunc k (Nat.le_succ _) U) V → I k V)
    {Point : Nat → Env → Heap → Prop}
    (readPoint : ∀ h l L d c, J h (.goto E K l L d c) → Point l (envOf L d) h)
    (returns : NormalReturnsAt Point I (program E K) table start (envOf L d) h₀ Ret)
    (vars : ∀ i, isVal (envOf L d i) = true) (adm : WorldAdm W) (heap : HeapOk n W h₀)
    (safe : SafeRet J Ξ T Q R F Ret (fun _ _ _ _ => True) n W none h₀ (.goto E K start L d comp)) :
    SafePostExcW Ξ T Q R n W h₀ (.goto E K start L d comp) := by
  have follow : ∀ {k} {U : WorldT k} {p h t st j}, Sim E K t st →
      Execution (program E K) j h₀ (.at start (envOf L d)) h st →
      PastMoments (program E K) table start (envOf L d) h₀ j →
      Pending Point I (program E K) table start (envOf L d) h₀ k p h st →
      StateValues st → I k U → WorldAdm U → HeapOk k U h →
      SafeRet J Ξ T Q R F Ret (fun _ _ _ _ => True) k U p h t → SafePostExcW Ξ T Q R k U h t := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs; exact hs
    | succ k ih =>
      intro U p h t st j sim reached past pending values keep world heapOK hs
      obtain ⟨refs,checked,out⟩ := hs
      refine ⟨refs,?_⟩
      rcases out with ended | ⟨V,h',t',ext,adm',step,heap',rest⟩
      · exact .inl ended
      · obtain ⟨st',transition,sim'⟩ := sim_step_back sim step
        have stateRefs := stateRefs_of_sim sim refs
        have atPoint : ∀ l ρ, st = .at l ρ → Point l ρ h := by
          intro l ρ eq
          subst st
          cases sim
          exact readPoint _ _ _ _ _ checked
        obtain ⟨holds,pend'⟩ := advance keep atPoint returns pending reached past values stateRefs world heapOK transition
        have more := rest (retAt_of_graph sim sim' holds)
        rw [sim_pend sim transition sim'] at more
        exact .inr ⟨V,h',t',ext,adm',step,heap',ih sim' (execution_snoc reached transition)
          (extendMoments past reached (currentMoment world heapOK stateRefs values)) pend'
          (stateValues_step transition values) (persist keep ext) adm' heap' more⟩
  exact follow .goto .refl (fun _ _ _ no => by omega) .none vars initial adm heap safe

theorem safe_of_normalReturnsWith {E K table start L d comp h₀ n} {W : WorldT n} {F Ret J Ξ T Q R}
    {I : ∀ n, WorldT n → Prop} (initial : I n W)
    (persist : ∀ {k} {U : WorldT (k+1)} {V : WorldT k}, I (k+1) U → WExt (trunc k (Nat.le_succ _) U) V → I k V)
    (returns : NormalReturnsWith I (program E K) table start (envOf L d) h₀ Ret)
    (vars : ∀ i, isVal (envOf L d i) = true) (adm : WorldAdm W) (heap : HeapOk n W h₀)
    (safe : SafeRet J Ξ T Q R F Ret (fun _ _ _ _ => True) n W none h₀ (.goto E K start L d comp)) :
    SafePostExcW Ξ T Q R n W h₀ (.goto E K start L d comp) := by
  refine safe_of_normalReturnsAt (table := table) (Point := fun _ _ _ => True) initial persist (fun _ _ _ _ _ _ => trivial) ?_ vars adm heap safe
  intro label node ρ j ticks after t s keep _
  exact returns s keep

theorem safe_of_normalReturns {E K table start L d comp h₀ n} {W : WorldT n} {F Ret J Ξ T Q R}
    (returns : NormalReturns (program E K) table start (envOf L d) h₀ Ret)
    (vars : ∀ i, isVal (envOf L d i) = true) (adm : WorldAdm W) (heap : HeapOk n W h₀)
    (safe : SafeRet J Ξ T Q R F Ret (fun _ _ _ _ => True) n W none h₀ (.goto E K start L d comp)) :
    SafePostExcW Ξ T Q R n W h₀ (.goto E K start L d comp)  := by
  refine safe_of_normalReturnsWith (table := table) (I := fun _ _ => True) trivial (fun _ _ => trivial) ?_ vars adm heap safe
  intro label node ρ j ticks after t s _
  exact returns s

end Verification.SourceClaimJson.CallbackInferencePlan
