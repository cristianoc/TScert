import Verification.Source.Claims.CallbackCallerPrefix
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open ControlFlow GraphCode ProgramTyping PositiveGraphs PositiveRules ProgramCertificates HeapObservations
open CallbackInferencePlan TolerantFrames PointClaims PassUnit

theorem frame_refs {n} {W : WorldT n} {E K l L d comp c t}
    (outer : RefsOk W (.goto E K l L d comp)) (inner : RefsOk W t) : RefsOk W (.frame E K t L d c none comp) := by
  intro loc item
  simp only [refs,List.mem_append] at item
  rcases item with ((expr | here) | localRef) | defaultRef
  · exact outer loc (by simp only [refs,List.mem_append]; exact .inl (.inl expr))
  · exact inner loc here
  · exact outer loc (by simp only [refs,List.mem_append]; exact .inl (.inr localRef))
  · exact outer loc (by simp [refs,defaultRef])

/-- Run one ordinary prefix expression, then resume the actual graph continuation
at the reached heap and extended world. A thrown expression exits its frame. -/
theorem frameContinue {Ξ A B : Fam} {Q : Post} (excAdm : Adm Ξ) {n} {W : WorldT n} {h t E K L d l c comp}
    (adm : WorldAdm W) (heap : HeapOk n W h) (outer : RefsOk W (.goto E K l L d comp))
    (run : SafePostExc Ξ A Q (fun _ => True) n W h t)
    (next : ∀ j (le : j ≤ n) U, WExt (trunc j le W) U → WorldAdm U → ∀ h' v, HeapOk j U h' →
      isVal v = true → A j U v → Q h' v → RefsOk U v →
      SafePostExc Ξ B (fun _ _ => True) (fun _ => True) j U h' (.frame E K v L d c none comp)) :
    SafePostExc Ξ B (fun _ _ => True) (fun _ => True) n W h (.frame E K t L d c none comp) := by
  induction n generalizing t h with
  | zero => exact frame_refs outer run
  | succ n ih =>
    have refs := frame_refs (c := c) outer run.1
    rcases run.2 with (⟨hv,ty,post⟩ | ⟨⟨ex,throws,scope,mem⟩,_⟩) | ⟨V,h',u,ext,world,step,ok,more⟩
    · exact next _ (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) adm _ _ heap hv ty post run.1
    · have refExc := RefsOk_trunc (Nat.le_succ n) (run.1.sub (Kinds.raises_refs throws))
      refine ⟨refs,.inr ⟨_,h,.throw ex,WExt_refl _,WorldAdm_trunc _ adm,.frameRaise throws,HeapOk_trunc n W h heap,?_⟩⟩
      cases n with
      | zero => exact refExc
      | succ m => exact ⟨refExc,.inl (.inr ⟨⟨ex,.throwV (raises_val throws) (raises_sourceVal throws),
          scope,excAdm.down _ W _ mem⟩,trivial⟩)⟩
    · refine ⟨refs,.inr ⟨V,h',_,ext,world,.frameC step,ok,ih world ok
        (RefsOk_mono ext (RefsOk_trunc _ outer)) more ?_⟩⟩
      intro j le U e
      apply next j (by omega) U
      simpa only [trunc_trunc] using WExt_trans (WExt_trunc le ext) e

def PrefixMap (pushed : Bool) (dest : ControlFlow.Target) : Continuation := if pushed then .bind dest else .effect dest

def prefixPush (pushed : Bool) (v : α) (L : List α) := if pushed then v::L else L
def prefixPushEnv (pushed : Bool) (v : Tm) (ρ : Env) := if pushed then push v ρ else ρ

theorem prefixPush_env {pushed v L d} : prefixPushEnv pushed v (envOf L d) = envOf (prefixPush pushed v L) d := by
  cases pushed <;> simp [prefixPushEnv,prefixPush,push_envOf]

/-- A finite prefix ending at the checked direct call. Every edge is the
actual normal continuation; a target slot either has its predecessor's type
or is unnecessary for this theorem. -/
inductive PrefixPlan {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (I : PositiveCertificates.InstanceImageCheck G)
    (codes : CodeEntry ι → Bool) (P : Program) (cut : Nat) (final : List (Option (Ty ι))) :
    Nat → List (Option (Ty ι)) → Type where
  | done : PrefixPlan G I codes P cut final cut final
  | step {l Γ term A flag dest Δ} (node : P[l]? = some ⟨term,PrefixMap flag dest,none⟩)
      (expression : PrefixExpression G I codes Γ term A)
      (slots : ∀ (i : Nat) B, Δ[i]?.join = some B →
        (prefixPush flag (some A) Γ)[PointClaims.slot dest.mapping i]?.join = some B)
      (tail : PrefixPlan G I codes P cut final dest.label Δ) : PrefixPlan G I codes P cut final l Γ

private theorem prefixEval {P l term cont h ρ ticks h' v}
    (node : P[l]? = some ⟨term,cont,none⟩) (steps : Steps ticks h (instantiate 0 ρ term) h' v) :
    Execution P (ticks+1) h (.at l ρ) h' (.eval v ρ cont none) := by
  have lift {h t j h' u} (ss : Steps j h t h' u) : Execution P j h (.eval t ρ cont none) h' (.eval u ρ cont none) := by
    induction ss with
    | refl => exact .refl
    | next s _ ih => exact .next (.expr s) ih
  exact .next (.enter node) (lift steps)

private theorem chainExecution {P h a j h' b k h'' c} (r : Execution P j h a h' b) (s : Execution P k h' b h'' c) :
    ∃ t, Execution P t h a h'' c := by
  induction r with
  | refl => exact ⟨_,s⟩
  | next step _ ih => obtain ⟨j,rest⟩ := ih s; exact ⟨_,.next step rest⟩

private theorem pushed_partial {ι : Type} {G : NormalGraph ι} {Γ ρ n W A v}
    (typed : PartialEnv G Γ ρ n W) (value : meaning G A n W v) (flag : Bool) :
    PartialEnv G (prefixPush flag (some A) Γ) (prefixPushEnv flag v ρ) n W := by
  cases flag
  · exact typed
  · refine ⟨?_,?_⟩
    · intro i; cases i with | zero => exact (meaning_value value).2 | succ i => exact typed.1 i
    · intro i B hit
      cases i with
      | zero => simp [prefixPush] at hit; cases hit; exact value
      | succ i => exact typed.2 i B hit

theorem PrefixPlan.safe {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {I codes P start cut final l Γ}
    (plan : PrefixPlan G I codes P cut final l Γ) (codeTable : CodesSound G codes)
    (source : P.all (fun n => ObjectCoherence.sourceTerm n.expression) = true)
    {comp entry h₀} {T : Fam} {Keep : ∀ n, WorldT n → Prop}
    (stable : ∀ {n} {W : WorldT n} {j} (le : j ≤ n) {U}, WExt (trunc j le W) U → Keep n W → Keep j U)
    (atCut : ∀ {j h L d n W}, Execution P j h₀ (.at start entry) h (.at cut (envOf L d)) →
      Keep n W → PartialEnv G final (envOf L d) n W → RootsOk W (envOf L d) → (∀ i, isVal (envOf L d i) = true) →
      WorldAdm W → HeapOk n W h → SafePostExc (excOf G) T (fun _ _ => True) (fun _ => True) n W h (gotoOf P cut L d comp))
    {j h L d n W} (path : Execution P j h₀ (.at start entry) h (.at l (envOf L d)))
    (typed : PartialEnv G Γ (envOf L d) n W) (roots : RootsOk W (envOf L d)) (values : ∀ i, isVal (envOf L d i) = true)
    (keep : Keep n W) (world : WorldAdm W) (heap : HeapOk n W h) :
    SafePostExc (excOf G) T (fun _ _ => True) (fun _ => True) n W h (gotoOf P l L d comp) := by
  induction plan generalizing j h L d n with
  | done => exact atCut path keep typed roots values world heap
  | @step l Γ term A flag dest Δ node expr mapped tail ih =>
    let E := P.map (·.expression)
    let K := P.map fun nd => (nd.continuation,nd.handler)
    have atExpr : E[l]? = some term := by simp [E,List.getElem?_map,node]
    have atCont : K[l]? = some (PrefixMap flag dest,none) := by simp [K,List.getElem?_map,node]
    have enter : Step h (gotoOf P l L d comp) h (.frame E K (instantiate 0 (envOf L d) term) L d (PrefixMap flag dest) none comp) :=
      .gotoEnter atExpr atCont
    have outer := gotoOf_refsOk (start := l) (comp := comp) source roots
    have pre : AdminPrefix W h (gotoOf P l L d comp) _ := .next outer enter .refl
    apply pre.safe world heap
    intro k le
    have world' := WorldAdm_trunc le world
    have heap' := heapAtLower le heap
    have typed' := typed.transfer k le _ (WExt_refl _)
    have termRefs : RefsOk W (instantiate 0 (envOf L d) term) := by
      intro r hit
      rcases Kinds.instantiate_refs _ _ _ _ hit with ht | ⟨i,hi⟩
      · exact program_source_refsOk source W _ (List.mem_of_getElem? node) r ht
      · exact roots i r hi
    have localSafe := expr.safe codeTable typed' world' heap' (RefsOk_trunc le termRefs)
    have normal := safePostExc_trace (SafePostExc.of_post (R := fun _ => True) (fun _ => trivial) (of_safe localSafe))
    apply frameContinue (PositiveGraphs.builtinExc_adm G _) world' heap' (RefsOk_trunc le outer) normal
    intro m small U ext au hh v ok hv ty post rv
    let current := envOf L d
    let pushed := prefixPushEnv flag v current
    let pack := envMap dest.mapping (prefixPush flag v L) d
    have pushedTypes := pushed_partial (typed'.transfer _ small _ ext) ty flag
    have envEq : mapEnv dest.mapping pushed = envOf pack.1 pack.2 := by
      rw [← mapEnv_envOf,← prefixPush_env]
    have atTarget : PartialEnv G Δ (envOf pack.1 pack.2) m U := by
      rw [← envEq]
      exact ⟨fun i => pushedTypes.1 _,fun i B hit => pushedTypes.2 _ B (mapped i B hit)⟩
    have baseRefs := fun i => RefsOk_mono ext (RefsOk_trunc small (RefsOk_trunc le (roots i)))
    have targetRefs : RootsOk U (envOf pack.1 pack.2) := by
      rw [← envEq]
      have all : RootsOk U pushed := by cases flag <;> first | exact baseRefs | exact push_refs rv baseRefs
      exact fun _ => all _
    have targetVals : ∀ i, isVal (envOf pack.1 pack.2 i) = true := by
      rw [← envEq]
      have all : ∀ i, isVal (pushed i) = true := by
        intro i; cases flag <;> first | exact values i | cases i <;> first | exact hv | exact values _
      exact fun _ => all _
    have nextGraph : Transition P hh (.eval v current (PrefixMap flag dest) none) hh (.at dest.label (envOf pack.1 pack.2)) := by
      rw [← envEq]
      cases flag <;> first | exact .effect hv | exact .bind hv
    obtain ⟨ticks,steps⟩ := post.2
    obtain ⟨t,upTo⟩ := chainExecution path (prefixEval node steps)
    obtain ⟨t',complete⟩ := chainExecution upTo (.next nextGraph .refl)
    have advance : Step hh (.frame E K v L d (PrefixMap flag dest) none comp) hh (gotoOf P dest.label pack.1 pack.2 comp) := by
      cases flag <;> first | exact .frameBind hv | exact .frameEffect hv
    have present := frame_refs (c := PrefixMap flag dest) (RefsOk_mono ext (RefsOk_trunc small (RefsOk_trunc le outer))) rv
    have edge : AdminPrefix U hh _ _ := .next present advance .refl
    apply edge.safe au ok
    intro b below
    exact ih complete (atTarget.transfer _ below _ (WExt_refl _)) (fun i => RefsOk_trunc below (targetRefs i))
      targetVals (stable below (WExt_refl _) (stable small ext (stable le (WExt_refl _) keep))) (WorldAdm_trunc below au) (heapAtLower below ok)

/-- Resume a checked straight-line edge after the call produces its result. -/
theorem resumeChecked {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {P Γ Δ A flag dest}
    (mapped : ∀ i B, Δ[i]?.join = some B →
      (prefixPush flag (some A) Γ)[PointClaims.slot dest.mapping i]?.join = some B)
    {n W h L d comp v T}
    (typed : PartialEnv G Γ (envOf L d) n W) (roots : RootsOk W (envOf L d))
    (values : ∀ i, isVal (envOf L d i) = true) (value : meaning G A n W v)
    (hv : isVal v = true) (rv : RefsOk W v) (world : WorldAdm W) (heap : HeapOk n W h)
    (outer : RefsOk W (gotoOf P dest.label L d comp))
    (next : ∀ {j U L' d'}, PartialEnv G Δ (envOf L' d') j U → RootsOk U (envOf L' d') →
      (∀ i, isVal (envOf L' d' i) = true) → WorldAdm U → HeapOk j U h →
      SafePostExc (excOf G) T (fun _ _ => True) (fun _ => True) j U h (gotoOf P dest.label L' d' comp)) :
    SafePostExc (excOf G) T (fun _ _ => True) (fun _ => True) n W h
      (.frame (P.map (·.expression)) (P.map fun nd => (nd.continuation,nd.handler)) v L d (PrefixMap flag dest) none comp) := by
  let pack := envMap dest.mapping (prefixPush flag v L) d
  have envEq : mapEnv dest.mapping (prefixPushEnv flag v (envOf L d)) = envOf pack.1 pack.2 := by
    rw [← mapEnv_envOf,← prefixPush_env]
  have pushed := pushed_partial typed value flag
  have target : PartialEnv G Δ (envOf pack.1 pack.2) n W := by
    rw [← envEq]
    exact ⟨fun i => pushed.1 _,fun i B hit => pushed.2 _ B (mapped i B hit)⟩
  have targetRefs : RootsOk W (envOf pack.1 pack.2) := by
    rw [← envEq]
    have all : RootsOk W (prefixPushEnv flag v (envOf L d)) := by
      cases flag <;> first | exact roots | exact push_refs rv roots
    exact fun _ => all _
  have targetVals : ∀ i, isVal (envOf pack.1 pack.2 i) = true := by
    rw [← envEq]
    have all : ∀ i, isVal (prefixPushEnv flag v (envOf L d) i) = true := by
      intro i; cases flag <;> first | exact values i | cases i <;> first | exact hv | exact values _
    exact fun _ => all _
  have advance : Step h
      (.frame (P.map (·.expression)) (P.map fun nd => (nd.continuation,nd.handler)) v L d (PrefixMap flag dest) none comp)
      h (gotoOf P dest.label pack.1 pack.2 comp) := by
    cases flag <;> first | exact .frameBind hv | exact .frameEffect hv
  have edge : AdminPrefix W h _ _ := .next (frame_refs outer rv) advance .refl
  apply edge.safe world heap
  intro j below
  exact next (target.transfer _ below _ (WExt_refl _)) (fun i => RefsOk_trunc below (targetRefs i))
    targetVals (WorldAdm_trunc below world) (heapAtLower below heap)

end Verification.SourceClaimJson.CallbackInterfaceCheck
