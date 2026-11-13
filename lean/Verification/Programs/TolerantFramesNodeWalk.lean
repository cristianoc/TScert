import Verification.Programs.TolerantFramesNodeEdges

/-! # Tolerant frames: every node of the pass delivers

`stepEdgesSound_of` composes, at every visited node, the step theorem
(`checkedStep_parts`) with the node's exits (`normalTarget_of_exits`, the
edge lemmas of `TolerantFramesNodeEdges`) into the typed per-node obligation
`StepEdgesSoundT`, which `run_sound_of_walk_typed` consumes. What the pass
accepted at a node enters as `NodeAccepted`: `SinglePass.run`'s driver is a
`while` loop no proof unfolds, so each value it computes at a node and each
check it passes there is a field, phrased by the pass's own functions
(`checkedStep`, `edgeStoreOf`, `edgeTransfer`, `headEntry`, `checkIn`). The
exits' fields are discharged from the edge checks by `exitDelivers_of_edge`,
`exitDelivers_head`, `handlerDelivers_of_edge` and `handlerDelivers_head`. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Exits
variable {ι : Type} [DecidableEq ι] [Hashable ι]

omit [DecidableEq ι] [Hashable ι] in
theorem envOk_tail {G : NormalGraph ι} {A : Ty ι} {Γ : List (Ty ι)} {v : Tm} {ρ : Env} {n : Nat} {W : WorldT n}
    (he : EnvOk G (A :: Γ) (push v ρ) n W) : EnvOk G Γ ρ n W :=
  ⟨fun i => by simpa [push] using he.1 (i + 1), fun i B hi => by simpa [push] using he.2 (i + 1) B (by simpa using hi)⟩

/-- **A normal exit into a node other than a loop head delivers**
(`ExitDelivers`), at every environment: the walk records the state
`edgeTransfer` builds (`hrec`); the mapped names are the mapping's
(`MapNamesSound`); the step's yields hold of its value on a pushed edge
(`hY`); a fresh result holds a fresh store (`hfo`); the edge's type check
gives the target's types (`htc`). -/
theorem exitDelivers_of_edge {G : NormalGraph ι} {w : Walk ι} {ctx : Nat → List (Ty ι)} {A : Ty ι}
    {Γ : List (Ty ι)} {entry : SinglePass.State} {store : Store} {result width : Nat} {pushed outFresh : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool} {t : Target}
    {I : List (PromiseCalls.Implication ι)} {ys : List (PromiseCalls.Yield ι)} {start : List Nat} 
    {m : Nat}
    (hpo : observed.isSome = true → pushed = true) (hpp : promote.isSome = true → pushed = false)
    (hmap : MapNamesSound (if pushed then result :: entry.names else entry.names) t.mapping)
    (hrec : (edgeTransfer (if pushed then result :: entry.names else entry.names) t.mapping pushed false outFresh
      entry result (edgeStoreOf G (if pushed then A :: Γ else Γ) entry.store store
        (if pushed then result :: entry.names else entry.names) (result :: entry.names) width pushed false observed
        promote) (I ++ freshImplOf pushed false ys entry.names result)) ∈ w.incoming t.label)
    (hY : ∀ ρ (s' : IndexedHeap) v, pushed = true → PromiseCalls.YieldsOk G ys ρ s'.n s'.W v)
    (hfo : ∀ v, pushed = true → outFresh = true → result ∉ entry.fresh → FreshAt m v)
    (htc : ∀ ρ (s' : IndexedHeap) v, EnvOk G (A :: Γ) (push v ρ) s'.n s'.W → ObservedOk observed promote v →
      EnvOk G (ctx t.label) (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) s'.n s'.W)
    (ρ : Env) :
    ExitDelivers (edgePreT G w start ε ctx) G A Γ (StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I start ε)
      ρ m t pushed observed promote := by
  intro s' v _ hF he ho
  refine normal_edge_delivers hF ho hpo hpp (fun hs => ?_) (hY ρ s' v) hmap (hfo v) hrec (htc ρ s' v he ho)
  rw [hpo hs]; simpa using he

/-- **A normal exit into a loop head delivers** (`ExitDelivers`): the walk
records the head's entry as the edge's state (`hrecHead`), the head's entry
being `headEntry` of its given facts (`hentry`); where the edge is not
vacuous (`V = false`), the pass's head query, implication, input and
promised-input checks hold (`hq`, `himp`, `hin`, `harg`); where it is, no
environment meets the edge's context (`hvac`). -/
theorem exitDelivers_head {G : NormalGraph ι} {w : Walk ι} {ctx : Nat → List (Ty ι)} {A : Ty ι}
    {Γ : List (Ty ι)} {entry : SinglePass.State} {store : Store} {result width : Nat} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool} {t : Target}
    {I : List (PromiseCalls.Implication ι)} {ys : List (PromiseCalls.Yield ι)} {startNames : List Nat} 
    {m : Nat} {req : HeapKnowledge.Knowledge} {gimp : List (PromiseCalls.Implication ι)} {argName : Option Nat}
    {argSlots : List Nat} {inputSlots : List (Nat × Nat)} {hwidth hfresh : Nat} {V : Bool}
    (hpo : observed.isSome = true → pushed = true) (hpp : promote.isSome = true → pushed = false)
    (hrecHead : (w.entry t.label, w.implies t.label) ∈ w.incoming t.label)
    (hentry : w.entry t.label =
        (SinglePass.headEntry req false hwidth hfresh startNames argName argSlots inputSlots gimp).1 ∧
      w.implies t.label =
        (SinglePass.headEntry req false hwidth hfresh startNames argName argSlots inputSlots gimp).2.1)
    (hnd : startNames.Nodup) (hlt : ∀ x ∈ startNames, x < hfresh)
    (hargs : ∀ a, argName = some a → ∃ q : Nat, startNames[q]? = some a)
    (hvac : V = true → ∀ (ρ : Env) (s' : IndexedHeap) v, EnvOk G (A :: Γ) (push v ρ) s'.n s'.W →
      ObservedOk observed promote v → False)
    (hq : V = false → KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (ctx t.label))
      (HeapKnowledge.withTypedLinks G (if pushed then A :: Γ else Γ)
        (ControlFlow.withTypedCells G (if pushed then A :: Γ else Γ) req t.mapping
          (materialize (⟨if pushed then result :: entry.names else entry.names,
              edgeStoreOf G (if pushed then A :: Γ else Γ) entry.store store
                (if pushed then result :: entry.names else entry.names) (result :: entry.names) width pushed false
                observed promote, []⟩ : SinglePass.State)
            (if pushed then width + 1 else width)
            (((atomsOf req).flatMap Atom.names).map (PointClaims.slot t.mapping)) true).1)) req t.mapping = true)
    (himp : V = false → ∀ x ∈ gimp, ∃ y ∈ I ++ freshImplOf pushed false ys entry.names result,
      (if pushed then result :: entry.names else entry.names)[PointClaims.slot t.mapping x.test]? = some y.test ∧
      (if pushed then result :: entry.names else entry.names)[PointClaims.slot t.mapping x.target]? = some y.target ∧
      ∀ n (W : WorldT n) v, meaning G y.type n W v → meaning G x.type n W v)
    (hin : V = false → ∀ p ∈ inputSlots,
      (if pushed then result :: entry.names else entry.names)[PointClaims.slot t.mapping p.1]? = startNames[p.2]?)
    (harg : V = false → ∀ j ∈ argSlots,
      (if pushed then result :: entry.names else entry.names)[PointClaims.slot t.mapping j]? = argName)
    (hY : ∀ ρ (s' : IndexedHeap) v, pushed = true → PromiseCalls.YieldsOk G ys ρ s'.n s'.W v)
    (htc : ∀ ρ (s' : IndexedHeap) v, EnvOk G (A :: Γ) (push v ρ) s'.n s'.W → ObservedOk observed promote v →
      EnvOk G (ctx t.label) (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) s'.n s'.W)
    (ρ : Env) :
    ExitDelivers (edgePreT G w startNames ε ctx) G A Γ
      (StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I startNames ε) ρ m t pushed observed promote := by
  intro s' v _ hF he ho
  cases hV : V with
  | true => exact (hvac hV ρ s' v he ho).elim
  | false =>
    have hS := edgeStore_normal (Γ := if pushed then A :: Γ else Γ) (width := width)
      (stateHolds_freshImpl (pushed := pushed) hF (hY ρ s' v)) ho hpo hpp (fun hs => by rw [hpo hs]; simpa using he)
    have heΓ : EnvOk G (if pushed then A :: Γ else Γ) (if pushed then push v ρ else ρ) s'.n s'.W := by
      cases pushed with
      | true => simpa using he
      | false => simpa using envOk_tail he
    have hest := headEstablishes_of_edge hS heΓ (htc ρ s' v he ho) (hq hV) (himp hV) (hin hV) (harg hV)
    refine ⟨⟨_, hrecHead, ?_⟩, htc ρ s' v he ho⟩
    rw [hentry.1, hentry.2]
    exact (headEntry_holds hnd hlt hargs hest).1

/-- **A handler exit into a node other than a loop head delivers**: from
the step's throw state, the thrown value at the name `x` above every name
(`hb`), at a type admitting every thrown value (`admitsAll`). -/
theorem handlerDelivers_of_edge {G : NormalGraph ι} {w : Walk ι} {ctx : Nat → List (Ty ι)}
    {Γ : List (Ty ι)} {thrownTy : Ty ι} {entry : SinglePass.State} {store : Store} {result width x : Nat}
    {outFresh : Bool} {t : Target} {I : List (PromiseCalls.Implication ι)} {ys : List (PromiseCalls.Yield ι)}
    {start : List Nat}  {m : Nat}
    (w' : StoreWF entry.store) (hb : NamesBelow entry I start x)
    (hmap : MapNamesSound (x :: entry.names) t.mapping)
    (hrec : (edgeTransfer (x :: entry.names) t.mapping true true outFresh entry result
      (edgeStoreOf G (thrownTy :: Γ) entry.store store (x :: entry.names) (result :: entry.names) width true true
        none none) (I ++ freshImplOf true true ys entry.names result)) ∈ w.incoming t.label)
    (htc : ∀ ρ (s' : IndexedHeap) e, EnvOk G (thrownTy :: Γ) (push e ρ) s'.n s'.W →
      EnvOk G (ctx t.label) (PointClaims.mapEnv t.mapping (push e ρ)) s'.n s'.W)
    (hadm : ControlFlow.admitsAll G thrownTy = true)
    (ρ : Env) (s' : IndexedHeap) (e : Tm)
    (hS : StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ I start ε ρ m s')
    (he : EnvOk G Γ ρ s'.n s'.W) (_hsc : Scoped 0 e) (hx : excOf G s'.n s'.W e) :
    edgePreT G w start ε ctx t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s' :=
  handler_edge_delivers hS w' hb hmap hrec (htc ρ s' e (he.push (ControlFlow.admitsAll_sound hadm hx)))

end Exits

/-! ## Every node of the pass -/

section Nodes
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **What the pass accepted at a visited node**: the values `SinglePass.run`
computes there and the checks it passes, by the pass's own functions. The
node `node` and its claim `c` (the label's context `ctx l`); the state the
step starts from (`entry`: the walk's entry with the node's stated assertion
joined, holding where the node's assertion does, `stated`); the accepted
step (`checkedStep`) with its premises (the store well-formed, the names below
the counter, the width, the incoming summary table checked); the claim's type
giving each value the shape its continuation needs (`shape`) and, at a
return, the result type (`ret`); each normal exit delivering at every
environment (`exits`, by `exitDelivers_of_edge` or `exitDelivers_head`);
the handler delivering from the throw state (`handler`, by
`handlerDelivers_of_edge`). -/
structure NodeAccepted (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (suggestions : List (Sequent ι)) (index : KnownIndex ι) (codes : CodeEntry ι → Bool) (aliases : List (ι × ι))
    (pc : PassChecker G images) (undefTy : Option (Ty ι)) (P : ControlFlow.Program) (w : Walk ι)
    (startNames : List Nat) (ε : HeapKnowledge.EntryState) (ctx : Nat → List (Ty ι)) (Tres : Fam) (m : Nat) (l : Nat) where
  node : Node
  hP : P[l]? = some node
  c : PointClaim ι
  hctx : ctx l = c.context
  entry : SinglePass.State
  stated : ∀ ρ (s : IndexedHeap), passPreT G w startNames ε ctx l ρ m s →
    StateHolds G entry (w.implies l) startNames ε ρ m s
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
  shape : ∀ n (W : WorldT n) v, meaning G c.type n W v → ShapeOk v node.continuation
  ret : node.continuation = .ret → ∀ n (W : WorldT n) v, meaning G c.type n W v → Tres n W v
  exits : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node → ∀ ρ,
    ExitDelivers (edgePreT G w startNames ε ctx) G c.type c.context
      (StateHolds G ⟨st.result :: entry.names, st.store, entry.fresh⟩ (w.implies l) startNames ε) ρ m t pushed
      observed promote
  handler : ∀ t, node.handler = some t → ∀ ρ (s' : IndexedHeap) e,
    StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ (w.implies l) startNames ε ρ m s' →
    EnvOk G c.context ρ s'.n s'.W → Scoped 0 e → excOf G s'.n s'.W e →
    edgePreT G w startNames ε ctx t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s'

/-- **Every node of the pass delivers** (`StepEdgesSoundT`): where the pass
accepted every visited node (`NodeAccepted`), the codes are sound and the
direct call and the search keep the summary table checked, each visited
node's step and exits meet the typed node obligations, with the exception
family `excOf G` and no post on the heap at the graph's exits. -/
theorem stepEdgesSound_of {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool}
    {aliases : List (ι × ι)} {pc : PassChecker G images} {undefTy : Option (Ty ι)} {P : ControlFlow.Program}
    {w : Walk ι} {startNames : List Nat} {ctx : Nat → List (Ty ι)} {Tres : Fam} {m : Nat}
    (hacc : ∀ l, w.visited l →
      Nonempty (NodeAccepted G images pool fuel suggestions index codes aliases pc undefTy P w startNames ε ctx Tres m l))
    (hcodes : CodesSound G codes) (hdir : DirectKeepsSummaries G images undefTy)
    (hsrch : SearchKeepsSummaries G images pool fuel suggestions index codes aliases pc.checker) :
    StepEdgesSoundT P G w startNames ε ctx (excOf G) Tres (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp
  obtain ⟨na⟩ := hacc l hp.1.1
  have hS := na.stated ρ s hp
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  obtain ⟨-, -, -, cn, ce, hparts⟩ :=
    checkedStep_parts na.hstep hS na.wf na.below na.width he hcodes na.sums hdir hsrch
  obtain ⟨hj, ho⟩ := nodeObligations_of_parts (pre := edgePreT G w startNames ε ctx) (Ξres := excOf G)
    (Tres := Tres) (Qres := fun _ => True) (Rres := fun _ => True) (x := na.node.handler) hparts he
    (fun j U v hv => na.shape (j + 1) U v hv)
    (fun s' v _ hv hF he' _ => normalTarget_of_exits (fun t p o q hm => na.exits t p o q hm ρ) na.ret
      (fun _ => trivial) s' v hv hF he' (na.shape _ _ v (he'.2 0 _ rfl)))
    (fun s' e _ hFe he' hsc hx => by
      cases hh : na.node.handler with
      | none => exact ⟨hx, trivial⟩
      | some t => exact na.handler t hh ρ s' e hFe he' hsc hx)
  exact ⟨na.node, na.hP, _, _, cn, ce, _, _, hj, ho⟩

end Nodes

/-! ## The names after a step -/

section Below
variable {ι : Type}

/-- **The step keeps the names below the counter**: where the entry's names,
start names and implications are below the counter `fresh` and the result
is an entry name with the counter kept or the counter with the counter
advanced (`checkedStep_parts`), the state after the step is below the next
counter, given its store's facts are (`hstore`, the delta's names). -/
theorem namesBelow_step {entry : SinglePass.State} {store : Store} {I : List (PromiseCalls.Implication ι)}
    {start : List Nat} {fresh result next : Nat} (hnb : NamesBelow entry I start fresh)
    (hres : (result ∈ entry.names ∧ next = fresh) ∨ (result = fresh ∧ next = fresh + 1))
    (hstore : ∀ a ∈ storeAll store, ∀ x ∈ a.names, x < next) :
    NamesBelow ⟨result :: entry.names, store, entry.fresh⟩ I start next := by
  have hle : fresh ≤ next := by rcases hres with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  obtain ⟨h1, -, h3, h4, h5⟩ := namesBelow_mono hle hnb
  refine ⟨fun x hx => ?_, hstore, h3, h4, h5⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · rcases hres with ⟨hm, -⟩ | ⟨rfl, rfl⟩
    · exact h1 _ hm
    · omega
  · exact h1 x hx

/-- **The step keeps the names no wider than the context**: the pushed
names at the pushed context. -/
theorem width_step {names : List Nat} {result : Nat} {A : Ty ι} {Γ : List (Ty ι)}
    (h : names.length ≤ Γ.length) : (result :: names).length ≤ (A :: Γ).length := by
  simp only [List.length_cons]; omega

end Below

end Verification.TolerantFrames
