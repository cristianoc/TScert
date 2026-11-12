import Verification.Programs.TolerantFramesNodeSound

/-! # Tolerant frames: a node's exits into their targets

What each exit of a node delivers at its target, from the state after the
step (`checkedStep_parts`) and the pass's checks on the edge (`SinglePass.run`,
the edge loop): an edge into a node other than a loop head, the state
`edgeTransfer` builds (`edge_normal_sound`, `edge_handler_sound`) with the
implications the edge carries; an edge into a loop head, the head's given
facts, implications, inputs and promised input (`HeadEstablishes`), from the
head query (`head_query_sound`) and the edge's checks of the implications,
inputs and promised input; a branch, the target its value selects. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Edges
variable {ι : Type}

/-- The implications an edge carries beyond the entry's (`SinglePass.lean`,
`freshImpl` in the edge loop): on a pushed edge other than a handler's, each
conditional yield's implication of the result. -/
def freshImplOf (pushed isHandler : Bool) (ys : List (PromiseCalls.Yield ι)) (entryNames : List Nat)
    (result : Nat) : List (PromiseCalls.Implication ι) :=
  if !pushed || isHandler then [] else
    ys.filterMap fun y => if y.conditional && !y.onFalse then
      (entryNames[y.target]?).map fun tgt => ⟨result, tgt, y.type⟩ else none

theorem freshImplOf_handler (pushed : Bool) (ys : List (PromiseCalls.Yield ι)) (entryNames : List Nat)
    (result : Nat) : freshImplOf pushed true ys entryNames result = [] := by
  simp [freshImplOf]

/-- **The state after a step carries the edge's implications**: where the
step's yields hold of its value on a pushed edge (`YieldsOk`). -/
theorem stateHolds_freshImpl [DecidableEq ι] {G : NormalGraph ι} {entry : SinglePass.State} {store : Store}
    {result : Nat} {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {v : Tm} {m : Nat}
    {s : IndexedHeap} {pushed : Bool} {ys : List (PromiseCalls.Yield ι)}
    (hS : StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I start E (push v ρ) m s)
    (hY : pushed = true → PromiseCalls.YieldsOk G ys ρ s.n s.W v) :
    StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ (I ++ freshImplOf pushed false ys entry.names result)
      start E (push v ρ) m s := by
  refine stateHolds_addImplies hS fun η hn => ?_
  cases pushed with
  | false => simp [freshImplOf, PromiseCalls.ImpliesOk]
  | true => simpa [freshImplOf] using freshImpl_ok (hY rfl) hn

/-- **A normal edge's store holds** at the edge's environment: the step's
state with the observation's or the promoted truthiness's facts. -/
theorem edgeStore_normal [DecidableEq ι] [Hashable ι] {G : NormalGraph ι} {Γ : List (Ty ι)}
    {entry : SinglePass.State} {store : Store} {result width : Nat} {v : Tm} {ρ : Env}
    {pushed : Bool} {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I start E (push v ρ) m s)
    (hobs : ObservedOk observed promote v)
    (hpo : observed.isSome = true → pushed = true) (hpp : promote.isSome = true → pushed = false)
    (he : observed.isSome = true → EnvOk G Γ (push v ρ) s.n s.W) :
    StateHolds G ⟨if pushed then result :: entry.names else entry.names,
      edgeStoreOf G Γ entry.store store (if pushed then result :: entry.names else entry.names)
        (result :: entry.names) width pushed false observed promote, entry.fresh⟩ I start E
      (if pushed then push v ρ else ρ) m s := by
  cases pushed with
  | true =>
    simp only [if_true, edgeStoreOf, Bool.false_eq_true, if_false]
    cases observed with
    | some o => exact edgeStore_observed _ hS (he rfl) hobs
    | none =>
      cases promote with
      | some q => cases hpp rfl
      | none => exact hS
  | false =>
    simp only [Bool.false_eq_true, if_false, edgeStoreOf]
    cases observed with
    | some o => cases hpo rfl
    | none =>
      cases promote with
      | some q => exact stateHolds_tail (edgeStore_promote _ hS hobs)
      | none => exact stateHolds_tail hS

/-- **An edge into a node other than a loop head delivers its recorded
state**: where the walk records the state and implications `edgeTransfer`
builds from the edge's store and the edge's implications (`freshImplOf`)
among the target's incoming states, the target's typed edge assertion holds
at the target's environment, its types given by the edge's type check
(`htc`). -/
theorem normal_edge_delivers [DecidableEq ι] [Hashable ι] {G : NormalGraph ι} {w : Walk ι} {ctx : Nat → List (Ty ι)}
    {Γ : List (Ty ι)} {entry : SinglePass.State} {store : Store} {result width : Nat} {v : Tm} {ρ : Env}
    {pushed outFresh : Bool} {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    {t : Target} {I : List (PromiseCalls.Implication ι)} {ys : List (PromiseCalls.Yield ι)} {start : List Nat}
    {E : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I start E (push v ρ) m s)
    (hobs : ObservedOk observed promote v)
    (hpo : observed.isSome = true → pushed = true) (hpp : promote.isSome = true → pushed = false)
    (he : observed.isSome = true → EnvOk G Γ (push v ρ) s.n s.W)
    (hY : pushed = true → PromiseCalls.YieldsOk G ys ρ s.n s.W v)
    (hmap : MapNamesSound (if pushed then result :: entry.names else entry.names) t.mapping)
    (hfo : pushed = true → outFresh = true → result ∉ entry.fresh → FreshAt m v)
    (hrec : (edgeTransfer (if pushed then result :: entry.names else entry.names) t.mapping pushed false outFresh
      entry result (edgeStoreOf G Γ entry.store store (if pushed then result :: entry.names else entry.names)
        (result :: entry.names) width pushed false observed promote)
      (I ++ freshImplOf pushed false ys entry.names result)) ∈ w.incoming t.label)
    (htc : EnvOk G (ctx t.label) (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) s.n s.W) :
    edgePreT G w start E ctx t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) m s :=
  ⟨⟨_, hrec, edge_normal_sound (stateHolds_freshImpl hS hY) hobs hpo hpp he hmap hfo⟩, htc⟩

/-- **A handler edge into a node other than a loop head delivers its
recorded state**: the thrown value at the name `x` above every name. -/
theorem handler_edge_delivers [DecidableEq ι] [Hashable ι] {G : NormalGraph ι} {w : Walk ι}
    {ctx : Nat → List (Ty ι)} {Γ : List (Ty ι)} {entry : SinglePass.State} {store : Store} {result width x : Nat}
    {e : Tm} {ρ : Env} {outFresh : Bool} {t : Target} {I : List (PromiseCalls.Implication ι)}
    {ys : List (PromiseCalls.Yield ι)} {start : List Nat} {E : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ I start E ρ m s)
    (w' : StoreWF entry.store) (hb : NamesBelow entry I start x) (hmap : MapNamesSound (x :: entry.names) t.mapping)
    (hrec : (edgeTransfer (x :: entry.names) t.mapping true true outFresh entry result
      (edgeStoreOf G Γ entry.store store (x :: entry.names) (result :: entry.names) width true true none none)
      (I ++ freshImplOf true true ys entry.names result)) ∈ w.incoming t.label)
    (htc : EnvOk G (ctx t.label) (PointClaims.mapEnv t.mapping (push e ρ)) s.n s.W) :
    edgePreT G w start E ctx t.label (PointClaims.mapEnv t.mapping (push e ρ)) m s := by
  rw [freshImplOf_handler, List.append_nil] at hrec
  exact ⟨⟨_, hrec, edge_handler_sound hS w' hb hmap⟩, htc⟩

/-- The edge's store state, its fresh names left out, at the materialization
the pass reads (`{ names, store := edgeStore }`). -/
theorem stateHolds_edge {G : NormalGraph ι} {names : List Nat} {S : Store} {F : List Nat}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G ⟨names, S, F⟩ I start E ρ m s) : StateHolds G { names, store := S } I start E ρ m s :=
  stateHolds_noFresh hS

/-- **An edge into a loop head establishes the head's entry**
(`HeadEstablishes`), from the pass's checks on the edge (`SinglePass.run`,
the edge loop into a statement entry): the head query over the edge's facts
(`checkIn`, `head_query_sound`); each given implication held by an
implication the edge carries whose test and target are the names of the
mapped slots, at a type within the given one (the type check `same` or
`subtypeUsing`, read through its soundness); each given input's and the
promised input's slot named by the start name it states. The edge's state
holds at the source environment `ρx` (the step's state, or its edge store),
typed by the edge's context `Γe`; the head's types hold at the mapped
environment (`htc`). -/
theorem headEstablishes_of_edge [DecidableEq ι] {G : NormalGraph ι} {Γe tc : List (Ty ι)} {names : List Nat}
    {edgeStore : Store} {F : List Nat} {I : List (PromiseCalls.Implication ι)} {startNames : List Nat}
    {ρ0 ρx : Env} {m : Nat} {s : IndexedHeap} {θ : PointClaims.Mapping} {req : HeapKnowledge.Knowledge}
    {gimp : List (PromiseCalls.Implication ι)} {argName : Option Nat} {argSlots : List Nat}
    {inputSlots : List (Nat × Nat)} {d : Nat}
    (hS : StateHolds G ⟨names, edgeStore, F⟩ I startNames ρ0 ρx m s)
    (he : EnvOk G Γe ρx s.n s.W) (htc : EnvOk G tc (PointClaims.mapEnv θ ρx) s.n s.W)
    (hq : KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc)
      (HeapKnowledge.withTypedLinks G Γe (ControlFlow.withTypedCells G Γe req θ
        (materialize { names, store := edgeStore } d (((atomsOf req).flatMap Atom.names).map
          (PointClaims.slot θ)) true).1)) req θ = true)
    (himp : ∀ x ∈ gimp, ∃ y ∈ I, names[PointClaims.slot θ x.test]? = some y.test ∧
      names[PointClaims.slot θ x.target]? = some y.target ∧
      ∀ n (W : WorldT n) v, meaning G y.type n W v → meaning G x.type n W v)
    (hin : ∀ p ∈ inputSlots, names[PointClaims.slot θ p.1]? = startNames[p.2]?)
    (harg : ∀ j ∈ argSlots, names[PointClaims.slot θ j]? = argName) :
    HeadEstablishes G req gimp startNames argName argSlots inputSlots ρ0 (PointClaims.mapEnv θ ρx) s := by
  have hk := stateHolds_materialize_whole (stateHolds_edge hS) d
    (((atomsOf req).flatMap Atom.names).map (PointClaims.slot θ)) true
  obtain ⟨η, hn, -, hI, -, hst⟩ := hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨n, W, h, pos, adm, ok⟩ := s
    cases n with
    | zero => exact absurd pos (Nat.lt_irrefl 0)
    | succ n => exact (head_query_sound hq hk he ok htc).1
  · intro x hx ht
    obtain ⟨y, hy, h1, h2, hle⟩ := himp x hx
    have e1 : PointClaims.mapEnv θ ρx x.test = η y.test := hn _ _ h1
    have e2 : PointClaims.mapEnv θ ρx x.target = η y.target := hn _ _ h2
    rw [e2]; rw [e1] at ht
    exact hle _ _ _ (hI y hy ht)
  · intro j q x hp hq
    have h1 := hin (j, q) hp
    rw [hq] at h1
    exact (hn _ _ h1).trans (hst q x hq)
  · intro j a q hj ha hq
    have h1 := harg j hj
    rw [ha] at h1
    exact (hn _ _ h1).trans (hst q a hq)

/-! ## A node's normal exits -/

/-- **What a normal exit delivers**: from the state `Fn` after the step at the
pushed environment, its types and what the exit observes of the value, the
target's assertion at its environment. -/
def ExitDelivers (pre : Nat → Assertion) (G : NormalGraph ι) (A : Ty ι) (Γ : List (Ty ι)) (Fn : Assertion)
    (ρ : Env) (m : Nat) (t : Target) (pushed : Bool) (observed : Option BranchRefinement.Observation)
    (promote : Option Bool) : Prop :=
  ∀ (s' : IndexedHeap) v, isVal v = true → Fn (push v ρ) m s' → EnvOk G (A :: Γ) (push v ρ) s'.n s'.W →
    ObservedOk observed promote v → pre t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) m s'

/-- **A continuation's normal target from its exits**: where every normal
exit of the node (`Exit.ofNode`) delivers, and a branch's value is a
Boolean, a value's normal target holds at a `bind`, `effect` or `branch`
continuation; at a return, where the claim's type gives the result type. -/
theorem normalTarget_of_exits {pre : Nat → Assertion} {G : NormalGraph ι} {A : Ty ι} {Γ : List (Ty ι)}
    {Fn : Assertion} {ρ : Env} {m : Nat} {node : Node} {Tres : Fam} {Qres : Heap → Prop}
    (hex : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node →
      ExitDelivers pre G A Γ Fn ρ m t pushed observed promote)
    (hret : node.continuation = .ret → ∀ n (W : WorldT n) v, meaning G A n W v → Tres n W v)
    (hQ : ∀ h, Qres h)
    (s' : IndexedHeap) (v : Tm) (hv : isVal v = true) (hF : Fn (push v ρ) m s')
    (he : EnvOk G (A :: Γ) (push v ρ) s'.n s'.W) (hshape : ShapeOk v node.continuation) :
    NormalTarget pre Tres Qres ρ m s' v node.continuation := by
  have mem : ∀ t pushed observed promote, Exit.normal t pushed observed promote ∈ Exit.ofNode node →
      ObservedOk observed promote v →
      pre t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) m s' :=
    fun t p o q hm ho => hex t p o q hm s' v hv hF he ho
  unfold Exit.ofNode at mem
  match hk : node.continuation, hshape with
  | .ret, _ => exact ⟨hret hk _ _ v (he.2 0 A rfl), hQ _⟩
  | .bind t, _ =>
    rw [hk] at mem
    have := mem t true none none (by simp) trivial
    simp only [if_true] at this
    exact this
  | .effect t, _ =>
    rw [hk] at mem
    have := mem t false none none (by simp) trivial
    simp only [Bool.false_eq_true, if_false] at this
    exact this
  | .branch y n, hs =>
    rw [hk] at mem
    rcases hs with rfl | rfl
    · exact .inl ⟨rfl, by simpa using mem y false none (some true) (by simp) rfl⟩
    · exact .inr ⟨rfl, by simpa using mem n false none (some false) (by simp) rfl⟩
  | .branchBind .., hs => exact hs.elim
  | .tagBind .., hs => exact hs.elim

end Edges

end Verification.TolerantFrames
