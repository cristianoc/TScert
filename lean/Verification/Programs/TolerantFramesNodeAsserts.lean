import Verification.Programs.TolerantFramesNodeAsserted
import Verification.Programs.TolerantFramesGuarantee
import Verification.Programs.TolerantFramesEntry
import Verification.Programs.TolerantFramesNodeEdges

/-! # Tolerant frames: the written assertions in the node assertion

`AssertionsHeld` reads each written assertion from the node's entry state
(`passPreT`), which does not entail every written fact (Leg 14b: a written
assertion on its edges and in the entry state). The node assertion here
states the written assertion itself (`passPreA`: `passPreT` and
`AssertsAt`, over the table `run` reads, `stated`), and every edge into a
label establishes it: on an edge into a node other than a loop head the
edge's assertion check (`assertsAt_of_edge`, by `assertion_query_sound`),
on an edge into a loop head the head query, whose given facts are the
written assertion with the claims' index facts (`assertsAt_of_head`), at
the start the entry check (`assertsAt_start`). The walk's theorems at the
typed assertion carry over (`nodesChecked_of_walkA`, `asserted_of_walkA`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Asserts
variable {ι : Type}

/-- The written assertion `stated l` holds at the environment and heap. -/
def AssertsAt (stated : Nat → Option HeapKnowledge.Knowledge) (l : Nat) (ρ : Env) (s : IndexedHeap) : Prop :=
  ∀ req, stated l = some req → HeapKnowledge.Holds req ρ s.h

/-- **The node assertion stating the written assertion**: `passPreT` and
the label's written assertion holding. -/
def passPreA (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι))
    (stated : Nat → Option HeapKnowledge.Knowledge) : Nat → Assertion :=
  fun l ρ m s => passPreT G w startNames ρ0 ctx l ρ m s ∧ AssertsAt stated l ρ s

/-- **The edge assertion stating the target's written assertion**:
`edgePreT` and the target's written assertion holding. -/
def edgePreA (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι))
    (stated : Nat → Option HeapKnowledge.Knowledge) : Nat → Assertion :=
  fun t ρ m s => edgePreT G w startNames ρ0 ctx t ρ m s ∧ AssertsAt stated t ρ s

theorem passPreA_adminClosed {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {m : Nat} :
    AdminClosed (passPreA G w startNames ρ0 ctx stated) m :=
  fun l ρ s s' ha hh ⟨hp, hA⟩ => ⟨passPreT_adminClosed l ρ s s' ha hh hp, fun req hr => hh ▸ hA req hr⟩

/-- **Each visited node's step and edges deliver, stating the written
assertions**: `StepEdgesSoundT` with the targets' `edgePreA`. -/
def StepEdgesSoundA (P : ControlFlow.Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge) (Ξres Tres : Fam)
    (Qres Rres : Heap → Prop) (m : Nat) : Prop :=
  ∀ l ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s → ∃ node, P[l]? = some node ∧
    ∃ (Ξ T : Fam) (cn ce : Footprints.Closed) (Qn : Post) (Qe : Heap → Prop),
      SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
        s.n s.W s.h (instantiate 0 ρ node.expression) ∧
      NodeObligations (edgePreA G w startNames ρ0 ctx stated) Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s
        node.continuation node.handler

variable [DecidableEq ι] [Hashable ι] in
/-- **The walk checks every node at the assertion stating the written
assertions**: `nodesChecked_of_walk` with `StepEdgesSoundA`; the written
assertion an edge state establishes is the target's. -/
theorem nodesChecked_of_walkA {P : ControlFlow.Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {Ξres Tres : Fam} {ρ0 : Env} {m : Nat} {stated : Nat → Option HeapKnowledge.Knowledge}
    (hT : Traversed G w startNames given ctx edgesIn fresh)
    (hstep : StepEdgesSoundA P G w startNames ρ0 ctx stated Ξres Tres (fun _ => True) (fun _ => True) m)
    (hheads : HeadsEntered G w startNames ρ0 given m) (hmerges : MergesSound G w given ctx edgesIn) :
    NodesChecked P (passPreA G w startNames ρ0 ctx stated) Ξres Tres (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp
  obtain ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hsafe, ho⟩ := hstep l ρ s hp.1
  exact ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hsafe,
    nodeObligations_mono (fun t ρ s h => ⟨⟨entries_of_traversed hT hheads hmerges t ρ s h.1.1, h.1.2⟩, h.2⟩) ho⟩

/-- **`asserted` from the walk at the assertion stating the written
assertions**: the written assertion holds at every node entry at its
label a run from the start reaches with budget left. -/
theorem asserted_of_walkA {P : ControlFlow.Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ρ0 : Env} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {Ξres Tres : Fam}
    {m : Nat} (hnodes : NodesChecked P (passPreA G w startNames ρ0 ctx stated) Ξres Tres (fun _ => True)
      (fun _ => True) m)
    {start : Nat} {ρ : Env} {s : IndexedHeap} (hpre : passPreA G w startNames ρ0 ctx stated start ρ m s)
    {l : Nat} {req : HeapKnowledge.Knowledge} (hl : stated l = some req) {j : Nat} {h' : Heap} {ρ' : Env}
    (hrun : Transitions P j s.h (.at start ρ) h' (.at l ρ')) (hj : j < s.n) : HeapKnowledge.Holds req ρ' h' := by
  obtain ⟨s', he, hp'⟩ := reached_pre hnodes passPreA_adminClosed hpre hrun hj
  exact he ▸ hp'.2 req hl

/-- **The stated table holds every assertion** where `run` reads the
request's assertions by label (`byLabel`) and no label is stated twice:
then `AssertsAt` at every label gives `AssertionsHeld`'s statement. -/
theorem holds_of_assertsAt {assertions : List (Nat × HeapKnowledge.Knowledge)}
    {stated : Nat → Option HeapKnowledge.Knowledge} (hst : ∀ l k, (l, k) ∈ assertions → stated l = some k)
    {l : Nat} {k : HeapKnowledge.Knowledge} (hl : (l, k) ∈ assertions) {ρ : Env} {s : IndexedHeap}
    (hA : AssertsAt stated l ρ s) : HeapKnowledge.Holds k ρ s.h :=
  hA k (hst l k hl)

/-! ## Each edge establishes the target's written assertion -/

/-- A knowledge's facts hold where those of the knowledge with more index
facts hold. -/
theorem holds_of_indices_append {k : HeapKnowledge.Knowledge} {xs : List HeapKnowledge.IndexAtom} {ρ : Env}
    {h : Heap} (hk : HeapKnowledge.Holds { k with indices := k.indices ++ xs } ρ h) : HeapKnowledge.Holds k ρ h :=
  ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha => hk.2.2.2.2.2 a (List.mem_append_left _ ha)⟩

variable [DecidableEq ι] [Hashable ι]

omit [Hashable ι] in
/-- **An edge into a node other than a loop head establishes its written
assertion** (`SinglePass.run`, "A target's assertion established on the
edge"): where the edge is not vacuous, the check over the edge's
materialized facts `k` (`assertionSource`) accepts the target's written
assertion `req`; the facts hold at the edge's environment `ρe`, which the
edge's context `Γe` types, the observation holds of slot 0 and the target's
context types the mapped environment. -/
theorem assertsAt_of_edge {G : NormalGraph ι} {Γe Δ : List (Ty ι)} {k : HeapKnowledge.Knowledge}
    {θ : PointClaims.Mapping} {observed : Option BranchRefinement.Observation}
    {stated : Nat → Option HeapKnowledge.Knowledge} {t : Nat} {ρe : Env} {s : IndexedHeap}
    (hq : ∀ req, stated t = some req →
      KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G Δ) (assertionSource G Γe req k θ observed) req θ = true)
    (hk : HeapKnowledge.Holds k ρe s.h) (he : EnvOk G Γe ρe s.n s.W)
    (ho : ∀ o, observed = some o → o.holds (ρe 0)) (htc : EnvOk G Δ (PointClaims.mapEnv θ ρe) s.n s.W) :
    AssertsAt stated t (PointClaims.mapEnv θ ρe) s := by
  intro req hr
  obtain ⟨n, W, h, pos, adm, ok⟩ := s
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ n => exact assertion_query_sound (hq req hr) hk he ok ho htc

omit [DecidableEq ι] [Hashable ι] in
/-- **An edge into a loop head establishes its written assertion**: the
head's given facts are the written assertion with the claims' index facts
(`SinglePass.run`, `given`), and the edge establishes them
(`HeadEstablishes.facts`, from `headEstablishes_of_edge`). -/
theorem assertsAt_of_head {G : NormalGraph ι} {stated : Nat → Option HeapKnowledge.Knowledge} {t : Nat}
    {written : HeapKnowledge.Knowledge} {cf : List HeapKnowledge.IndexAtom}
    {gimp : List (PromiseCalls.Implication ι)} {startNames : List Nat} {argName : Option Nat}
    {argSlots : List Nat} {inputSlots : List (Nat × Nat)} {ρ0 ρ' : Env} {s : IndexedHeap}
    (hw : (stated t).getD {} = written)
    (hest : HeadEstablishes G { written with indices := written.indices ++ cf } gimp startNames argName argSlots
      inputSlots ρ0 ρ' s) :
    AssertsAt stated t ρ' s := by
  intro req hr
  rw [hr] at hw
  subst hw
  exact holds_of_indices_append hest.facts

omit [Hashable ι] in
/-- **The start's written assertion holds at an entry meeting the inputs**:
the entry check (`entryRefusal`) accepting, its entailment of the written
and supplied facts (`entryRefusal_ok`, `entryKnows_sound`). -/
theorem assertsAt_start {G : NormalGraph ι} {inputs : List (Ty ι)} {claims : List (PointClaim ι)} {start : Nat}
    {goal : ControlFlow.Goal ι} {stated : Nat → Option HeapKnowledge.Knowledge}
    {supplied : List HeapKnowledge.IndexAtom} {givenImplies : List (PromiseCalls.Implication ι)}
    {givenArgs : List Nat} {givenInputs : List (Nat × Nat)} {entryIndices : List HeapKnowledge.IndexAtom}
    {entrySeparation : HeapSeparation.Separation}
    (hacc : SinglePass.entryRefusal G inputs claims start goal (stated start) supplied givenImplies givenArgs
      givenInputs entryIndices entrySeparation = none)
    {ρ : Env} {s : IndexedHeap} (he : EnvOk G inputs ρ s.n s.W) (hs : HeapSeparation.Holds entrySeparation ρ)
    (hi : HeapKnowledge.IndexHolds entryIndices ρ s.h) : AssertsAt stated start ρ s := by
  intro req hr
  have hk := ControlFlow.entryKnows_sound (entryRefusal_ok hacc).2.2.2.2.2 he hs hi
  rw [hr] at hk
  exact holds_of_indices_append hk

omit [DecidableEq ι] [Hashable ι] in
/-- **A normal exit delivers the target's written assertion with its
state**: `ExitDelivers` at `edgePreT` and the written assertion at every
exit's target environment give `ExitDelivers` at `edgePreA`. -/
theorem exitDeliversA_of {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} {A : Ty ι} {Γ : List (Ty ι)}
    {Fn : Assertion} {ρ : Env} {m : Nat} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    (hd : ExitDelivers (edgePreT G w startNames ρ0 ctx) G A Γ Fn ρ m t pushed observed promote)
    (hA : ∀ (s' : IndexedHeap) v, isVal v = true → Fn (push v ρ) m s' → EnvOk G (A :: Γ) (push v ρ) s'.n s'.W →
      ObservedOk observed promote v →
      AssertsAt stated t.label (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) s') :
    ExitDelivers (edgePreA G w startNames ρ0 ctx stated) G A Γ Fn ρ m t pushed observed promote :=
  fun s' v hv hF he ho => ⟨hd s' v hv hF he ho, hA s' v hv hF he ho⟩

/-- **The edge's materialized facts hold where the step's state does**: the
facts `run` materializes for the assertion check, over the edge's store
(`edgeStore_normal`, `stateHolds_materialize`). -/
theorem edgeFacts_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {entry : SinglePass.State} {store : Store}
    {result width : Nat} {v : Tm} {ρ : Env} {pushed : Bool} {observed : Option BranchRefinement.Observation}
    {promote : Option Bool} {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E : Env} {m : Nat}
    {s : IndexedHeap} {slots : List Nat}
    (hS : StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I start E (push v ρ) m s)
    (hobs : ObservedOk observed promote v)
    (hpo : observed.isSome = true → pushed = true) (hpp : promote.isSome = true → pushed = false)
    (he : observed.isSome = true → EnvOk G Γ (push v ρ) s.n s.W) :
    HeapKnowledge.Holds (materialize (⟨if pushed then result :: entry.names else entry.names,
        edgeStoreOf G Γ entry.store store (if pushed then result :: entry.names else entry.names)
          (result :: entry.names) width pushed false observed promote, []⟩ : SinglePass.State)
      (if pushed then width + 1 else width) slots false).1 (if pushed then push v ρ else ρ) s.h := by
  have hE := stateHolds_edge (edgeStore_normal (Γ := Γ) (width := width) hS hobs hpo hpp he)
  exact stateHolds_materialize hE _ _ true

end Asserts

end Verification.TolerantFrames
