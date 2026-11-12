import Verification.Programs.TolerantFramesGuarantee
import Verification.Programs.TolerantFramesNodeWalk

/-! # Tolerant frames: the values the footprint check reads at a node

The pass checks each node under a bound (`SinglePass.run`, the footprint
bound at a node): inside the no-return region `dead`, `GraphCode.deadNode`
and no throw bound; outside it, `SinglePass.footprintCheck` at the fresh
receiver slots, the step's derivation and the handler's liveness. This
module restates `run`'s local bindings there (`passRecvFresh`,
`passDerivOf`, `passLiveHandler`, `passCallFresh`, `passDeadEvidence`) and
proves what the state gives of them: the fresh receiver slots hold fresh
stores (`freshOk_recv`), a copy of a fresh slot returns a fresh store
(`copyFresh`). `TolerantFramesNodeCallFresh` composes them into
`FootprintKept`. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Values
variable {ι : Type}

/-- The step's derivation as `run` reads it at the footprint check. -/
def passDerivOf (c : PointClaim ι) (node : Node) (st : Stepped ι) : ProgramCertificates.Evidence ι :=
  st.stepDeriv.getD (.node ⟨c.context, node.expression, c.type⟩ .var [])

/-- A call's result fresh, as `run`'s `outFresh` reads it off the derivation's
selected effect. -/
def passCallFresh (node : Node) (deriv : ProgramCertificates.Evidence ι) : Bool :=
  (match ExpressionEffects.selectedEffect deriv with | some eff => eff.fresh | none => false) &&
    ExpressionEffects.selectedOperands deriv && (ProgramCertificates.claim deriv).term == node.expression

/-- The fresh receiver slots of the step (`run`'s `F` at the footprint
check): the receiver's slot where it holds a fresh name. -/
def passRecvFresh (node : Node) (entry : SinglePass.State) : List Nat :=
  match PromiseCalls.receiverSlot node.expression with
  | some i => if (entry.names[i]?).any entry.fresh.contains then [i] else []
  | none => []

/-- Whether the node's handler is outside the no-return region. -/
def passLiveHandler (dead : List Bool) (node : Node) : Bool :=
  match node.handler with
  | some t => !GraphCode.deadAt dead t.label
  | none => false

/-- The evidence `run` passes `GraphCode.deadNode` at a node of `dead`. -/
def passDeadEvidence (c : PointClaim ι) (node : Node) : NodeEvidence ι :=
  ⟨none, some ⟨c.context, node.expression, c.type⟩, [], {}, none, {}, none, [], [], [], none⟩

theorem passDeadEvidence_result (c : PointClaim ι) (node : Node) :
    ControlFlow.result (passDeadEvidence c node) = c.type := rfl

theorem option_any_some {α : Type} {o : Option α} {f : α → Bool} (h : o.any f = true) :
    ∃ x, o = some x ∧ f x = true := by
  cases o with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

/-- `run` reads the region as an array (`deadArr.getD l false`); the
guarantee as the list (`GraphCode.deadAt`). -/
theorem deadAt_toList (a : Array Bool) (l : Nat) : GraphCode.deadAt a.toList l = a.getD l false := by
  simp [GraphCode.deadAt, Array.getD, List.getD]
  split <;> simp_all

end Values

section Bound
variable {ι : Type}

/-- **The fresh receiver slots hold fresh stores**: a slot `passRecvFresh`
lists holds a fresh name of the entry state, whose value the state gives a
store allocated at or past the mark. -/
theorem freshOk_recv {G : NormalGraph ι} {node : Node} {entry : SinglePass.State}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G entry I start E ρ m s) : GraphCode.FreshOk (passRecvFresh node entry) m ρ := by
  obtain ⟨η, hn, -, -, hF, -⟩ := hS
  intro i hi
  simp only [passRecvFresh] at hi
  split at hi
  · split at hi
    · rename_i hany
      obtain rfl : i = _ := List.mem_singleton.mp hi
      obtain ⟨x, hx, hc⟩ := option_any_some hany
      rw [hn _ x hx]
      exact hF x (by simpa using hc)
    · cases hi
  · cases hi

/-- **A copy of a fresh slot returns a fresh store**: where the term is a
slot holding a fresh name, every run of it to a value returns that slot's
value, whose store the state gives fresh at the mark. -/
theorem copyFresh {G : NormalGraph ι} {node : Node} {entry : SinglePass.State}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    {Γ : List (Ty ι)} (hS : StateHolds G entry I start E ρ m s) (he : EnvOk G Γ ρ s.n s.W)
    (hwidth : entry.names.length ≤ Γ.length)
    (hc : (match node.expression with
      | .var i => (entry.names[i]?).any entry.fresh.contains
      | _ => false) = true) {k : Nat} {h' : Heap} {v : Tm}
    (hst : Steps k s.h (instantiate 0 ρ node.expression) h' v) : FreshAt m v := by
  obtain ⟨η, hn, -, -, hF, -⟩ := hS
  split at hc
  · rename_i i hi
    obtain ⟨x, hx, hm⟩ := option_any_some hc
    have hval : instantiate 0 ρ node.expression = ρ i := by rw [hi]; simp [instantiate]
    rw [hval] at hst
    have hi' : i < Γ.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hx).1 hwidth
    obtain ⟨A, hA⟩ : ∃ A, Γ[i]? = some A := ⟨_, List.getElem?_eq_getElem hi'⟩
    have hv : isVal (ρ i) = true := (meaning_value (he.2 i A hA)).1
    rw [PromiseCalls.steps_value hv hst, hn _ x hx]
    exact hF x (by simpa using hm)
  · cases hc

/-- A continuation's obligation where every successor meets `X` at every
environment and a return meets `Q`. -/
theorem contKeeps_of {X : Nat → Env → Heap → Prop} {Q : Heap → Tm → Prop} {ρ : Env} {v : Tm} {h : Heap}
    {k : Continuation} (hs : ∀ t ∈ CertificateProducer.successors k, ∀ ρ', X t.label ρ' h) (hr : k = .ret → Q h v) :
    ContKeeps X Q ρ v h k := by
  cases k with
  | ret => exact hr rfl
  | bind t => exact hs t (by simp [CertificateProducer.successors]) _
  | effect t => exact hs t (by simp [CertificateProducer.successors]) _
  | branch y n =>
    exact ⟨fun _ => hs y (by simp [CertificateProducer.successors]) _,
      fun _ => hs n (by simp [CertificateProducer.successors]) _⟩
  | branchBind y n =>
    exact ⟨fun _ => hs y (by simp [CertificateProducer.successors]) _,
      fun _ => hs n (by simp [CertificateProducer.successors]) _⟩
  | tagBind tag y n =>
    simp only [ContKeeps]
    split
    · exact hs y (by simp [CertificateProducer.successors]) _
    · exact hs n (by simp [CertificateProducer.successors]) _

end Bound

end Verification.TolerantFrames
