import Verification.Programs.TolerantFramesGuarantee
import Verification.Programs.TolerantFramesNodeWalk

/-! # Tolerant frames: the footprint check kept along a run

`FootprintKept` (`TolerantFramesGuarantee`) asks, at every node entry where
the pass's typed assertion holds and the node is in the no-return region
`dead` or the heap is within `Φ` from the invocation's entry `h₀`, that every
run of the node's term with budget left reaches an exit meeting the same
property at its target, a return within `Φ` (its value fresh where the bound
states a fresh result) and an escaping throw within `Φ` where the bound
covers throws.

The pass checks each node under a bound (`SinglePass.run`, the footprint
bound at a node): inside `dead`, `GraphCode.deadNode` and no throw bound;
outside it, `SinglePass.footprintCheck` at the fresh receiver slots, the
step's derivation and the handler's liveness. `BoundChecked` is that check,
over the values `run` computes there (`passRecvFresh`, `passDerivOf`,
`passLiveHandler`, `passOutFresh`, `passDeadEvidence`, which restate `run`'s
local bindings). `footprintKept_of` composes the per-node footprint theorem
(`footprint_exits`) with the step theorem (`checkedStep_parts`) into
`FootprintKept`; the fresh receiver slots' stores (`FreshOk`) are the
state's fresh names (`freshOk_recv`). -/
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

/-- Whether the result holds a fresh store (`run`'s `outFresh`): a copy of a
slot holding a fresh name, or a call stating a fresh result. -/
def passOutFresh (node : Node) (entry : SinglePass.State) (deriv : ProgramCertificates.Evidence ι) : Bool :=
  (match node.expression with
    | .var i => (entry.names[i]?).any entry.fresh.contains
    | _ => false) || passCallFresh node deriv

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
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **The footprint bound's check at a node** (`run`, "The footprint bound at
this node", under `bound = some (Φ, ret, exc)` and the region `dead`): inside
the region, `deadNode` with no throw bound; outside it, `footprintCheck` at
the step's values. -/
def BoundChecked {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool} {aliases : List (ι × ι)}
    {pc : PassChecker G images} {undefTy : Option (Ty ι)} {P : ControlFlow.Program} {w : Walk ι}
    {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {Tres : Fam} {m : Nat} {l : Nat}
    (na : NodeAccepted G images pool fuel suggestions index codes aliases pc undefTy P w startNames ρ0 ctx Tres m l)
    (Φ : Footprints.Closed) (dead : List Bool) (ret exc : Bool) : Prop :=
  (GraphCode.deadAt dead l = true →
    GraphCode.deadNode G dead na.node (passDeadEvidence na.c na.node) = true ∧ exc = false) ∧
  (GraphCode.deadAt dead l = false →
    footprintCheck G images codes na.ans.summaries.toList Φ (passRecvFresh na.node na.entry) na.c na.node
      na.st.stepK (passDerivOf na.c na.node na.st) (passLiveHandler dead na.node) exc ret
      (passOutFresh na.node na.entry (passDerivOf na.c na.node na.st)) = true)

/-- **(Named hypothesis) A call's fresh result within the budget**: where
`run`'s `outFresh` reads a fresh result off the step's derivation's selected
effect (`passCallFresh`), from a state where the node assertion holds,
every run of the node's term with fewer steps than the state's budget to a
value returns a store allocated at or past the mark (`callFresh_of_checked`
gives it from the derivation's check). -/
def CallFreshBelow (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (ctx : Nat → List (Ty ι)) (m l : Nat) (node : Node) (deriv : ProgramCertificates.Evidence ι) : Prop :=
  passCallFresh node deriv = true → ∀ ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s →
    ∀ k h' v, k < s.n → Steps k s.h (instantiate 0 ρ node.expression) h' v → isVal v = true → FreshAt m v

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
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

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
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

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
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

/-- **The footprint check keeps the bound at every node** (`FootprintKept`):
where the pass accepted every visited node (`NodeAccepted`, at the mark
`|h₀|`), checked its bound there (`BoundChecked`, with `ret` the bound's
fresh result and `exc` its throw bound) and a call's fresh result holds a
fresh store (`CallFreshBelow`), the codes are sound and the direct call and the
search keep the summary table checked, every node keeps `BoundX`: a run of a
node outside `dead` from a heap within `Φ` stays within it on each exit
(`footprint_exits`, its fresh receivers from the state, `freshOk_recv`), a
return's value fresh where `ret` (`passOutFresh`: a copy of a fresh slot,
`copyFresh`, or a fresh call, `CallFreshBelow`); a run of a node of `dead`
reaches a target of `dead` or no normal exit (`deadNode`: an empty result
type, or a continuation into `dead`), and a throw a handler of `dead`, or
escapes with no throw bound. -/
theorem footprintKept_of {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool}
    {aliases : List (ι × ι)} {pc : PassChecker G images} {undefTy : Option (Ty ι)} {P : ControlFlow.Program}
    {w : Walk ι} {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)} {Tres : Fam}
    {Φ : Footprints.Closed} {h₀ : Heap} {dead : List Bool} {ret exc : Bool}
    (hacc : ∀ l, w.visited l → ∃ na : NodeAccepted G images pool fuel suggestions index codes aliases pc undefTy P w
      startNames ρ0 ctx Tres h₀.length l, BoundChecked na Φ dead ret exc ∧
        CallFreshBelow G w startNames ρ0 ctx h₀.length l na.node (passDerivOf na.c na.node na.st))
    (hcodes : CodesSound G codes) (hdir : DirectKeepsSummaries G images undefTy)
    (hsrch : SearchKeepsSummaries G images pool fuel suggestions index codes aliases pc.checker) :
    FootprintKept P G w startNames ρ0 ctx Φ h₀ dead ret exc := by
  intro l ρ s hp hX
  obtain ⟨na, hb, hcf⟩ := hacc l hp.1.1
  have hS := na.stated ρ s hp
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.2
  obtain ⟨hsums', hkS, -, cn, ce, hj, hn, hx⟩ :=
    checkedStep_parts na.hstep hS na.wf na.below na.width he hcodes na.sums hdir hsrch
  have hex := (stepExits_of hj hn hx).2
  refine ⟨na.node, na.hP, fun k h' t' hst hk => ?_⟩
  cases hd : GraphCode.deadAt dead l with
  | true =>
    obtain ⟨hdn, hexc⟩ := hb.1 hd
    simp only [GraphCode.deadNode, passDeadEvidence_result, Bool.and_eq_true, Bool.or_eq_true] at hdn
    refine ⟨fun hv => ?_, fun e hr => ?_⟩
    · obtain ⟨s', -, -, -, hT, -⟩ := (hex k h' t' hst hk).1 hv
      rcases hdn.1 with hempty | hcont
      · exact (ExpressionEffects.emptyType_sound hempty hT).elim
      · simp only [GraphCode.deadContinuation, Bool.and_eq_true, List.all_eq_true] at hcont
        exact contKeeps_of (fun t ht _ => .inl (hcont.2 t ht))
          (fun hk' => by rw [hk'] at hcont; simp at hcont)
    · cases hh : na.node.handler with
      | none => intro hexc'; rw [hexc] at hexc'; cases hexc'
      | some t =>
        have := hdn.2
        simp only [GraphCode.deadHandler, hh] at this
        exact .inl this
  | false =>
    have hΦ : Φ.Holds h₀ s.h := hX.resolve_left (by simp [hd])
    have hfc := hb.2 hd
    have hsafe : Safe (excOf G) (meaning G na.c.type) s.n s.W s.h (instantiate 0 ρ na.node.expression) :=
      HeapObservations.erase hj.post
    obtain ⟨hN, hT⟩ := footprint_exits hfc hcodes hsums' (freshOk_recv hS) he hkS hsafe hΦ hst hk
    obtain ⟨-, -, hret, -⟩ := footprintCheck_sound hfc
    refine ⟨fun hv => contKeeps_of (fun _ _ _ => .inr (hN hv)) fun hk' => ⟨hN hv, fun hr => ?_⟩,
      fun e hr => ?_⟩
    · have hof := hret hk' hr
      simp only [passOutFresh, Bool.or_eq_true] at hof
      rcases hof with hc | hc
      · exact copyFresh hS he na.width hc hst
      · exact hcf hc ρ s hp k h' t' hk hst hv
    · cases hh : na.node.handler with
      | none =>
        intro hexc
        exact hT (by simp [hexc]) e hr
      | some t =>
        simp only [HandlerKeeps, BoundX]
        cases hdt : GraphCode.deadAt dead t.label with
        | true => exact .inl rfl
        | false => exact .inr (hT (by simp [passLiveHandler, hh, hdt]) e hr)

end Bound

end Verification.TolerantFrames
