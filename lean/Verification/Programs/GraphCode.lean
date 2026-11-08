import Verification.Programs.Parametricity
import Verification.Programs.ExpressionEffects

/-! # Graph code: a closure whose body is a checked graph

A closure's code may be a control-flow graph (`CallCode.graph`), the body form
a module function has. Invoking it starts a run of that graph at its entry
(`Tm.goto`), which the term machine executes node by node (`Tm.frame`), with
the graph machine's transitions as its steps. This file proves that the two
machines agree: a run of graph code simulates `ControlFlow.Transition`
step for step, so the graph checker's safety theorem (`accepted_inputs_safe`)
is safety of the term that runs the code. -/
namespace Verification.GraphCode
open ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)
open CertificateProducer (successors)

/-- The graph a code's node lists describe. -/
def program (E : List Tm) (K : List (Continuation × Option Target)) : Program :=
  (E.zip K).map fun (e, k, x) => ⟨e, k, x⟩

theorem program_node {E : List Tm} {K : List (Continuation × Option Target)} {l : Nat}
    {node : Node} (h : (program E K)[l]? = some node) :
    E[l]? = some node.expression ∧ K[l]? = some (node.continuation, node.handler) := by
  simp only [program, List.getElem?_map] at h
  obtain ⟨⟨e, k, x⟩, hz, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.getElem?_zip_eq_some.mp hz
  exact ⟨this.1, this.2⟩

theorem push_envOf (v : Tm) (L : List Tm) (d : Tm) : push v (envOf L d) = envOf (v :: L) d := by
  funext i; cases i <;> rfl

theorem mapEnv_envOf (m : Option (List Nat)) (L : List Tm) (d : Tm) :
    mapEnv m (envOf L d) = envOf (envMap m L d).1 (envMap m L d).2 := by
  funext i
  cases m with
  | none => rfl
  | some slots =>
    simp only [mapEnv, slot, envOf, envMap]
    by_cases hi : i < slots.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    · have hn : slots[i]? = none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hn]

/-- A term that runs graph code, and the graph machine's state it stands for. -/
inductive Sim (E : List Tm) (K : List (Continuation × Option Target)) : Tm → State → Prop where
  | goto : Sim E K (.goto E K l L d) (.at l (envOf L d))
  | frame : Sim E K (.frame E K t L d k x) (.eval t (envOf L d) k x)
  | done : isVal v = true → Sim E K v (.done v)
  | raised : isVal v = true → isSourceVal v = true → Sim E K (.throw v) (.raised v)

theorem sim_goto {E K l m L d} :
    Sim E K (.goto E K l (envMap m L d).1 (envMap m L d).2) (.at l (mapEnv m (envOf L d))) := by
  rw [mapEnv_envOf]; exact .goto

/-- Each transition of the graph is one step of the term that runs it. -/
theorem sim_step {E K ts s h h' s'} (hs : Sim E K ts s)
    (step : Transition (program E K) h s h' s') : ∃ ts', Step h ts h' ts' ∧ Sim E K ts' s' := by
  cases hs with
  | goto =>
    cases step with
    | enter hn =>
      obtain ⟨he, hk⟩ := program_node hn
      exact ⟨_, .gotoEnter he hk, .frame⟩
  | frame =>
    cases step with
    | expr st => exact ⟨_, .frameC st, .frame⟩
    | ret hv => exact ⟨_, .frameRet hv, .done hv⟩
    | bind hv =>
      refine ⟨_, .frameBind hv, ?_⟩
      rw [push_envOf]; exact sim_goto
    | effect hv => exact ⟨_, .frameEffect hv, sim_goto⟩
    | yes => exact ⟨_, .frameYes, sim_goto⟩
    | no => exact ⟨_, .frameNo, sim_goto⟩
    | yesBind =>
      refine ⟨_, .frameYesBind, ?_⟩
      rw [push_envOf]; exact sim_goto
    | noBind =>
      refine ⟨_, .frameNoBind, ?_⟩
      rw [push_envOf]; exact sim_goto
    | tagBind hv =>
      refine ⟨_, .frameTag hv, ?_⟩
      rw [push_envOf]; exact sim_goto
    | handle hr =>
      refine ⟨_, .frameHandle hr, ?_⟩
      rw [push_envOf]; exact sim_goto
    | raise hr => exact ⟨_, .frameRaise hr, .raised (raises_val hr) (raises_sourceVal hr)⟩
  | done hv => cases step
  | raised _ _ => cases step

/-- **The term running graph code is as safe as the graph.** -/
theorem safe_of_sim {E K T} : ∀ (n : Nat) (W : WorldT n) (h : Heap) {ts s},
    Sim E K ts s → SafeGraph Ξ (program E K) T n W h s → Safe Ξ T n W h ts := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ts s hs hg
    rcases hg with (⟨v, rfl, hv, hT⟩ | ⟨v, rfl, hsc⟩) | ⟨U, h', s', hx, hu, step, hh, hg⟩
    · cases hs; exact Or.inl (Or.inl ⟨hv, hT⟩)
    · cases hs with
      | raised hv hj => exact Or.inl (Or.inr ⟨v, .throwV hv hj, hsc⟩)
    · obtain ⟨ts', st, hs'⟩ := sim_step hs step
      exact Or.inr ⟨U, h', ts', hx, hu, st, hh, ih U h' hs' hg⟩

/-- A graph run started at an entry the checker accepted is safe. -/
theorem goto_safe {G : NormalGraph ι} [DecidableEq ι] {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)} {Rty : Goal ι}
    {E K C start inputs} {codes : CodeEntry ι → Bool} {entrySeparation : HeapSeparation.Separation}
    {entryIndices : List HeapKnowledge.IndexAtom}
    (hc : checkEntryUsing (sums := sums) (entrySeparation := entrySeparation) (entryIndices := entryIndices)
      G images Rty (program E K) C start inputs codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (n W h L d) (he : EnvOk G inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W h)
    (hsep : HeapSeparation.Holds entrySeparation (envOf L d) := by exact HeapSeparation.empty_holds _)
    (hidx : HeapKnowledge.IndexHolds entryIndices (envOf L d) h := by exact HeapKnowledge.indexHolds_nil _ _) :
    Safe (excOf G) (GoalHolds G Rty (Rty.argument (envOf L d))) n W h (.goto E K start L d) :=
  safe_of_sim n W h .goto (accepted_inputs_safe hc n W h (envOf L d) he hw hh hcodes hsums hsep hidx)

/-- A normal-return postcondition up to the current budget, independent of the
world chosen by a parallel safety derivation. Throws impose no postcondition. -/
def ReturnsPost (Q : HeapObservations.Post) (n : Nat) (h : Heap) (t : Tm) : Prop :=
  ∀ k h' v, k < n → HeapObservations.Steps k h t h' v → isVal v = true → Q h' v

theorem returnsPost_of_safePost {T Q} : ∀ {n W h t},
    HeapObservations.SafePost Ξ T Q n W h t → ReturnsPost Q n h t := by
  intro n
  induction n with
  | zero => intro W h t hs k h' v hk; omega
  | succ n ih =>
    intro W h t hs k h' v hk run hv
    cases run with
    | refl =>
      rcases hs with (⟨_, _, hq⟩ | hr) | ⟨_, _, _, _, _, st, _, _⟩
      · exact hq
      · exact absurd hr (val_not_thrown hv)
      · exact False.elim (value_no_step hv st)
    | next st run =>
      rcases hs with (⟨ht, _, _⟩ | hr) | ⟨U, h'', t'', _, _, st', _, hs'⟩
      · exact False.elim (value_no_step ht st)
      · exact absurd st hr.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st st'
        exact ih hs' _ _ _ (by omega) run hv

theorem ReturnsPost.step {Q n h t h' t'} (hp : ReturnsPost Q (n+1) h t)
    (st : Step h t h' t') : ReturnsPost Q n h' t' := by
  intro k h'' v hk run hv
  exact hp (k+1) h'' v (by omega) (.next st run) hv

theorem ReturnsPost.value {Q n h v} (hp : ReturnsPost Q (n+1) h v)
    (hv : isVal v = true) : Q h v := hp 0 h v (by omega) .refl hv

/-- A postcondition of the heap a run raises in, up to the current budget,
independent of the world a parallel safety derivation chose. -/
def RaisesPost (R : Heap → Prop) (n : Nat) (h : Heap) (t : Tm) : Prop :=
  ∀ k h' t' v, k < n → HeapObservations.Steps k h t h' t' → Raises t' v → R h'

theorem raisesPost_of_safePostExc {T Q R} : ∀ {n W h t},
    HeapObservations.SafePostExc Ξ T Q R n W h t → RaisesPost R n h t := by
  intro n
  induction n with
  | zero => intro W h t hs k h' t' v hk; omega
  | succ n ih =>
    intro W h t hs k h' t' v hk run hr
    cases run with
    | refl =>
      rcases hs with (⟨hv, _, _⟩ | ⟨_, hR⟩) | ⟨_, _, _, _, _, st, _, _⟩
      · rw [raises_not_val hr] at hv; contradiction
      · exact hR
      · exact absurd st (raises_no_step hr)
    | next st run =>
      rcases hs with (⟨ht, _, _⟩ | ⟨hth, _⟩) | ⟨U, h'', t'', _, _, st', _, hs'⟩
      · exact False.elim (value_no_step ht st)
      · exact absurd st hth.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st st'
        exact ih hs' _ h' t' v (by omega) run hr

theorem RaisesPost.step {R n h t h' t'} (hp : RaisesPost R (n+1) h t)
    (st : Step h t h' t') : RaisesPost R n h' t' := by
  intro k h'' t'' v hk run hr
  exact hp (k+1) h'' t'' v (by omega) (.next st run) hr

theorem RaisesPost.raised {R n h t v} (hp : RaisesPost R (n+1) h t) (hr : Raises t v) : R h :=
  hp 0 h t v (by omega) .refl hr

/-! ## Fresh stores along a graph

A run within a footprint may change a store beyond it where that store was
allocated during the run: the old locations are those below where the run
started, and a store allocated later is none of them. A node's facts name the
slots of its entry whose values have such a store; each edge carries them,
and a node's value adds to them where it is fresh. The facts read no heap:
an object's fields are fixed at its allocation. -/

open Footprints (FreshAt)

/-- The values at the slots `F` have an array store allocated at or after `b`. -/
def FreshOk (F : List Nat) (b : Nat) (ρ : Env) : Prop := ∀ i ∈ F, FreshAt b (ρ i)

/-- A label's facts: none past the list. -/
def factsAt (facts : List (List Nat)) (l : Nat) : List Nat := facts.getD l []

/-- Labels in a region from which no normal return is possible. Missing
labels are outside the region. Membership is checked at every node. -/
def deadAt (dead : List Bool) (l : Nat) : Bool := dead.getD l false

def deadContinuation (dead : List Bool) (k : Continuation) : Bool :=
  k != .ret && (successors k).all fun t => deadAt dead t.label

def deadHandler (dead : List Bool) (x : Option Target) : Bool :=
  match x with
  | none => true
  | some t => deadAt dead t.label

@[nospecialize] def deadNode (G : NormalGraph ι) (dead : List Bool)
    (node : Node) (c : NodeEvidence ι) : Bool :=
  (ExpressionEffects.emptyType G (result c) || deadContinuation dead node.continuation) &&
    deadHandler dead node.handler

/-- One refinement step after another, each reading the region by label in
constant time, until a step changes nothing or the fuel runs out. -/
def deadIterate (nodes : Array (Node × Bool)) : Nat → Array Bool → Array Bool
  | 0, dead => dead
  | fuel + 1, dead =>
    let at_ := fun (l : Nat) => dead.getD l false
    let next := nodes.map fun (node, empty) =>
      (empty || (node.continuation != .ret && (successors node.continuation).all fun t => at_ t.label)) &&
        (match node.handler with | none => true | some t => at_ t.label)
    if next = dead then dead else deadIterate nodes fuel next

/-- Candidate region, refined by removing nodes whose normal or exceptional
successor may return. The independent node check validates the result. -/
@[nospecialize] def inferDead (G : NormalGraph ι) (P : Program) (C : Certificate ι) (exc : Bool) : List Bool :=
  if exc then [] else
  let nodes := ((P.zip C).map fun (node, c) => (node, ExpressionEffects.emptyType G (result c))).toArray
  (deadIterate nodes (P.length + 1) (Array.replicate P.length true)).toList

/-- Whether a continuation binds the value it receives at slot 0 of its
destinations. -/
def pushes : Continuation → Bool
  | .bind _ | .branchBind _ _ | .tagBind _ _ _ => true
  | _ => false

/-- Whether slot `j` of a destination's environment, before its slot map, is
fresh: the bound value where the continuation binds it and it is fresh, a
source slot otherwise. -/
def freshSlot (F : List Nat) (pushed out : Bool) : Nat → Bool
  | 0 => if pushed then out else F.contains 0
  | j + 1 => if pushed then F.contains j else F.contains (j + 1)

/-- The destinations' facts follow from the source's and from the node's
value, fresh where `out`; and a return under a fresh-result goal returns a
fresh value. -/
def edgesFresh (facts : List (List Nat)) (F : List Nat) (out ret : Bool) (k : Continuation) : Bool :=
  (successors k).all (fun t => (factsAt facts t.label).all fun i =>
    freshSlot F (pushes k) out (slot t.mapping i)) &&
    (k != .ret || !ret || out)

/-- What an edge check establishes of the value a node returns. -/
def TargetsFresh (facts : List (List Nat)) (b : Nat) (ret : Bool) (ρ : Env) (v : Tm) (k : Continuation) : Prop :=
  (∀ t ∈ successors k, FreshOk (factsAt facts t.label) b
    (mapEnv t.mapping (if pushes k then push v ρ else ρ))) ∧
    (k = .ret → ret = true → FreshAt b v)

theorem edgesFresh_sound {facts : List (List Nat)} {F : List Nat} {out ret : Bool} {k : Continuation}
    {b : Nat} {ρ : Env} {v : Tm} (he : edgesFresh facts F out ret k = true)
    (hF : FreshOk F b ρ) (hout : out = true → FreshAt b v) : TargetsFresh facts b ret ρ v k := by
  simp only [edgesFresh, Bool.and_eq_true, List.all_eq_true] at he
  refine ⟨fun t ht i hi => ?_, fun hk hr => ?_⟩
  · have hs := he.1 t ht i hi
    simp only [mapEnv]
    generalize slot t.mapping i = j at hs ⊢
    cases hp : pushes k
    · simp only [hp, Bool.false_eq_true, if_false] at hs ⊢
      cases j with
      | zero => exact hF 0 (by simpa [freshSlot] using hs)
      | succ j => exact hF (j + 1) (by simpa [freshSlot] using hs)
    · simp only [hp, if_true] at hs ⊢
      cases j with
      | zero => exact hout (by simpa [freshSlot] using hs)
      | succ j => exact hF j (by simpa [freshSlot] using hs)
  · subst hk
    simp [hr] at he
    exact hout he.2

/-- A slot copy of a fresh slot. -/
def varFresh (F : List Nat) : Tm → Bool
  | .var j => F.contains j
  | _ => false

/-- A call at a selected signature stating a fresh result. -/
def callFresh [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι)) (c : NodeEvidence ι) (t : Tm) : Bool :=
  (match ExpressionEffects.selectedEffect c.expression with
    | some eff => eff.fresh
    | none => false) &&
    ExpressionEffects.selectedOperands c.expression &&
    decide ((ProgramCertificates.claim c.expression).term = t) &&
    ProgramCertificates.checkTreeUsing G images c.expression (sums := sums)

/-- A call whose receiver is a slot holding a fresh store. -/
def receiverFresh (F : List Nat) : Tm → Bool
  | .invoke _ (.var j) _ => F.contains j
  | _ => false

theorem receiverFresh_sound {F : List Nat} {b : Nat} {ρ : Env} {t : Tm}
    (hr : receiverFresh F t = true) (hF : FreshOk F b ρ) :
    FreshAt b (ExpressionEffects.receiverOf (instantiate 0 ρ t)) := by
  cases t <;> simp [receiverFresh] at hr
  rename_i f r args
  cases r <;> simp at hr
  rename_i i
  simpa [ExpressionEffects.receiverOf, instantiate] using hF i hr

/-- A selected call within the bound: its footprint within it, and its
receiver's store, where the signature excepts it, fresh or the bound letting
everything change. -/
def selectedWithinAt (Φ : Footprints.Closed) (F : List Nat) (e : ProgramCertificates.Evidence ι) : Bool :=
  ExpressionEffects.selectedOperands e && match ExpressionEffects.selectedEffect e with
    | some eff => eff.footprint.le Φ && (if eff.receiverOwn then eff.ownChange.le Φ else
        (!eff.receiverStore || Φ == .top || receiverFresh F (ProgramCertificates.claim e).term))
    | none => false

/-- A node's run is within a closed bound `Φ` on the locations below `b`, on
normal return, from the heap it starts in, where the slots `F` hold stores
allocated at or after `b`; and its value has such a store where `out`. Where
`thr`, the heap a throw leaves is within the bound too. The precondition is
the same point context and knowledge that ordinary graph checking
established. -/
def NodeWithin [DecidableEq ι] (G : NormalGraph ι) (Φ : Footprints.Closed) (c : NodeEvidence ι) (t : Tm)
    (F : List Nat) (out thr : Bool) : Prop :=
  ∀ n W h ρ (b : Nat), b ≤ h.length → FreshOk F b ρ →
    EnvOk G (entry c) ρ n W → PromiseCalls.ImpliesOk G c.implies ρ n W → HeapKnowledge.Holds (entryFacts G c) ρ h →
    WorldAdm W → HeapOk n W h →
    HeapObservations.SafePostExc (excOf G) (meaning G (result c))
      (fun h' v => Φ.HoldsOn (· < b) h h' ∧ (out = true → FreshAt b v))
      (fun h' => thr = true → Φ.HoldsOn (· < b) h h') n W h (instantiate 0 ρ t)

/-- A handler's facts follow from the node's: the thrown value, bound at
slot 0, is never fresh, and each other slot keeps the freshness of the source
slot it maps. -/
def handlerFresh (facts : List (List Nat)) (F : List Nat) (l : Target) : Bool :=
  (factsAt facts l.label).all fun i => match slot l.mapping i with
    | 0 => false
    | j + 1 => F.contains j

theorem handlerFresh_sound {facts : List (List Nat)} {F : List Nat} {l : Target} {b : Nat} {ρ : Env}
    (hf : handlerFresh facts F l = true) (hF : FreshOk F b ρ) (u : Tm) :
    FreshOk (factsAt facts l.label) b (mapEnv l.mapping (push u ρ)) := by
  intro i hi
  have hs := List.all_eq_true.mp hf i hi
  simp only [mapEnv]
  generalize slot l.mapping i = j at hs ⊢
  cases j with
  | zero => cases hs
  | succ j => exact hF j (by simpa using hs)

/-- While a node runs, the invocation need not be within its bound yet. Only
the node's normal return, within the bound on the locations below where the
invocation started, extends the invocation's run within it
(`Closed.Holds.trans_on`), and establishes its destinations' facts. A throw
a handler outside the checked no-return region catches is within the bound
too, and establishes the handler's facts; a throw leaving the invocation is within it where `exc`. -/
def BoundState (Φ : Footprints.Closed) (facts : List (List Nat)) (dead : List Bool)
    (ret exc : Bool) (initial : Heap) (n : Nat) (h : Heap) : State → Prop
  | .at l ρ => deadAt dead l = true ∨
      (Φ.Holds initial h ∧ FreshOk (factsAt facts l) initial.length ρ)
  | .done v => Φ.Holds initial h ∧ (ret = true → FreshAt initial.length v)
  | .eval t ρ k handler =>
      ReturnsPost (fun h' v => deadContinuation dead k = true ∨
        (Φ.Holds initial h' ∧ TargetsFresh facts initial.length ret ρ v k)) n h t ∧
      match handler with
      | none => exc = true → RaisesPost (Φ.Holds initial) n h t
      | some l => deadAt dead l.label = true ∨
          (RaisesPost (Φ.Holds initial) n h t ∧
          ∀ u, FreshOk (factsAt facts l.label) initial.length (mapEnv l.mapping (push u ρ)))
  | .raised _ => exc = true → Φ.Holds initial h

/-- A node no environment reaches: a slot of its entry has a type no value
meets. -/
def unreachableEntry (G : NormalGraph ι) (c : NodeEvidence ι) : Bool :=
  (entry c).any fun A => ExpressionEffects.emptyType G A

theorem unreachableEntry_sound {G : NormalGraph ι} {c : NodeEvidence ι} {ρ n W}
    (hu : unreachableEntry G c = true) (he : EnvOk G (entry c) ρ n W) : False := by
  obtain ⟨A, hA, hnil⟩ := List.any_eq_true.mp hu
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hA
  exact ExpressionEffects.emptyType_sound hnil (he.2 i A hi)

/-- What the bounded run reads of each node: none for a node no environment
reaches; inside the no-return region, checked closure under every exit and
an empty normal result at a return continuation; outside it, the node within
the bound and freshness transferred along normal edges and handlers outside
the region. Exceptional guarantees admit no region exemption. -/
def NodesWithin [DecidableEq ι] (G : NormalGraph ι) (Φ : Footprints.Closed) (P : Program) (C : Certificate ι)
    (facts : List (List Nat)) (dead : List Bool) (ret exc : Bool) : Prop :=
  ∀ (l : Nat) (node : Node) (c : NodeEvidence ι), P[l]? = some node → C[l]? = some c →
    unreachableEntry G c = true ∨
    ((deadAt dead l = true → deadNode G dead node c = true ∧ exc = false) ∧
     (deadAt dead l = false →
      (∀ t, node.handler = some t → deadAt dead t.label = true ∨ handlerFresh facts (factsAt facts l) t = true) ∧
      ∃ out, NodeWithin G Φ c node.expression (factsAt facts l) out
        ((!deadHandler dead node.handler) || exc) ∧
        edgesFresh facts (factsAt facts l) out ret node.continuation = true))

theorem bounded_step [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {Rty : Goal ι} {v0 : Tm} {P : Program}
    {C : Certificate ι} {facts : List (List Nat)} {dead : List Bool} {ret exc : Bool} {codes}
    (hg : checkGraphUsing (sums := sums) G images Rty P C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (hnodes : NodesWithin G Φ P C facts dead ret exc)
    {initial n W h s h' s'} (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hs : StateOk G Rty C v0 (n+1) W h s) (hp : BoundState Φ facts dead ret exc initial (n+1) h s)
    (st : Transition P h s h' s') : BoundState Φ facts dead ret exc initial n h' s' := by
  cases st with
  | @enter l node _ ρ hn =>
    obtain ⟨c, hc, he, hi, -, hf⟩ := hs
    rcases hnodes _ _ c hn hc with hu | ⟨hdead, hlive⟩
    · exact (unreachableEntry_sound hu he).elim
    cases hd : deadAt dead l with
    | true =>
      obtain ⟨hdn, hexc⟩ := hdead hd
      simp only [deadNode, Bool.and_eq_true, Bool.or_eq_true] at hdn
      refine ⟨?_, ?_⟩
      · rcases hdn.1 with hempty | hcont
        · obtain ⟨actual, hactual, hterm, -⟩ := graph_node hg hcodes hsums hc
          cases hn.symm.trans hactual
          have hsafe := HeapObservations.erase (HeapObservations.consequence
            (fun _ _ _ hu => hu.1) (fun _ _ h => h)
            (hterm n _ h ρ (he.transfer n (Nat.le_succ n) _ (WExt_refl _))
              (hi.transfer n (Nat.le_succ n) _ (WExt_refl _)) (entryFacts_holds he hf)
              (WorldAdm_trunc _ hw) (HeapOk_trunc n W h hh)))
          exact returnsPost_of_safePost (ExpressionEffects.noReturn_sound hempty hsafe)
        · intro k h' v hk run hv
          exact .inl hcont
      · cases hx : node.handler with
        | none => intro hx; rw [hexc] at hx; cases hx
        | some t => exact .inl (by simpa [deadHandler, hx] using hdn.2)
    | false =>
      have hp := hp.resolve_left (by simp [hd])
      obtain ⟨hx, out, ht, hedge⟩ := hlive hd
      have hrun := ht n _ h _ initial.length (Footprints.Closed.holds_iff.mp hp.1).1 hp.2
        (he.transfer n (Nat.le_succ n) _ (WExt_refl _))
        (hi.transfer n (Nat.le_succ n) _ (WExt_refl _)) (entryFacts_holds he hf)
        (WorldAdm_trunc _ hw) (HeapOk_trunc n W h hh)
      have hraises : ((!deadHandler dead node.handler) || exc) = true →
          RaisesPost (Φ.Holds initial) n h (instantiate 0 ρ node.expression) := by
        intro hthr k h'' t'' v hk run hr
        exact Footprints.Closed.Holds.trans_on hp.1 (raisesPost_of_safePostExc hrun k h'' t'' v hk run hr hthr)
      refine ⟨returnsPost_of_safePost (HeapObservations.weaken (fun _ _ hpost => .inr
        ⟨Footprints.Closed.Holds.trans_on hp.1 hpost.1, edgesFresh_sound hedge hp.2 hpost.2⟩) hrun.post), ?_⟩
      cases hk : node.handler with
      | none => intro hexc; exact hraises (by simp [hk, deadHandler, hexc])
      | some t =>
        cases hd : deadAt dead t.label with
        | true => exact .inl hd
        | false =>
          exact .inr ⟨hraises (by simp [hk, deadHandler, hd]),
            handlerFresh_sound ((hx t hk).resolve_left (by simp [hd])) hp.2⟩
  | @expr _ t _ t' ρ k handler st =>
    refine ⟨hp.1.step st, ?_⟩
    cases handler with
    | none => exact fun he => (hp.2 he).step st
    | some l => exact Or.imp id (fun h => ⟨h.1.step st, h.2⟩) hp.2
  | ret hv =>
    rcases hp.1.value hv with hd | ⟨hb, ht⟩
    · simp [deadContinuation] at hd
    · exact ⟨hb, ht.2 rfl⟩
  | bind hv =>
    rcases hp.1.value hv with hd | ⟨hb, ht⟩
    · exact .inl (by simpa [deadContinuation, successors] using hd)
    · exact .inr ⟨hb, by simpa [pushes] using ht.1 _ (by simp [successors])⟩
  | effect hv =>
    rcases hp.1.value hv with hd | ⟨hb, ht⟩
    · exact .inl (by simpa [deadContinuation, successors] using hd)
    · exact .inr ⟨hb, by simpa [pushes] using ht.1 _ (by simp [successors])⟩
  | yes =>
    rcases hp.1.value rfl with hd | ⟨hb, ht⟩
    · simp only [deadContinuation, successors, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hd
      exact .inl hd.2.1
    · exact .inr ⟨hb, by simpa [pushes] using ht.1 _ (by simp [successors])⟩
  | no =>
    rcases hp.1.value rfl with hd | ⟨hb, ht⟩
    · simp only [deadContinuation, successors, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hd
      exact .inl hd.2.2
    · exact .inr ⟨hb, by simpa [pushes] using ht.1 _ (by simp [successors])⟩
  | yesBind =>
    rcases hp.1.value rfl with hd | ⟨hb, ht⟩
    · simp only [deadContinuation, successors, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hd
      exact .inl hd.2.1
    · exact .inr ⟨hb, by simpa [pushes] using ht.1 _ (by simp [successors])⟩
  | noBind =>
    rcases hp.1.value rfl with hd | ⟨hb, ht⟩
    · simp only [deadContinuation, successors, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hd
      exact .inl hd.2.2
    · exact .inr ⟨hb, by simpa [pushes] using ht.1 _ (by simp [successors])⟩
  | tagBind hv =>
    rcases hp.1.value hv with hd | ⟨hb, ht⟩
    · simp only [deadContinuation, successors, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true] at hd
      split
      · exact .inl hd.2.1
      · exact .inl hd.2.2
    · apply Or.inr
      refine ⟨hb, ?_⟩
      split
      · exact by simpa [pushes] using ht.1 _ (by simp [successors])
      · exact by simpa [pushes] using ht.1 _ (by simp [successors])
  | handle hr => exact Or.imp id (fun h => ⟨h.1.raised hr, h.2 _⟩) hp.2
  | raise hr => exact fun he => (hp.2 he).raised hr

/-- The effect proof reuses ordinary graph progress and its point assertions.
There is one control-flow checker, including for cycles and branch refinements. -/
theorem bounded_safe_of_sim [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {Rty : Goal ι} {v0 : Tm} {E : List Tm} {K : List (Continuation × Option Target)}
    {C : Certificate ι} {facts : List (List Nat)} {dead : List Bool} {ret exc : Bool}
    {codes : CodeEntry ι → Bool} (hg : checkGraphUsing (sums := sums) G images Rty (program E K) C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (hnodes : NodesWithin G Φ (program E K) C facts dead ret exc) (hv0 : isVal v0 = true) :
    ∀ n W h ts s initial, Sim E K ts s → WorldAdm W → HeapOk n W h →
      StateOk G Rty C v0 n W h s → BoundState Φ facts dead ret exc initial n h s →
      HeapObservations.SafePostExc (excOf G) (GoalHolds G Rty v0)
        (fun h' v => Φ.Holds initial h' ∧ (ret = true → FreshAt initial.length v))
        (fun h' => exc = true → Φ.Holds initial h') n W h ts := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ts s initial sim hw hh hs hp
    rcases state_progress hg hcodes hsums hv0 hw hh hs with
      (⟨v, rfl, hv, ht⟩ | ⟨v, rfl, hsc⟩) | ⟨U, h', s', hx, hu, st, hok, hs'⟩
    · cases sim; exact .inl (.inl ⟨hv, ht, hp⟩)
    · cases sim with
      | raised hv hj => exact .inl (.inr ⟨⟨v, .throwV hv hj, hsc⟩, hp⟩)
    · obtain ⟨ts', step, sim'⟩ := sim_step sim st
      exact .inr ⟨U, h', ts', hx, hu, step, hok,
        ih U h' ts' s' initial sim' hu hok hs'
          (bounded_step hg hcodes hsums hnodes hw hh hs hp st)⟩

theorem goto_bounded [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {Rty : Goal ι} {E : List Tm} {K : List (Continuation × Option Target)}
    {C : Certificate ι} {start inputs} {facts : List (List Nat)} {dead : List Bool} {ret exc : Bool}
    {codes : CodeEntry ι → Bool} {entrySeparation : HeapSeparation.Separation}
    {entryIndices : List HeapKnowledge.IndexAtom}
    (hc : checkEntryUsing (sums := sums) (entrySeparation := entrySeparation) (entryIndices := entryIndices)
      G images Rty (program E K) C start inputs codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (hnodes : NodesWithin G Φ (program E K) C facts dead ret exc)
    (hstart : factsAt facts start = [])
    (n W h L d) (he : EnvOk G inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W h)
    (hsep : HeapSeparation.Holds entrySeparation (envOf L d) := by exact HeapSeparation.empty_holds _)
    (hidx : HeapKnowledge.IndexHolds entryIndices (envOf L d) h := by exact HeapKnowledge.indexHolds_nil _ _) :
    HeapObservations.SafePostExc (excOf G) (GoalHolds G Rty (Rty.argument (envOf L d)))
      (fun h' v => Φ.Holds h h' ∧ (ret = true → FreshAt h.length v))
      (fun h' => exc = true → Φ.Holds h h') n W h (.goto E K start L d) := by
  simp only [checkEntryUsing_eq, Bool.and_eq_true] at hc
  have hx := hc.2
  split at hx
  · rename_i c hstart'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨⟨hin, himp, harg⟩, hk⟩, hslot⟩ := hx
    -- The promised argument, where the goal states one, is an input's value.
    have hv0 : isVal (Rty.argument (envOf L d)) = true := by
      unfold Goal.argument
      cases hs : Rty.slot with
      | none => rfl
      | some s =>
        rw [hs] at hslot
        have hlt : s < inputs.length := by simpa using hslot
        exact (meaning_value (he.2 s inputs[s] (List.getElem?_eq_getElem hlt))).1
    apply bounded_safe_of_sim hc.1 hcodes hsums hnodes hv0 n W h _ _ h .goto hw hh
    · refine ⟨c, hstart', ?_, ?_, ?_, ?_⟩
      · simpa only [hin] using he
      · rw [himp]; exact PromiseCalls.ImpliesOk.nil G _ n W
      · intro p hp
        rw [harg] at hp
        unfold Goal.argument
        cases hs : Rty.slot with
        | none => rw [hs] at hp; cases hp
        | some s =>
          rw [hs] at hp
          cases List.mem_singleton.mp hp
          rfl
      · exact entryKnows_sound hk (by simpa only [hin] using he) hsep hidx
    · apply Or.inr
      refine ⟨Footprints.Closed.Holds.refl Φ h, ?_⟩
      rw [hstart]; intro i hi; cases hi
  · contradiction

/-! ## The postcondition a graph's returns establish

A unit stating facts of its result and of its inputs (`Effect.ensures`:
position `0` the result, `q + 1` the entry value of input `q`) is checked at
each return: the knowledge after the returned expression, its result at slot
`0`, entails each fact, an input's position read at a slot holding that
input's entry value there. Which slots hold an input's entry value is
carried along every edge (`trackTable`, untrusted; `edgesTrack` checks each
edge a run may take). The facts then hold of every value a normal run
returns, with the inputs' entry values, in the heap it returns in. -/

/-- Pairs of a slot and an input: the slot holds the input's entry value. -/
abbrev Tracked := List (Nat × Nat)

/-- Each pair's slot holds, in `ρ`, its input's value in `ρ0`. -/
def TracksAt (t : Tracked) (ρ ρ0 : Env) : Prop := ∀ p ∈ t, ρ p.1 = ρ0 p.2

/-- The pairs after a value is pushed. -/
def shiftTracked (t : Tracked) : Tracked := t.map fun p => (p.1 + 1, p.2)

theorem shiftTracked_holds {t : Tracked} {ρ ρ0 : Env} (v : Tm) (h : TracksAt t ρ ρ0) :
    TracksAt (shiftTracked t) (push v ρ) ρ0 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact h q hq

/-- Each target pair is read through the mapping from a source pair. -/
def trackFollows (sources : Tracked) (m : Mapping) (targets : Tracked) : Bool :=
  targets.all fun p => sources.contains (slot m p.1, p.2)

theorem trackFollows_sound {sources targets : Tracked} {m : Mapping} {ρ ρ0 : Env}
    (hc : trackFollows sources m targets = true) (hs : TracksAt sources ρ ρ0) :
    TracksAt targets (mapEnv m ρ) ρ0 := by
  intro p hp
  exact hs _ (List.contains_iff_mem.mp (List.all_eq_true.mp hc p hp))

/-- A node's edges, its handler's included, each with whether it pushes a
value before its mapping. -/
def edgesOf (k : Continuation) (x : Option Target) : List (Target × Bool) :=
  (match k with
    | .ret => []
    | .bind t => [(t, true)]
    | .effect t => [(t, false)]
    | .branch y n => [(y, false), (n, false)]
    | .branchBind y n => [(y, true), (n, true)]
    | .tagBind _ y n => [(y, true), (n, true)]) ++ x.toList.map fun t => (t, true)

/-- A node's pairs: none where the table reaches no run there. -/
def trackedAt (T : List (Option Tracked)) (l : Nat) : Option Tracked := T[l]?.bind id

/-- The pairs at each node: the seed at the entry, carried along every edge
to each slot whose mapping reads a slot holding the input, those every
predecessor carries. Untrusted: `edgesTrack` checks every edge. -/
@[nospecialize] def trackTable (P : Program) (C : Certificate ι) (start : Nat) (seed : Tracked) :
    List (Option Tracked) := Id.run do
  let widths := (C.map fun c => (entry c).length).toArray
  let mut table : Array (Option Tracked) := Array.replicate P.length none
  table := table.set! start (some seed)
  for _ in List.range (2 * P.length + 2) do
    let mut changed := false
    for (node, l) in P.zipIdx do
      let some here := table.getD l none | continue
      for e in edgesOf node.continuation node.handler do
        let sources := if e.2 then shiftTracked here else here
        let carried := (List.range (widths.getD e.1.label 0)).flatMap fun i =>
          sources.filterMap fun p => if p.1 == slot e.1.mapping i then some (i, p.2) else none
        let current := table.getD e.1.label none
        let merged := match current with
          | none => some carried
          | some old => some (old.filter carried.contains)
        if merged != current then
          table := table.set! e.1.label merged
          changed := true
    if !changed then break
  return table.toList

/-- Every edge out of a node the table reaches carries its pairs: the table
reaches the target, and the target's pairs follow. -/
def edgesTrack (T : List (Option Tracked)) (l : Nat) (node : Node) : Bool :=
  match trackedAt T l with
  | none => true
  | some here => (edgesOf node.continuation node.handler).all fun e =>
      match trackedAt T e.1.label with
      | none => false
      | some there => trackFollows (if e.2 then shiftTracked here else here) e.1.mapping there

/-- Each edge's target holds its pairs after the edge. -/
def NextTracks (T : List (Option Tracked)) (k : Continuation) (x : Option Target) (ρ ρ0 : Env) : Prop :=
  ∀ e ∈ edgesOf k x, ∀ v, ∃ t, trackedAt T e.1.label = some t ∧
    TracksAt t (mapEnv e.1.mapping (if e.2 then push v ρ else ρ)) ρ0

theorem edgesTrack_sound {T : List (Option Tracked)} {l : Nat} {node : Node} {here : Tracked} {ρ ρ0 : Env}
    (hc : edgesTrack T l node = true) (hl : trackedAt T l = some here) (hs : TracksAt here ρ ρ0) :
    NextTracks T node.continuation node.handler ρ ρ0 := by
  intro e he v
  simp only [edgesTrack, hl] at hc
  have hx := List.all_eq_true.mp hc e he
  split at hx
  · cases hx
  · rename_i there ht
    refine ⟨there, ht, trackFollows_sound hx ?_⟩
    rcases e with ⟨tgt, b⟩
    cases b
    · exact hs
    · exact shiftTracked_holds v hs

/-- The source slot of a fact's position at a return: `0` the result, `q + 1`
the slot after the result holding input `q`'s entry value. -/
def trackedSlot (t : Tracked) (j : Nat) : Nat :=
  if j = 0 then 0 else match t.find? (fun p => p.2 == j - 1) with
    | some p => p.1 + 1
    | none => 0

/-- One past the largest position a list of facts names. -/
def slotBound (ens : List HeapKnowledge.IndexFact) : Nat :=
  (ens.flatMap HeapKnowledge.IndexFact.slots).foldr max 0 + 1

theorem le_foldr_max {l : List Nat} {s : Nat} (h : s ∈ l) : s ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- The mapping reading a return's facts from its output's slots. -/
def returnMapping (t : Tracked) (ens : List HeapKnowledge.IndexFact) : Mapping :=
  some ((List.range (slotBound ens)).map (trackedSlot t))

/-- Each fact names the result or an input some pair holds. -/
def namesTracked (t : Tracked) (ens : List HeapKnowledge.IndexFact) : Bool :=
  ens.all fun F => F.slots.all fun j => j == 0 || t.any fun p => p.2 == j - 1

theorem returnMapping_eq {t : Tracked} {ens : List HeapKnowledge.IndexFact} {F : HeapKnowledge.IndexFact}
    (hF : F ∈ ens) (hn : namesTracked t ens = true) {ρ ρ0 : Env} {v : Tm} (ht : TracksAt t ρ ρ0) :
    ∀ s ∈ F.slots, mapEnv (returnMapping t ens) (push v ρ) s = push v ρ0 s := by
  intro s hs
  have hlt : s < slotBound ens :=
    Nat.lt_succ_of_le (le_foldr_max (List.mem_flatMap.mpr ⟨F, hF, hs⟩))
  have hmap : slot (returnMapping t ens) s = trackedSlot t s := by
    simp [returnMapping, slot, hlt]
  simp only [mapEnv, hmap]
  have hj := List.all_eq_true.mp (List.all_eq_true.mp hn F hF) s hs
  unfold trackedSlot
  cases s with
  | zero => rfl
  | succ q =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [Bool.or_eq_true] at hj
    rcases hj with h0 | hj
    · simp at h0
    simp only [Nat.add_sub_cancel] at hj
    cases hf : t.find? (fun p => p.2 == q) with
    | none =>
      obtain ⟨p, hp, hpq⟩ := List.any_eq_true.mp hj
      exact absurd hpq (by simpa using List.find?_eq_none.mp hf p hp)
    | some p =>
      have hp := List.mem_of_find?_eq_some hf
      have hpq : p.2 = q := by simpa using List.find?_some hf
      show ρ p.1 = ρ0 q
      rw [← hpq]
      exact ht p hp

/-- What a return meets in the heap `h` it returns in: each fact, at `ρ`, the
result pushed onto the inputs' entry values. -/
def EnsuresAt (ens : List HeapKnowledge.IndexFact) (h : Heap) (ρ : Env) : Prop :=
  ∀ F ∈ ens, F.HoldsAt ρ h

/-- Whether a knowledge, its result at slot `0`, entails the facts, each
input's position read at the slot after the result its pair names. -/
def returnEntails (k : HeapKnowledge.Knowledge) (t : Tracked) (ens : List HeapKnowledge.IndexFact) : Bool :=
  namesTracked t ens && HeapKnowledge.indicesCheckWith (HeapKnowledge.guardTags k) (HeapLinks.aliases k.links) k.links k.indices
    (ens.map fun F => ⟨F, none, false⟩) (returnMapping t ens)

theorem returnEntails_sound {k : HeapKnowledge.Knowledge} {t : Tracked} {ens : List HeapKnowledge.IndexFact}
    {ρ ρ0 : Env} {h : Heap} {v : Tm}
    (hc : returnEntails k t ens = true) (hk : HeapKnowledge.Holds k (push v ρ) h) (ht : TracksAt t ρ ρ0) :
    EnsuresAt ens h (push v ρ0) := by
  simp only [returnEntails, Bool.and_eq_true] at hc
  intro F hF
  have hheld := HeapKnowledge.indicesCheckWith_sound (HeapKnowledge.guardTags_sound hk)
    (fun x y hy => HeapLinks.aliases_eq hk.2.2.1 hy) hk.2.2.1
    hc.2 hk.2.2.2.2.2 ⟨F, none, false⟩ (List.mem_map_of_mem hF) (fun b hb => by cases hb)
  exact (HeapKnowledge.IndexFact.holdsAt_congr (returnMapping_eq hF hc.1 ht)).mp hheld

/-- The inputs a list of facts names, each held at its own slot on entry:
position `q + 1` names input `q`. -/
def namedInputs (ens : List HeapKnowledge.IndexFact) : Tracked :=
  ((ens.flatMap HeapKnowledge.IndexFact.slots).filterMap fun j =>
    if j = 0 then none else some (j - 1, j - 1)).eraseDups

/-- The table reaches the entry with pairs each holding its input at its own slot. -/
def startTracks (T : List (Option Tracked)) (start : Nat) : Bool :=
  match trackedAt T start with
  | some t => t.all fun p => p.1 == p.2
  | none => false

/-- A return the table reaches entails the facts: its node's entry admits no
value, its result type none (a throw), or its output entails them. -/
def returnOk (G : NormalGraph ι) (c : NodeEvidence ι) (k : Continuation) (here : Option Tracked)
    (ens : List HeapKnowledge.IndexFact) : Bool :=
  match k, here with
  | .ret, some t => unreachableEntry G c || ExpressionEffects.emptyType G (result c) ||
      returnEntails (outFacts G c) t ens
  | _, _ => true

/-- With the table `T`: it reaches the entry, every edge out of a node it
reaches carries its pairs, and every return it reaches entails the facts. -/
def returnsEnsureWith (G : NormalGraph ι) (P : Program) (C : Certificate ι)
    (ens : List HeapKnowledge.IndexFact) (start : Nat) (T : List (Option Tracked)) : Bool :=
  startTracks T start && (List.range P.length).all fun l =>
    match P[l]?, C[l]? with
    | some node, some c => edgesTrack T l node && returnOk G c node.continuation (trackedAt T l) ens
    | _, _ => true

/-- Every return of a graph a run may reach entails the facts, the inputs'
slots carried by `trackTable`. -/
def returnsEnsure (G : NormalGraph ι) (P : Program) (C : Certificate ι)
    (ens : List HeapKnowledge.IndexFact) (start : Nat) : Bool :=
  returnsEnsureWith G P C ens start (trackTable P C start (namedInputs ens))

/-- The same check, each node's failure located at it. -/
def returnsEnsureResult (G : NormalGraph ι) (P : Program) (C : Certificate ι)
    (ens : List HeapKnowledge.IndexFact) (start : Nat) : ProgramCertificates.CheckResult ι Unit :=
  let T := trackTable P C start (namedInputs ens)
  (ProgramCertificates.CheckResult.ofBool (startTracks T start)).bind fun _ =>
  ProgramCertificates.CheckResult.all (List.range P.length) fun l =>
    (ProgramCertificates.CheckResult.ofBool (match P[l]?, C[l]? with
      | some node, some c => edgesTrack T l node && returnOk G c node.continuation (trackedAt T l) ens
      | _, _ => true)).at (.node l)

theorem returnsEnsureResult_accepted (G : NormalGraph ι) (P : Program) (C : Certificate ι)
    (ens : List HeapKnowledge.IndexFact) (start : Nat) :
    (returnsEnsureResult G P C ens start).accepted = returnsEnsure G P C ens start := by
  simp only [returnsEnsureResult, returnsEnsure, returnsEnsureWith, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, ProgramCertificates.CheckResult.accepted_all,
    ProgramCertificates.CheckResult.accepted_at]

/-- A run whose values meet no type returns none: any postcondition holds of
its normal returns. -/
theorem SafePost_empty {Ξ T : Fam} {Q Q' : HeapObservations.Post} (hT : ∀ k U u, T k U u → False) :
    ∀ {n W h t}, HeapObservations.SafePost Ξ T Q n W h t → HeapObservations.SafePost Ξ T Q' n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with (⟨_, ht, _⟩ | hr) | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · exact (hT _ _ _ ht).elim
    · exact .inl (.inr hr)
    · exact .inr ⟨U, h', t', hx, hu, st, hh, ih hs⟩

theorem returnsEnsure_reassign (G : NormalGraph ι) (η : MixedAssignment ι) (P : Program) (C : Certificate ι)
    (ens : List HeapKnowledge.IndexFact) (start : Nat) :
    returnsEnsure (reassign G η) P C ens start = returnsEnsure G P C ens start := by
  simp only [returnsEnsure, returnsEnsureWith, returnOk, unreachableEntry, ExpressionEffects.emptyType]
  rfl

theorem returnsEnsure_at {G : NormalGraph ι} {P : Program} {C : Certificate ι}
    {ens : List HeapKnowledge.IndexFact} {start : Nat} {T : List (Option Tracked)}
    (h : returnsEnsureWith G P C ens start T = true) {l : Nat} {node : Node}
    {c : NodeEvidence ι} (hn : P[l]? = some node) (hc : C[l]? = some c) :
    edgesTrack T l node = true ∧ returnOk G c node.continuation (trackedAt T l) ens = true := by
  simp only [returnsEnsureWith, Bool.and_eq_true, List.all_eq_true] at h
  have hl : l ∈ List.range P.length := List.mem_range.mpr (List.getElem?_eq_some_iff.mp hn).1
  have := h.2 l hl
  rw [hn, hc] at this
  simpa only [Bool.and_eq_true] using this

/-- What the run reads of a state for the postcondition, `ρ0` the inputs'
entry values: at a node, its pairs hold; a return's expression returns
values meeting the facts, and each edge's target holds its pairs; a
finished run's value meets them in its heap. -/
def EnsState (T : List (Option Tracked)) (ens : List HeapKnowledge.IndexFact) (ρ0 : Env) (n : Nat) (h : Heap) :
    State → Prop
  | .at l ρ => ∃ t, trackedAt T l = some t ∧ TracksAt t ρ ρ0
  | .eval t ρ k x => (k = Continuation.ret → ReturnsPost (fun h' v => EnsuresAt ens h' (push v ρ0)) n h t) ∧
      NextTracks T k x ρ ρ0
  | .done v => EnsuresAt ens h (push v ρ0)
  | _ => True

theorem ensures_step [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {sums : List (ProgramCertificates.ReadSummary ι)} {Rty : Goal ι} {v0 : Tm} {P : Program}
    {C : Certificate ι} {ens : List HeapKnowledge.IndexFact} {codes} {start : Nat}
    {T : List (Option Tracked)} {ρ0 : Env}
    (hg : checkGraphUsing (sums := sums) G images Rty P C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (hens : returnsEnsureWith G P C ens start T = true)
    {n W h s h' s'} (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hs : StateOk G Rty C v0 (n+1) W h s) (hp : EnsState T ens ρ0 (n+1) h s)
    (st : Transition P h s h' s') : EnsState T ens ρ0 n h' s' := by
  cases st with
  | @enter l node _ ρ hn =>
    obtain ⟨c, hc, he, hi, -, hf⟩ := hs
    obtain ⟨t, htl, htr⟩ := hp
    obtain ⟨hedges, hret⟩ := returnsEnsure_at hens hn hc
    refine ⟨fun hk => ?_, edgesTrack_sound hedges htl htr⟩
    obtain ⟨actual, hactual, hterm, -⟩ := graph_node hg hcodes hsums hc
    cases hn.symm.trans hactual
    have hrun := hterm n _ h ρ (he.transfer n (Nat.le_succ n) _ (WExt_refl _))
      (hi.transfer n (Nat.le_succ n) _ (WExt_refl _)) (entryFacts_holds he hf)
      (WorldAdm_trunc _ hw) (HeapOk_trunc n W h hh)
    simp only [returnOk, hk, htl, Bool.or_eq_true] at hret
    rcases hret with (hu | hempty) | hr
    · exact (unreachableEntry_sound hu he).elim
    · exact returnsPost_of_safePost (SafePost_empty
        (fun _ _ _ hu => ExpressionEffects.emptyType_sound hempty hu.1) hrun)
    exact returnsPost_of_safePost (HeapObservations.weaken
      (fun h'' v hq => returnEntails_sound hr hq htr) hrun)
  | expr st => exact ⟨fun hk => (hp.1 hk).step st, hp.2⟩
  | ret hv => exact (hp.1 rfl).value hv
  | @bind v _ _ l _ hv => exact hp.2 (l, true) (List.mem_append_left _ (List.mem_singleton_self _)) v
  | @effect v _ _ l _ hv => exact hp.2 (l, false) (List.mem_append_left _ (List.mem_singleton_self _)) v
  | @yes _ _ y n _ => exact hp.2 (y, false) (List.mem_append_left _ (by simp)) .tru
  | @no _ _ y n _ => exact hp.2 (n, false) (List.mem_append_left _ (by simp)) .fls
  | @yesBind _ _ y n _ => exact hp.2 (y, true) (List.mem_append_left _ (by simp)) .tru
  | @noBind _ _ y n _ => exact hp.2 (n, true) (List.mem_append_left _ (by simp)) .fls
  | @tagBind v _ _ tag y n _ hv =>
    split
    · exact hp.2 (y, true) (List.mem_append_left _ (by simp)) v
    · exact hp.2 (n, true) (List.mem_append_left _ (by simp)) v
  | @handle _ v _ _ _ l hr => exact hp.2 (l, true) (List.mem_append_right _ (by simp)) v
  | raise hr => trivial

/-- **A graph's returns meet its postcondition**: run from a state the safety
proof and the postcondition's reading admit, it is safe, and every value it
returns meets the facts, with the inputs' entry values `ρ0`, in the heap it
returns in. -/
theorem ensures_safe_of_sim [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {sums : List (ProgramCertificates.ReadSummary ι)} {Rty : Goal ι} {v0 : Tm} {E : List Tm}
    {K : List (Continuation × Option Target)} {C : Certificate ι} {ens : List HeapKnowledge.IndexFact}
    {codes : CodeEntry ι → Bool} {start : Nat} {T : List (Option Tracked)} {ρ0 : Env}
    (hg : checkGraphUsing (sums := sums) G images Rty (program E K) C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (hens : returnsEnsureWith G (program E K) C ens start T = true) (hv0 : isVal v0 = true) :
    ∀ n W h ts s, Sim E K ts s → WorldAdm W → HeapOk n W h →
      StateOk G Rty C v0 n W h s → EnsState T ens ρ0 n h s →
      HeapObservations.SafePost (excOf G) (GoalHolds G Rty v0) (fun h' v => EnsuresAt ens h' (push v ρ0))
        n W h ts := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ts s sim hw hh hs hp
    rcases state_progress hg hcodes hsums hv0 hw hh hs with
      (⟨v, rfl, hv, ht⟩ | ⟨v, rfl, hsc⟩) | ⟨U, h', s', hx, hu, st, hok, hs'⟩
    · cases sim; exact .inl (.inl ⟨hv, ht, hp⟩)
    · cases sim with
      | raised hv hj => exact .inl (.inr ⟨v, .throwV hv hj, hsc⟩)
    · obtain ⟨ts', step, sim'⟩ := sim_step sim st
      exact .inr ⟨U, h', ts', hx, hu, step, hok,
        ih U h' ts' s' sim' hu hok hs' (ensures_step hg hcodes hsums hens hw hh hs hp st)⟩

/-- A graph run started at an entry the checker accepted, whose returns
entail the postcondition, is safe, and every value it returns meets it,
with the inputs' values at the start. -/
theorem goto_ensures [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {sums : List (ProgramCertificates.ReadSummary ι)} {Rty : Goal ι} {E : List Tm}
    {K : List (Continuation × Option Target)} {C : Certificate ι} {start inputs}
    {ens : List HeapKnowledge.IndexFact} {codes : CodeEntry ι → Bool}
    {entrySeparation : HeapSeparation.Separation} {entryIndices : List HeapKnowledge.IndexAtom}
    (hc : checkEntryUsing (sums := sums) (entrySeparation := entrySeparation) (entryIndices := entryIndices)
      G images Rty (program E K) C start inputs codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    (hens : returnsEnsure G (program E K) C ens start = true)
    (n W h L d) (he : EnvOk G inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W h)
    (hsep : HeapSeparation.Holds entrySeparation (envOf L d) := by exact HeapSeparation.empty_holds _)
    (hidx : HeapKnowledge.IndexHolds entryIndices (envOf L d) h := by exact HeapKnowledge.indexHolds_nil _ _) :
    HeapObservations.SafePost (excOf G) (GoalHolds G Rty (Rty.argument (envOf L d)))
      (fun h' v => EnsuresAt ens h' (push v (envOf L d))) n W h (.goto E K start L d) := by
  simp only [checkEntryUsing_eq, Bool.and_eq_true] at hc
  have hx := hc.2
  have hstartT : startTracks (trackTable (program E K) C start (namedInputs ens)) start = true := by
    simp only [returnsEnsure, returnsEnsureWith, Bool.and_eq_true] at hens; exact hens.1
  split at hx
  · rename_i c hstart'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨⟨hin, himp, harg⟩, hk⟩, hslot⟩ := hx
    have hv0 : isVal (Rty.argument (envOf L d)) = true := by
      unfold Goal.argument
      cases hs : Rty.slot with
      | none => rfl
      | some s =>
        rw [hs] at hslot
        have hlt : s < inputs.length := by simpa using hslot
        exact (meaning_value (he.2 s inputs[s] (List.getElem?_eq_getElem hlt))).1
    apply ensures_safe_of_sim hc.1 hcodes hsums hens hv0 n W h _ _ .goto hw hh
    · refine ⟨c, hstart', ?_, ?_, ?_, ?_⟩
      · simpa only [hin] using he
      · rw [himp]; exact PromiseCalls.ImpliesOk.nil G _ n W
      · intro p hp
        rw [harg] at hp
        unfold Goal.argument
        cases hs : Rty.slot with
        | none => rw [hs] at hp; cases hp
        | some s =>
          rw [hs] at hp
          cases List.mem_singleton.mp hp
          rfl
      · exact entryKnows_sound hk (by simpa only [hin] using he) hsep hidx
    · simp only [startTracks] at hstartT
      split at hstartT
      · rename_i t ht
        refine ⟨t, ht, fun p hp => ?_⟩
        have := List.all_eq_true.mp hstartT p hp
        rw [beq_iff_eq.mp this]
      · cases hstartT
  · contradiction

/-- **A node the bound check accepts is within the bound** on the locations
below where the invocation started: an inspection, which preserves the heap,
a typed write of a field holding a value, or a call at a selected signature
within the bound, its receiver's store, where the signature excepts it, fresh;
each beside the node's ordinary safety. Its value is fresh where it copies a
fresh slot or a call's signature states a fresh result. -/
theorem nodePost_of_checked [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {c : NodeEvidence ι} {t : Tm} {F : List Nat}
    (hscope : ProgramCertificates.checkScope (entry c).length t = true)
    (hcases : ((ExpressionEffects.check G (entry c) t || ExpressionEffects.writeWithin G (entry c) Φ t) ||
      (decide ((ProgramCertificates.claim c.expression).term = t) &&
        (ProgramCertificates.checkTreeUsing G images c.expression (sums := sums) ||
          PromiseCalls.requiresTree G images (entryFacts G c) (fun _ => false) sums c.expression) &&
        selectedWithinAt Φ F c.expression) || ExpressionEffects.emptyType G (result c)) = true)
    (hterm : ExpressionOk G c t) (hsums : ProgramCertificates.SummariesSound G images sums) :
    ∀ n W h ρ (b : Nat), b ≤ h.length → FreshOk F b ρ →
      EnvOk G (entry c) ρ n W → PromiseCalls.ImpliesOk G c.implies ρ n W → HeapKnowledge.Holds (entryFacts G c) ρ h →
      WorldAdm W → HeapOk n W h →
      HeapObservations.SafePost (excOf G) (meaning G (result c))
        (fun h' v => Φ.HoldsOn (· < b) h h' ∧ ((varFresh F t || callFresh G images sums c t) = true → FreshAt b v))
        n W h (instantiate 0 ρ t) := by
  intro j V h' ρ b hb hF henv himp hknowledge hworld hheap
  have hsafe := HeapObservations.erase (HeapObservations.consequence (fun _ _ _ hu => hu.1) (fun _ _ h => h)
    (hterm j V h' ρ henv himp hknowledge hworld hheap))
  -- A slot copy returns the slot's value.
  by_cases hvar : varFresh F t = true
  · cases t <;> simp only [varFresh, reduceCtorEq] at hvar
    rename_i i
    simp only [ProgramCertificates.checkScope, decide_eq_true_eq] at hscope
    have hval : isVal (ρ i) = true := by
      obtain ⟨A, hA⟩ : ∃ A, (entry c)[i]? = some A := ⟨_, List.getElem?_eq_getElem hscope⟩
      exact (meaning_value (henv.2 i A hA)).1
    have hinst : instantiate 0 ρ (.var i) = ρ i := by simp [instantiate]
    rw [hinst] at hsafe ⊢
    exact HeapObservations.refine_value hval
      ⟨(Footprints.Closed.Holds.refl Φ h').on _, fun _ => hF i (List.contains_iff_mem.mp hvar)⟩ hsafe
  simp only [Bool.not_eq_true] at hvar
  -- The node's footprint.
  have hwithin : HeapObservations.SafePost (excOf G) (meaning G (result c))
      (fun h'' _ => Φ.HoldsOn (· < b) h' h'') j V h' (instantiate 0 ρ t) := by
    simp only [Bool.or_eq_true] at hcases
    rcases hcases with ((hexpr | hwrite) | hcall) | hempty
    rotate_right
    · exact ExpressionEffects.noReturn_sound hempty hsafe
    · exact HeapObservations.weaken (fun h'' _ hq =>
        (Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _) hq).on _)
        (ExpressionEffects.sound hexpr hscope henv hworld hheap hsafe)
    · exact HeapObservations.weaken (fun _ _ hq => hq.on _)
        (ExpressionEffects.write_within hwrite henv hheap hsafe)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcall
      obtain ⟨⟨hterm', htree⟩, hsel⟩ := hcall
      simp only [selectedWithinAt, Bool.and_eq_true] at hsel
      obtain ⟨hops, hsel⟩ := hsel
      split at hsel
      · rename_i eff heff
        simp only [Bool.and_eq_true] at hsel
        obtain ⟨hle, hr⟩ := hsel
        have hs : HeapObservations.SafePost (excOf G) (meaning G (ProgramCertificates.claim c.expression).type)
            (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term))
            (ExpressionEffects.actualsOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term)) h')
            j V h' (instantiate 0 ρ (ProgramCertificates.claim c.expression).term) := by
          simp only [Bool.or_eq_true] at htree
          rcases htree with htree | htree
          · exact ExpressionEffects.selected_sound c.expression htree hops heff
              (ProgramCertificates.codesSound_none _) hsums (by simpa only [ControlFlow.entry] using henv) hworld hheap
          · obtain ⟨eff', heff', hs⟩ := PromiseCalls.requiresTree_sound (ProgramCertificates.codesSound_none _) hsums
              c.expression htree
            rw [heff] at heff'
            cases heff'
            exact hs (by simpa only [ControlFlow.entry] using henv) hknowledge hworld hheap
        rw [hterm'] at hs
        apply HeapObservations.weaken (fun h'' v hq => ?_) hs
        split at hr
        · rename_i ho
          exact ((CallEffects.Effect.within_own hq.1 ho).mono hr).on _
        rename_i ho
        simp only [Bool.not_eq_true] at ho
        simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hr
        rcases hr with (hr | hr) | hr
        · exact ((CallEffects.Effect.within_holds hq.1 hr ho).mono hle).on _
        · rw [hr]; exact (CallEffects.Effect.within_top hq.1).on _
        · refine (CallEffects.Effect.within_below hq.1 (fun _ => ?_) (fun h => by rw [ho] at h; cases h)).mono hle
          rw [hterm'] at hr
          exact receiverFresh_sound hr hF
      · cases hsel
  -- The node's value.
  by_cases hcf : callFresh G images sums c t = true
  · simp only [callFresh, Bool.and_eq_true, decide_eq_true_eq] at hcf
    obtain ⟨⟨⟨hfr, hops⟩, hterm'⟩, htree⟩ := hcf
    split at hfr
    · rename_i eff heff
      have hs := ExpressionEffects.selected_sound c.expression htree hops heff
        (ProgramCertificates.codesSound_none _) hsums (by simpa only [ControlFlow.entry] using henv) hworld hheap
      rw [hterm'] at hs
      have hboth := HeapObservations.cross_upto j (fun _ _ _ _ _ _ _ _ hu _ => hu) V V h' _ hheap hheap hwithin hs
      exact HeapObservations.weaken (fun h'' v hq =>
        ⟨hq.1, fun _ => (hq.2.2.1 hfr).lower (Nat.le_trans hb (Nat.le_refl _))⟩) hboth
    · cases hfr
  · simp only [Bool.not_eq_true] at hcf
    exact HeapObservations.weaken (fun _ _ hq => ⟨hq, fun h => by simp [hvar, hcf] at h⟩) hwithin

/-- Whether a node's throw is within the bound: an inspection, a typed
write, or a selected invocation or construction within the bound whose
signature states its footprint on a throw. -/
def throwsWithin [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (F : List Nat) (c : NodeEvidence ι) (t : Tm) : Bool :=
  (ExpressionEffects.check G (entry c) t || ExpressionEffects.writeWithin G (entry c) Φ t) ||
    (decide ((ProgramCertificates.claim c.expression).term = t) &&
      (ProgramCertificates.checkTreeUsing G images c.expression (sums := sums) ||
        PromiseCalls.requiresTree G images (entryFacts G c) (fun _ => false) sums c.expression) &&
      selectedWithinAt Φ F c.expression && ExpressionEffects.selectedThrows c.expression &&
      (match ExpressionEffects.selectedEffect c.expression with
      | some eff => eff.onThrow
      | none => false)) ||
  -- A node no environment reaches: a slot of its entry has no value.
  (entry c).any (fun A => ExpressionEffects.emptyType G A)

theorem throwsWithin_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {c : NodeEvidence ι} {t : Tm} {F : List Nat}
    (hscope : ProgramCertificates.checkScope (entry c).length t = true)
    (hthrows : throwsWithin G images sums Φ F c t = true)
    (hterm : ExpressionOk G c t) (hsums : ProgramCertificates.SummariesSound G images sums) :
    ∀ n W h ρ (b : Nat), b ≤ h.length → FreshOk F b ρ →
      EnvOk G (entry c) ρ n W → PromiseCalls.ImpliesOk G c.implies ρ n W → HeapKnowledge.Holds (entryFacts G c) ρ h →
      WorldAdm W → HeapOk n W h →
      HeapObservations.SafePostExc (excOf G) (meaning G (result c)) (fun _ _ => True)
        (fun h' => Φ.HoldsOn (· < b) h h') n W h (instantiate 0 ρ t) := by
  intro j V h' ρ b _ hF henv himp hknowledge hworld hheap
  have hsafe := HeapObservations.erase (HeapObservations.consequence (fun _ _ _ hu => hu.1) (fun _ _ h => h)
    (hterm j V h' ρ henv himp hknowledge hworld hheap))
  simp only [throwsWithin, Bool.or_eq_true] at hthrows
  rcases hthrows with ((hexpr | hwrite) | hcall) | hempty
  rotate_right
  · obtain ⟨A, hA, hnil⟩ := List.any_eq_true.mp hempty
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hA
    exact (ExpressionEffects.emptyType_sound hnil (henv.2 i A hi)).elim
  · exact HeapObservations.SafePostExc.weaken (fun _ _ _ => trivial)
      (fun h'' hq => (Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _) hq).on _)
      (ExpressionEffects.sound_exc hexpr hscope henv hworld hheap hsafe)
  · exact HeapObservations.SafePostExc.weaken (fun _ _ _ => trivial) (fun _ hq => hq.on _)
      (ExpressionEffects.write_within_exc hwrite henv hheap hsafe)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcall
    obtain ⟨⟨⟨⟨hterm', htree⟩, hsel⟩, hthr⟩, hon⟩ := hcall
    simp only [selectedWithinAt, Bool.and_eq_true] at hsel
    obtain ⟨hops, hsel⟩ := hsel
    split at hsel
    · rename_i eff heff
      rw [heff] at hon
      simp only at hon
      simp only [Bool.and_eq_true] at hsel
      obtain ⟨hle, hr⟩ := hsel
      have hs : HeapObservations.SafePostExc (excOf G) (meaning G (ProgramCertificates.claim c.expression).type)
          (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term))
            (ExpressionEffects.actualsOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term)) h')
          (eff.excPost (ExpressionEffects.receiverOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term)) h')
          j V h' (instantiate 0 ρ (ProgramCertificates.claim c.expression).term) := by
        rcases Bool.or_eq_true_iff.mp htree with htree | hreq
        · exact ExpressionEffects.selected_sound_exc c.expression htree hops hthr heff
            (ProgramCertificates.codesSound_none _) hsums (by simpa only [ControlFlow.entry] using henv) hworld hheap
        · obtain ⟨eff', heff', hs⟩ := PromiseCalls.requiresTree_sound_exc
            (ProgramCertificates.codesSound_none _) hsums c.expression hreq
          rw [heff] at heff'; cases heff'
          exact hs (by simpa only [ControlFlow.entry] using henv) hknowledge hworld hheap
      rw [hterm'] at hs
      apply HeapObservations.SafePostExc.weaken (fun _ _ _ => trivial) (fun h'' hq => ?_) hs
      have hq := hq hon
      split at hr
      · rename_i ho
        exact ((CallEffects.Effect.within_own hq ho).mono hr).on _
      rename_i ho
      simp only [Bool.not_eq_true] at ho
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hr
      rcases hr with (hr | hr) | hr
      · exact ((CallEffects.Effect.within_holds hq hr ho).mono hle).on _
      · rw [hr]; exact (CallEffects.Effect.within_top hq).on _
      · refine (CallEffects.Effect.within_below hq (fun _ => ?_) (fun h => by rw [ho] at h; cases h)).mono hle
        rw [hterm'] at hr
        exact receiverFresh_sound hr hF
    · cases hsel

/-- A node within the bound on normal return, and on a throw where its
throw is checked. -/
theorem nodeWithin_of_checked [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {c : NodeEvidence ι} {t : Tm} {F : List Nat} {thr : Bool}
    (hscope : ProgramCertificates.checkScope (entry c).length t = true)
    (hcases : ((ExpressionEffects.check G (entry c) t || ExpressionEffects.writeWithin G (entry c) Φ t) ||
      (decide ((ProgramCertificates.claim c.expression).term = t) &&
        (ProgramCertificates.checkTreeUsing G images c.expression (sums := sums) ||
          PromiseCalls.requiresTree G images (entryFacts G c) (fun _ => false) sums c.expression) &&
        selectedWithinAt Φ F c.expression) || ExpressionEffects.emptyType G (result c)) = true)
    (hthrows : thr = true → throwsWithin G images sums Φ F c t = true)
    (hterm : ExpressionOk G c t) (hsums : ProgramCertificates.SummariesSound G images sums) :
    NodeWithin G Φ c t F (varFresh F t || callFresh G images sums c t) thr := by
  intro j V h' ρ b hb hF henv himp hknowledge hworld hheap
  have hpost := nodePost_of_checked hscope hcases hterm hsums j V h' ρ b hb hF henv himp hknowledge hworld hheap
  cases thr with
  | false =>
    exact HeapObservations.SafePostExc.of_post (fun _ h => absurd h (by simp)) hpost
  | true =>
    have hexc := throwsWithin_sound hscope (hthrows rfl) hterm hsums j V h' ρ b hb hF henv himp hknowledge hworld hheap
    have hboth := HeapObservations.SafePostExc.cross_upto j (fun _ _ _ _ _ _ _ _ hu _ => hu) V V h' _ hheap hheap
      (HeapObservations.SafePostExc.of_post (R := fun _ => True) (fun _ => trivial) hpost) hexc
    exact HeapObservations.SafePostExc.weaken (fun _ _ hq => hq.1) (fun _ hq _ => hq.2) hboth

/-! ## A unit's table of checked code

Graph code is checked by the graph checker, and its creation is typed by
naming what was checked (`ProgramCertificates.Rule.funGraph`). A unit's
certificate therefore checks its codes in order, each against the table of the
ones before it — a code creates only code nested in it, whose check comes
first — and the unit's own graph against the whole table. -/

/-- A table as the evidence checker reads it. -/
def admits [DecidableEq ι] (table : List (CodeEntry ι)) (c : CodeEntry ι) : Bool :=
  table.contains c

/-- Candidate facts, read by no proof: from every slot at each label but the
entry, which has none, each pass, in the order control flows from the entry
(the last node first), removes what a transfer does not establish, until none
does; without a fresh call, or without a fixpoint, none at all. The check
below decides whether the result holds on every edge. -/
@[nospecialize] def freshPass (nodes : List ((Node × NodeEvidence ι) × Nat)) (calls : Array Bool)
    (facts : Array (List Nat)) : Array (List Nat) :=
  nodes.foldr (fun ((node, _), l) facts =>
    let F := facts.getD l []
    let out := varFresh F node.expression || calls.getD l false
    let facts := (successors node.continuation).foldl (fun facts t =>
      facts.modify t.label fun D => D.filter fun i =>
        freshSlot F (pushes node.continuation) out (slot t.mapping i)) facts
    -- A handler binds the thrown value, never fresh, before the node's slots.
    match node.handler with
    | some t => facts.modify t.label fun D => D.filter fun i => freshSlot F true false (slot t.mapping i)
    | none => facts) facts

@[nospecialize] def freshIterate (nodes : List ((Node × NodeEvidence ι) × Nat)) (calls : Array Bool) :
    Nat → Array (List Nat) → Option (Array (List Nat))
  | 0, _ => none
  | fuel + 1, facts =>
    let next := freshPass nodes calls facts
    if next = facts then some facts else freshIterate nodes calls fuel next

@[nospecialize] def inferFresh [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (P : Program) (C : Certificate ι) (start : Nat) : List (List Nat) :=
  let nodes := (P.zip C).zipIdx
  let calls := (nodes.map fun ((node, c), _) => callFresh G images sums c node.expression).toArray
  if !calls.any id then [] else
  let init := (nodes.map fun ((_, c), l) => if l = start then [] else List.range (entry c).length).toArray
  ((freshIterate nodes calls (P.length + 2) init).map Array.toList).getD []

/-- One node of a graph within the bound: a handler's facts following from
its own, and its throw within the bound where a handler outside the checked
no-return region catches it or the invocation's throws are bounded (`exc`); its destinations' facts following from its own; and an
inspection (which preserves the heap), a typed write of a field holding a
value, or a call at a selected signature within the bound. Pure graphs retain
the independent operational rule, which also covers their handlers. -/
@[nospecialize] def nodeChecked [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (facts : List (List Nat)) (dead : List Bool) (ret exc : Bool) (l : Nat) (node : Node) (c : NodeEvidence ι) : Bool :=
  if deadAt dead l then deadNode G dead node c && !exc else
  let F := factsAt facts l
  -- The unreachability test, which expands every type of the node's entry,
  -- runs only where the node is not otherwise within the bound.
  ((match node.handler with | none => true | some t => deadAt dead t.label || handlerFresh facts F t) &&
    (!((!deadHandler dead node.handler) || exc) || throwsWithin G images sums Φ F c node.expression) &&
    ProgramCertificates.checkScope (entry c).length node.expression &&
    edgesFresh facts F (varFresh F node.expression || callFresh G images sums c node.expression) ret node.continuation &&
    ((ExpressionEffects.check G (entry c) node.expression ||
      ExpressionEffects.writeWithin G (entry c) Φ node.expression) ||
      (decide ((ProgramCertificates.claim c.expression).term = node.expression) &&
        (ProgramCertificates.checkTreeUsing G images c.expression (sums := sums) ||
          PromiseCalls.requiresTree G images (entryFacts G c) (fun _ => false) sums c.expression) &&
        selectedWithinAt Φ F c.expression) ||
      -- A node typed at a type no value has never returns normally.
      ExpressionEffects.emptyType G (result c))) || unreachableEntry G c

@[nospecialize] def nodeCheckedResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (facts : List (List Nat)) (dead : List Bool) (ret exc : Bool) (l : Nat) (node : Node) (c : NodeEvidence ι) :
    ProgramCertificates.CheckResult ι Unit :=
  if deadAt dead l then ProgramCertificates.CheckResult.ofBool (deadNode G dead node c && !exc) else
  let F := factsAt facts l
  ((ProgramCertificates.CheckResult.ofBool ((match node.handler with | none => true | some t => deadAt dead t.label || handlerFresh facts F t) &&
      (!((!deadHandler dead node.handler) || exc) || throwsWithin G images sums Φ F c node.expression) &&
      ProgramCertificates.checkScope (entry c).length node.expression &&
      edgesFresh facts F (varFresh F node.expression || callFresh G images sums c node.expression) ret node.continuation)).bind fun _ =>
    ((ProgramCertificates.CheckResult.ofBool (ExpressionEffects.check G (entry c) node.expression ||
      ExpressionEffects.writeWithin G (entry c) Φ node.expression)).orElse fun _ =>
    (ProgramCertificates.CheckResult.ofBool (decide ((ProgramCertificates.claim c.expression).term = node.expression))).bind fun _ =>
    ((ProgramCertificates.checkTreeResult G images c.expression (sums := sums)).orElse fun _ =>
      ProgramCertificates.CheckResult.ofBool
        (PromiseCalls.requiresTree G images (entryFacts G c) (fun _ => false) sums c.expression)).bind fun _ =>
    ProgramCertificates.CheckResult.ofBool (selectedWithinAt Φ F c.expression)).orElse fun _ =>
    ProgramCertificates.CheckResult.ofBool (ExpressionEffects.emptyType G (result c))).orElse fun _ =>
  ProgramCertificates.CheckResult.ofBool (unreachableEntry G c)

theorem nodeCheckedResult_accepted [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (facts : List (List Nat)) (dead : List Bool) (ret exc : Bool) (l : Nat) (node : Node) (c : NodeEvidence ι) :
    (nodeCheckedResult G images sums Φ facts dead ret exc l node c).accepted = nodeChecked G images sums Φ facts dead ret exc l node c := by
  unfold nodeCheckedResult nodeChecked
  split <;> simp only [ ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_orElse, ProgramCertificates.CheckResult.accepted_ofBool,
    ProgramCertificates.checkTreeUsing, Bool.and_assoc]

/-- Every node within the bound, at the facts inferred for the graph, the
entry with none; with `ret`, every return a fresh value. -/
@[nospecialize] def compositionalCheckedResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (ret exc : Bool) (start : Nat) (P : Program) (C : Certificate ι) :
    ProgramCertificates.CheckResult ι Unit :=
  let facts := inferFresh G images sums P C start
  let dead := inferDead G P C exc
  (ProgramCertificates.CheckResult.ofBool (factsAt facts start).isEmpty).bind fun _ =>
  ProgramCertificates.CheckResult.all (P.zip C).zipIdx fun ((node, c), l) =>
    (nodeCheckedResult G images sums Φ facts dead ret exc l node c).at (.node l)

@[nospecialize] def compositionalChecked [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (ret exc : Bool) (start : Nat) (P : Program) (C : Certificate ι) : Bool :=
  (compositionalCheckedResult G images sums Φ ret exc start P C).accepted

theorem compositionalChecked_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (ret exc : Bool) (start : Nat) (P : Program) (C : Certificate ι) :
    compositionalChecked G images sums Φ ret exc start P C = (
  (factsAt (inferFresh G images sums P C start) start).isEmpty &&
    (P.zip C).zipIdx.all fun ((node, c), l) => nodeChecked G images sums Φ (inferFresh G images sums P C start) (inferDead G P C exc) ret exc l node c
  ) := by
  simp only [compositionalChecked, compositionalCheckedResult, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, ProgramCertificates.CheckResult.accepted_all,
    ProgramCertificates.CheckResult.accepted_at, nodeCheckedResult_accepted]

theorem inferFresh_reassign [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (η : MixedAssignment ι) (P : Program) (C : Certificate ι) (start : Nat) :
    inferFresh (reassign G η) (images.reassign η) sums P C start = inferFresh G images sums P C start := by
  simp only [inferFresh, callFresh, Parametricity.checkTree_reassign]
  rfl

theorem entryFacts_reassign [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι) (c : NodeEvidence ι) :
    entryFacts (reassign G η) c = entryFacts G c := rfl

@[simp] theorem compositionalChecked_reassign [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι)) (η : MixedAssignment ι) (Φ : Footprints.Closed) (ret exc : Bool) (start : Nat)
    (P : Program) (C : Certificate ι) :
    compositionalChecked (reassign G η) (images.reassign η) sums Φ ret exc start P C =
      compositionalChecked G images sums Φ ret exc start P C := by
  simp only [compositionalChecked_eq, inferFresh_reassign, nodeChecked, callFresh, throwsWithin,
    Parametricity.checkTree_reassign, entryFacts_reassign, Parametricity.requiresTree_reassign,
    inferDead, deadNode, ExpressionEffects.emptyType]
  rfl

/-- The node checks give the premise the bounded run reads. -/
theorem nodes_of_checked [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {ret exc : Bool} {Rty : Goal ι} {P : Program} {C : Certificate ι} {codes}
    (hgraph : checkGraphUsing (sums := sums) G images Rty P C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes) (hsums : ProgramCertificates.SummariesSound G images sums)
    {facts : List (List Nat)} {dead : List Bool}
    (hall : ((P.zip C).zipIdx.all fun ((node, c), l) => nodeChecked G images sums Φ facts dead ret exc l node c) = true) :
    NodesWithin G Φ P C facts dead ret exc := by
  intro l node c hn hc
  have hzip : (P.zip C)[l]? = some (node, c) := List.getElem?_zip_eq_some.mpr ⟨hn, hc⟩
  have hmem : ((node, c), l) ∈ (P.zip C).zipIdx := List.mem_zipIdx_iff_getElem?.mpr hzip
  have hp := List.all_eq_true.mp hall _ hmem
  cases hd : deadAt dead l with
  | true =>
    simp only [nodeChecked, hd, if_true, Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact .inr ⟨fun _ => hp, (fun h => by cases h)⟩
  | false =>
    simp only [nodeChecked, hd, Bool.false_eq_true, if_false, Bool.or_eq_true, Bool.and_eq_true] at hp
    rcases hp with ⟨⟨⟨⟨hx, hthr⟩, hscope⟩, hedge⟩, hcases⟩ | hu
    rotate_right
    · exact .inl hu
    obtain ⟨actual, hactual, hterm, -⟩ := graph_node hgraph hcodes hsums hc
    cases hn.symm.trans hactual
    refine .inr ⟨(fun h => by cases h), fun _ => ?_⟩
    refine ⟨fun t ht => by simpa [ht] using hx, _, nodeWithin_of_checked hscope ?_ (fun h => ?_) hterm hsums, hedge⟩
    · simpa only [Bool.or_eq_true, Bool.and_eq_true] using hcases
    simp only [Bool.not_eq_true'] at hthr
    rcases hthr with hthr | hthr
    · rw [h] at hthr; cases hthr
    · exact hthr

/-- Definition effects supplement, rather than replace, ordinary safety. A
footprint letting everything change, without a fresh result or a footprint on
a throw, holds of every run (`Closed.top_safe`); any other bound is
established node by node (`compositionalChecked`), or, without a fresh result,
by a graph of pure nodes, which keeps the heap a prefix at every step, a raise
included; either holds beside the entry's goal, a promise included. A fresh
result is established node by node whatever the footprint. -/
@[nospecialize] def effectCheckedResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (c : CodeEntry ι) (C : Certificate ι) : ProgramCertificates.CheckResult ι Unit :=
  (ProgramCertificates.CheckResult.ofBool (!c.row.effect.freshObject &&
    (c.row.effect.requires.isNone && (c.row.effect.elements.isNone && !c.row.effect.receiverGrows)))).bind fun _ =>
  if c.row.effect.footprint = .top ∧ c.row.effect.fresh = false ∧ c.row.effect.onThrow = false then pure () else
    (ProgramCertificates.CheckResult.ofBool (!c.row.effect.fresh && c.exprs.all Purity.pureTerm)).orElse fun _ =>
    compositionalCheckedResult G images sums c.row.effect.footprint c.row.effect.fresh c.row.effect.onThrow c.start
      (program c.exprs c.conts) C

@[nospecialize] def effectChecked [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (c : CodeEntry ι) (C : Certificate ι) : Bool :=
  (effectCheckedResult G images sums c C).accepted

theorem effectChecked_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (c : CodeEntry ι) (C : Certificate ι) :
    effectChecked G images sums c C = (!c.row.effect.freshObject &&
      (c.row.effect.requires.isNone && (c.row.effect.elements.isNone && !c.row.effect.receiverGrows)) && (
  decide (c.row.effect.footprint = .top ∧ c.row.effect.fresh = false ∧ c.row.effect.onThrow = false) ||
    ((!c.row.effect.fresh && c.exprs.all Purity.pureTerm) ||
      compositionalChecked G images sums c.row.effect.footprint c.row.effect.fresh c.row.effect.onThrow c.start
        (program c.exprs c.conts) C)
  )) := by
  cases hfo : (!c.row.effect.freshObject && (c.row.effect.requires.isNone && (c.row.effect.elements.isNone && !c.row.effect.receiverGrows)))
  · simp only [effectChecked, effectCheckedResult, hfo, ProgramCertificates.CheckResult.accepted_ofBool,
      ProgramCertificates.CheckResult.accepted_bind, Bool.false_and]
  · by_cases h : c.row.effect.footprint = .top ∧ c.row.effect.fresh = false ∧ c.row.effect.onThrow = false <;>
      simp [effectChecked, effectCheckedResult, hfo, h, ProgramCertificates.CheckResult.accepted_orElse,
        ProgramCertificates.CheckResult.accepted_ofBool, ProgramCertificates.CheckResult.accepted_bind,
        compositionalChecked] <;> rfl

/-- What a code entry's graph is checked to return: its signature's result,
or its signature's promise about the parameter it names, at that parameter's
place in the frame. -/
def _root_.Verification.ProgramTyping.CodeEntry.goal (c : CodeEntry ι) : Goal ι :=
  match c.row.effect.promise with
  | some (.guards p) => .guards c.row.result (frameOffset c.store + p)
  | some (.asserts p) => .asserts c.row.result (frameOffset c.store + p)
  | none => .plain c.row.result

/-- What code assumes of its frame at entry: its signature's precondition on
the call's values, at the frame's slots, which are the call's positions for
code collecting no rest (`TypingBasics.PreAt`). -/
def codeEntryIndices (c : CodeEntry ι) : List HeapKnowledge.IndexAtom :=
  if c.store = none then c.row.effect.pre.map fun F => { fact := F } else []

theorem codeEntryIndices_holds {c : CodeEntry ι} {L : List Tm} {h : Heap}
    (hp : PreAt c.row.effect c.store L h) : HeapKnowledge.IndexHolds (codeEntryIndices c) (envOf L .nul) h := by
  intro a ha _
  unfold codeEntryIndices at ha
  split at ha
  · rename_i hs
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp ha
    exact hp hs F hF
  · cases ha

/-- One code entry, checked at its signature from the frame the signature
describes, against an earlier table. -/
@[nospecialize] def codeCheckedResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (table : List (CodeEntry ι)) (c : CodeEntry ι) (C : ControlFlow.Certificate ι) : ProgramCertificates.CheckResult ι Unit :=
  (ProgramCertificates.CheckResult.ofBool (decide (c.arity ≤ c.row.arguments.length) &&
    c.row.effect.below c.arity)).bind fun _ =>
  (effectCheckedResult G images sums c C).bind fun _ =>
  checkEntryResult (sums := sums) (entryIndices := codeEntryIndices c) G images c.goal (program c.exprs c.conts)
    C c.start (codeFrame c.arity c.row c.captures c.store) (admits table)

@[nospecialize] def codeCheckedUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (table : List (CodeEntry ι)) (c : CodeEntry ι) (C : ControlFlow.Certificate ι) : Bool :=
  (codeCheckedResult G images sums table c C).accepted

theorem codeCheckedUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (table : List (CodeEntry ι)) (c : CodeEntry ι) (C : ControlFlow.Certificate ι) :
    codeCheckedUsing G images sums table c C = (
  decide (c.arity ≤ c.row.arguments.length) && c.row.effect.below c.arity && effectChecked G images sums c C &&
    checkEntryUsing (sums := sums) (entryIndices := codeEntryIndices c) G images c.goal (program c.exprs c.conts)
      C c.start (codeFrame c.arity c.row c.captures c.store) (admits table)
  ) := by
  simp only [codeCheckedUsing, codeCheckedResult, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, effectChecked, checkEntryUsing, Bool.and_assoc]

/-- A checked entry meets its signature in the graph reassigned at every
assignment: the check reads none (`Parametricity.checkEntry_reassign`). -/
theorem codeChecked_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {table c C} (htable : ProgramCertificates.CodesSound G (admits table))
    (hsums : ProgramCertificates.SummariesSound G images sums)
    (h : codeCheckedUsing G images sums table c C = true) : ∀ η, c.Spec (reassign G η) := by
  intro η
  simp only [codeCheckedUsing_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨harity, hbelow⟩, heff⟩, hentry⟩ := h
  have hc : checkEntryUsing (sums := sums) (entryIndices := codeEntryIndices c) (reassign G η) (images.reassign η)
      c.goal (program c.exprs c.conts) C c.start
      (codeFrame c.arity c.row c.captures c.store) (admits table) = true := by
    exact (Parametricity.checkEntry_reassign G η images _ _ _ _ _ _ _ _ _).trans hentry
  have hs' := Parametricity.summariesSound_reassign G η images hsums
  have ht : ProgramCertificates.CodesSound (reassign G η) (admits table) :=
    fun e he η' => htable e he η'
  refine ⟨harity, hbelow, ?_⟩
  intro n W heap L he hw hh hvalues hpre
  have hidx := codeEntryIndices_holds hpre
  have hs := goto_safe hc ht hs' n W heap L .nul he hw hh (hidx := hidx)
  -- The goal the graph is checked at is the signature's result, its
  -- promise included.
  have hres : GoalHolds (reassign G η) c.goal (c.goal.argument (envOf L .nul)) =
      c.row.effect.result (meaning (reassign G η) c.row.result)
        (framePromised c.row.effect (frameOffset c.store) L) := by
    rcases hpr : c.row.effect.promise with _ | (p | p)
    · have hg : c.goal = .plain c.row.result := by simp [CodeEntry.goal, hpr]
      rw [hg, CallEffects.Effect.result_none hpr]
      rfl
    · have hg : c.goal = .guards c.row.result (frameOffset c.store + p) := by
        simp [CodeEntry.goal, hpr]
      rw [hg]
      simp only [CallEffects.Effect.result, framePromised, hpr, CallEffects.TypePromise.result,
        CallEffects.TypePromise.param]
      rfl
    · have hg : c.goal = .asserts c.row.result (frameOffset c.store + p) := by
        simp [CodeEntry.goal, hpr]
      rw [hg]
      simp only [CallEffects.Effect.result, framePromised, hpr, CallEffects.TypePromise.result,
        CallEffects.TypePromise.param]
      rfl
  have hsafe : Safe (excOf (reassign G η)) (c.row.effect.result (meaning (reassign G η) c.row.result)
      (framePromised c.row.effect (frameOffset c.store) L)) n W heap
      (.goto c.exprs c.conts c.start L .nul) := hres ▸ hs
  rw [effectChecked_eq] at heff
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at heff
  obtain ⟨⟨hfo, hel⟩, heff⟩ := heff
  have hens := CallEffects.Effect.below_ensures hbelow
  have hnen : ∀ F, F ∈ c.row.effect.ensures → False := fun F hF => by rw [hens] at hF; cases hF
  have hnel : ∀ R, c.row.effect.elements = some R → False := by
    intro R hR
    simp only [Option.isNone_iff_eq_none] at hel
    rw [hel.2.1] at hR; cases hR
  have hngr : c.row.effect.receiverGrows = true → False := fun hg => by
    have := hel.2.2; rw [hg] at this; cases this
  by_cases htop : c.row.effect.footprint = .top ∧ c.row.effect.fresh = false ∧ c.row.effect.onThrow = false
  · -- No footprint on a throw: the throw's postcondition is vacuous.
    apply HeapObservations.SafePostExc.of_post (fun _ r h => absurd h (by simp [htop.2.2]))
    refine HeapObservations.weaken (fun h' v hp r args => ?_) (Footprints.Closed.top_safe hsafe)
    refine ⟨CallEffects.Effect.within_of_holds ?_, fun hf => (by rw [htop.2.1] at hf; cases hf),
      fun hf => (by rw [hfo] at hf; cases hf), fun R hR => (hnel R hR).elim, fun F hF => (hnen F hF).elim,
      fun hg => (hngr hg).elim⟩
    rw [htop.1]
    exact hp
  · simp only [htop, decide_false, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at heff
    rcases heff with hp | hp
    · simp only [Bool.not_eq_true'] at hp
      have hfresh := hp.1
      have hp : ∀ e ∈ c.exprs, Purity.pureTerm e = true := List.all_eq_true.mp hp.2
      exact HeapObservations.SafePostExc.weaken
        (fun h' v hq r _ => ⟨CallEffects.Effect.within_of_holds
          (Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _)
            ((CallEffects.Effect.post_ofFootprint _ .undef [] _ _ _).mp hq)), fun hf => (by rw [hfresh] at hf; cases hf),
          fun hf => (by rw [hfo] at hf; cases hf), fun R hR => (hnel R hR).elim, fun F hF => (hnen F hF).elim,
      fun hg => (hngr hg).elim⟩)
        (fun h' hq r _ => CallEffects.Effect.within_of_holds
          (Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _) hq))
        (CallEffects.pure_safe_exc (r := .undef) (args := []) (.goto hp hvalues rfl) hsafe)
    · rw [← compositionalChecked_reassign G images sums η, compositionalChecked_eq] at hp
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hp
      have hgraph : checkGraphUsing (sums := sums) (reassign G η) (images.reassign η) c.goal
          (program c.exprs c.conts) C (admits table) = true := by
        have hchecked := hc
        simp only [checkEntryUsing_eq, Bool.and_eq_true] at hchecked
        exact hchecked.1
      have hb := goto_bounded hc ht hs' (nodes_of_checked hgraph ht hs' hp.2) hp.1 n W heap L .nul he hw hh
        (hidx := hidx)
      rw [hres] at hb
      exact HeapObservations.SafePostExc.weaken
        (fun h' v hq r _ => ⟨CallEffects.Effect.within_of_holds hq.1, hq.2, fun hf => (by rw [hfo] at hf; cases hf),
          fun R hR => (hnel R hR).elim, fun F hF => (hnen F hF).elim,
      fun hg => (hngr hg).elim⟩)
        (fun h' hq r ho => CallEffects.Effect.within_of_holds (hq ho)) hb

/-- Check codes in order, each against the table of those before it. -/
@[nospecialize] def extendTableResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι)) :
    List (CodeEntry ι) → List (CodeEntry ι × ControlFlow.Certificate ι) →
      ProgramCertificates.CheckResult ι (List (CodeEntry ι))
  | table, [] => pure table
  | table, (c, C) :: rest =>
      ((codeCheckedResult G images sums table c C).at (.code table.length)).bind fun _ => extendTableResult G images sums (table ++ [c]) rest

@[nospecialize] def extendTable [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (table : List (CodeEntry ι)) (checks : List (CodeEntry ι × ControlFlow.Certificate ι)) :
    Option (List (CodeEntry ι)) :=
  (extendTableResult G images sums table checks).value

theorem extendTable_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (table : List (CodeEntry ι)) (checks : List (CodeEntry ι × ControlFlow.Certificate ι)) :
    extendTable G images sums table checks = match checks with
    | [] => some table
    | (c, C) :: rest =>
        if codeCheckedUsing G images sums table c C then extendTable G images sums (table ++ [c]) rest else none := by
  cases checks with
  | nil => rfl
  | cons pair rest =>
    rcases pair with ⟨c, C⟩
    rw [extendTable, extendTableResult, ProgramCertificates.CheckResult.value_bind_const]
    rfl

theorem extendTable_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)} :
    ProgramCertificates.SummariesSound G images sums →
    ∀ {table checks result}, ProgramCertificates.CodesSound G (admits table) →
      extendTable G images sums table checks = some result →
      ProgramCertificates.CodesSound G (admits result)
  | _, table, [], result, ht, h => by
    rw [extendTable_eq] at h
    simp only [Option.some.injEq] at h; subst h; exact ht
  | hsums, table, (c, C) :: rest, result, ht, h => by
    rw [extendTable_eq] at h
    dsimp only at h
    split at h
    · rename_i hc
      apply extendTable_sound hsums _ h
      intro e he
      simp only [admits, List.contains_append, Bool.or_eq_true, List.contains_cons,
        List.contains_nil, Bool.or_false, beq_iff_eq] at he
      rcases he with he | rfl
      · exact ht e he
      · exact codeChecked_sound ht hsums hc
    · contradiction

/-- A unit's codes, checked from the empty table. -/
@[nospecialize] def checkCodesResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (checks : List (CodeEntry ι × ControlFlow.Certificate ι)) :
    ProgramCertificates.CheckResult ι (List (CodeEntry ι)) :=
  extendTableResult G images sums [] checks

@[nospecialize] def checkCodesUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι))
    (checks : List (CodeEntry ι × ControlFlow.Certificate ι)) : Option (List (CodeEntry ι)) :=
  (checkCodesResult G images sums checks).value

/-- A checked table is sound at every reassignment of the graph's parameter
rows, since `CodesSound` quantifies over all of them. -/
theorem checkCodes_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {checks table} (hsums : ProgramCertificates.SummariesSound G images sums)
    (h : checkCodesUsing G images sums checks = some table) :
    ProgramCertificates.CodesSound G (admits table) :=
  extendTable_sound hsums (fun c hc => by simp [admits] at hc) h

/-! ### A node's referenced derivation

The footprint inspection of calls, throws and fresh results reads a node
referencing its step's proof, or stating only its sequent, as the node with
that derivation written out (`NodeEvidence.explicit`), as the graph check
does (`ControlFlow.checkGraphResult_explicit`). -/

section
variable [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
  (c : NodeEvidence ι)

theorem nodeChecked_explicit (Φ : Footprints.Closed) (facts : List (List Nat)) (dead : List Bool) (ret exc : Bool)
    (l : Nat) (node : Node) :
    nodeChecked G images sums Φ facts dead ret exc l node c.explicit = nodeChecked G images sums Φ facts dead ret exc l node c := rfl

theorem callFresh_explicit (t : Tm) : callFresh G images sums c.explicit t = callFresh G images sums c t := rfl

theorem throwsWithin_explicit (Φ : Footprints.Closed) (F : List Nat) (t : Tm) :
    throwsWithin G images sums Φ F c.explicit t = throwsWithin G images sums Φ F c t := rfl

end

end Verification.GraphCode
