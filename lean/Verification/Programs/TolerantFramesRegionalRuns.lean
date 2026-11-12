import Verification.Programs.TolerantFramesRegionalNode
import Verification.Programs.TolerantFramesGuarantee

/-! # Tolerant frames: the regional check kept along a run

`RegionsKept` (`TolerantFramesGuarantee`) asks each node to keep regional
facts `X` along every run of its term. The facts are the graph's tables at
the node's label holding (`ArgumentRegionGraph.LabelHolds`) and the regions
within the stated bound from the invocation's entry (`RegionX`), as
`ArgumentRegionGraph.bounded_step` carries them for the certificate checker.
A node's regional obligation (`NodeWithinAt`, from `checkNode_sound`) also
reads the traversed fields fixed in the current world
(`ArgumentPathTracking.StableNow`), which `X` (a property of the
environment and heap) cannot state: the node assertion carries it
(`passPreS`), every admissible transition keeps it, and the walk's
theorems hold at that assertion (`nodesChecked_stable`,
`regionally_of_walk_stable`). Proved: `regionsKept_of` (the composition at
every visited node), `regionalTyped_of_tree` (the node's typing from the
derivation's tree check), `regionNodeEntry_of` (the entry's typing, its
implications and facts from the node assertion). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules
open GraphCode GraphCode.ArgumentRegionGraph

section Regional
variable {ι : Type}

/-- **The regional facts at a node entry**: the regions within `Φ` from the
invocation's entry heap `h₀` at the entry values `ρ0`, and the graph's
tables at the label holding. -/
def RegionX (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (ft : ArgumentRegionFresh.FreshTables) (ρ0 : Env) (h₀ : Heap) :
    Nat → Env → Heap → Prop :=
  fun l ρ h => ArgumentStoreRegionsWithin Φ regions ρ0 h₀ h ∧ LabelHolds table ft l ρ ρ0 h₀ h

/-- **The node assertion with the traversed fields fixed**: `passPreT` and
the regions' single-field paths of the entry values fixed in the current
world (`StableNow`), the premise every node's regional obligation reads. -/
def passPreS (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env) (ctx : Nat → List (Ty ι))
    (regions : List ArgumentStoreRegion) (h₀ : Heap) : Nat → Assertion :=
  fun l ρ m s => passPreT G w startNames ρ0 ctx l ρ m s ∧
    ArgumentPathTracking.StableNow (ArgumentPathTracking.stableFields regions) ρ0 h₀ s.W

/-- **(Named hypothesis) The regional check keeps its facts, at the
assertion with the fields fixed**: `RegionsKept` at `passPreS`. -/
def RegionsKeptS (P : Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (ctx : Nat → List (Ty ι)) (X : Nat → Env → Heap → Prop) (Φ : Footprints.Closed)
    (regions : List ArgumentStoreRegion) (h₀ : Heap) (exc : Bool) : Prop :=
  NodesKeep P (passPreS G w startNames ρ0 ctx regions h₀) X (RegionQ Φ regions ρ0 h₀)
    (RegionR Φ regions ρ0 h₀ exc) h₀.length

/-- **(Named hypothesis) The node's typing at the regional check's
evidence** (`ExpressionOk`): every environment meeting the evidence's
context, implications and facts runs the node's term safely at the
evidence's result type. -/
def RegionalTyped [DecidableEq ι] (G : NormalGraph ι) (c : NodeEvidence ι) (node : Node) : Prop :=
  ExpressionOk G c node.expression

/-- **What the run checks at a visited node under a regional check**: the
node, the evidence `run` checks it at (`cEv`), the node's regional
obligation over the graph's tables, and the evidence's entry (context,
implications, facts) holding where the node assertion does. -/
structure RegionNodeOk [DecidableEq ι] (G : NormalGraph ι) (P : Program) (w : Walk ι) (startNames : List Nat)
    (ρ0 : Env) (ctx : Nat → List (Ty ι)) (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (ft : ArgumentRegionFresh.FreshTables) (exc : Bool) (m : Nat)
    (l : Nat) where
  node : Node
  hP : P[l]? = some node
  c : NodeEvidence ι
  within : NodeWithinAt G Φ regions table ft exc l node c
  entry : ∀ ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s →
    EnvOk G (ControlFlow.entry c) ρ s.n s.W ∧ PromiseCalls.ImpliesOk G c.implies ρ s.n s.W ∧
      HeapKnowledge.Holds (entryFacts G c) ρ s.h

/-- **A node the run checks under a regional check meets `RegionNodeOk`**:
the check over the node's own tables `T`, `ft` (`SinglePass.run`, the
regional check), those tables agreeing with the graph's (`TablesAgree`),
the evidence typed (`RegionalTyped`), the summaries checked and the
evidence's entry holding where the node assertion does. -/
def RegionNodeOk.ofCheck [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {sums : List (ReadSummary ι)}
    {P : Program} {w : Walk ι} {startNames : List Nat} {ρ0 : Env} {ctx : Nat → List (Ty ι)}
    {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion}
    {T table : List (List ArgumentPathTracking.Fact)} {ft ft' : ArgumentRegionFresh.FreshTables} {exc : Bool}
    {m l : Nat} {node : Node} (hP : P[l]? = some node) {c : NodeEvidence ι}
    (hc : checkNode G images sums Φ regions T ft exc l node c = true) (ha : TablesAgree T table ft ft' l node)
    (ht : RegionalTyped G c node) (hsums : SummariesSound G images sums)
    (hentry : ∀ ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s →
      EnvOk G (ControlFlow.entry c) ρ s.n s.W ∧ PromiseCalls.ImpliesOk G c.implies ρ s.n s.W ∧
        HeapKnowledge.Holds (entryFacts G c) ρ s.h) :
    RegionNodeOk G P w startNames ρ0 ctx Φ regions table ft' exc m l :=
  ⟨node, hP, c, checkNode_sound (checkNode_mono ha hc) ht hsums, hentry⟩

/-- **A continuation's obligation from the targets' tables**: the regions
within and every successor's tables holding at its environment give
`ContKeeps` of `RegionX`. -/
theorem contKeeps_regionX {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion}
    {table : List (List ArgumentPathTracking.Fact)} {ft : ArgumentRegionFresh.FreshTables} {ρ0 : Env} {h₀ : Heap}
    {ρ : Env} {v : Tm} {h : Heap} {k : Continuation}
    (hw : ArgumentStoreRegionsWithin Φ regions ρ0 h₀ h)
    (ht : ∀ target ∈ successors k, LabelHolds table ft target.label
      (PointClaims.mapEnv target.mapping (if pushes k then push v ρ else ρ)) ρ0 h₀ h) :
    ContKeeps (RegionX Φ regions table ft ρ0 h₀) (RegionQ Φ regions ρ0 h₀) ρ v h k := by
  cases k with
  | ret => exact hw
  | bind t => exact ⟨hw, by simpa [pushes] using ht t (by simp [successors])⟩
  | effect t => exact ⟨hw, by simpa [pushes] using ht t (by simp [successors])⟩
  | branch y n =>
    exact ⟨fun _ => ⟨hw, by simpa [pushes] using ht y (by simp [successors])⟩,
      fun _ => ⟨hw, by simpa [pushes] using ht n (by simp [successors])⟩⟩
  | branchBind y n =>
    exact ⟨fun hv => ⟨hw, by subst hv; simpa [pushes] using ht y (by simp [successors])⟩,
      fun hv => ⟨hw, by subst hv; simpa [pushes] using ht n (by simp [successors])⟩⟩
  | tagBind tg y n =>
    simp only [ContKeeps]
    split
    · exact ⟨hw, by simpa [pushes] using ht y (by simp [successors])⟩
    · exact ⟨hw, by simpa [pushes] using ht n (by simp [successors])⟩

variable [DecidableEq ι]

/-- **The regional check is kept at every visited node**: where the run
checks every visited node (`RegionNodeOk`), each node keeps `RegionX` from
`passPreS` (`RegionsKeptS`): the node's regional obligation at the entry
state gives the regions within and the targets' tables on every exit
(`checkEdges_sound`, `edgesFresh_holds`, `edgesFields_holds`), and on a
throw the handler's tables (`checkHandler_sound`, `handlerFresh_holds`,
`handlerFields_holds`) or, escaping, the regions within where the bound
covers throws. -/
theorem regionsKept_of {P : Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion}
    {table : List (List ArgumentPathTracking.Fact)} {ft : ArgumentRegionFresh.FreshTables} {exc : Bool}
    {h₀ : Heap}
    (hacc : ∀ l, w.visited l →
      Nonempty (RegionNodeOk G P w startNames ρ0 ctx Φ regions table ft exc h₀.length l)) :
    RegionsKeptS P G w startNames ρ0 ctx (RegionX Φ regions table ft ρ0 h₀) Φ regions h₀ exc := by
  intro l ρ s ⟨hpT, hst⟩ hX
  obtain ⟨na⟩ := hacc l hpT.1.1
  refine ⟨na.node, na.hP, ?_⟩
  obtain ⟨he, hi, hk⟩ := na.entry ρ s hpT
  obtain ⟨origins, outF, outC, outFs, ht, hedge, hhandler, hfr, hef, hec, hfl, hefl, hhf⟩ := na.within
  have hrun := ht s.n s.W s.h ρ h₀ ρ0 hX.1 hX.2.1 hX.2.2.1.values hX.2.2.2 he hi hk s.adm s.ok (fun _ => hst)
  have hfresh := hfr s.n s.W s.h ρ h₀.length (ArgumentStoreRegionsWithin.iff_post.mp hX.1).1 hX.2.2.1 he hi hk
    s.adm s.ok
  have hfld := hfl s.n s.W s.h ρ h₀.length (ArgumentStoreRegionsWithin.iff_post.mp hX.1).1 hX.2.2.1.values
    hX.2.2.2 he hi hk s.adm s.ok
  have hboth0 := SafePostExc.cross_upto s.n (fun _ _ _ _ _ _ _ _ hu _ => hu) _ _ s.h _ s.ok s.ok hrun hfresh
  have hboth := SafePostExc.cross_upto s.n (fun _ _ _ _ _ _ _ _ hu _ => hu) _ _ s.h _ s.ok s.ok hboth0 hfld
  have hret : ReturnsPost (fun h' v => ArgumentStoreRegionsWithin Φ regions ρ0 h₀ h' ∧
      ∀ target ∈ successors na.node.continuation, LabelHolds table ft target.label
        (PointClaims.mapEnv target.mapping (if pushes na.node.continuation then push v ρ else ρ)) ρ0 h₀ h')
      s.n s.h (instantiate 0 ρ na.node.expression) := returnsPost_of_safePost (HeapObservations.weaken
    (fun _ _ post => ⟨post.1.1.1, fun target htarget =>
      ⟨ArgumentPathTracking.checkEdges_sound hedge hX.2.1 post.1.1.2 target htarget,
        ⟨edgesFresh_holds hef hX.2.2.1.values post.1.2.1 target htarget,
          edgesFresh_holds hec post.1.2.2.2 post.1.2.2.1 target htarget⟩,
        edgesFields_holds hefl post.2.1 post.2.2 target htarget⟩⟩) hboth.post)
  intro j h' t' hs hj
  refine ⟨fun hv => ?_, fun e hr => ?_⟩
  · obtain ⟨hw, htg⟩ := hret j h' t' hj hs hv
    exact contKeeps_regionX hw htg
  · have hr' := raisesPost_of_safePostExc hboth j h' t' e hj hs hr
    cases hk' : na.node.handler with
    | none => exact fun hexc => hr'.1.1 (by simp [hk', hexc])
    | some target =>
      have hcells := hr'.1.2 (by simp [hk'])
      obtain ⟨hhv, hhc, hhfl⟩ := hhf target hk'
      exact ⟨hr'.1.1 (by simp [hk']), ArgumentPathTracking.checkHandler_sound hhandler hX.2.1 target hk' e,
        ⟨handlerFresh_holds hhv hX.2.2.1.values e, handlerFresh_holds hhc hcells e⟩,
        handlerFields_holds hhfl hr'.2 e⟩

/-! ## The evidence the run checks at a node -/

/-- The evidence `run` checks a node's regional obligation at
(`SinglePass.run`, `cEv`): the step's derivation as the ordinary evidence,
or its step evidence, the node's sequent, the entry's facts `kHere`. -/
def passRegionalEvidence (c : PointClaim ι) (node : Node) (stepDeriv : Option (ProgramCertificates.Evidence ι))
    (stepEffect : Option (HeapExpressionRules.StepEvidence ι)) (kHere : HeapKnowledge.Knowledge) : NodeEvidence ι :=
  let ordinaryEv : Option (OrdinaryEvidence ι) := match stepDeriv, stepEffect with
    | some d, _ => some (.proof d)
    | none, some _ => some .effect
    | none, none => none
  ⟨ordinaryEv, some ⟨c.context, node.expression, c.type⟩, [], kHere, stepEffect, {}, none, [], [], [], none⟩

/-- The check of the step's derivation the regional evidence needs: claimed
at the node's term and context, its tree accepted (`passDerivChecked`'s
conjuncts, its tree disjunct). -/
def regionalDerivChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (d : ProgramCertificates.Evidence ι) : Bool :=
  (claim d).term == node.expression && (claim d).context == c.context && checkTreeUsing G images d codes sums

/-- **The derivation's tree check gives the regional evidence's typing**
(`RegionalTyped`): with the step's derivation `d` accepted by
`regionalDerivChecked`, the evidence's entry is the node's context and
every environment it types runs the node's term at `d`'s type. -/
theorem regionalTyped_of_tree {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {c : PointClaim ι} {node : Node} {d : ProgramCertificates.Evidence ι}
    {se : Option (HeapExpressionRules.StepEvidence ι)} {kHere : HeapKnowledge.Knowledge}
    (hd : regionalDerivChecked G images codes sums c node d = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) :
    ControlFlow.entry (passRegionalEvidence c node (some d) se kHere) = c.context ∧
      RegionalTyped G (passRegionalEvidence c node (some d) se kHere) node := by
  simp only [regionalDerivChecked, Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨hterm, hctx⟩, htree⟩ := hd
  refine ⟨by simpa [ControlFlow.entry, passRegionalEvidence, NodeEvidence.expression] using hctx, ?_⟩
  intro n W h ρ he _ _ hw hh
  have hs := HasTyUsing.sound (checkTreeUsing_sound d htree hcodes hsums) n W h ρ
    (by simpa [ControlFlow.entry, passRegionalEvidence, NodeEvidence.expression] using he) hw hh
  rw [hterm] at hs
  have hs' : Safe (excOf G) (fun k U u => meaning G (result (passRegionalEvidence c node (some d) se kHere)) k U u ∧
      PromiseCalls.YieldsOk G (passRegionalEvidence c node (some d) se kHere).yields ρ k U u) n W h
      (instantiate 0 ρ node.expression) :=
    Safe_mono n (fun _ _ _ v hv => ⟨by simpa [result, passRegionalEvidence, NodeEvidence.expression] using hv,
      fun y hy => by simp [passRegionalEvidence] at hy⟩) W h _ hs
  exact of_value_property (fun _ _ _ v _ => outFacts_holds he (HeapKnowledge.empty _ _))
    hs'

/-- **A copy's regional evidence is typed** (`RegionalTyped`), its step
having no derivation and no step evidence (`stepDeriv`, `stepEffect` none): where the term is a slot `i` whose context type is the
claim's (`copiedOf`), at every environment the context types the term's
value is the slot's, of the claim's type, with no yields and no output
facts. -/
theorem regionalTyped_copy {G : NormalGraph ι} {c : PointClaim ι} {node : Node}
    {kHere : HeapKnowledge.Knowledge} {i : Nat} (hi : node.expression = .var i)
    (hty : c.context[i]? = some c.type) :
    ControlFlow.entry (passRegionalEvidence c node none none kHere) = c.context ∧
      RegionalTyped G (passRegionalEvidence c node none none kHere) node := by
  have hent : ControlFlow.entry (passRegionalEvidence c node none none kHere) = c.context := by
    simp [ControlFlow.entry, passRegionalEvidence, NodeEvidence.expression, NodeEvidence.header, claim]
  refine ⟨hent, ?_⟩
  intro n W h ρ he _ _ _ _
  rw [hent] at he
  have hval : instantiate 0 ρ node.expression = ρ i := by rw [hi]; simp [instantiate]
  rw [hval]
  have hm := he.2 i c.type hty
  exact HeapObservations.value (meaning_value hm).1
    ⟨by simpa [result, passRegionalEvidence, NodeEvidence.expression, NodeEvidence.header, claim] using hm,
      fun y hy => by simp [passRegionalEvidence] at hy⟩
    (outFacts_holds (hent ▸ he) (HeapKnowledge.empty _ _))

omit [DecidableEq ι] in
/-- **The regional evidence's entry holds where the node assertion does**:
its context the node's (`hent`, which `regionalTyped_of_tree` gives), no
implications, and its facts the entry state's materialization, which holds
where the entry state does (`stateHolds_materialize_whole`). -/
theorem regionNodeEntry_of [Hashable ι] {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {ctx : Nat → List (Ty ι)} {m l : Nat} {c : PointClaim ι} {node : Node} {entry : SinglePass.State}
    {sd : Option (ProgramCertificates.Evidence ι)} {se : Option (HeapExpressionRules.StepEvidence ι)}
    (hctx : ctx l = c.context)
    (hstated : ∀ ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s →
      StateHolds G entry (w.implies l) startNames ρ0 ρ m s)
    (hent : ControlFlow.entry (passRegionalEvidence c node sd se
      (SinglePass.materialize entry c.context.length (List.range c.context.length) true).1) = c.context)
    (ρ : Env) (s : IndexedHeap) (hp : passPreT G w startNames ρ0 ctx l ρ m s) :
    let cEv := passRegionalEvidence c node sd se
      (SinglePass.materialize entry c.context.length (List.range c.context.length) true).1
    EnvOk G (ControlFlow.entry cEv) ρ s.n s.W ∧ PromiseCalls.ImpliesOk G cEv.implies ρ s.n s.W ∧
      HeapKnowledge.Holds (entryFacts G cEv) ρ s.h := by
  intro cEv
  have he : EnvOk G (ControlFlow.entry cEv) ρ s.n s.W := by rw [hent, ← hctx]; exact hp.2
  refine ⟨he, PromiseCalls.ImpliesOk.nil G ρ s.n s.W, entryFacts_holds he ?_⟩
  exact stateHolds_materialize_whole (hstated ρ s hp) _ _ true

/-- **The start's regional facts**: where the start's table holds each
region's own position (`checkEntry`) and no fresh value, cell or field, the
regional facts hold at the entry values and heap. -/
theorem regionX_start {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion}
    {table : List (List ArgumentPathTracking.Fact)} {ft : ArgumentRegionFresh.FreshTables} {start : Nat}
    (hstart : ArgumentPathTracking.checkEntry (ArgumentPathTracking.atLabel table start) = true)
    (hfresh : ((factsAt ft.values start).isEmpty && (factsAt ft.cells start).isEmpty) = true)
    (hfieldStart : (fieldsAt ft.fields start).isEmpty = true) (ρ0 : Env) (h₀ : Heap) :
    RegionX Φ regions table ft ρ0 h₀ start ρ0 h₀ := by
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hfresh
  simp only [List.isEmpty_iff] at hfieldStart
  refine ⟨(Footprints.Closed.Holds.refl Φ h₀).on _, ArgumentPathTracking.checkEntry_sound hstart _ _, ⟨?_, ?_⟩, ?_⟩
  · intro i hi; rw [hfresh.1] at hi; cases hi
  · intro i hi; rw [hfresh.2] at hi; cases hi
  · intro p hp; rw [hfieldStart] at hp; cases hp

/-! ## The walk at the assertion with the fields fixed -/

omit [DecidableEq ι] in
/-- **A property every admissible transition keeps joins the node
obligations**: where each node meets its obligations from `pre` and `S`
holds at its entry state, it meets them with targets `pre ∧ S`. -/
theorem nodesChecked_stable {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop}
    {m : Nat} {S : IndexedHeap → Prop} (hS : ∀ s s', Admissible s s' → S s → S s')
    (hn : NodesChecked P pre Ξres Tres Qres Rres m) :
    NodesChecked P (fun l ρ m s => pre l ρ m s ∧ S s) Ξres Tres Qres Rres m := by
  intro l ρ s ⟨hp, hs⟩
  obtain ⟨node, hP, Ξ, T, cn, ce, Qn, Qe, hsafe, ho⟩ := hn l ρ s hp
  refine ⟨node, hP, Ξ, T, cn, ce, Qn, Qe, hsafe, ⟨ho.shape, fun s' v ha hv hT hq => ?_, fun s' e ha hsc hΞ hq => ?_⟩⟩
  · have ht := ho.normal s' v ha hv hT hq
    have hs' := hS s s' ha.1 hs
    cases hk : node.continuation <;> rw [hk] at ht
    · exact ht
    · exact ⟨ht, hs'⟩
    · exact ⟨ht, hs'⟩
    · exact ht.imp (fun h => ⟨h.1, h.2, hs'⟩) (fun h => ⟨h.1, h.2, hs'⟩)
    · exact ht.imp (fun h => ⟨h.1, h.2, hs'⟩) (fun h => ⟨h.1, h.2, hs'⟩)
    · exact ht.imp (fun h => ⟨h.1, h.2, hs'⟩) (fun h => ⟨h.1, h.2, hs'⟩)
  · have ht := ho.raise s' e ha hsc hΞ hq
    cases hx : node.handler <;> rw [hx] at ht
    · exact ht
    · exact ⟨ht, hS s s' ha.1 hs⟩

theorem stableNow_admissible {regions : List ArgumentStoreRegion} {ρ0 : Env} {h₀ : Heap} {s s' : IndexedHeap}
    (ha : Admissible s s') (hs : ArgumentPathTracking.StableNow (ArgumentPathTracking.stableFields regions) ρ0 h₀ s.W) :
    ArgumentPathTracking.StableNow (ArgumentPathTracking.stableFields regions) ρ0 h₀ s'.W :=
  hs.transfer ha.1 ha.2

end Regional

end Verification.TolerantFrames
