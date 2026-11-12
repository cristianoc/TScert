import Verification.Programs.TolerantFramesComposeRunSound
import Verification.Programs.TolerantFramesRegionalFacts

/-! # Regional checks and typing at checked nodes

`RegionsRecorded` supplies graph tables agreeing with each node's checked
tables. `RegionsTyped` supplies the regional evidence's typing. Their
composition is `regionsHeld_of`. The evidence uses `regionalFacts kHere
stepK`, whose meaning follows from the node's entry state and checked step
(`regionNodeEntry_checked`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore
open GraphCode GraphCode.ArgumentRegionGraph

section Reassign
variable {ι : Type} [DecidableEq ι]

/-- **The regional check of one node at a reassignment** (as
`checkNodes_reassign` for the graph). -/
theorem checkNode_reassign (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι)) (η : MixedAssignment ι) (Φ : Footprints.Closed)
    (regions : List ArgumentStoreRegion) (table : List (List ArgumentPathTracking.Fact))
    (ft : ArgumentRegionFresh.FreshTables) (exc : Bool) (l : Nat) (node : Node) (c : NodeEvidence ι) :
    checkNode (reassign G η) (images.reassign η) sums Φ regions table ft exc l node c =
      checkNode G images sums Φ regions table ft exc l node c := by
  simp only [checkNode, stepEffects, callStep, checkClosedNode, checkRead, throwsWithin,
    checkFresh, cellsKept, freshOut, callFresh,
    Parametricity.checkTree_reassign, entryFacts_reassign, Parametricity.requiresTree_reassign,
    ExpressionEffects.emptyType]
  rfl

/-- **The regional derivation check at a reassignment.** -/
theorem regionalDerivChecked_reassign (G : NormalGraph ι) (η : MixedAssignment ι) (images : InstanceImageCheck G)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node)
    (stepK : HeapKnowledge.Knowledge) (deriv : Option (ProgramCertificates.Evidence ι)) :
    regionalDerivChecked (reassign G η) (images.reassign η) codes sums c node stepK deriv =
      regionalDerivChecked G images codes sums c node stepK deriv := by
  cases deriv with
  | none => rfl
  | some d => exact derivChecked_reassign G η images codes sums c node stepK d

end Reassign

section Held
variable {ι : Type} [Labels ι]

/-- **The evidence `run` checks a visited node's regional obligation at**:
`passRegionalEvidence` at the node's claim, its step's derivation and step
evidence, and `regionalFacts` of the entry materialization and step knowledge. -/
def passRegionalEvidenceOf {G : NormalGraph ι} {I : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G I} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {l : Nat} (r : NodeChecked G I codes pc P w startNames ctx l) : NodeEvidence ι :=
  passRegionalEvidence r.c r.node r.st.stepDeriv r.st.stepEffect
    (regionalFacts (SinglePass.materialize r.entry r.c.context.length (List.range r.c.context.length) true).1 r.st.stepK)

/-- A checked node supplies both sources of its regional entry knowledge. -/
theorem regionNodeEntry_checked {G : NormalGraph ι} {I : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G I} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {l : Nat} (r : NodeChecked G I codes pc P w startNames ctx l)
    (hc : CodesSound G codes) {ρ0 : Env} {m : Nat}
    (hent : ControlFlow.entry (passRegionalEvidenceOf r) = r.c.context)
    (ρ : Env) (s : IndexedHeap) (hp : passPreT G w startNames ρ0 ctx l ρ m s) :
    EnvOk G (ControlFlow.entry (passRegionalEvidenceOf r)) ρ s.n s.W ∧
      PromiseCalls.ImpliesOk G (passRegionalEvidenceOf r).implies ρ s.n s.W ∧
      HeapKnowledge.Holds (entryFacts G (passRegionalEvidenceOf r)) ρ s.h := by
  have he : EnvOk G r.c.context ρ s.n s.W := r.hctx ▸ hp.2
  have hS : StateHolds G r.entry (w.implies l) startNames ρ0 ρ m s := r.hentry ▸ hp.1.2
  have hk := (stepChecked_parts r.hstep hS r.wf r.below r.width he hc r.sums).2.1
  refine ⟨hent ▸ he, PromiseCalls.ImpliesOk.nil G ρ s.n s.W, entryFacts_holds (hent ▸ he) ?_⟩
  exact regionalFacts_holds (stateHolds_materialize_whole hS _ _ true) hk

variable (ι) in
/-- The visits' regional checks over tables agreeing with the graph's,
with entry provenance and empty freshness at the start. -/
def RegionsRecorded : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r →
      ∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
        ∃ (table : List (List ArgumentPathTracking.Fact)) (ft : ArgumentRegionFresh.FreshTables),
          ArgumentPathTracking.checkEntry (ArgumentPathTracking.atLabel table c.start) = true ∧
          ((factsAt ft.values c.start).isEmpty && (factsAt ft.cells c.start).isEmpty) = true ∧
          (fieldsAt ft.fields c.start).isEmpty = true ∧
          ∀ l (hl : r.w.visited l), ∃ (T : List (List ArgumentPathTracking.Fact))
            (ftl : ArgumentRegionFresh.FreshTables) (sums : List (ReadSummary ι)),
            SummariesSound G I sums ∧
            checkNode G I sums Φ regions T ftl exc l (r.node l hl).node (passRegionalEvidenceOf (r.node l hl)) = true ∧
            TablesAgree T table ftl ft l (r.node l hl).node

variable (ι) in
/-- The regional evidence has the node's context and is typed at every
admitted reassignment. -/
def RegionsTyped : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, WalkChecked c r →
      ∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
        ∀ l (hl : r.w.visited l), ControlFlow.entry (passRegionalEvidenceOf (r.node l hl)) = (r.node l hl).c.context ∧
          ∀ η, admits η → RegionalTyped (reassign G η) (passRegionalEvidenceOf (r.node l hl)) (r.node l hl).node

/-- **The regional evidence typed where the step's derivation passes its
tree check** (`regionalTyped_of_tree` at every reassigned graph): a node
whose step has a derivation `d` the regional derivation check accepts and
whose tree `checkTreeUsing` accepts over a sound summary table meets
`RegionsTyped`'s statement. -/
theorem regionsTyped_of_tree {G : NormalGraph ι} {I : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {pc : PassChecker G I} {P : ControlFlow.Program} {w : Walk ι} {startNames : List Nat}
    {ctx : Nat → List (Ty ι)} {l : Nat} (r : NodeChecked G I codes pc P w startNames ctx l)
    {sums : List (ReadSummary ι)} {d : ProgramCertificates.Evidence ι} (hd : r.st.stepDeriv = some d)
    (hrd : regionalDerivChecked G I codes sums r.c r.node r.st.stepK r.st.stepDeriv = true)
    (htree : checkTreeUsing G I d codes sums = true) (hcodes : CodesSound G codes) (hsums : SummariesSound G I sums) :
    ControlFlow.entry (passRegionalEvidenceOf r) = r.c.context ∧
      ∀ η, RegionalTyped (reassign G η) (passRegionalEvidenceOf r) r.node := by
  unfold passRegionalEvidenceOf
  rw [hd] at hrd ⊢
  refine ⟨(regionalTyped_of_tree hrd htree hcodes hsums).1, fun η => ?_⟩
  have hrd' := (regionalDerivChecked_reassign G η I codes sums r.c r.node r.st.stepK (some d)).trans hrd
  have ht' : checkTreeUsing (reassign G η) (I.reassign η) d codes sums = true :=
    (Parametricity.checkTree_reassign G η I d codes sums).trans htree
  exact (regionalTyped_of_tree hrd' ht' (codesSound_reassign hcodes η)
    (Parametricity.summariesSound_reassign G η I hsums)).2

/-- **(`regionsHeld_of`) The regional premise from the visits' regional
checks** (`RegionsHeld`): the regional facts `RegionX` over the graph's
tables, holding at the start (`regionX_start`), kept at every visited node
(`regionsKept_of`) from `RegionNodeOk` there (`RegionNodeOk.ofCheck`: the
check at the reassigned graph, `checkNode_reassign`; the tables agreeing;
the evidence typed; the summary table sound there; the evidence's entry
facts holding where the node assertion does, `regionNodeEntry_of`). -/
theorem regionsHeld_of (hrec : RegionsRecorded ι) (htyped : RegionsTyped ι) : RegionsHeld ι := by
  intro G I c after admits hp r hchk η hη Φ regions exc hreg
  obtain ⟨table, ft, hs1, hs2, hs3, hnodes⟩ := hrec G I c after admits hp r hchk Φ regions exc hreg
  refine ⟨fun ρ0 h₀ => RegionX Φ regions table ft ρ0 h₀, fun ρ0 h₀ => ⟨regionX_start hs1 hs2 hs3 ρ0 h₀, ?_⟩⟩
  refine regionsKept_of fun l hl => ?_
  obtain ⟨T, ftl, sums, hsums, hc, ha⟩ := hnodes l hl
  obtain ⟨hent, hty⟩ := htyped G I c after admits hp r hchk Φ regions exc hreg l hl
  obtain ⟨pc', hpc'⟩ := scope_reassign hp.2.1 hη
  let rn := nodeChecked_reassign hpc' (r.node l hl)
  exact ⟨RegionNodeOk.ofCheck (r.node l hl).hP
    ((checkNode_reassign G I sums η Φ regions T ftl exc l _ _).trans hc) ha (hty η hη)
    (Parametricity.summariesSound_reassign G η I hsums)
    (regionNodeEntry_checked rn (codesSound_reassign hp.2.2.1 η) hent)⟩

end Held

end Verification.TolerantFrames
