import Verification.Programs.TolerantFramesGuaranteeTarget
import Verification.Programs.TolerantFramesWalkReassignWalk
import Verification.Programs.TolerantFramesComposeEdges

/-! # Tolerant frames: the graph theorem

`run_sound` proves the unit lane's `RunSound` (`TolerantFramesGuaranteeTarget`):
an accepted call of the pass, under its checker's scope, with sound codes
and the read summaries it leaves sound, guarantees `GraphGuarantee` of its
options at its inputs. Its premises are the named hypotheses of the
graph-level proof, each a definition below:

- `RunTraversed`: the driver's walk of an accepted call (`RunWalk`): every
  visited node checked with its searches as oracles (`NodeChecked`), the
  walk's construction (`Traversed`), each edge into a head recorded as the
  head's entry, and the start entered with its head entry;
- `NodesMean`: each visited node's step means at every admitted reassigned
  graph what it states (`NodeMeaning`: the stated assertion, the shapes, the
  return type, the exits, the handler);
- `LinearNearFuelEq`, `MergesEntailedChecked`, `MergesImpliesHold`: the
  merges' premises (`MergesSound`);
- `FootprintsKept`, `ReturnsKept`, `RegionsHeld`, `AssertionsKept`: the
  per-node hypotheses of the guarantee's other fields (`PassWalkSound`).

The proof carries each checked node to every admitted assignment
(`nodeChecked_reassign`, the checker there from `CheckerScope`:
`passCheckerReassign_ordinary`, `passCheckerReassign_lexical`), gives the
node obligations there (`stepEdgesSound_of_checked`), the heads entered
(`headsEntered_of_recorded`), the start entered (`start_passPreT`,
`start_entered_passPreT`), and assembles `GraphGuarantee`
(`run_guarantee`), restated in the unit lane's record
(`GraphGuarantee.toTarget`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules LabelStore

section Reach

/-- The unit lane's reachability is `Transitions`: the same constructors. -/
theorem transitions_of_reachesIn {P : Program} {k : Nat} {h h' : Heap} {s s' : State}
    (hr : Target.ReachesIn P k h s h' s') : Transitions P k h s h' s' := by
  induction hr with
  | refl => exact .refl
  | step ht _ ih => exact .next ht ih

end Reach

section Run
variable {ι : Type} [Labels ι]

omit [Labels ι] in
/-- **The guarantee in the unit lane's record**: the fields are the same
propositions, the reachability read as `Transitions`. -/
theorem GraphGuarantee.toTarget {G : NormalGraph ι} {admits : MixedAssignment ι → Prop} {P : Program}
    {start : Nat} {goal : Goal ι} {inputs : List (Ty ι)} {sep : HeapSeparation.Separation}
    {idx : List HeapKnowledge.IndexAtom} {assertions : List (Nat × HeapKnowledge.Knowledge)}
    {bound : Option (Footprints.Closed × Bool × Bool)} {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)}
    (g : GraphGuarantee G admits P start goal inputs sep idx assertions bound ensures regional) :
    Target.GraphGuarantee G admits P start goal inputs sep idx assertions bound ensures regional where
  safe := g.safe
  bounded := g.bounded
  ensured := g.ensured
  regionally := g.regionally
  asserted η hη n W h ρ he l k hl j h' ρ' hj hr := g.asserted η hη n W h ρ he l k hl j h' ρ' hj
    (transitions_of_reachesIn hr)

omit [Labels ι] in
/-- **A merge at a reassigned graph** is the merge at the graph: `mergeState`
reads the graph through no rule whose result depends on the assignment. -/
theorem mergeState_reassign [DecidableEq ι] [Hashable ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (context : List (Ty ι)) (preds : List SinglePass.State)
    (edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) (fresh : Nat) :
    SinglePass.mergeState (reassign G η) context preds edgesIn fresh = SinglePass.mergeState G context preds edgesIn fresh :=
  rfl

omit [Labels ι] in
/-- **The walk's construction at a reassigned graph**: `Traversed` reads the
graph only through `mergeState` (`mergeState_reassign`). -/
theorem Traversed.reassign [DecidableEq ι] [Hashable ι] {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} (h : Traversed G w startNames given ctx edgesIn fresh) (η : MixedAssignment ι) :
    Traversed (reassign G η) w startNames given ctx edgesIn fresh :=
  { h with merge := fun t hg h2 => by rw [mergeState_reassign]; exact h.merge t hg h2 }

/-- **A checker's scope gives the checker at each admitted assignment**:
the ordinary checker at every assignment (`passCheckerReassign_ordinary`);
a qualified body's at each instance its scope admits
(`passCheckerReassign_lexical`). -/
theorem scope_reassign {G : NormalGraph ι} {I : InstanceImageCheck G} {pc : SinglePass.PassChecker G I}
    {admits : MixedAssignment ι → Prop} (hs : Target.CheckerScope G I pc admits) {η : MixedAssignment ι}
    (hη : admits η) : ∃ pc' : SinglePass.PassChecker (reassign G η) (I.reassign η), PassCheckerReassign G η I pc pc' := by
  cases hs with
  | ordinary => exact ⟨_, passCheckerReassign_ordinary G η I⟩
  | qualified q =>
    obtain ⟨θ, As, hlen, hall, hb, rfl⟩ := hη
    exact passCheckerReassign_lexical q.source q.domain q.aliases q.aliases_sound q.body q.check_eq q.ordinary θ As
      hlen hall hb

/-- **The walk enters the start with its head entry**: the pass's entry
check accepts; the start is visited; its entry is `headEntry` over the
given invariant (`startGiven`), as the start (`isStart = true`) where no
edge enters it and as any head where one does (`reentered`, the counter at
or past the inputs' width); and its context is the inputs. -/
def StartEntered {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I) (w : Walk ι)
    (ctx : Nat → List (Ty ι)) : Prop :=
  ∃ (written : Option HeapKnowledge.Knowledge) (supplied : List HeapKnowledge.IndexAtom)
    (givenImplies : List (PromiseCalls.Implication ι)) (givenArgs : List Nat) (givenInputs : List (Nat × Nat))
    (fresh : Nat) (reentered : Bool),
    SinglePass.entryRefusal G c.inputs c.claims c.start c.goal written supplied givenImplies givenArgs givenInputs
      c.entryIndices c.entrySeparation = none ∧
    w.visited c.start ∧ (reentered = true → c.inputs.length ≤ fresh) ∧
    w.entry c.start = (SinglePass.headEntry (startGiven written c.entryIndices c.entrySeparation supplied) (!reentered)
      c.inputs.length fresh (List.range c.inputs.length) (c.goal.slot.bind ((List.range c.inputs.length)[·]?))
      givenArgs givenInputs givenImplies).1 ∧
    w.implies c.start = (SinglePass.headEntry (startGiven written c.entryIndices c.entrySeparation supplied)
      (!reentered) c.inputs.length fresh (List.range c.inputs.length)
      (c.goal.slot.bind ((List.range c.inputs.length)[·]?)) givenArgs givenInputs givenImplies).2.1 ∧
    ctx c.start = c.inputs

/-- **What the driver records of an accepted call** (`run_traversed`'s
conclusion): the walk, the label contexts, each merge's edges and fresh
counter, and each loop head (`given`); every visited node checked at `G`
with its searches as oracles; the walk's construction; each edge state
recorded into a head being the head's entry; the start entered. -/
structure RunWalk (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) where
  w : Walk ι
  given : Nat → Bool
  ctx : Nat → List (Ty ι)
  edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)
  fresh : Nat → Nat
  node : ∀ l, w.visited l → NodeChecked G I c.codes c.passChecker c.P w (List.range c.inputs.length) ctx l
  traversed : Traversed G w (List.range c.inputs.length) given ctx edgesIn fresh
  heads : ∀ t, given t = true → ∀ e ∈ w.incoming t, e = (w.entry t, w.implies t)
  start : StartEntered c w ctx

/-- The premises `RunSound` gives a call. -/
def RunPremises (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) (after : Answered G)
    (admits : MixedAssignment ι → Prop) : Prop :=
  c.Accepts after ∧ Target.CheckerScope G I c.passChecker admits ∧ CodesSound G c.codes ∧
    SummariesSound G I after.summaries.toList ∧
    (∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
      GraphCode.ArgumentPathTracking.checkEntryFields G c.inputs regions = true)

variable (ι) in
/-- **(Named hypothesis) The driver's walk** (`run_traversed`): an accepted
call whose final summaries are sound records a walk (`RunWalk`). -/
def RunTraversed : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) (after : Answered G),
    c.Accepts after → SummariesSound G I after.summaries.toList → Nonempty (RunWalk G I c)

variable (ι) in
/-- **(Named hypothesis) Each checked node means what it states** at every
admitted reassigned graph: from the checks the pass makes at the node and
on its edges (the exit lemmas `exitDelivers_of_edge`, `exitDelivers_head`,
`handlerDelivers_of_edge`, the shape check, the return check), the
stated assertion, the shapes, the return type, the exits and the handler
(`NodeMeaning`) at the goal's result type. -/
def NodesMean : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalk G I c, ∀ η, admits η → ∀ ρ0 m l (hl : r.w.visited l),
      NodeMeaning (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx
        (GoalHolds (reassign G η) c.goal (c.goal.argument ρ0)) m l (r.node l hl).node (r.node l hl).c
        (r.node l hl).entry (r.node l hl).st

variable (ι) in
/-- **(Named hypothesis) Every merge's entailed bounds pass the check**
(`EntailedChecked`) at every view. -/
def MergesEntailedChecked : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalk G I c, ∀ t, r.given t = false → 2 ≤ (r.w.incoming t).length →
      EntailedChecked ((r.w.incoming t).map (·.1)) (r.ctx t).length (r.fresh t)

variable (ι) in
/-- **(Named hypothesis) Every merge's joined implications hold** at every
admitted reassigned graph, wherever an edge state into the merge holds. -/
def MergesImpliesHold : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalk G I c, ∀ η, admits η →
      ∀ t, r.given t = false → 2 ≤ (r.w.incoming t).length →
      ∀ startNames ρ0 m ρ (s : IndexedHeap), edgePre (reassign G η) r.w startNames ρ0 t ρ m s →
        PromiseCalls.ImpliesOk (reassign G η)
          (CertificateProducer.meetImplications (reassign G η) (r.edgesIn t) (r.ctx t).length (r.ctx t)) ρ s.n s.W

variable (ι) in
/-- **(Named hypothesis) The footprint check keeps the bound** at every
admitted reassigned graph (`FootprintKept`). -/
def FootprintsKept : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalk G I c, ∀ η, admits η →
      ∀ Φ fr ex, c.bound = some (Φ, fr, ex) → ∃ dead, ∀ ρ0 h₀,
        FootprintKept c.P (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx Φ h₀ dead fr ex

variable (ι) in
/-- **(Named hypothesis) The return check establishes `ensures`** at every
admitted reassigned graph (`ReturnsEnsured`). -/
def ReturnsKept : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalk G I c, ∀ η, admits η →
      c.ensures ≠ [] → ∀ ρ0 m, ReturnsEnsured c.P (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx c.ensures m

variable (ι) in
/-- **(Named hypothesis) The regional check keeps its facts** at every
admitted reassigned graph (`RegionsKept`), its facts holding at the start. -/
def RegionsHeld : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalk G I c, ∀ η, admits η →
      ∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
        ∃ X : Env → Heap → Nat → Env → Heap → Prop, ∀ ρ0 h₀, X ρ0 h₀ c.start ρ0 h₀ ∧
          RegionsKept c.P (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx (X ρ0 h₀) Φ regions h₀ exc

variable (ι) in
/-- **(Named hypothesis) Each stated assertion holds** where the node
assertion at its label does, at every admitted reassigned graph
(`AssertionsHeld`). -/
def AssertionsKept : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalk G I c, ∀ η, admits η →
      ∀ ρ0 m, AssertionsHeld (reassign G η) r.w (List.range c.inputs.length) ρ0 r.ctx c.assertions m

/-- **The start entered at a reassigned graph**: the start's typed assertion
holds at every entry meeting the inputs, the separation and the index facts
(`start_passPreT` where no edge enters the start, `start_entered_passPreT`
where one does; the entry check is the same at `reassign G η`). -/
theorem StartEntered.entered {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I} {w : Walk ι}
    {ctx : Nat → List (Ty ι)} (h : StartEntered c w ctx) (η : MixedAssignment ι) :
    ∀ ρ m (s : IndexedHeap), EnvOk (reassign G η) c.inputs ρ s.n s.W → HeapSeparation.Holds c.entrySeparation ρ →
      HeapKnowledge.IndexHolds c.entryIndices ρ s.h →
      passPreT (reassign G η) w (List.range c.inputs.length) ρ ctx c.start ρ m s := by
  obtain ⟨written, supplied, givenImplies, givenArgs, givenInputs, fresh, reentered, hacc, hv, hfr, hentry, himp,
    hctx⟩ := h
  have hacc' := (entryRefusal_reassign G η c.inputs c.claims c.start c.goal written supplied givenImplies givenArgs
    givenInputs c.entryIndices c.entrySeparation).trans hacc
  intro ρ m s he hs hi
  cases reentered with
  | false => exact start_passPreT hacc' hv hentry himp hctx he hs hi
  | true => exact start_entered_passPreT hacc' hv (hfr rfl) hentry himp hctx he hs hi

/-- **THE GRAPH THEOREM** (`RunSound`, the unit lane's statement): from the
driver's walk (`RunTraversed`), the nodes' meaning at every admitted
reassigned graph (`NodesMean`), the merges' premises (`LinearNearFuelEq`,
`MergesEntailedChecked`, `MergesImpliesHold`) and the per-node hypotheses
of the guarantee's other fields (`FootprintsKept`, `ReturnsKept`,
`RegionsHeld`, `AssertionsKept`), an accepted call of the pass guarantees
`GraphGuarantee` of its options at its inputs. -/
theorem run_sound (hrun : RunTraversed ι) (hmean : NodesMean ι) (hnear : LinearNearFuelEq)
    (hent : MergesEntailedChecked ι) (himp : MergesImpliesHold ι) (hfoot : FootprintsKept ι) (hret : ReturnsKept ι)
    (hreg : RegionsHeld ι) (hasr : AssertionsKept ι) : Target.RunSound ι := by
  intro G I c after admits hacc hscope hcodes hsums hfields
  have hp : RunPremises G I c after admits := ⟨hacc, hscope, hcodes, hsums, hfields⟩
  obtain ⟨r⟩ := hrun G I c after hacc hsums
  refine GraphGuarantee.toTarget (run_guarantee fun η hη => ?_)
  obtain ⟨pc', hpc⟩ := scope_reassign hscope hη
  refine ⟨r.w, r.given, r.ctx, r.edgesIn, r.fresh,
    { walk := fun ρ0 m => ?_
      entered := r.start.entered η
      footprint := hfoot G I c after admits hp r η hη
      returns := hret G I c after admits hp r η hη
      regions := hreg G I c after admits hp r η hη
      asserted := hasr G I c after admits hp r η hη }⟩
  exact
    { traversed := r.traversed.reassign η
      steps := stepEdgesSound_of_checked
        (fun l hl => ⟨nodeChecked_reassign hpc (r.node l hl), hmean G I c after admits hp r η hη ρ0 m l hl⟩)
        (codesSound_reassign hcodes η)
      heads := headsEntered_of_recorded r.heads
      merges := ⟨hnear, fun t hg h2 => ⟨hent G I c after admits hp r t hg h2, himp G I c after admits hp r η hη t hg h2⟩⟩ }

end Run

end Verification.TolerantFrames
