import Verification.Programs.TolerantFramesGuaranteeTarget
import Verification.Programs.TolerantFramesWalkReassignWalk
import Verification.Programs.TolerantFramesComposeEdges
import Verification.Programs.TolerantFramesGuaranteeWalk
import Verification.Programs.TolerantFramesWalkJoined

/-! # Tolerant frames: the graph theorem

The driver's walk of an accepted call (`RunWalkA`): every visited node
checked with its searches as oracles (`NodeChecked`), the walk's
construction with each entry's written facts (`TraversedA`), each edge into
a head recorded as the head's entry, and the start entered with its head
entry (`StartEntered`, entered at every reassigned graph:
`StartEntered.entered`); the premises `RunSound` gives a call
(`RunPremises`); every assertion of the call the written assertion at its
label (`AssertionsLabelled`). The graph theorem over them is
`run_sound_pass` (`TolerantFramesComposeYields`). -/
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
check accepts, the start's written assertion `stated c.start`; the start is
visited; its entry is `headEntry` over the given invariant (`startGiven`),
as the start (`isStart = true`) where no edge enters it and as any head
where one does (`reentered`, the counter at or past the inputs' width); and
its context is the inputs. -/
def StartEntered {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I) (w : Walk ι)
    (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge) : Prop :=
  let written := stated c.start
  ∃ (supplied : List HeapKnowledge.IndexAtom)
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

/-- **What the driver records of an accepted call** (`run_traversedA`'s
conclusion): the walk, the loop heads (`given`), the label contexts, each
merge's edges and fresh counter, the written assertions by label (`stated`,
the table `runWalk` reads); every visited node checked at `G` with its
searches as oracles; the walk's construction with each entry's written
facts (`TraversedA`); each edge state into a head being the head's entry;
the start entered. -/
structure RunWalkA (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) where
  w : Walk ι
  given : Nat → Bool
  ctx : Nat → List (Ty ι)
  edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)
  fresh : Nat → Nat
  stated : Nat → Option HeapKnowledge.Knowledge
  node : ∀ l, w.visited l → NodeChecked G I c.codes c.passChecker c.P w (List.range c.inputs.length) ctx l
  traversed : TraversedA G w (List.range c.inputs.length) given ctx edgesIn fresh stated
  heads : ∀ t, given t = true → ∀ e ∈ w.incoming t, e = (w.entry t, w.implies t)
  start : StartEntered c w ctx stated
  /-- The written assertions by label are the table `runWalk` reads. -/
  stated_eq : ∀ t, stated t = (CertificateProducer.byLabel c.P.toArray.size c.assertions)[t]?.getD none

/-- The premises `RunSound` gives a call. -/
def RunPremises (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) (after : Answered G)
    (admits : MixedAssignment ι → Prop) : Prop :=
  c.Accepts after ∧ Target.CheckerScope G I c.passChecker admits ∧ CodesSound G c.codes ∧
    SummariesSound G I after.summaries.toList ∧
    (∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
      GraphCode.ArgumentPathTracking.checkEntryFields G c.inputs regions = true)

variable (ι) in
/-- **(Named hypothesis) The driver's walk** (`run_traversedA`): an accepted
call whose final summaries are sound records a walk (`RunWalkA`). -/
def RunTraversedA : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) (after : Answered G),
    c.Accepts after → SummariesSound G I after.summaries.toList → Nonempty (RunWalkA G I c)

variable (ι) in
/-- **(Named hypothesis) Every assertion of the call is the written
assertion at its label** (`stated`, the table `run` checks the edges
against). -/
def AssertionsLabelled : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) after admits,
    RunPremises G I c after admits → ∀ r : RunWalkA G I c, ∀ l k, (l, k) ∈ c.assertions → r.w.visited l →
      r.stated l = some k

/-- **The start entered at a reassigned graph**: the start's typed and
written assertion holds at every entry meeting the inputs, the separation
and the index facts (`start_passPreT` where no edge enters the start,
`start_entered_passPreT` where one does, `assertsAt_start`; the entry check
is the same at `reassign G η`). -/
theorem StartEntered.entered {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I} {w : Walk ι}
    {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge} (h : StartEntered c w ctx stated)
    (η : MixedAssignment ι) :
    ∀ ρ m (s : IndexedHeap), EnvOk (reassign G η) c.inputs ρ s.n s.W → HeapSeparation.Holds c.entrySeparation ρ →
      HeapKnowledge.IndexHolds c.entryIndices ρ s.h →
      passPreA (reassign G η) w (List.range c.inputs.length) ρ ctx stated c.start ρ m s := by
  obtain ⟨supplied, givenImplies, givenArgs, givenInputs, fresh, reentered, hacc, hv, hfr, hentry, himp,
    hctx⟩ := h
  have hacc' := (entryRefusal_reassign G η c.inputs c.claims c.start c.goal (stated c.start) supplied givenImplies
    givenArgs givenInputs c.entryIndices c.entrySeparation).trans hacc
  intro ρ m s he hs hi
  refine ⟨?_, assertsAt_start hacc' he hs hi⟩
  cases reentered with
  | false => exact start_passPreT hacc' hv hentry himp hctx he hs hi
  | true => exact start_entered_passPreT hacc' hv (hfr rfl) hentry himp hctx he hs hi

omit [Labels ι] in
/-- The entry fields check at a reassigned graph. -/
theorem checkEntryFields_reassign [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (inputs : List (Ty ι)) (regions : List Footprints.ArgumentStoreRegion) :
    GraphCode.ArgumentPathTracking.checkEntryFields (reassign G η) inputs regions =
      GraphCode.ArgumentPathTracking.checkEntryFields G inputs regions := rfl

end Run

end Verification.TolerantFrames
