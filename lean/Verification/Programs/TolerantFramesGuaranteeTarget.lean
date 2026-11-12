import Verification.Source.RequestJson
import Verification.Programs.SinglePass

/-! # Tolerant frames: the unit lane's statement of the graph theorem

The definitions below are copied from the unit lane, branch
`engine-proof-unit`, `lean/Verification/Source/Claims/PassUnit.lean` at
c99647d3 (`ReachesIn`, `EntryHolds`, `GraphGuarantee`, `CheckerScope`,
`RunCall`, `RunCall.result`, `RunCall.Accepts`, `regionOf`, `RunSound`,
`RunKeepsSummaries`), each declaration syntactically identical to its
source; that module is not on this branch, so it cannot be imported. The
namespace is this lane's, and the opened namespaces are the source's but
`SourceExtraction`, which no copied declaration reads. `run_sound`
(`TolerantFramesRunSound`) proves `RunSound` from the graph-level proof's
named hypotheses. -/
namespace Verification.TolerantFrames.Target
open Lean ProgramTyping RequestJson ControlFlow PositiveGraphs PositiveRules LabelStore
open PositiveCertificates (InstanceImageCheck)
open HeapExpressionRules (Checker)
open CertificateProducer (Answered)

/-! ## Reachability of the graph machine -/

/-- `ReachesIn P k h s h' s'`: the graph machine of `P` goes from `s` on heap
`h` to `s'` on heap `h'` in exactly `k` transitions. -/
inductive ReachesIn (P : Program) : Nat → Heap → State → Heap → State → Prop where
  | refl : ReachesIn P 0 h s h s
  | step : Transition P h s h₁ s₁ → ReachesIn P k h₁ s₁ h' s' → ReachesIn P (k + 1) h s h' s'

section
variable {ι : Type} [Labels ι]

/-! ## Entry conditions and graph guarantees -/

/-- What a request assumes of its entry: an environment meeting its inputs'
types at budget `n` and world `W`, its entry separation and index facts, an
admissible world and a heap the world types. -/
def EntryHolds (G : NormalGraph ι) (inputs : List (Ty ι)) (sep : HeapSeparation.Separation)
    (idx : List HeapKnowledge.IndexAtom) (ρ : Env) (n : Nat) (W : WorldT n) (h : Heap) : Prop :=
  EnvOk G inputs ρ n W ∧ HeapSeparation.Holds sep ρ ∧ HeapKnowledge.IndexHolds idx ρ h ∧
    WorldAdm W ∧ HeapOk n W h

/-- **What an accepted run of a graph guarantees**, at every assignment
`admits` lets through: safety from every entry meeting `inputs`; within a
footprint where `bound` names one; the stated postcondition where `ensures`
is not empty; within the regional bound where `regional` names one (each of
these three for the term running any node lists whose graph is `P`); and each
stated assertion true at every state reached at its label within the
budget. -/
structure GraphGuarantee (G : NormalGraph ι) (admits : MixedAssignment ι → Prop) (P : Program)
    (start : Nat) (goal : Goal ι) (inputs : List (Ty ι)) (sep : HeapSeparation.Separation)
    (idx : List HeapKnowledge.IndexAtom) (assertions : List (Nat × HeapKnowledge.Knowledge))
    (bound : Option (Footprints.Closed × Bool × Bool)) (ensures : List HeapKnowledge.IndexFact)
    (regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)) : Prop where
  safe : ∀ η, admits η → ∀ n W h ρ, EntryHolds (reassign G η) inputs sep idx ρ n W h →
    SafeGraph (excOf (reassign G η)) P (GoalHolds (reassign G η) goal (goal.argument ρ)) n W h (.at start ρ)
  bounded : ∀ Φ fresh onThrow, bound = some (Φ, fresh, onThrow) → ∀ E K, GraphCode.program E K = P →
    ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → (∀ v ∈ L, isVal v = true) → isVal d = true →
    HeapObservations.SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' v => Φ.Holds h h' ∧ (fresh = true → Footprints.FreshAt h.length v))
      (fun h' => onThrow = true → Φ.Holds h h') n W h (.goto E K start L d)
  ensured : ensures ≠ [] → ∀ E K, GraphCode.program E K = P → ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h →
    HeapObservations.SafePost (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' v => GraphCode.EnsuresAt ensures h' (push v (envOf L d))) n W h (.goto E K start L d)
  regionally : ∀ Φ regions exc, regional = some (Φ, regions, exc) → ∀ E K, GraphCode.program E K = P →
    ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h →
    HeapObservations.SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' _ => Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      (fun h' => exc = true → Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      n W h (.goto E K start L d)
  asserted : ∀ η, admits η → ∀ n W h ρ, EntryHolds (reassign G η) inputs sep idx ρ n W h →
    ∀ l k, (l, k) ∈ assertions → ∀ j h' ρ', j < n → ReachesIn P j h (.at start ρ) h' (.at l ρ') →
      HeapKnowledge.Holds k ρ' h'

/-- The assignments a pass checker's acceptance covers: every one for the
ordinary checker, a qualified body's admitted instances for its checker
(`SinglePass.PassChecker.qualified` at the body's subtyping). -/
inductive CheckerScope (G : NormalGraph ι) (I : InstanceImageCheck G) :
    SinglePass.PassChecker G I → (MixedAssignment ι → Prop) → Prop where
  | ordinary : CheckerScope G I .ordinary (fun _ => True)
  | qualified (q : QualifiedBody G I) : CheckerScope G I (.qualified q.body q.ordinary) q.Admits

/-! ## A call of the pass -/

/-- One call of `SinglePass.run`: every argument it takes, over the graph
`G` and image check `I`. -/
structure RunCall (G : NormalGraph ι) (I : InstanceImageCheck G) where
  pool : List (Ty ι)
  fuel : Nat
  P : Program
  claims : List (CertificateProducer.PointClaim ι)
  start : Nat
  inputs : List (Ty ι)
  goal : Goal ι
  assertions : List (Nat × HeapKnowledge.Knowledge)
  cuts : List Nat
  candidates : List (Nat × List HeapKnowledge.IndexAtom)
  entryIndices : List HeapKnowledge.IndexAtom
  suggestions : List (ProgramCertificates.Sequent ι)
  known : List (ProgramCertificates.Evidence ι)
  codes : CodeEntry ι → Bool
  aliases : List (ι × ι)
  passChecker : SinglePass.PassChecker G I
  answers : Answered G
  reference : Array HeapKnowledge.Knowledge
  debugNode : Nat
  bound : Option (Footprints.Closed × Bool × Bool)
  givenImplies : Array (List (PromiseCalls.Implication ι))
  givenArgs : Array (List Nat)
  ensures : List HeapKnowledge.IndexFact
  givenInputs : Array (List (Nat × Nat))
  entrySeparation : HeapSeparation.Separation
  observe : Option Nat
  tracing : Bool
  observeEntry : Bool
  regional : Option SinglePass.Regional

/-- The call's result. -/
def RunCall.result {G : NormalGraph ι} {I : InstanceImageCheck G} (c : RunCall G I) :
    SinglePass.Outcome ι × SinglePass.Counts × Answered G × SinglePass.Trace :=
  SinglePass.run G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions c.cuts c.candidates
    c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers c.reference c.debugNode
    c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation c.observe c.tracing
    c.observeEntry c.regional

/-- The call accepted, leaving the answers `after`. -/
def RunCall.Accepts {G : NormalGraph ι} {I : InstanceImageCheck G} (c : RunCall G I) (after : Answered G) : Prop :=
  ∃ counts trace, c.result = (.accepted, counts, after, trace)

/-- A regional option's bound, regions and throw flag. -/
def regionOf (rg : Option SinglePass.Regional) :
    Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool) :=
  rg.map fun g => (g.Φ, g.regions, g.exc)

/-- **The graph-level hypothesis** (the tolerant-frames lane's target): an
accepted call of the pass, whose checker covers `admits`, run with sound
codes and with the read summaries it leaves sound, and with each region's
entry field condition, guarantees what its options ask (`GraphGuarantee`)
from every entry meeting the inputs it is given. The pass checks the start's
context against those inputs itself (`SinglePass.entryRefusal`). Every
other argument is a free proposal: the candidates, given implications,
arguments and inputs, known evidence, cached answers, reference and pool are
arbitrary. -/
def RunSound (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : RunCall G I) (after : Answered G)
    (admits : MixedAssignment ι → Prop),
    c.Accepts after → CheckerScope G I c.passChecker admits →
    ProgramCertificates.CodesSound G c.codes → ProgramCertificates.SummariesSound G I after.summaries.toList →
    (∀ Φ regions exc, regionOf c.regional = some (Φ, regions, exc) →
      GraphCode.ArgumentPathTracking.checkEntryFields G c.inputs regions = true) →
    GraphGuarantee G admits c.P c.start c.goal c.inputs c.entrySeparation c.entryIndices c.assertions c.bound
      c.ensures (regionOf c.regional)

/-- **The pass keeps the read summaries it was given**: every summary of
the answers a call starts from is among those it leaves. -/
def RunKeepsSummaries (ι : Type) [Labels ι] : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : RunCall G I),
    ∀ s ∈ c.answers.summaries.toList, s ∈ c.result.2.2.1.summaries.toList

end

end Verification.TolerantFrames.Target
