import Verification.Programs.TolerantFramesMergeGraph
import Verification.Programs.TolerantFramesGuaranteeRuns
import Verification.Programs.TolerantFramesEdge
import Verification.Programs.TolerantFramesMergeHead
import Verification.Programs.TolerantFramesNodeSound

/-! # Tolerant frames: what an accepted run guarantees, from its walk

The unit lane states what an accepted run of the pass guarantees
(`PassUnit.GraphGuarantee`, branch `engine-proof-unit`): safety from every
entry, the footprint and fresh result where a bound is stated, the
postcondition at returns, the regional bound, and every stated assertion at
every state reached at its label. `GraphGuarantee` below is that record field
by field, the reachability relation being `Transitions`, which has the same
constructors as the unit lane's `ReachesIn`.

The per-node hypotheses of its fields are instances of `NodesKeep` in the
pass's terms: the footprint check's (`FootprintKept`), the return check's
(`ReturnsEnsured`) and the regional check's (`RegionsKept`); `run_guarantee`
(`TolerantFramesRunSound`) assembles the fields. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules

section Guarantee
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- What a request assumes of its entry (the unit lane's `EntryHolds`). -/
def EntryHolds (G : NormalGraph ι) (inputs : List (Ty ι)) (sep : HeapSeparation.Separation)
    (idx : List HeapKnowledge.IndexAtom) (ρ : Env) (n : Nat) (W : WorldT n) (h : Heap) : Prop :=
  EnvOk G inputs ρ n W ∧ HeapSeparation.Holds sep ρ ∧ HeapKnowledge.IndexHolds ⟨ρ, h⟩ idx ρ h ∧
    WorldAdm W ∧ HeapOk n W h

/-- **What an accepted run of a graph guarantees** (the unit lane's
`GraphGuarantee`, field by field). -/
structure GraphGuarantee (G : NormalGraph ι) (admits : MixedAssignment ι → Prop) (P : Program)
    (start : Nat) (goal : Goal ι) (inputs : List (Ty ι)) (sep : HeapSeparation.Separation)
    (idx : List HeapKnowledge.IndexAtom) (assertions : List (Nat × HeapKnowledge.Knowledge))
    (bound : Option (Footprints.Closed × Bool × Bool)) (ensures : List HeapKnowledge.IndexFact)
    (regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)) : Prop where
  safe : ∀ η, admits η → ∀ n W h ρ, EntryHolds (reassign G η) inputs sep idx ρ n W h →
    (∀ node ∈ P, RefsOk W node.expression) → (∀ i, RefsOk W (ρ i)) →
    SafeGraph (excOf (reassign G η)) P (GoalHolds (reassign G η) goal (goal.argument ρ)) n W h (.at start ρ)
  bounded : ∀ Φ fresh onThrow, bound = some (Φ, fresh, onThrow) → ∀ E K, GraphCode.program E K = P →
    ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → RefsOk W (.goto E K start L d) →
    (∀ v ∈ L, isVal v = true) → isVal d = true →
    SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' v => Φ.Holds h h' ∧ (fresh = true → Footprints.FreshAt h.length v))
      (fun h' => onThrow = true → Φ.Holds h h') n W h (.goto E K start L d)
  ensured : ensures ≠ [] → ∀ E K, GraphCode.program E K = P → ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → RefsOk W (.goto E K start L d) →
    SafePost (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' v => GraphCode.EnsuresAt ensures ⟨envOf L d, h⟩ h' (push v (envOf L d))) n W h (.goto E K start L d)
  regionally : ∀ Φ regions exc, regional = some (Φ, regions, exc) → ∀ E K, GraphCode.program E K = P →
    ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → RefsOk W (.goto E K start L d) →
    SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' _ => Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      (fun h' => exc = true → Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      n W h (.goto E K start L d)
  asserted : ∀ η, admits η → ∀ n W h ρ, EntryHolds (reassign G η) inputs sep idx ρ n W h →
    (∀ node ∈ P, RefsOk W node.expression) → (∀ i, RefsOk W (ρ i)) →
    ∀ l k, (l, k) ∈ assertions → ∀ j h' ρ', j < n → Transitions P j h (.at start ρ) h' (.at l ρ') →
      HeapKnowledge.Holds k ⟨ρ, h⟩ ρ' h'

/-! ## The per-node hypotheses, in the pass's terms -/

/-- At a node entry under a bound `Φ` from the invocation's entry heap `h₀`:
the node is in the region `dead` from which no normal return is possible, or
the heap is within `Φ` from `h₀`. -/
def BoundX (Φ : Footprints.Closed) (h₀ : Heap) (dead : List Bool) : Nat → Env → Heap → Prop :=
  fun l _ h => GraphCode.deadAt dead l = true ∨ Φ.Holds h₀ h

/-- A return under the bound: within `Φ` from `h₀`, the value's store fresh
where the bound states a fresh result. -/
def BoundQ (Φ : Footprints.Closed) (h₀ : Heap) (fresh : Bool) : Heap → Tm → Prop :=
  fun h v => Φ.Holds h₀ h ∧ (fresh = true → Footprints.FreshAt h₀.length v)

/-- An escaping throw under the bound: within `Φ` where the bound covers
throws. -/
def BoundR (Φ : Footprints.Closed) (h₀ : Heap) (onThrow : Bool) : Heap → Prop :=
  fun h => onThrow = true → Φ.Holds h₀ h

/-- **(Named hypothesis) The footprint check keeps the bound**: from a node
entry where the pass's assertion holds, with mark `|h₀|`, and the node is
dead or the heap within `Φ` from `h₀`, every run of its term with budget
left reaches an exit whose target is dead or within `Φ`, a return within
`Φ` with a fresh result where `fresh`, an escaping throw within `Φ` where
`onThrow`. -/
def FootprintKept (P : Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ε : HeapKnowledge.EntryState)
    (ctx : Nat → List (Ty ι)) (Φ : Footprints.Closed) (h₀ : Heap) (dead : List Bool) (fresh onThrow : Bool) : Prop :=
  NodesKeep P (passPreT G w startNames ε ctx) (BoundX Φ h₀ dead) (BoundQ Φ h₀ fresh) (BoundR Φ h₀ onThrow) h₀.length

/-- A return meets `ensures` at the returned value and the entry values. -/
def EnsuresQ (ens : List HeapKnowledge.IndexFact) (ε : HeapKnowledge.EntryState) : Heap → Tm → Prop :=
  fun h v => GraphCode.EnsuresAt ens ε h (push v ε.env)

/-- **(Named hypothesis) The return check establishes `ensures`**: from a
node entry where the pass's assertion holds, every run of its term with
budget left to a value at a return continuation meets `ensures` at the value
and the entry values `ε.env`. -/
def ReturnsEnsured (P : Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ε : HeapKnowledge.EntryState)
    (ctx : Nat → List (Ty ι)) (ens : List HeapKnowledge.IndexFact) (m : Nat) : Prop :=
  NodesKeep P (passPreT G w startNames ε ctx) (fun _ _ _ => True) (EnsuresQ ens ε) (fun _ => True) m

/-- A return within the regional bound from the entry heap `h₀`. -/
def RegionQ (Φ : Footprints.Closed) (regions : List Footprints.ArgumentStoreRegion) (ε : HeapKnowledge.EntryState) (h₀ : Heap) :
    Heap → Tm → Prop :=
  fun h _ => Footprints.ArgumentStoreRegionsWithin Φ regions ε.env h₀ h

/-- An escaping throw within the regional bound where it covers throws. -/
def RegionR (Φ : Footprints.Closed) (regions : List Footprints.ArgumentStoreRegion) (ε : HeapKnowledge.EntryState) (h₀ : Heap)
    (exc : Bool) : Heap → Prop :=
  fun h => exc = true → Footprints.ArgumentStoreRegionsWithin Φ regions ε.env h₀ h

omit [Hashable ι] in
/-- **The start entered, typed**: `start_passPre` with the start's context
the request's inputs, whose types the entry gives. -/
theorem start_passPreT {G : NormalGraph ι} {w : Walk ι} {inputs : List (Ty ι)} {ctx : Nat → List (Ty ι)}
    {claims : List (CertificateProducer.PointClaim ι)} {start : Nat} {goal : ControlFlow.Goal ι}
    {written : Option HeapKnowledge.Knowledge} {supplied : List HeapKnowledge.IndexAtom}
    {givenImplies : List (PromiseCalls.Implication ι)} {givenArgs : List Nat} {givenInputs : List (Nat × Nat)}
    {entryIndices : List HeapKnowledge.IndexAtom} {entrySeparation : HeapSeparation.Separation} {fresh : Nat}
    (hacc : SinglePass.entryRefusal G inputs claims start goal written supplied givenImplies givenArgs givenInputs
      entryIndices entrySeparation = none)
    (hv : w.visited start)
    (hentry : w.entry start = (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true
      inputs.length fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs
      givenInputs givenImplies).1)
    (himp : w.implies start = (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true
      inputs.length fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs
      givenInputs givenImplies).2.1)
    (hctx : ctx start = inputs)
    {ρ : Env} {m : Nat} {s : IndexedHeap} (he : EnvOk G inputs ρ s.n s.W)
    (hs : HeapSeparation.Holds entrySeparation ρ) (hi : HeapKnowledge.IndexHolds ⟨ρ, s.h⟩ entryIndices ρ s.h) :
    passPreT G w (List.range inputs.length) ⟨ρ, s.h⟩ ctx start ρ m s :=
  ⟨start_passPre hacc hv hentry himp he hs hi, hctx ▸ he⟩

end Guarantee

end Verification.TolerantFrames
