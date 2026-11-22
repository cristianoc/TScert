import Verification.Semantics.SurvivalSeparation
import Verification.Semantics.ExitSchemas

/-! Experimental rules for inferring preservation requirements at calls of a
callback parameter. The input identifies live facts, the possible writes in
scope, and the roots that retain their identity at the interface. The Lean
controls supply these premises at the lowered rule boundary. -/
namespace Verification.SourceClaimJson.CallbackPreservation
open Footprints HeapKnowledge CallEffects

/-- Label a source scope refusal with the name used in the paper. -/
def scopeRefusal (check reason : String) : String :=
  s!"callback scope [{check}]: {reason}"

/-- The message names a scope refusal of `scopeRefusal`'s form. -/
def carriesScopeRefusal (message : String) : Bool :=
  (message.splitOn "callback scope [").length > 1

/-- Facts the continuation needs at this invocation. Both languages give
their supports to the existing call stability rule. -/
structure LiveFacts where
  heap : List FactKind := []
  index : List IndexFact := []

def LiveFacts.support? (facts : LiveFacts) : Option Footprint := do
  let index ← facts.index.mapM (·.support? {})
  return facts.heap.flatMap FactKind.support ++ index.flatten

/-- A root correspondence with the path to the same object in the destination
scope. The input stands for checked identity at the invocation, not mere
equality of source names. -/
abbrev RootMap := Nat → Option (Nat × List String)

/-- Exact projection of a requirement. A missing root refuses the
projection. Effect instantiation uses the existing conservative renaming
instead, since widening a write effect is safe for the stability check. -/
def projectRegion (roots : RootMap) : Region → Option Region
  | .field x k | .path x [] k => do
    let (y, q) ← roots x
    return if q.isEmpty then .field y k else .path y q k
  | .path x p k => do
    let (y, q) ← roots x
    return .path y (q ++ p) k
  | .fields x | .pathFields x [] => do
    let (y, q) ← roots x
    return if q.isEmpty then .fields y else .pathFields y q
  | .pathFields x p => do
    let (y, q) ← roots x
    return .pathFields y (q ++ p)
  | .cells x | .pathCells x [] => do
    let (y, q) ← roots x
    return if q.isEmpty then .cells y else .pathCells y q
  | .pathCells x p => do
    let (y, q) ← roots x
    return .pathCells y (q ++ p)
  | .spine x p => do
    let (y, q) ← roots x
    return .spine y (q ++ p)
  | .inCls r c => (projectRegion roots r).map (·.inCls c)
  | .all => some .all
  | .cls c => some (.cls c)

def project (roots : RootMap) (support : Footprint) : Option Footprint :=
  support.mapM fun (r, change) => (projectRegion roots r).map (·, change)

/-- A demand on one callback parameter at one invocation. The footprints
describe changes the continuation tolerates, at the receiving function's
interface positions. Several demands for a parameter are conjunctive. -/
structure Demand where
  parameter : Nat
  support : Exits Footprint
  /-- Receiver and ordinary arguments at this invocation, in interface slots. -/
  actualRoots : List (Option (Nat × List String)) := []
  deriving DecidableEq, Repr

/-- Local evidence at one invocation. `possible` bounds what a callback
can write from here before any caller obligations are imposed. It may be
unrestricted. The prototype takes that bound as a premise and uses the
existing separation checker to discharge individual support entries. -/
structure Site where
  parameter : Nat
  live : Exits LiveFacts
  possible : Exits Footprint
  localEvidence : SepEvidence
  toInterface : RootMap

def Site.infer (site : Site) : Except String Demand := do
  let inferExit := fun (exit : Completion) => do
    let some support := (site.live.get exit).support?
      | throw "a live fact has no supported footprint"
    let residual := support.filter fun entry =>
      !stable site.localEvidence [entry] (site.possible.get exit)
    let some projected := project site.toInterface residual
      | throw "a callback obligation cannot be expressed at the interface"
    return projected
  return ⟨site.parameter, ⟨← inferExit .normal, ← inferExit .exceptional⟩, []⟩

/-- Forward a demand through another function's callback parameter. Both
the parameter mapping and the protected roots come from the forwarding call. -/
def Demand.forward (demand : Demand) (parameter : Nat) (roots : RootMap) : Option Demand := do
  let actuals := demand.actualRoots.map fun value => do
    let (slot, rest) ← value
    let (root, path) ← roots slot
    return (root, path ++ rest)
  return ⟨parameter, ⟨← project roots demand.support.normal, ← project roots demand.support.exceptional⟩, actuals⟩

structure Callback where
  effects : Exits Footprint
  actuals : Nat → Option Nat

/-- Match the demand against a callback effect in the caller. The effect
map includes its ordinary actuals and hidden capture actuals. -/
def Demand.check (demand : Demand) (roots : RootMap) (callbacks : Nat → Option Callback)
    (evidence : SepEvidence) : Bool :=
  match callbacks demand.parameter with
  | none => false
  | some callback =>
    let checkExit := fun exit =>
      match project roots (demand.support.get exit) with
      | some support => stable evidence support ((callback.effects.get exit).renameM callback.actuals)
      | none => false
    checkExit .normal && checkExit .exceptional

/-- Check an invocation under a published requirement. Each support entry
must follow from local evidence or be covered by the published allowance. -/
def Site.checkPublished (site : Site) (demand : Demand) (toBody : RootMap) : Bool :=
  let checkExit := fun exit => do
    let support ← (site.live.get exit).support?
    let required ← project (fun root => some (root, [])) support
    let published ← project toBody (demand.support.get exit)
    return (support.zip required).all fun (entry, region, change) =>
      stable site.localEvidence [entry] (site.possible.get exit) ||
        published.any fun (r, c) => decide (r = region) && c.le change
  demand.parameter == site.parameter &&
    checkExit .normal == some true && checkExit .exceptional == some true

/-- Recheck a body's selected facts at the invocation. This is the
existing forward stability check, applied to the full support, including
entries the inference discharged locally. -/
def Site.checkContinuation (site : Site) (effects : Exits Footprint) : Bool :=
  let checkExit := fun exit =>
    let facts := site.live.get exit
    let effect := effects.get exit
    (frame site.localEvidence facts.heap effect).length == facts.heap.length &&
      facts.index.all (·.keeps site.localEvidence.query {} effect)
  checkExit .normal && checkExit .exceptional

end Verification.SourceClaimJson.CallbackPreservation
