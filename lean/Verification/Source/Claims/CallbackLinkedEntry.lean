import Verification.Source.Claims.CallbackPrefixWitness
import Verification.Source.Claims.LoweredModules

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins CallbackEffectInference CallbackInferencePlan ControlFlow ProgramTyping
open PositiveRules LabelStore PassUnit GraphCode CertificateProducer

/-- The closed component being checked contains exactly two declarations. -/
inductive LocalMember where
  | caller | producer
  deriving DecidableEq

inductive SourceSlot where
  | linked (declaration : LocalMember)
  | outside (name : String)
  deriving DecidableEq

/-- The code and ordered captures read from the file's existing module
code and interface layout projections. A local capture resolves to a
declaration and an outside capture must have a modeled realm binding. -/
structure SourceModule (f : FilePlans) where
  graph : LoweredModule
  bindings : List SourceSlot
  types : List (Ty (EquationStore.CheckedLabel f.F.equations f.F.primitive))

def readSourceModule (f : FilePlans) (caller producer i : Nat) : Except String (SourceModule f) := do
  let [graph] := f.moduleCodes [i] | throw (CallbackPreservation.scopeRefusal "readSourceModule" "missing receiverless source module code")
  let caps := f.captures i
  if graph.rest || caps.map Prod.fst != f.fr.captureNames i || caps.map Prod.fst != graph.siblings then
    throw (CallbackPreservation.scopeRefusal "readSourceModule" "source capture names disagree with the lowered module frame")
  let names ← caps.mapM fun (name,_) => do
    let owners := f.fr.units.zipIdx.filterMap fun ((fn,_,init),j) =>
      if init.isNone && fn.name == name then some j else none
    match owners with
    | [] =>
      if !(SourceTypes.prototypeNames.contains name || (hostModel? name).isSome) then
        throw (CallbackPreservation.scopeRefusal "readSourceModule" s!"capture {name} has no modeled outside binding")
      return SourceSlot.outside name
    | [owner] =>
      if owner == caller then return SourceSlot.linked .caller
      if owner == producer then return SourceSlot.linked .producer
      throw (CallbackPreservation.scopeRefusal "readSourceModule" s!"capture {name} is a third local declaration")
    | _ => throw (CallbackPreservation.scopeRefusal "readSourceModule" s!"capture {name} names several local declarations")
  return ⟨graph,names,caps.map Prod.snd⟩

def SourceModule.realize {f : FilePlans} (m : SourceModule f)
    (outside : String → Nat → Tm) (fields : List (PropKey × Nat)) (oid : Nat) :
    PassUnit.ModuleCode (EquationStore.CheckedLabel f.F.equations f.F.primitive) LocalMember :=
  { arity := m.graph.ar, exprs := m.graph.code.1, conts := m.graph.code.2,
    start := m.graph.code.1.length - 1, kind := .call, fields, oid, captures := m.types,
    slots := m.bindings.map fun
      | .linked owner => Slot.linked owner
      | .outside name => Slot.outside (outside name)
    comp := m.graph.comp }

def sourceModules {f : FilePlans} (a b : SourceModule f) (outside : String → Nat → Tm)
    (fields : LocalMember → List (PropKey × Nat)) (identity : LocalMember → Nat) :
    LocalMember → PassUnit.ModuleCode (EquationStore.CheckedLabel f.F.equations f.F.primitive) LocalMember
  | .caller => a.realize outside (fields .caller) (identity .caller)
  | .producer => b.realize outside (fields .producer) (identity .producer)

/-- Identity, code, fixed arity, component and the typed capture order of
a source declaration, compared with the request used for its proof. -/
def SourceModule.agrees {f : FilePlans} (m : SourceModule f) (r : Req f) (name : String)
    (binding : String → SourceSlot) : Prop :=
  m.graph.name = name ∧ m.graph.code = realizedCode r ∧ m.graph.ar = r.inputs.length - r.siblings.length ∧
  m.graph.comp = r.comp ∧ m.bindings = r.siblings.map binding ∧
  m.types = r.inputs.drop (r.inputs.length - r.siblings.length)

private instance {f : FilePlans} {m : SourceModule f} {r : Req f} {n : String} {keep : String → SourceSlot} :
    Decidable (m.agrees r n keep) := by unfold SourceModule.agrees; infer_instance

end Verification.SourceClaimJson.CallbackInterfaceCheck
