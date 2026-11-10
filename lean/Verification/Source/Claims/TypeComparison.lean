import Verification.Source.Claims.Extraction
import Verification.Source.Lowering.Synthesis

/-! The comparison of a unit's computed types with its claims
(`Synthesis.compareUnit`), a measurement only. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping SourceExtraction
open EquationGraphs (Tree)

/-- A module value's type as the unit reads it: its written signature, its
annotation, or else its initializer's claim; a module cell's contract. -/
def moduleValueType (value : ModuleValue Tree) : Compiler (Ty Tree) := do
  match value.2.2 with
  | .ok (.written ty) => lower (Fragment.translate ty)
  | .ok (.claimed _ (some ty)) => lower (Fragment.translate ty)
  | .ok (.claimed A none) | .ok (.cell A) => SourceClaims.resolve (← table) A
  | .error reason => throw reason

/-- Unit `i`'s computed types against its claims. -/
def Front.compareTypes (fr : Front) (i : Nat) : Except String Json := do
  let some (f, _, initClaims) := fr.units[i]? | throw s!"no unit {i}"
  let c ← match initClaims with
    | some c => pure c
    | none => match fr.d.functions.find? (fun c => c.name == f.name && c.namePos == f.namePos) with
      | some c => pure c
      | none => throw s!"missing claims for '{f.name}'"
  let module := if initClaims.isSome then fr.moduleFunctions ++ fr.classSelves
    else fr.moduleFunctions ++ fr.moduleConstants
  -- A generic module function read as a value is its scheme
  -- (`Scheme.moduleScheme`); called, it is instantiated at the call.
  let schemes := fr.generics.map fun g => (g.name, (do
    let (T, slot) ← Scheme.moduleScheme (← table) g
    let _ := T
    lower (do set T; Fragment.translate slot) : Compiler (Ty Tree)))
  let generics := fr.generics.map fun g => (g.name,
    ({ binders := g.binders, instantiate := fun θ => (·.1) <$> g.instantiate θ } : Synthesis.Generic))
  Synthesis.compareUnit fr.d.types f c.normalized (module.map (fun v => (v.1, moduleValueType v)) ++ schemes)
    generics

end Verification.SourceClaimJson
