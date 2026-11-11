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
  | .ok (.claimed A (some ty)) => do
    let D ← lower (Fragment.translate ty)
    let A ← SourceClaims.resolve (← table) A
    -- semantic.ml:231-241 / statement_analysis.ml:338-340: an immutable
    -- annotation retains a keeping effect only at the same signature.
    let T ← table
    let G := SourceTypes.graph T
    match PositiveRules.expand G D, PositiveRules.expand G A with
    | [.arrs L S], [.arrs actual _] =>
      let retain (a : CallEffects.Arrow (Ty Tree)) :=
        match actual.find? fun b =>
          { b.effect with onThrow := false } == CallEffects.Effect.ofFootprint ⟨.keep, .keep⟩ &&
          (sameMeaning T a.receiver b.receiver ||
            (PositiveRules.expand G a.receiver == [.source] && PositiveRules.expand G b.receiver == [.top])) &&
          sameMeaning T a.result b.result &&
          a.arguments.length == b.arguments.length &&
          (a.arguments.zip b.arguments).all (fun (x, y) => sameMeaning T x y) with
        | some b => { a with effect := b.effect }
        | none => a
      return [← lower (SourceTypes.use (.arrs (L.map retain) S))]
    | _, _ => pure D
  | .ok (.claimed A none) | .ok (.cell A) => SourceClaims.resolve (← table) A
  | .error reason => throw reason

/-- The generic module functions a unit's walk instantiates at its calls,
and the scheme a read of one as a value is (`Scheme.moduleScheme`). -/
def Front.genericValues (fr : Front) :
    List (String × Compiler (Ty Tree)) × List (String × Synthesis.Generic) :=
  (fr.generics.map fun g => (g.name, (do
    let (T, slot) ← Scheme.moduleScheme (← table) g
    lower (do set T; Fragment.translate slot) : Compiler (Ty Tree))),
   fr.generics.map fun g => (g.name,
    ({ binders := g.binders,
       widenBinders := (((fr.ast.getObjValAs? (Array Json) "functions").toOption.getD #[]).toList.find? fun j =>
         (j.getObjValAs? String "name").toOption == some g.name &&
         (j.getObjValAs? Span "namePos").toOption == some g.pos).toList.flatMap fun j =>
           ((j.getObjValAs? (Array Json) "typeParams").toOption.getD #[]).toList.filterMap fun p =>
             if p.getObjValD "bound" == Json.null then (p.getObjValAs? String "name").toOption else none,
       instantiate := (fun θ => (·.1) <$> g.instantiate θ),
       resolution := g.resolution, bounds := (fun θ => Prod.snd <$> g.instantiate θ) } : Synthesis.Generic)))

/-- A unit's claims retyped by the walk (`Synthesis.retypeUnit`): the
extraction of the single pass without a producer's types (mode 8). -/
def retypeByWalk (parts : String := "xec") (force : List String := []) : Retype := fun fr T f fc module scope =>
  let (schemes, generics) := fr.genericValues
  Synthesis.retypeUnit T f fc (module.map (fun v => (v.1, moduleValueType v)) ++ schemes) generics parts force scope

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
  let (schemes, generics) := fr.genericValues
  Synthesis.compareUnit fr.d.types f c.normalized (module.map (fun v => (v.1, moduleValueType v)) ++ schemes)
    generics

end Verification.SourceClaimJson
