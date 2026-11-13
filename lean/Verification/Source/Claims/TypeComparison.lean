import Verification.Source.Claims.Extraction
import Verification.Source.Lowering.Synthesis

/-! A module value's type as a unit reads it, and a front's generic
values (`Front.genericValues`), as the single pass's front computes them. -/
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
       widenBinders := g.widenBinders,
       instantiate := (fun θ => (·.1) <$> g.instantiate θ),
       resolution := g.resolution, bounds := (fun θ => Prod.snd <$> g.instantiate θ) } : Synthesis.Generic)))

end Verification.SourceClaimJson
