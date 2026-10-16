-- Equations/Trees.lean owns closed-tree constructors, substitutions, rendering and label interpretation.
import Verification.Source.Equations.Trees
-- Equations/Declarations.lean decodes declaration terms and represents binder contexts.
import Verification.Source.Equations.Declarations
-- Equations/ClaimWire.lean decodes producer rows and rewrites claim label lists.
import Verification.Source.Equations.ClaimWire
-- Equations/State.lean owns construction drafts, pending jobs and obligations.
import Verification.Source.Equations.State
-- Equations/Interning.lean allocates keyed heads and lifts parameterized signatures.
import Verification.Source.Equations.Interning
-- Equations/Core.lean lowers type terms, declaration bodies and producer labels.
import Verification.Source.Equations.Core
-- Equations/Annotations.lean walks source annotations and establishes unit binder scopes.
import Verification.Source.Equations.Annotations
-- Equations/Instances.lean proposes scheme instances by structural matching.
import Verification.Source.Equations.Instances
-- Equations/Finishing.lean compacts heads and validates equations and declared bounds.
import Verification.Source.Equations.Finishing
-- Equations/Source.lean combines source annotations, imported values, generics and claims.
import Verification.Source.Equations.Source

/-! Lowering source declarations to recursive equations (`RECURSIVE-EQUATIONS.md`
§8). The parser's declaration document, the function tree's annotations and
the source-claims labels become one table of equations, validated by
`Equations.ofRaw`, and unions of closed labels over it. Heads are made per
source declaration, per unit and per type-literal occurrence, never per
instance, so a growing family (`Pair<[T, U]>`, `Promise`'s `catch`) is
finitely many heads. Head allocation is keyed by source occurrence and has no
instance-count cutoff. An alias cycle not guarded by a constructor is refused.
The subtype execution budget governs the subsequent declared-bound checks.

Lowering is untrusted in what it proposes (the hash-consing of literal
heads) and trusted in what it states: the equations
are the meaning of the source. The source path reads it through
`EquationLowering.source` (`SourceClaimJson.equationFront`), and the store
extraction grows is its state (`EquationStore`). -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-- **The source path's lowering.** `ast` is the parser's function tree with
its declaration document (`tools/declaration-types.mts`), `claims` the
source-claims document (§9.1). -/
def source (ast claims : Json) (budget : PositiveCertificates.SearchBudget := {}) : Except Failure SourceLowering := do
  let document ← (field ast "declarations").mapError Failure.refusal
  let ds ← (definitions document).mapError Failure.refusal
  if let some i := (List.range ds.size).find? (fun i => ds[i]!.identity == arrayProtoIdentity) then
    if i != 0 || !ds[i]!.parameters.isEmpty then throw (.refusal "ArrayProto must be the first declaration")
  let ((annotations, values, generics, units, initBinders, claims), s) ←
    ((lowerSource ast claims).run { doc := ds, subtypeBudget := budget }).mapError Failure.refusal
  let b ← (compact s).mapError Failure.refusal
  let _ ← b.finish
  let rn := b.rn
  let rename (j : Json) : Except String Json := do
    let ts ← (← j.getArr?).toList.mapM Tree.fromJson
    return unionJson (rn ts)
  return {
    store := b.store
    annotations := annotations.map fun (p, U) => (p, rn U)
    arrays := s.arrayAnnotations.map fun (p, a) => (p, a.map rn)
    values := values.map fun (n, sp, U) => (n, sp, rn U)
    generics := generics.map fun g =>
      { g with type := g.type.map (·.map rn), bounds := g.bounds.map fun (n, B) => (n, B.map rn) }
    units := units.map fun (p, bs) => (p, bs.map fun (n, t, B) => (n, treeRename b.rename t, B.map rn))
    initBinders := initBinders.map fun (n, t, B) => (n, treeRename b.rename t, B.map rn)
    claims := ← (documentForm rename claims).mapError Failure.refusal }


end Verification.EquationLowering
