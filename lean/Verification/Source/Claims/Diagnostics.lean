import Verification.Source.Lowering.Types

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)
/-- A generic module value's instance checks (`moduleInstances`) are not
ordinary graph sequents, but their failures use the same mandatory located
diagnostic channel. A reader consumes this record structurally and derives
all prose from it. A type argument outside its binder's bound belongs to the
scheme the call eliminates, and says so. -/
def directFailure (T : EquationStore.State) (failure : DirectObligation.Located Tree)
    (outcome : DiagnosticOutcome := .notEstablished) (site : Option String := none) : String :=
  let judgment := failure.judgment
  let message := match outcome with
    | .notEstablished => match site with
      | none => s!"quantified call does not satisfy the closure's bound: cannot establish {failure.judgment.render T}"
      | some site => s!"{site} does not establish its declared bound: {failure.judgment.render T}"
    | .exhausted .. =>
      s!"subtype search exhausted: {failure.judgment.render T}"
  match judgment with
  | .subtyping _ actual expected => subtypeFailure T failure.pos failure.role actual expected outcome message

def sourceRefusal (T : EquationStore.State) (pos : Span)
    (role : DirectObligation.SourceRole) (reason : String) : String :=
  RequestJson.withDiagnostic s!"source refusal at [{pos.1},{pos.2}): {reason}"
    ([("kind",toJson "source-refusal"),("phase",toJson "request-validation"),
     ("outcome",toJson RequestJson.DiagnosticOutcome.notEstablished),("id",toJson s!"refusal:{pos.1}"),
     ("sourceMap",toJson (SourceMapEntry.mk pos role.wire none [])),
     ("reason",toJson reason),("fuel",toJson 0)] ++ (StoreView.projection T []).fields)


end Verification.SourceClaimJson
