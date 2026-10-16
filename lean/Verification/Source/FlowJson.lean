import Verification.Source.FlowGraph
-- ExpressionPlan supplies the same operand schedule consumed by source lowering.
import Verification.Source.ExpressionPlan
-- ExecutionRoots.lean identifies the expression plans owned by each source action.
import Verification.Source.ExecutionRoots
-- BindingPlan supplies lexical binding and parameter-default execution schedules.
import Verification.Source.BindingPlan
-- SourceFacts decides which mutable bindings a body holds in cells.
import Verification.Source.SourceFacts

/-! The claim-independent execution graphs exposed to the producer. The
consumer reconstructs these graphs from source; supplied graph edges carry no
acceptance authority. -/
namespace Verification.SourceFlow
open Lean RequestJson Fragment

private def savedJson (s : SourceExecution.Saved) : Json :=
  Json.mkObj [("id",toJson s.id),("name",toJson s.name),
    ("source",toJson s.source),("role",toJson s.role)]

private def effectJson : SourceExecution.Effect → Json
  | .none => Json.mkObj [("kind",toJson "none")]
  | .havoc => Json.mkObj [("kind",toJson "havoc")]
  | .cellWrite name value => Json.mkObj [("kind",toJson "cellWrite"),
      ("name",toJson name),("value",toJson value)]
  | .cellUpdate name source => Json.mkObj [("kind",toJson "cellUpdate"),
      ("name",toJson name),("source",toJson source)]

private def referenceJson : SourceExecution.Reference → Json
  | .local name source => Json.mkObj [("kind",toJson "local"),
      ("name",toJson name),("source",toJson source)]
  | .field original receiver key => Json.mkObj [("kind",toJson "field"),
      ("source",toJson original.span),("receiver",savedJson receiver),
      ("key",key.map savedJson |>.getD .null)]

private def operationJson : SourceExecution.Operation → Json
  | .evaluate original _ effect => Json.mkObj [("kind",toJson "evaluate"),
      ("source",toJson original.span),("effect",effectJson effect)]
  | .methodRead original receiver key call => Json.mkObj [("kind",toJson "methodRead"),
      ("source",toJson original.span),("receiver",savedJson receiver),
      ("key",key.map savedJson |>.getD .null),("call",toJson call.span)]
  | .invokeSaved original _ receiver method => Json.mkObj [("kind",toJson "invokeSaved"),
      ("source",toJson original.span),("receiver",savedJson receiver),("method",savedJson method)]
  | .snapshotSpread original value call => Json.mkObj [("kind",toJson "snapshotSpread"),
      ("source",toJson original.span),("value",savedJson value),("call",toJson call.span)]
  | .snapshotObject original value => Json.mkObj [("kind",toJson "snapshotObject"),
      ("source",toJson original.span),("value",savedJson value)]
  | .referenceRead source reference => Json.mkObj [("kind",toJson "referenceRead"),
      ("source",toJson source),("reference",referenceJson reference)]
  | .referenceWrite source reference value => Json.mkObj [("kind",toJson "referenceWrite"),
      ("source",toJson source),("reference",referenceJson reference),("value",savedJson value)]
  | .updateSaved original reference previous rhs => Json.mkObj [("kind",toJson "updateSaved"),
      ("source",toJson original.span),("reference",referenceJson reference),
      ("previous",savedJson previous),("rhs",rhs.map savedJson |>.getD .null)]
  | .positionRead source array index => Json.mkObj [("kind",toJson "positionRead"),
      ("source",toJson source),("array",savedJson array),("index",toJson index)]
  | .arrayRest source array start slice => Json.mkObj [("kind",toJson "arrayRest"),
      ("source",toJson source),("array",savedJson array),("start",toJson start),("slice",toJson slice)]
  | .emptyObject source => Json.mkObj [("kind",toJson "emptyObject"),("source",toJson source)]
  | .addField original base key value final => Json.mkObj [("kind",toJson "addField"),
      ("source",toJson original.span),("base",savedJson base),("key",toJson key),("value",savedJson value),("final",toJson final)]
  | .mergeObjects source left right final assign => Json.mkObj [("kind",toJson "mergeObjects"),
      ("source",toJson source),("left",savedJson left),("right",savedJson right),("final",toJson final),("assign",toJson assign)]

private def testJson : SourceExecution.Test → Json
  | .truthy => toJson "truthy"
  | .nullish => toJson "nullish"
  | .defined => toJson "defined"

private partial def planJson : SourceExecution.Plan → Json
  | .observe source evaluate => Json.mkObj [("kind",toJson "observe"),
      ("source",toJson source),("evaluate",planJson evaluate)]
  | .atom source operation => Json.mkObj [("kind",toJson "atom"),
      ("source",toJson source),("operation",operationJson operation)]
  | .sequence source binding evaluate next => Json.mkObj [("kind",toJson "sequence"),
      ("source",toJson source),("binding",savedJson binding),
      ("evaluate",planJson evaluate),("next",planJson next)]
  | .choose source condition test binding evaluate yes no => Json.mkObj [
      ("kind",toJson "choose"),("source",toJson source),("condition",toJson condition),
      ("test",testJson test),("binding",savedJson binding),("evaluate",planJson evaluate),
      ("yes",planJson yes),("no",planJson no)]

private def descriptorJson (d : Descriptor) : Json :=
  Json.mkObj [("name",toJson d.name),("source",toJson d.span)]

private def scopeJson (scope : Scope) : Json := toJson (scope.map descriptorJson)

private def actionJson : Action → Json
  | .finish => Json.mkObj [("kind",toJson "end")]
  | .jump target => Json.mkObj [("kind",toJson "jump"),("target",toJson target)]
  | .declaration source mutable binding next => Json.mkObj [("kind",toJson "declaration"),
      ("statement",toJson source),("name",toJson binding.name),("initializer",toJson binding.init.span),
      ("mutable",toJson mutable),("next",toJson next)]
  | .statement st next => Json.mkObj [("kind",toJson "stmt"),("statement",toJson st.pos),("next",toJson next)]
  | .branch st yes no => Json.mkObj [("kind",toJson "branch"),("statement",toJson st.pos),
      ("yes",toJson yes),("no",toJson no)]
  | .returnValue st => Json.mkObj [("kind",toJson "return"),("statement",toJson st.pos)]
  | .saveReturn st binding next => Json.mkObj [("kind",toJson "returnSave"),("statement",toJson st.pos),
      ("binding",descriptorJson binding),("next",toJson next)]
  | .returnHeld binding => Json.mkObj [("kind",toJson "returnHeld"),("binding",descriptorJson binding)]
  | .rethrow binding => Json.mkObj [("kind",toJson "rethrow"),("binding",descriptorJson binding)]
  | .discardThrow binding next => Json.mkObj [("kind",toJson "discardThrow"),
      ("binding",descriptorJson binding),("next",toJson next)]
  | .iteratorStart st binding next => Json.mkObj [("kind",toJson "iteratorStart"),
      ("statement",toJson st.pos),("binding",descriptorJson binding),("next",toJson next)]
  | .iteratorStep st binding element yes no => Json.mkObj [("kind",toJson "iteratorStep"),
      ("statement",toJson st.pos),("binding",descriptorJson binding),("element",descriptorJson element),
      ("yes",toJson yes),("no",toJson no)]

private def handlerJson (h : Handler) : Json :=
  Json.mkObj [("target",toJson h.target),("scope",scopeJson h.scope),("binding",descriptorJson h.binding)]

private partial def bindingPlanJson : SourceExecution.BindingPlan → Json
  | .finish => Json.mkObj [("kind",toJson "finish")]
  | .evaluate value plan next => Json.mkObj [("kind",toJson "evaluate"),
      ("value",savedJson value),("plan",planJson plan),("next",bindingPlanJson next)]
  | .defaultValue value result fallback next => Json.mkObj [("kind",toJson "defaultValue"),
      ("value",savedJson value),("result",savedJson result),("fallback",planJson fallback),("next",bindingPlanJson next)]
  | .bind name origin value next => Json.mkObj [("kind",toJson "bind"),
      ("name",toJson name),("origin",toJson origin),("value",savedJson value),("next",bindingPlanJson next)]
  | .input name index value next => Json.mkObj [("kind",toJson "input"),
      ("name",toJson name),("index",toJson index),("value",savedJson value),("next",bindingPlanJson next)]
  | .readField source receiver field value next => Json.mkObj [("kind",toJson "readField"),
      ("source",toJson source),("receiver",savedJson receiver),("field",toJson field),
      ("value",savedJson value),("next",bindingPlanJson next)]
  | .readPosition source array index value next => Json.mkObj [("kind",toJson "readPosition"),
      ("source",toJson source),("array",savedJson array),("index",toJson index),
      ("value",savedJson value),("next",bindingPlanJson next)]
  | .objectRest source receiver drop value next => Json.mkObj [("kind",toJson "objectRest"),
      ("source",toJson source),("receiver",savedJson receiver),("drop",toJson drop),
      ("value",savedJson value),("next",bindingPlanJson next)]
  | .arrayRest source array start slice value next => Json.mkObj [("kind",toJson "arrayRest"),
      ("source",toJson source),("array",savedJson array),("start",toJson start),("slice",toJson slice),
      ("value",savedJson value),("next",bindingPlanJson next)]

def Graph.json (g : Graph) (defaults : List (String × Span × Nat × Option Expr) := []) : Json :=
  Json.mkObj [("owner",toJson g.owner),("bodySpans",toJson g.bodySpans),("entry",toJson g.entry),
    ("cells",scopeJson g.cells),
    ("prologue",(SourceExecution.bindingPrologue g.owner defaults).map bindingPlanJson |>.getD .null),
    ("nodes",toJson (g.nodes.toList.zipIdx.map fun (node,id) =>
      let expressions := SourceExecution.actionExpressions node.action
        (if id == g.entry then defaults.filterMap (fun (p : String × Span × Nat × Option Expr) => p.2.2.2) else [])
      Json.mkObj [
        ("id",toJson id),("point",toJson (pointId g.owner id)),("source",toJson node.source),
        ("scope",scopeJson node.scope),("handler",node.handler.map handlerJson |>.getD .null),
        ("action",actionJson node.action),
        ("bindingPlan",(SourceExecution.bindingAction node.action).map bindingPlanJson |>.getD .null),
        ("executions",toJson (expressions.map fun (e : Expr) =>
          Json.mkObj [("source",toJson e.span),("plan",planJson (SourceExecution.build e))]))]))]

/-- Expression-bodied closures execute parameter defaults on entry. A block
    body carries its default prologue as ordinary graph statements. -/
private partial def defaultPrologues : Json → Except String (List (Span × List (String × Span × Nat × Option Expr)))
  | .arr xs => do return (← xs.toList.mapM defaultPrologues).flatten
  | .obj fields => do
    let raw := Json.obj fields
    let own ← if (raw.getObjValAs? String "k").toOption == some "lambda" then do
      let expression ← decodeExpr raw
      match expression with
      | .lambda origin _ _ params defaults variadic _ body =>
        match body with
        | .block .. => pure []
        | _ =>
          if defaults.isEmpty then pure [] else do
            let fixed := if variadic then params.dropLast else params
            let order ← parameterOrder fixed defaults
            let inputs ← order.mapM fun index => do
              let some (name,_) := fixed[index]? | throw "invalid parameter schedule"
              pure (name,origin,index+1,defaults.lookup index)
            pure [(body.span,inputs)]
      | _ => pure []
    else pure []
    return own ++ (← fields.toList.mapM (fun (_,value) => defaultPrologues value)).flatten
  | _ => pure []

/-- A body's graph, with the mutable bindings it holds in cells. -/
private def bodyGraph (owner : Span) (params : List String) (body : List Stmt)
    (module : Bool := false) : Except String Graph := do
  let graph ← build owner [] body
  let cells := (SourceExtraction.cellLocals params body module).map
    fun (name, source) => (⟨name, some (source.getD owner)⟩ : Descriptor)
  return { graph with cells := cells }

/-- Nested executable bodies have their own owner, independent of the point
where their closure is created or of the signatures proposed for that closure. -/
partial def nestedGraphs : Json → Except String (List Graph)
  | .arr xs => do return (← xs.toList.mapM nestedGraphs).flatten
  | .obj fields => do
    let j := Json.obj fields
    let own ← if (j.getObjValAs? String "k").toOption == some "lambda" then do
      let lam ← decodeExpr j
      let body ← decodeExpr (← jField j "body")
      let statements := match body with
        | .block _ ss => ss
        | e => [.ret e.span e]
      let params := match lam with
        | .lambda _ _ _ ps .. => ps.map Prod.fst
        | _ => []
      pure [← bodyGraph body.span params statements]
    else pure []
    return own ++ (← fields.toList.mapM (fun (_,v) => nestedGraphs v)).flatten
  | _ => pure []

/-- Decode only execution syntax. Annotations remain uninterpreted payloads;
no producer claim or declaration-type elaboration chooses a control edge. -/
def graphs (ast : Json) : Except String (List Graph) := do
  let functions ← jArr ast "functions"
  let top ← functions.mapM fun raw => do
    let (f, _) ← decodeFn raw
    bodyGraph f.namePos (f.params.map (·.name)) f.body
  let init ← decodeInit ast
  let initial ← if init.isEmpty then pure [] else do pure [← bodyGraph (0,0) [] init (module := true)]
  let nested ← nestedGraphs (Json.arr ((← jArr ast "init") ++ functions).toArray)
  let all := initial ++ top ++ nested
  if (all.map (·.owner)).eraseDups.length != all.length then
    throw "duplicate executable body identities"
  return all

def document (ast : Json) : Except String Json := do
  let defaults ← defaultPrologues ast
  return toJson ((← graphs ast).map fun graph => graph.json ((defaults.lookup graph.owner).getD []))

end Verification.SourceFlow
