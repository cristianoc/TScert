import Verification.Source.SourceClaimWire
import Verification.Source.SourceClaimDiagnostics
import Verification.Source.FlowGraph
import Verification.Source.SourceFacts

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)
private abbrev Sites := List Nat × List Span × List Span
private def joinSites (a b : Sites) : Sites := (a.1 ++ b.1,a.2.1 ++ b.2.1,a.2.2 ++ b.2.2)
/-- Field reads and fresh rest objects/arrays have independently checked
result claims at their pattern spans. -/
private partial def patternClaimSpans : Fragment.Pattern Fragment.Expr → List Span
  | .name .. => []
  | .object _ props rest => props.flatMap (fun (_, t, _) => t.span :: patternClaimSpans t) ++
      match rest with
      | some (q, t) => q :: patternClaimSpans t
      | none => []
  | .array _ elems rest => elems.flatMap (fun (_, t, _) => patternClaimSpans t) ++
      match rest with
      | some (_, q, _, t) => q :: patternClaimSpans t
      | none => []
mutual
private partial def exprSitesCore (includeBodies : Bool) : Fragment.Expr → Sites
  | .var p _ | .lit p _ => ([],[p],[])
  -- A defaulted parameter's expression is an ordinary source expression, so it
  -- is a claim site like any other; the parameter name is not one.
  | .lambda p _ _ _ defaults _ _ e =>
    if !includeBodies then ([],[p],[p]) else
    defaults.attach.foldl (fun acc ⟨d,_⟩ => joinSites acc (exprSitesCore includeBodies d.2))
      (joinSites ([],[p],[p]) (exprSitesCore includeBodies e))
  | .shapeTest p _ _ e | .not p e | .unary p _ e | .cast p _ e | .read p _ e => joinSites ([],[p],[]) (exprSitesCore includeBodies e)
  | .alloc p _ es | .build p _ es => es.foldl (fun acc a => joinSites acc (exprSitesCore includeBodies a)) ([],[p],[])
  | .withValue p a b _ _ | .write p _ a b | .singletonTest p _ _ _ a b | .equality p _ a b | .coalesce p a b | .logical p _ a b => joinSites ([],[p],[]) (joinSites (exprSitesCore includeBodies a) (exprSitesCore includeBodies b))
  -- An assignment is an expression site, and the name it assigns is not one:
  -- the producer claims the value written, not the location.
  | .index p _ a b | .arith p _ a b | .logicalAssign p _ a b | .elemAt p a b | .comma p a b | .inKeys p a b => joinSites ([],[p],[]) (joinSites (exprSitesCore includeBodies a) (exprSitesCore includeBodies b))
  | .arrayLit p es _ => es.foldl (fun acc a => joinSites acc (exprSitesCore includeBodies a)) ([],[p],[])
  | .objectAssign p t ss => ss.foldl (fun acc a => joinSites acc (exprSitesCore includeBodies a))
      (joinSites ([],[p],[]) (exprSitesCore includeBodies t))
  -- A field target is a site, where the value written is claimed, and so
  -- are its receiver and key; a local target is not one.
  | .arrayAssign p targets rest rhs =>
    let reference := fun (acc : Sites) (t : Fragment.Expr) =>
      t.referenceParts.foldl (fun acc a => joinSites acc (exprSitesCore includeBodies a))
        (match t with | .var .. => acc | t => joinSites acc ([],[t.span],[]))
    let withRest := match rest with
      | some (_, _, q) => reference ([],[],[]) q.target
      | none => ([],[],[])
    targets.foldl (fun acc q => let acc := reference acc q.target; match q.default_ with
      | some d => joinSites acc (exprSitesCore includeBodies d) | none => acc)
      (joinSites (joinSites ([],p :: (rest.map (·.1)).toList,[]) (exprSitesCore includeBodies rhs)) withRest)
  | .elemWrite p a b c => joinSites ([],[p],[]) (joinSites (exprSitesCore includeBodies a) (joinSites (exprSitesCore includeBodies b) (exprSitesCore includeBodies c)))
  | .update p _ a none _ => joinSites ([],[p],[]) (exprSitesCore includeBodies a)
  | .update p _ a (some r) _ => joinSites ([],[p],[]) (joinSites (exprSitesCore includeBodies a) (exprSitesCore includeBodies r))
  | .indexWrite p _ a b c => joinSites ([],[p],[]) (joinSites (exprSitesCore includeBodies a) (joinSites (exprSitesCore includeBodies b) (exprSitesCore includeBodies c)))
  | .nullishAssign p _ np e => joinSites ([],[p,np],[]) (exprSitesCore includeBodies e)
  | .assign p _ _ e => joinSites ([],[p],[]) (exprSitesCore includeBodies e)
  | .bindWithReceiver p f receiver args | .callWithReceiver p f receiver args => args.foldl (fun acc a => joinSites acc (exprSitesCore includeBodies a))
      (joinSites ([],[p],[]) (joinSites (exprSitesCore includeBodies f) (exprSitesCore includeBodies receiver)))
  | .call p f args _ _ | .invoke p f args _ _ => args.foldl (fun acc a => joinSites acc (exprSitesCore includeBodies a)) (joinSites ([],[p],[]) (exprSitesCore includeBodies f))
  -- A class value is one expression; its constructor's body has its own sites.
  | .ctor p lam fs =>
    let own := fs.foldl (fun acc f => joinSites acc (exprSitesCore includeBodies f.2)) ([],[p],[])
    match lam with
    | .lambda _ _ _ _ _ _ _ e => if !includeBodies then own else joinSites own (exprSitesCore includeBodies e)
    | _ => own
  | .construct p f args _ _ => args.foldl (fun acc a => joinSites acc (exprSitesCore includeBodies a)) (joinSites ([],[p],[]) (exprSitesCore includeBodies f))
  | .applyWithReceiver p f receiver list =>
    joinSites ([],[p],[]) (joinSites (exprSitesCore includeBodies f) (joinSites (exprSitesCore includeBodies receiver)
      ((list.map (exprSitesCore includeBodies)).getD ([],[],[]))))
  -- The saved receiver's read, spelled at the `?.` token, is a site of its own.
  | .optional p _ r b => joinSites ([],[p],[]) (joinSites (exprSitesCore includeBodies r) (exprSitesCore includeBodies b))
  | .ifBody p a b c => joinSites ([],[p],[]) (joinSites (exprSitesCore includeBodies a) (joinSites (exprSitesCore includeBodies b) (exprSitesCore includeBodies c)))
  -- A closure's statements are its body's sites, as a function's are.
  | .block _ ss => if !includeBodies then ([],[],[]) else ss.foldl (fun s st => joinSites s (stmtSitesCore includeBodies st)) ([],[],[])
private partial def stmtSitesCore (includeBodies : Bool) : Fragment.Stmt → Sites
  | .brk p _ | .cont p => ([p.1],[],[])
  | .ret p e | .effect p e | .throw p e => joinSites ([p.1],[],[]) (exprSitesCore includeBodies e)
  -- A `try` is an entry; its blocks' statements have their own.
  | .tryStmt p body handler finalizer =>
    (body ++ ((handler.map (·.2)).getD []) ++ finalizer.getD []).foldl
      (fun s st => joinSites s (stmtSitesCore includeBodies st)) ([p.1],[],[])
  -- One entry for the statement; every declarator's initializer is a site.
  | .constants p bs | .mutables p bs => bs.foldl (fun acc b => joinSites acc (exprSitesCore includeBodies b.init)) ([p.1],[],[])
  -- Initializers, defaults, field reads and fresh rests each own a claim.
  | .destructure p target d init =>
    (d.toList ++ target.defaults).foldl (fun acc e => joinSites acc (exprSitesCore includeBodies e))
      (joinSites ([p.1],patternClaimSpans target,[]) (exprSitesCore includeBodies init))
  | .loop p c body update => joinSites ([p.1],[],[]) (joinSites (exprSitesCore includeBodies c)
      ((body ++ update).foldl (fun s st => joinSites s (stmtSitesCore includeBodies st)) ([],[],[])))
  -- A block has no entry of its own.
  | .block _ _ body => body.foldl (fun s st => joinSites s (stmtSitesCore includeBodies st)) ([],[],[])
  -- An iterator's closing region is an entry, as a `try` is; its body's and
  -- its close's statements have their own.
  | .closing p close body =>
    (body ++ close).foldl (fun s st => joinSites s (stmtSitesCore includeBodies st)) ([p.1],[],[])
  | .ite p c a b =>
    joinSites ([p.1],[],[]) (joinSites (exprSitesCore includeBodies c)
      ((a ++ b.getD []).foldl (fun s st => joinSites s (stmtSitesCore includeBodies st)) ([],[],[])))
  -- The loop's span is its iteration intrinsic's call's, and the element is
  -- claimed at the name it binds.
  | .forOf p _ np _ i body => joinSites ([p.1],[p, np],[]) (joinSites (exprSitesCore includeBodies i)
      (body.foldl (fun s st => joinSites s (stmtSitesCore includeBodies st)) ([],[],[])))

end
private def stmtSites := stmtSitesCore true

def allFunctionSites (f : Fragment.Fn) : Sites :=
  f.body.foldl (fun s st => joinSites s (stmtSites st)) ([],[],[])

def functionSites (f : Fragment.Fn) : List Nat × List Span :=
  let sites := allFunctionSites f
  (sites.1, sites.2.1)

/-- Source sites owned by one elaboration action. Structural successors own
separate claims even when they share source syntax. -/
private def actionSites : SourceFlow.Action → List Span
  | .declaration _ _ binding _ => (exprSitesCore false binding.init).2.1
  | .statement st _ | .returnValue st | .saveReturn st _ _ => (stmtSitesCore false st).2.1
  | .branch (.ite _ cond _ _) _ _ | .branch (.loop _ cond _ _) _ _ => (exprSitesCore false cond).2.1
  | .iteratorStart (.forOf pos _ namePos _ iterable _) _ _ =>
      pos :: namePos :: (exprSitesCore false iterable).2.1
  | .iteratorStep (.forOf pos _ namePos _ _ _) _ _ _ _ => [pos,namePos]
  | .finish | .jump _ | .returnHeld _ | .rethrow _ | .discardThrow _ _ => []
  | .branch _ _ _ | .iteratorStart _ _ _ | .iteratorStep _ _ _ _ _ => []

/-- Expression-bodied closures run their parameter defaults in their entry
prologue. Block-bodied defaults are ordinary statements in the parser's body. -/
partial def prologueSites : Json → Except String (List (Span × List Span))
  | .arr xs => do return (← xs.toList.mapM prologueSites).flatten
  | .obj fields => do
    let raw := Json.obj fields
    let own ← if (raw.getObjValAs? String "k").toOption == some "lambda" then do
      let body ← Fragment.decodeExpr (← jField raw "body")
      match body with
      | .block .. => pure []
      | _ =>
        let defaults ← (← jArr raw "params").flatMapM fun p => do
          match (p.getObjVal? "default").toOption with
          | none => pure []
          | some e => pure ((exprSitesCore false (← Fragment.decodeExpr e)).2.1)
        pure [(body.span,defaults)]
    else pure []
    return own ++ (← fields.toList.mapM (fun (_,v) => prologueSites v)).flatten
  | _ => pure []

def checkPointSites (graphs : List SourceFlow.Graph)
    (prologues : List (Span × List Span)) (entries : List (Entry Tree))
    (expressions : List (Expression Tree)) (contracts : List (StorageContract Tree)) : Except String Unit := do
  let nodes := graphs.flatMap fun g => g.nodes.toList.zipIdx.map fun (node,id) =>
    (SourceFlow.pointId g.owner id,node)
  for e in entries do
    let some node := nodes.lookup e.point | throw "entry claim names a foreign or missing execution point"
    if node.source.1 != e.start then throw "entry claim source does not match its execution point"
  for e in expressions do
    let some node := nodes.lookup e.point | throw "expression claim names a foreign or missing execution point"
    let prologue := graphs.any fun g =>
      SourceFlow.pointId g.owner g.entry == e.point &&
      ((prologues.lookup g.owner).getD []).contains e.pos
    if !(actionSites node.action).contains e.pos && !prologue then
      throw s!"expression claim at {e.pos} is outside its execution point {e.point}"
  let declarations := nodes.flatMap fun (_,node) => match node.action with
    | .declaration _ true b _ => [(b.init.span,b.name)]
    | _ => []
  for c in contracts do
    if !declarations.contains (c.pos,c.name) then
      throw "storage contract names no mutable declaration of the unit"

/-- A module constant holds no value until its declaration runs. Walking the
top-level code in order, a step may reach a module function, directly or
through the functions that one mentions, only when every module constant those
functions mention already holds its value. Mentions over-approximate calls, so
this refuses some safe orders and admits no unsafe one. -/
def checkInitializationOrder (T : EquationStore.State)
    (fns : List (Fragment.Fn × List Fragment.TypeParam)) (init : List Fragment.Stmt) :
    Except String Unit := do
  let constants := init.flatMap fun
    | .constants _ bs => bs.map (·.name)
    | _ => []
  let bodies := fns.map fun (g, _) => (g.name, g.body.flatMap stmtNames)
  let isFunction (n : String) := bodies.any (·.1 == n)
  let reach (start : List String) : List String := Id.run do
    let mut seen := start.filter isFunction |>.eraseDups
    for _ in List.range (bodies.length + 1) do
      let next := seen.flatMap (fun g => (bodies.lookup g).getD []) |>.filter isFunction
      seen := (seen ++ next).eraseDups
    return seen
  let mut ready : List String := []
  for s in init do
    let reached := reach (stmtNames s)
    let read := reached.flatMap (fun g => (bodies.lookup g).getD []) |>.filter constants.contains
    if let some c := read.find? (fun c => !ready.contains c) then
      throw (sourceRefusal T s.pos .initializationOrder
        s!"a module function this step reaches reads '{c}' before its declaration runs")
    if let .constants _ bs := s then ready := ready ++ bs.map (·.name)


end Verification.SourceClaimJson
