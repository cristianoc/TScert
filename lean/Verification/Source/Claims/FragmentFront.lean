import Verification.Source.Claims.Json
import Verification.Source.Claims.TypeComparison

/-! The claims-free front of the single pass (mode 8): a file's units
lowered from its fragment alone. The store holds the fragment's declarations
and annotations; each function's signature is its declaration's, at the
footprint it writes (`Modifies<…>`, else the ordinary effect); every
expression's and statement entry's type, and every `let`'s storage contract,
is the walk's (`Synthesis.retypeUnit`); the execution points are the flow
graphs' (`SourceFlow.pointId`); an import is read at its declared type. The
loop heads' facts are the given file's (`FilePlans.passGroup`). -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping SourceExtraction
open EquationGraphs (Tree)

/-- A written-footprint stand-in: the footprint a function or an import would
state if written, supplied apart from the source for a measurement
(`TSCERT_STANDINS`). -/
structure StandIn where
  name : String
  footprint : Footprints.Closed
  onThrow : Bool := false
  resultFootprint : Footprints.Closed := .top
  deriving FromJson, ToJson

/-- The stand-ins of a file: for the file's functions and for its imports. -/
structure StandIns where
  functions : List StandIn := []
  imports : List StandIn := []
  deriving FromJson, ToJson

/-- A type the front states by none of its own: the annotation's, which the
claims-free retyping reads (`retypeFromFragment`). -/
private def annotated (what : String) : Json :=
  Json.mkObj [("unavailable", toJson s!"not handled: {what} without its annotation")]

/-- **The fragment's claims document**: each function's identity, its
parameters' names, and the footprint its declaration writes (`Modifies<…>`)
or a stand-in names, else the ordinary effect; its types left to its
annotations, its points to the walk. The type table holds the primitives
alone. -/
def fragmentClaims (ast : Json) (fileKey : String) (standIns : StandIns := {}) : Except String Json := do
  -- The functions' identities and written effects, their annotations as
  -- the source spells them.
  let bare := ast.setObjVal! "declarations" (Json.mkObj [("roots", Json.arr #[]),
    ("definitions", Json.arr #[]), ("values", Json.arr #[]), ("symbols", Json.arr #[]),
    ("applications", Json.arr #[])])
  let all ← Fragment.decodeAstWithParams bare
  let init ← Fragment.decodeInit ast
  let primitives : List (PositiveGraphs.GraphRow Nat) := [.clauses [.nul], .clauses [.boolLit true],
    .clauses [.boolLit false], .clauses [.undef]]
  let functions := all.map fun (f, _) =>
    let (footprint, onThrow, resultFootprint) := match standIns.functions.find? (·.name == f.name), f.stated with
      | some s, _ => (s.footprint, s.onThrow, s.resultFootprint)
      | none, some s => (s.closed, s.onThrow, Footprints.Closed.top)
      | none, none => (.top, false, .top)
    Json.mkObj [("name", toJson f.name), ("namePos", toJson f.namePos),
      ("params", Json.arr (f.params.map fun p => Json.mkObj [("name", toJson p.name),
        ("type", annotated "a parameter's type"), ("current", Json.null)]).toArray),
      ("result", annotated "a result type"), ("entries", Json.arr #[]), ("expressions", Json.arr #[]),
      ("contracts", Json.arr #[]), ("footprint", toJson footprint), ("onThrow", toJson onThrow),
      ("resultFootprint", toJson resultFootprint)]
  let empty := Json.mkObj [("entries", Json.arr #[]), ("expressions", Json.arr #[]), ("contracts", Json.arr #[])]
  return Json.mkObj ([("file", toJson fileKey), ("sourceSha256", ast.getObjValD "sourceSha256"),
    ("types", toJson (primitives.map toJson)), ("functions", Json.arr functions.toArray),
    ("modules", Json.arr #[]), ("qualified", Json.arr #[])] ++
    (if init.isEmpty then [] else [("init", empty)]))

/-- A unit's flow graphs, its own and its nested closures', and their
entry prologues' sites (`prologueSites`). -/
def Front.flowGraphs (fr : Front) (f : Fragment.Fn) (init : Bool) :
    Except String (List SourceFlow.Graph × List (Span × List Span)) := do
  let owner := if init then (0, 0) else f.namePos
  let graph ← SourceFlow.build owner [] f.body
  let raw := if init then some (Json.mkObj [("body", (fr.ast.getObjVal? "init").toOption.getD (.arr #[]))])
    else fr.functionJsons.find? fun j =>
      (j.getObjValAs? String "name").toOption == some f.name &&
        (j.getObjValAs? Span "namePos").toOption == some f.namePos
  let nested ← match raw with
    | some j => SourceFlow.nestedGraphs j
    | none => pure []
  let prologues ← prologueSites (raw.getD .null)
  return (graph :: nested, prologues)

/-- **A unit's claims from its fragment** (mode 8): the walk's types
(`retypeByWalk`) at each execution point (`SourceFlow.pointId`) of its flow
graphs, each point holding its node's sites' expressions and its statement
entry's bindings, where `checkPointSites` places a producer's; its
parameters' and result's types its annotations', each read where the
extraction reads them. -/
def retypeFromFragment : Retype := fun fr T f fc module => do
  let init := f.name.isEmpty
  let (T, fc) ← SinglePass.timedKind "lower: of extractAll, the walk" fun _ => retypeByWalk "xec" fr T f fc module
  let (graphs, prologues) ← fr.flowGraphs f init
  let exprMap : Std.HashMap Span (SourceClaims.Candidate Tree) := fc.exprs.foldl (fun m (sp, c) => m.insert sp c) {}
  let envMap : Std.HashMap Nat (List (String × SourceClaims.Candidate Tree)) :=
    fc.envs.foldl (fun m (pos, bs) => m.insert pos bs) {}
  let points := graphs.flatMap fun g => g.nodes.toList.zipIdx.map fun (node, id) =>
    let sites := actionSites node.action ++ (if id == g.entry then (prologues.lookup g.owner).getD [] else [])
    let row : SourceClaims.PointData Tree := {
      exprs := sites.filterMap fun sp => (exprMap.get? sp).map (sp, ·)
      envs := ((envMap.get? node.source.1).map fun bs => [(node.source.1, bs)]).getD [] }
    (SourceFlow.pointId g.owner id, row)
  let fc := { fc with points }
  if init then return (T, fc)
  let action : Compiler ((List (String × SourceClaims.Candidate Tree) × SourceClaims.Candidate Tree) ×
      EquationStore.State) := do
    let params ← f.params.mapM fun p => do
      return (p.name, ← tryCatch (.ok <$> lower (Fragment.translate p.ty)) fun e =>
        pure (.error s!"not handled: the parameter '{p.name}''s annotation: {e}"))
    let ret ← tryCatch (do
        let ret ← match resultWithFootprint (← table) f.ret fc.resultFootprint with
          | .ok r => pure r
          | .error e => throw e
        .ok <$> lower (Fragment.translate ret)) fun e =>
      pure (.error s!"not handled: the result's annotation: {e}")
    return ((params, ret), ← table)
  let ((((params, ret), T), _)) ← runCompiler T [] action
  return (T, { fc with params, ret })

/-- **A unit's calls' type arguments from its walk** (mode 8): each call of a
generic module value at the type each binder takes there
(`Synthesis.Walk.instances`). A value whose binders a resolution qualifies
takes evidence the walk does not state: not handled. -/
def instancesFromWalk : Instances := fun fr T f c module => do
  let calls := f.body.flatMap Fragment.Stmt.callees
  let used := fr.generics.filter fun g => calls.any (·.2.2.1 == g.name)
  if used.isEmpty then return (T, c)
  if let some g := used.find? (!·.resolution.isEmpty) then
    throw s!"not handled: a call of '{g.name}', whose binders a resolution qualifies"
  let (schemes, generics) := fr.genericValues
  let (w, T) ← SinglePass.timedKind "lower: of extractAll, the walk" fun _ =>
    Synthesis.walkUnit T f (module.map (fun v => (v.1, moduleValueType v)) ++ schemes) generics
  let expressions := w.instances.filterMap fun (pos, θ) => do
    let (_, _, name, _) ← calls.find? (·.1 == pos)
    let g ← used.find? (·.name == name)
    let inst ← g.binders.mapM fun n => do
      return ({ name := n, type := .labels (← θ.lookup n), resolution := none } : Instantiation Tree)
    return ({ point := "", pos, type := .labels [], instantiate := some inst } : Expression Tree)
  return (T, { c with expressions := c.expressions ++ expressions })

/-- The front with its module constants and cells typed by the
initialization unit's walk: a constant at its initializer's computed type
with its annotation, a cell at its computed storage contract. -/
def Front.withInitTypes (fr : Front) : Front := Id.run do
  let some (f, _, some c) := fr.units.find? (·.2.2.isSome) | return fr
  let module := fr.moduleFunctions ++ fr.classSelves
  match retypeFromFragment fr fr.d.types f c.normalized module with
  | .error reason =>
    let failed := fun (v : ModuleValue Tree) => ((v.1, v.2.1, .error s!"not handled: the module initialization's walk: {reason}") : ModuleValue Tree)
    return { fr with moduleConstants := fr.moduleConstants.map failed }
  | .ok (T, ic) =>
    let typed : List (ModuleValue Tree) := fr.init.flatMap fun
      | .constants _ bs => (bs.filter fun b => !fr.classNames.contains b.name).map fun b =>
        (b.name, b.namePos, match ic.exprs.lookup b.init.span, b.annot with
          | some (.ok A), annot => .ok (.claimed (.ok A) annot)
          | _, some ty => .ok (.written ty)
          | some (.error m), none => .error s!"module constant '{b.name}': {m}"
          | none, none => .error s!"not handled: module constant '{b.name}': its initializer's type")
      | .mutables _ bs => (bs.filter (·.early)).map fun b =>
        (b.name, b.namePos, match ic.contracts.lookup (b.init.span, b.name) with
          | some C => .ok (.cell C)
          | none => .error s!"not handled: module cell '{b.name}': its storage contract")
      | _ => []
    return { fr with d := { fr.d with types := T }, moduleConstants := typed }

/-- **A selected unit's plans from the fragment alone** (mode 8): the front
of `fragmentClaims`, no import planned, each import read at its declared
type or at its stand-in's footprint, the module values typed by the
initialization's walk, and each selected group's units extracted over their
computed types (`retypeFromFragment`). -/
def fragmentPlans (ast : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget)
    (names : Option (List String)) (standIns : StandIns := {}) : Except String FilePlans := do
  let ast := ast.setObjVal! "modules" (Json.arr #[])
  let claims ← fragmentClaims ast fileKey standIns
  let qualified := standIns.imports.map fun s => (s.name, s.footprint, s.onThrow, s.resultFootprint)
  let fr ← SinglePass.timedKind "lower: fileFront" fun _ => fileFront ast claims fileKey budget qualified
  let fr := SinglePass.timedKind "lower: initialization's walk" fun _ => fr.withInitTypes
  let wanted := (fr.selected names).flatMap fr.group
  let (T, plans) := SinglePass.timedKind "lower: extractAll" fun _ =>
    fr.extractSome (wanted.foldl (·.insert ·) {}) (some retypeFromFragment) (some instancesFromWalk)
  let F ← SinglePass.timedKind "lower: freeze" fun _ => EquationStore.freeze T
  let plans := SinglePass.timedKind "lower: plans over the store" fun _ => plans.map fun e => e.bind (FunctionPlan.over F)
  return ⟨⟨ast, claims, qualified, []⟩, fr, F, plans⟩

end Verification.SourceClaimJson
