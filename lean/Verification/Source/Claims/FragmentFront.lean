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

/-- The generic closures a source tree creates, as their trees, outer first. -/
partial def genericLambdas : Json → List Json
  | .arr xs => xs.toList.flatMap genericLambdas
  | .obj kvs =>
    let j := Json.obj kvs
    let here := if (j.getObjValAs? String "k").toOption == some "lambda" &&
        ((j.getObjVal? "typeParams").toOption.bind (·.getArr?.toOption)).any (!·.isEmpty) then [j] else []
    here ++ kvs.toList.flatMap fun (_, v) => genericLambdas v
  | _ => []

/-- **A generic closure's scheme claim from its annotations** (mode 8): its
binders its own, each bound its written one (an earlier binder by name); its
receiver its written `this` (an arrow's, every value); its parameters and
result as written, a defaulted parameter with `undefined`, an array rest its
element (`ClosureSetup.lambdaSetup`'s own signature); its effect the one it
writes, else, for an expression body that, with its defaults, calls nothing
(`Synthesis.mayCall`),
keeping values and stores and bounding its throws, else the ordinary effect;
the walk checks its body's effect within it (`Synthesis.walkLambda`). The
scheme row and the binders its body reads as rigid rows are then
`Scheme.closureRows`'s, as for a producer's scheme claim
(claims.ml:546-564). A closure that writes no result, a guard, an async
closure, a resolution-qualified binder or a rest of no array is claimed at
no scheme. -/
def writtenSchemes (force : List String := []) : ClosureSchemes := fun T body => do
  let action : Compiler (List (Expression Tree)) := do
    let mut out : List (Expression Tree) := []
    for j in genericLambdas body do
      let .ok (.lambda pos receiver tps params defaults rest result guard stated async _ body) := Fragment.decodeExpr j
        | continue
      let some ret := result | continue
      if guard.isSome || async || tps.any (·.resolution.isSome) then continue
      let part (j : Json) : Compiler (Option (Ty Tree)) :=
        tryCatch (some <$> lower (Fragment.callableType j)) fun _ => pure none
      let names := tps.map (·.name)
      let bs ← tps.mapM (fun p => do
          match p.bound with
          | none => pure (some none)
          | some b => match ← part b with
            | some [l] =>
              match EquationStore.placeholderName (← table) l with
              | some m => pure (if names.contains m then some (some (ClaimType.param m)) else some (some (.labels [l])))
              | none => pure (some (some (.labels [l])))
            | some B => pure (some (some (.labels B)))
            | none => pure none)
      let some bounds := bs.mapM id | continue
      let fixed := if rest then params.dropLast else params
      let qs ← fixed.zipIdx.mapM fun ((_, ty), i) => do
        let A ← part ty
        pure (A.map fun A => if defaults.any (·.1 == i) then Synthesis.norm (A ++ [LabelStore.Labels.undef]) else A)
      let some ps := qs.mapM id | continue
      let restEl ← match rest, params.getLast? with
        | true, some (_, ty) => match Fragment.arrayElement ty (readonly := true) with
          | some el => pure (some (← part el))
          | none => pure (some none)
        | _, _ => pure none
      if restEl == some none then continue
      let some R ← part ret | continue
      let recv ← match receiver with
        | some (annot, _) => part annot
        | none => pure (some [← lower (SourceTypes.use .source)])
      let some recv := recv | continue
      -- (`TSCERT_FORCE=schemes`, and `literals`: keeping both, bounding its throws, the
      -- adversarial proposal)
      let effect := if force.contains "schemes" || force.contains "literals" then
          { (CallEffects.Effect.ofFootprint ⟨.keep, .keep⟩) with onThrow := true } else
        stated.getD (match body with
        | .block .. => .ordinary
        | x => if Synthesis.mayCall x || defaults.any (Synthesis.mayCall ·.2) then .ordinary
          else { (CallEffects.Effect.ofFootprint ⟨.keep, .keep⟩) with onThrow := true })
      let binders := (tps.zip bounds).map fun (p, b) =>
        ({ name := p.name, bound := b, resolution := none } : ResolutionWire.Binder (ClaimType Tree))
      let claim : ClaimType Tree :=
        .scheme binders (.labels recv) (ps.map .labels) (restEl.join.map .labels) (.labels R) effect
      out := out ++ [({ point := "", pos := pos, type := claim } : Expression Tree)]
    return out
  let ((es, T), _) ← runCompiler T [] (do return (← action, ← table))
  return (T, es)

/-- A type the front states by none of its own: the annotation's, which the
claims-free retyping reads (`retypeFromFragment`). -/
private def annotated (what : String) : Json :=
  Json.mkObj [("unavailable", toJson s!"not handled: {what} without its annotation")]

/-- **The fragment's claims document**: each function's identity, its
parameters' names, and the footprint its declaration writes (`Modifies<…>`)
or a stand-in names, else the ordinary effect; its types left to its
annotations, its points to the walk. The type table holds the primitives
alone. -/
def fragmentClaims (ast : Json) (fileKey : String) (standIns : StandIns := {}) (force : List String := []) :
    Except String Json := do
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
      -- A statement with store regions proposes `top`, the regional check
      -- of its own regions certifying the statement.
      | none, some s => if s.regions.isEmpty then (s.closed, s.onThrow, Footprints.Closed.top)
          else (.top, false, .top)
      -- Forced (`callees`): a function without a written footprint at
      -- keep/keep; (`throws`) bounding its throws too.
      | none, none =>
        if force.contains "throws" then (⟨.keep, .keep⟩, true, .top)
        else if force.contains "callees" then (⟨.keep, .keep⟩, false, .top) else (.top, false, .top)
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
def retypeFromFragment (force : List String := []) : Retype := fun fr T f fc module scope => do
  let init := f.name.isEmpty
  let (schemes, generics) := fr.genericValues
  let (T, fc, completion, declarations, spanEntries, exprsAt) ← SinglePass.timedKind "lower: of extractAll, the walk" fun _ =>
    Synthesis.retypeUnitWith T f fc (module.map (fun v => (v.1, moduleValueType v)) ++ schemes) generics "xec" force scope
  let (graphs, prologues) ← fr.flowGraphs f init
  let owner := if init then (0, 0) else f.namePos
  let exprMap : Std.HashMap Span (SourceClaims.Candidate Tree) := fc.exprs.foldl (fun m (sp, c) => m.insert sp c) {}
  let envMap : Std.HashMap Nat (List (String × SourceClaims.Candidate Tree)) :=
    fc.envs.foldl (fun m (pos, bs) => m.insert pos bs) {}
  -- A start several statements share (nested at one position): each node
  -- at its own statement's entry.
  let shared : Std.HashSet Nat := Id.run do
    let mut seen : Std.HashSet Nat := {}
    let mut twice : Std.HashSet Nat := {}
    for (sp, _) in spanEntries.toList do
      if seen.contains sp.1 then twice := twice.insert sp.1 else seen := seen.insert sp.1
    return twice
  let currentMap : Std.HashMap Nat (List (String × List (List PropKey × Ty Tree))) :=
    fc.entryCurrent.foldl (fun m (pos, cs) => m.insert pos cs) {}
  let sitesOf (g : SourceFlow.Graph) (node : SourceFlow.Node) (id : Nat) : List Span :=
    (actionSites node.action ++ (if id == g.entry then (prologues.lookup g.owner).getD [] else [])).eraseDups
  -- The spans that are sites of more than one statement (the parts a class's
  -- construction is lowered to share spans).
  let sharedSites : Std.HashSet Span := Id.run do
    let mut first : Std.HashMap Span Span := {}
    let mut out : Std.HashSet Span := {}
    for g in graphs do
      for (node, id) in g.nodes.toList.zipIdx do
        for sp in sitesOf g node id do
          match first.get? sp with
          | some src => if src != node.source then out := out.insert sp
          | none => first := first.insert sp node.source
    return out
  let points : List (String × SourceClaims.PointData Tree) := graphs.flatMap fun g => g.nodes.toList.zipIdx.map fun (node, id) =>
    let sites := sitesOf g node id
    -- The unit's completion holds the bindings where its body completes,
    -- each at the empty type where it never does.
    let own := if shared.contains node.source.1 then spanEntries.get? node.source else none
    let atEntry := match own with
      | some (vs, _) => vs.map fun (n, A) => (n, .ok A)
      | none => (envMap.get? node.source.1).getD []
    -- A statement of a finalizer's copy on a return's route: its entry
    -- in that copy.
    let route := (node.scope.find? (·.name.startsWith "%return@")).bind fun d =>
      declarations.get? (node.source.1, d.name)
    let bindings : List (String × SourceClaims.Candidate Tree) := if let some vs := route then
      vs.map fun (n, A) => (n, .ok A) else match node.action with
      | .finish => if g.owner != owner then atEntry else match completion with
        | some vs => vs.map fun (n, A) => (n, .ok A)
        | none => atEntry.map fun (n, _) => (n, .ok [])
      -- A declaration of a statement declaring several: the bindings before it.
      | .declaration _ _ b _ => match declarations.get? (node.source.1, b.name) with
        | some vs => vs.map fun (n, A) => (n, .ok A)
        | none => atEntry
      | _ => atEntry
    let row : SourceClaims.PointData Tree := {
      -- Each site's type as the walk records it; at a span sites of several
      -- statements share, as its own statement's walk records it.
      exprs := sites.filterMap fun sp =>
        ((if sharedSites.contains sp then exprsAt.get? (node.source, sp) else none) <|> exprMap.get? sp).map (sp, ·)
      envs := if bindings.isEmpty && (envMap.get? node.source.1).isNone then [] else [(node.source.1, bindings)]
      -- The member paths the walk narrowed there (their `current` contents).
      entryCurrent := match own, currentMap.get? node.source.1 with
        | some (_, []), _ => []
        | some (_, cs), _ | none, some cs => [(node.source.1, cs)]
        | none, none => [] }
    (SourceFlow.pointId g.owner id, row)
  -- Two graphs of one owner name a point once: its rows joined.
  let joined : Std.HashMap String (SourceClaims.PointData Tree) := points.foldl (fun m (id, row) =>
    match m.get? id with
    | some r => m.insert id { r with
        exprs := r.exprs ++ row.exprs.filter (fun (sp, _) => !r.exprs.any (·.1 == sp))
        envs := r.envs ++ row.envs.filter (fun (pos, _) => !r.envs.any (·.1 == pos))
        entryCurrent := r.entryCurrent ++ row.entryCurrent.filter (fun (pos, _) => !r.entryCurrent.any (·.1 == pos)) }
    | none => m.insert id row) {}
  let points := (points.map (·.1)).eraseDups.filterMap fun id => (joined.get? id).map (id, ·)
  -- Its own footprint the one its callers read (`fragmentClaims`): written,
  -- a stand-in's or forced, which its own unit then establishes.
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
(`Synthesis.Walk.instances`), a binder a resolution qualifies with the
certificate its type's form gives (`Synthesis.Walk.resolutions`). -/
def instancesFromWalk (force : List String := []) : Instances := fun fr T f c module scope => do
  let calls := f.body.flatMap Fragment.Stmt.callees
  let used := fr.generics.filter fun g => calls.any (·.2.2.1 == g.name)
  if used.isEmpty then return (T, c)
  let (schemes, generics) := fr.genericValues
  let (w, T) ← SinglePass.timedKind "lower: of extractAll, the walk" fun _ =>
    Synthesis.walkUnit T f (module.map (fun v => (v.1, moduleValueType v)) ++ schemes) generics force scope
      (schemes := c.expressions.filterMap fun e => match e.type with
        | .labels A => some (e.pos, A)
        | _ => none)
  let expressions := w.instances.filterMap fun (pos, θ) => do
    let (_, _, name, _) ← calls.find? (·.1 == pos)
    let g ← used.find? (·.name == name)
    -- Each binder but a resolution's observation and result, a qualified
    -- one with the certificate the walk checked.
    let hidden := g.resolution.flatMap (·.associated)
    let certificates := ((w.resolutions.find? (·.1 == pos)).map (·.2)).getD []
    let inst ← (g.binders.zipIdx.filter fun (_, i) => !hidden.contains i).mapM fun (n, _) => do
      let resolution := (certificates.lookup n).map fun c => ({ certificate := c } : ResolutionWire.Instance)
      return ({ name := n, type := .labels (← θ.lookup n), resolution } : Instantiation Tree)
    return ({ point := "", pos, type := .labels [], instantiate := some inst } : Expression Tree)
  return (T, { c with expressions := c.expressions ++ expressions })

/-- The front with its module constants and cells typed by the
initialization unit's walk: a constant at its initializer's computed type
with its annotation, a cell at its computed storage contract. -/
def Front.withInitTypes (fr : Front) (force : List String := []) : Front := Id.run do
  let some (f, _, some c) := fr.units.find? (·.2.2.isSome) | return fr
  let module := fr.moduleFunctions ++ fr.classSelves
  -- Its generic closures (a generic class's methods among them) claimed at
  -- the schemes their annotations state, as scheme rows, before the walk
  -- types the values holding them (`extractMember`'s order, the producer's
  -- claims.ml:546-564).
  let source := Json.mkObj [("body", (fr.ast.getObjVal? "init").toOption.getD (.arr #[]))]
  let atSchemes : Except String (EquationStore.State × Fragment.Fn × Function Tree) := do
    let closures := Scheme.genericClosures (source.getObjValD "body")
    if closures.isEmpty then return (fr.d.types, f, c)
    let (T, es) ← writtenSchemes force fr.d.types (source.getObjValD "body")
    let c := { c with expressions := c.expressions ++ es.filter fun e => !c.expressions.any (·.pos == e.pos) }
    let localCalls := (f.body.flatMap Fragment.Stmt.callees).filter fun call =>
      !fr.generics.any (·.name == call.2.2.1)
    let (T, c, scopes) ← Scheme.closureRows T [] closures localCalls c
    let source := Scheme.annotationAtScopes T scopes [] source
    let body ← Fragment.decodeInit (Json.mkObj [("init", source.getObjValD "body")])
    return (T, { f with body }, c)
  let (T0, f, c) := match atSchemes with
    | .ok r => r
    | .error _ => (fr.d.types, f, c)
  match retypeFromFragment force fr T0 f c.normalized module none with
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

/-- A module function's type with each signature's footprint `Φ`, bounding
its throws where `onThrow`. -/
def keepingType (A : Ty Tree) (onThrow : Bool) (Φ : Footprints.Closed := ⟨.keep, .keep⟩) : Compiler (Ty Tree) := do
  match PositiveRules.expand (SourceTypes.graph (← table)) A with
  | [.arrs L S] =>
    let e (x : CallEffects.Effect) : CallEffects.Effect := { x with closed := Φ, onThrow, regions := [] }
    return [← lower (SourceTypes.use (.arrs (L.map fun a => { a with effect := e a.effect })
      (S.map fun a => { a with effect := e a.effect })))]
  | _ => throw "a module function of no one signature"

/-- **Declarations' footprints** (section 9, "Declarations"): each function
a wanted unit reaches, callees first, walked as its unit is, each callee
read at the footprint found for it. A walk proposes the join of the changes
its writes and its calls' instances make, by class of location
(`Walk.valueChange`, `Walk.storeChange`, as a function literal's effect is
found, the producer's `footprint_stmts`, source.ml:1016-1122): keep/keep
where it changes nothing, and no proposal where the join is the ordinary
effect. It bounds the throws where none of its calls, iterations or
finalizers leaves one unbounded. A self-recursive function is walked with
itself at keep/keep, then at what that walk found, until a walk finds no
more than it assumed, three walks at most (the least fixed point over a
lattice of twelve footprints). Any other function, an async one, a generic
one, one with a rest, a written effect, a written promise or a stand-in
keeps what `fragmentClaims` gives it. Each proposal is a stand-in: its
callers read it and its own unit establishes it. -/
def declarationEffects (fr : Front) (wanted : List Nat) (standIns : StandIns) (force : List String) :
    List StandIn := Id.run do
  -- Callees first: the wanted units' reach in post-order.
  let mut order : List Nat := []
  let mut seen : Std.HashSet Nat := {}
  let mut stack : List (Nat × Bool) := wanted.reverse.map (·, false)
  for _ in List.range (4 * fr.units.length * (fr.units.length + 1) + 4) do
    match stack with
    | [] => break
    | (i, true) :: rest => stack := rest; order := order ++ [i]
    | (i, false) :: rest =>
      if seen.contains i then stack := rest
      else
        seen := seen.insert i
        stack := (fr.edges i).filter (!seen.contains ·) |>.map (·, false) |>.append ((i, true) :: rest)
  let (schemes, generics) := fr.genericValues
  let top : Footprints.Closed := ⟨.any, .any⟩
  let mut found : List (String × Footprints.Closed × Bool) := []
  for i in order do
    let some (f, tps, none) := fr.units[i]? | continue
    if !tps.isEmpty || f.async || f.stated.isSome || f.params.any (·.rest) ||
        standIns.functions.any (·.name == f.name) then continue
    let walkAt (own : Option (Footprints.Closed × Bool)) : Option (Footprints.Closed × Bool) :=
      let at_ := match own with
        | some o => (f.name, o) :: found
        | none => found
      let module := (fr.moduleFunctions ++ fr.moduleConstants).map fun v => (v.1, (match at_.lookup v.1 with
        | some (Φ, ot) => do keepingType (← moduleValueType v) ot Φ
        | none => moduleValueType v : Compiler (Ty Tree)))
      match Synthesis.walkUnit fr.d.types f (module ++ schemes) generics force none (strict := true) with
      | .ok (w, _) => some (if w.writes then ⟨w.valueChange, w.storeChange⟩ else ⟨.keep, .keep⟩, !w.throwWrites)
      | .error _ => none
    let within (a b : Footprints.Closed × Bool) : Bool := a.1.le b.1 && (a.2 || !b.2)
    let r : Option (Footprints.Closed × Bool) :=
      if (fr.mentions i).contains f.name then Id.run do
        let mut assumed : Footprints.Closed × Bool := (⟨.keep, .keep⟩, true)
        for _ in List.range 3 do
          match walkAt (some assumed) with
          | none => return none
          | some got =>
            if within got assumed then return some assumed
            assumed := (⟨assumed.1.value.max got.1.value, assumed.1.store.max got.1.store⟩, assumed.2 && got.2)
        return none
      else walkAt none
    if let some (Φ, ot) := r then
      if Φ != top then found := found ++ [(f.name, Φ, ot)]
  return found.map fun (n, Φ, ot) => { name := n, footprint := Φ, onThrow := ot }

/-- The front with the functions the stand-ins name at their footprints:
their claims' and their slots', as `fragmentClaims` and `fileFront` state a
stand-in's. -/
def Front.withStandIns (fr : Front) (sis : List StandIn) : Front :=
  let d := { fr.d with functions := fr.d.functions.map fun c => match sis.find? (·.name == c.name) with
    | some s => { c with footprint := s.footprint, onThrow := s.onThrow, resultFootprint := s.resultFootprint }
    | none => c }
  let ordinary := fr.units.filterMap fun (f, tps, c) => if tps.isEmpty && c.isNone then some f else none
  let slots := ordinarySlots d ordinary (sis.map (·.name))
  { fr with d, moduleFunctions := fr.moduleFunctions.map fun v => ((slots.find? (·.1 == v.1)).getD v) }

/-- The claims document with the functions the stand-ins name at their
footprints, as `fragmentClaims` states a stand-in's. -/
def withStandIns (claims : Json) (sis : List StandIn) : Json :=
  claims.setObjVal! "functions" (Json.arr ((claims.getObjValAs? (Array Json) "functions").toOption.getD #[] |>.map fun j =>
    match sis.find? (some ·.name == (j.getObjValAs? String "name").toOption) with
    | some s => ((j.setObjVal! "footprint" (toJson s.footprint)).setObjVal! "onThrow" (toJson s.onThrow)).setObjVal!
        "resultFootprint" (toJson s.resultFootprint)
    | none => j))

/-- **A selected unit's plans from the fragment alone** (mode 8): the front
of `fragmentClaims`, no import planned, each import read at its declared
type or at its stand-in's footprint, the module values typed by the
initialization's walk, and each selected group's units extracted over their
computed types (`retypeFromFragment`), the functions' footprints their
walks give (`declarationEffects`). -/
def fragmentPlans (ast : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget)
    (names : Option (List String)) (standIns : StandIns := {}) (force : List String := []) : Except String FilePlans := do
  let ast := ast.setObjVal! "modules" (Json.arr #[])
  let claims ← fragmentClaims ast fileKey standIns force
  let qualified := standIns.imports.map fun s => (s.name, s.footprint, s.onThrow, s.resultFootprint)
  let fr ← SinglePass.timedKind "lower: fileFront" fun _ => fileFront ast claims fileKey budget qualified
  -- The functions' footprints their walks give, as stand-ins; the claims
  -- and the front again where any is found.
  let computed := if force.contains "callees" || force.contains "throws" then [] else
    SinglePass.timedKind "lower: declarations' footprints" fun _ =>
      declarationEffects (fr.withInitTypes force) ((fr.selected names).flatMap fr.group) standIns force
  let (claims, fr) := if computed.isEmpty then (claims, fr) else (withStandIns claims computed, fr.withStandIns computed)
  let fr := SinglePass.timedKind "lower: initialization's walk" fun _ => fr.withInitTypes force
  let wanted := (fr.selected names).flatMap fr.group
  let (T, plans) := SinglePass.timedKind "lower: extractAll" fun _ =>
    fr.extractSome (wanted.foldl (·.insert ·) {}) (some (retypeFromFragment force)) (some (instancesFromWalk force))
      (some (writtenSchemes force))
  let F ← SinglePass.timedKind "lower: freeze" fun _ => EquationStore.freeze T
  let plans := SinglePass.timedKind "lower: plans over the store" fun _ => plans.map fun e => e.bind (FunctionPlan.over F)
  return ⟨⟨ast, claims, qualified, []⟩, fr, F, plans⟩

/-- The plans with each unit's loop-head facts the given file states
(`headFacts`, `headFactsOfCodes`) as its statement entries' candidates, its
own graph's and each code request's: the search's and the single pass's
given invariants, in place of the claims'. With `entries` (the referee,
mode 9), the other statement entries' facts too (`entryFacts`): the search
holds at each statement entry only what its candidates there give. -/
def FilePlans.withHeadFacts (f : FilePlans) (given : Std.HashMap String Json) (entries : Bool := false) : FilePlans :=
  { f with plans := f.plans.zipIdx.map fun (p, i) => p.map fun
    | .graph name pos r =>
      let line := given.get? (f.fr.unitId i)
      let field := fun (k : String) => (line.bind fun l => (l.getObjVal? k).toOption)
      let facts := fun (k : String) (sm : RequestJson.SourceMap) (cuts : List Nat) =>
        headFactsFromJson sm cuts ((field k).getD (Json.arr #[]))
      let ofCodes := fun (k : String) (ci : Nat) =>
        (((field k).bind fun cs => (cs.getArr?).toOption).bind (·[ci]?)).getD (Json.arr #[])
      .graph name pos { r with
        candidates := facts "headFacts" r.sourceMap (r.start :: r.cuts) ++
          (if entries then facts "entryFacts" r.sourceMap (r.start :: r.cuts) else [])
        codeSources := r.codeSources.zipIdx.map fun (c, ci) =>
          let start := ((r.codes[ci]?).map fun q => (q.asRequest r.toRequest).start).getD 0
          { c with candidates := headFactsFromJson c.sourceMap (start :: c.cuts) (ofCodes "headFactsOfCodes" ci) ++
            (if entries then headFactsFromJson c.sourceMap (start :: c.cuts) (ofCodes "entryFactsOfCodes" ci) else []) } } }

/-- The plans with each graph's statement entries reduced to its loop heads
(`SinglePass.loopHeads`) and its start, its own and each code request's: the
search then carries facts through every other statement entry as the single
pass does, the referee (mode 9) deciding mode 8's proposals over the same
state model. The statement entries are the search's alone: the proved check
reads none. -/
def FilePlans.headCuts (f : FilePlans) : FilePlans :=
  { f with plans := f.plans.map fun p => p.map fun
    | .graph name pos r =>
      let heads (P : ControlFlow.Program) (start : Nat) (cuts : List Nat) : List Nat :=
        let hs := (SinglePass.loopHeads P.toArray start).1
        cuts.filter fun l => l == start || hs.getD l false
      .graph name pos { r with
        cuts := heads r.program r.start r.cuts
        codeSources := r.codeSources.zipIdx.map fun (c, ci) => match r.codes[ci]? with
          | some q => let rq := q.asRequest r.toRequest; { c with cuts := heads rq.program rq.start c.cuts }
          | none => c } }

end Verification.SourceClaimJson
