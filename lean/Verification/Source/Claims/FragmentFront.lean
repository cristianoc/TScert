import Verification.Source.Claims.Json
import Verification.Source.Claims.TypeComparison
import Verification.Source.Claims.HeadInference
import Verification.Source.Claims.RegionInference
import Verification.Source.Claims.InterfaceRows
import Verification.Source.Claims.HeadDiagnosis
import Verification.Source.Claims.PassProposals

/-! The claims-free front of the single pass (mode 8): a file's units
lowered from its fragment alone. The store holds the fragment's declarations
and annotations; each function's signature is its declaration's, at the
footprint it writes (`Modifies<…>`, else the ordinary effect); every
expression's and statement entry's type, and every `let`'s storage contract,
is the walk's (`Synthesis.retypeUnit`); the execution points are the flow
graphs' (`SourceFlow.pointId`); an import is read at its declared type, at
the footprint its module's units establish where the fragment resolves it
to one (`fragmentPlansWithModules`). The loop heads' facts are the given
file's (`FilePlans.passGroup`). -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping SourceExtraction
open EquationGraphs (Tree)

/-- The generic closures a source tree creates, as their trees, outer first. -/
partial def genericLambdas : Json → List Json
  | .arr xs => xs.toList.flatMap genericLambdas
  | .obj kvs =>
    let j := Json.obj kvs
    let here := if (j.getObjValAs? String "k").toOption == some "lambda" &&
        ((j.getObjVal? "typeParams").toOption.bind (·.getArr?.toOption)).any (!·.isEmpty) then [j] else []
    here ++ kvs.toList.flatMap fun (_, v) => genericLambdas v
  | _ => []

/-- Whether an annotation contains a quantified callable. Inferred scheme
results leave nested scheme comparison to its existing source-signature
obligation (ClosureSetup.lean:258). -/
partial def nestedSchemeAnnotation : Json → Bool
  | .arr xs => xs.any nestedSchemeAnnotation
  | .obj kvs => (Json.obj kvs).getObjValD "k" == toJson "scheme" ||
      kvs.toList.any (fun (_, v) => nestedSchemeAnnotation v)
  | _ => false

/-- **A generic closure's scheme claim from its annotations** (mode 8): its
binders its own, each bound its written one (an earlier binder by name); its
receiver its written `this` (an arrow's, every value); its parameters and
result as written or proposed by the body walk, a defaulted parameter with `undefined`, an array rest its
element (`ClosureSetup.lambdaSetup`'s own signature); its effect the one it
writes, else, for an expression body that, with its defaults, calls nothing
(`Synthesis.mayCall`),
keeping values and stores and bounding its throws, else the ordinary effect;
the walk checks its body's effect within it (`Synthesis.walkLambda`). The
scheme row and the binders its body reads as rigid rows are then
`Scheme.closureRows`'s, as for a producer's scheme claim
(claims.ml:546-564). A guard, an async closure, a resolution-qualified binder or a rest of no array is claimed at
no scheme. -/
def writtenSchemes (force : List String := []) : ClosureSchemes := fun T body => do
  let action : Compiler (List (Expression Tree)) := do
    let mut out : List (Expression Tree) := []
    for j in genericLambdas body do
      let .ok (e@(.lambda pos receiver tps params defaults rest result guard stated async _ body)) := Fragment.decodeExpr j
        | continue
      if guard.isSome || async || tps.any (·.resolution.isSome) then continue
      if result.isNone && params.any (fun (_, ty) => nestedSchemeAnnotation ty) then continue
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
      let G := SourceTypes.graph (← table)
      if result.isNone && ps.any (fun A => A.any (fun l => (G.schemes l).isSome)) then continue
      let restEl ← match rest, params.getLast? with
        | true, some (_, ty) => match Fragment.arrayElement ty (readonly := true) with
          | some el => pure (some (← part el))
          | none => pure (some none)
        | _, _ => pure none
      if restEl == some none then continue
      -- An unwritten result is the body's, as in expression_closures.ml:
      -- 266-272. This preliminary walk supplies only a proposal; the
      -- scheme introduction checks the body again at its rigid rows.
      let R ← match result with
        | some ret => part ret
        | none => tryCatch (do
          let (A, _) ← (Synthesis.walkLambda {} e none).run {}
          let some A := A | pure none
          let G := SourceTypes.graph (← table)
          pure ((ProgramTyping.callSigs G A).head?.map (·.result))) fun _ => pure none
      let some R := R | continue
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

/-- The rules of the loop heads' proposals (`HeadInference.Rules`). -/
def headRules (force : List String) : HeadInference.Rules :=
  { counters := true, carried := true, falseCounters := force.contains "head-counters",
    falseCarried := force.contains "head-carried", falseSeparations := force.contains "head-separations",
    falsePaired := force.contains "head-paired", falseKinds := force.contains "head-kinds",
    falseArms := force.contains "head-arms", falseEnsures := force.contains "head-ensures",
    falseEntails := force.contains "head-entails", falseEvery := force.contains "head-every",
    falseExits := force.contains "head-exits", falseGuards := force.contains "head-guards",
    falseRestated := force.contains "head-restated", falseElements := force.contains "head-elements",
    falseCalled := force.contains "head-called", falseEliminated := force.contains "head-eliminated" }

/-- The names of a statement list's early bindings (`Fragment.Binding.early`),
nested statements' included: a term rooted at one reads no initialized
binding (`termRoot`). -/
partial def earlyNames (ss : List Fragment.Stmt) : List String :=
  ss.flatMap fun
    | .constants _ bs | .mutables _ bs => (bs.filter (·.early)).map (·.name)
    | .ite _ _ t e => earlyNames t ++ earlyNames (e.getD [])
    | .loop _ _ b u _ => earlyNames b ++ earlyNames u
    | .block _ _ b | .forOf _ _ _ _ _ b => earlyNames b
    | .tryStmt _ b h f => earlyNames b ++ earlyNames ((h.map (·.2)).getD []) ++ earlyNames (f.getD [])
    | .closing _ c b => earlyNames c ++ earlyNames b
    | _ => []

/-- The kind of the `length` of a value of a type in claim form, its labels
read in the store `T`: a string's where each of its clauses but `null` and
`undefined` is a string, an array's where each holds an array store, a typed
array's where each states a view length; a type in the parser's form by its
written type (`HeadInference.kindOfType`). -/
def lengthKindIn (T : EquationStore.State) (j : Json) : Option HeapKnowledge.Term.Kind :=
  match (Fragment.translate j).run T with
  | .error _ => HeadInference.kindOfType j
  | .ok (A, T) =>
    let field := fun (fs vs : List (PropKey × List Tree)) (k : PropKey) => (fs.lookup k <|> vs.lookup k).isSome
    let kinds := (PositiveRules.expand (SourceTypes.graph T) A).filterMap fun c => match c with
      | .nul | .undef => none
      | .str | .strLit _ | .strIn _ => some (some HeapKnowledge.Term.Kind.strLength)
      | .refs fs _ vs .. =>
        some (if field fs vs SourceTypes.storeField then some .length
          else if field fs vs viewLengthKey then some .view else none)
      | _ => some none
    match kinds with
    | some k :: ks => if ks.all (· == some k) then some k else none
    | _ => none

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
    SinglePass.work "walk: retype" (fr.fnItem f) fun _ => Synthesis.retypeUnitWith T f fc (module.map (fun v => (v.1, moduleValueType v)) ++ schemes) generics "xec" force scope
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
  -- The loop heads' proposals (`HeadInference.proposals`), by each loop
  -- statement's start: the producer's door, its entry claims at the loop's
  -- execution point, each fact naming only bindings in scope at the head
  -- and initialized there (no early binding).
  let lengthKind := lengthKindIn T
  -- (each function's postcondition by its name, a call's facts)
  -- (an imported function's or another module value's, where no unit of
  -- the file names it: its signature's, `Effect.ensures`)
  let ensuresOf := fun (n : String) => match fr.units.find? (·.1.name == n) with
    | some (g, _, _) => g.ensures
    | none => match module.find? (·.1 == n) with
      | some v => match runCompiler T [] (moduleValueType v) with
        | .ok (A, r) => match PositiveRules.expand (SourceTypes.graph r.types) A with
          | [.arrs [a] _] => a.effect.ensures
          | _ => []
        | .error _ => []
      | none => []
  let heads : Std.HashMap Nat (List HeadInference.Fact) :=
    (HeadInference.proposals
      { headRules force with
          kind := HeadInference.kindsOf f lengthKind
          arrays := HeadInference.arraysOf f lengthKind
          ensuresOf := ensuresOf } f.body
      (if (headRules force).carried then HeadInference.entryOf f else [])).foldl (fun m (pos, fs) => m.insert pos fs) {}
  let early := (earlyNames f.body).eraseDups
  let headClaims (g : SourceFlow.Graph) (node : SourceFlow.Node) : List (Nat × List HeadInference.Fact) :=
    let loopPos : Option Nat := match node.action with
      | .branch (.loop pos ..) _ _ | .iteratorStep (.forOf pos ..) _ _ _ _ => some pos.1
      | _ => none
    match loopPos with
    | some pos =>
      if g.owner != owner then [] else
      -- (the parameters are the body's ambient bindings, in no node's scope)
      let inScope := fun (n : String) =>
        (node.scope.any (·.name == n) || f.params.any (·.name == n)) && !early.contains n
      -- (a store separation names value bindings alone: no cell; and a
      -- binding it names whole, a value its type at the loop's entry makes
      -- an array, where the walk types it: no string, no null)
      let typed := (envMap.get? pos).getD []
      let holdsArray := fun (n : String) => match typed.lookup n with
        | some (.ok A) =>
          let field := fun (fs vs : List (PropKey × List Tree)) (k : PropKey) => (fs.lookup k <|> vs.lookup k).isSome
          let cs := PositiveRules.expand (SourceTypes.graph T) A
          !cs.isEmpty && cs.all fun
            | .refs fs _ vs .. => field fs vs SourceTypes.storeField || field fs vs viewLengthKey
            | _ => false
        | _ => true
      let apartFits : HeadInference.Fact → Bool
        | .apart _ a pa b pb => (!pa.isEmpty || holdsArray a) && (!pb.isEmpty || holdsArray b)
        | _ => true
      let fits := fun (F : HeadInference.Fact) => F.names.all inScope && match F with
        | .apart .. => F.names.all (fun n => !g.cells.any (·.name == n)) && apartFits F
        | _ => true
      match (heads.get? pos).map (·.filter fits) with
      | some (fs@(_ :: _)) => [(node.source.1, fs)]
      | _ => []
    | none => []
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
    -- (a held return is `%return@p%`; a `for...of`'s `%return@p` is its
    -- iterator's `return` method)
    let route := (node.scope.find? fun d => d.name.startsWith "%return@" && d.name.endsWith "%").bind fun d =>
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
        | none, none => []
      entryFacts := (headClaims g node).map fun (pos, fs) => (pos, fs.filterMap HeadInference.Fact.claim)
      entryStoresApart := (headClaims g node).map fun (pos, fs) => (pos, fs.filterMap HeadInference.Fact.storesClaim)
      entryEvery := (headClaims g node).map fun (pos, fs) => (pos, fs.filterMap HeadInference.Fact.everyClaim) }
    (SourceFlow.pointId g.owner id, row)
  -- Two graphs of one owner name a point once: its rows joined.
  let joined : Std.HashMap String (SourceClaims.PointData Tree) := points.foldl (fun m (id, row) =>
    match m.get? id with
    | some r => m.insert id { r with
        exprs := r.exprs ++ row.exprs.filter (fun (sp, _) => !r.exprs.any (·.1 == sp))
        envs := r.envs ++ row.envs.filter (fun (pos, _) => !r.envs.any (·.1 == pos))
        entryCurrent := r.entryCurrent ++ row.entryCurrent.filter (fun (pos, _) => !r.entryCurrent.any (·.1 == pos))
        entryFacts := r.entryFacts ++ row.entryFacts.filter (fun (pos, _) => !r.entryFacts.any (·.1 == pos))
        entryStoresApart := r.entryStoresApart ++
          row.entryStoresApart.filter (fun (pos, _) => !r.entryStoresApart.any (·.1 == pos)) }
    | none => m.insert id row) {}
  let points := (points.map (·.1)).eraseDups.filterMap fun id => (joined.get? id).map (id, ·)
  -- Its own footprint the one its callers read (`fragmentClaims`): written,
  -- a stand-in's or forced, which its own unit then establishes.
  -- A signature's interior replaces the claims at its body's execution
  -- points, the same overlay consumed by ClosureSetup.lambdaSetup.
  let arrowClaims := fc.arrowClaims.map fun (sp, rows) => (sp, rows.map fun row =>
    { row with points := points.map fun (id, point) => (id, {
        exprs := row.exprs.filter (fun (sp, _) => point.exprs.any (·.1 == sp))
        envs := row.envs.filter (fun (p, _) => point.envs.any (·.1 == p))
        entryCurrent := row.entryCurrent.filter (fun (p, _) => point.envs.any (·.1 == p)) }) })
  let fc := { fc with points, arrowClaims }
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
    SinglePass.work "walk: instances" (fr.fnItem f) fun _ => Synthesis.walkUnit T f (module.map (fun v => (v.1, moduleValueType v)) ++ schemes) generics force scope
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

/-- The front with each import that never returns read at the footprint
keeping values and stores: an import of one fixed signature whose declared
result is the empty type and that states no promise; an intrinsic is no
import. Its normal return
meets every footprint, having none; its throws stay unbounded. The reading
rests on the declared result alone, as every read of the import does. -/
def Front.withNeverImports (fr : Front) : Front := Id.run do
  let own := fr.units.map (·.1.name)
  let mut T := fr.d.types
  let mut out : List (ModuleValue Tree) := []
  for v in fr.moduleFunctions do
    let kept := out ++ [v]
    -- (an intrinsic, named `%…%`, keeps its reviewed contract)
    if own.contains v.1 || fr.qualifiedNames.contains v.1 || v.1.startsWith "%" ||
        v.1 == SourceExtraction.arrayPrototypeName then
      out := kept
      continue
    match runCompiler T [] (moduleValueType v) with
    | .ok (A, r) =>
      let T' := r.types
      match PositiveRules.expand (SourceTypes.graph T') A with
      | [.arrs [a] []] =>
        if a.effect.promise.isNone && (PositiveRules.expand (SourceTypes.graph T') a.result).isEmpty then
          match importedArrow T' A ⟨.keep, .keep⟩ false .top with
          | .ok J =>
            T := T'
            out := out ++ [(v.1, v.2.1, .ok (.written J))]
          | .error _ => out := kept
        else out := kept
      | _ => out := kept
    | .error _ => out := kept
  return { fr with d := { fr.d with types := T }, moduleFunctions := out }

/-- Whether a function's declaration states what a caller assumes beyond its
type and the ordinary effect: a postcondition or a guard's promise, which an
importer reads only at an entry its module establishes (`ordinaryImport`). -/
def Front.statesMore (fr : Front) (n : String) : Bool :=
  fr.units.any fun (f, _, c) => c.isNone && f.name == n && (!f.ensures.isEmpty || f.guard.isSome)

/-- Whether the front's claims state a function of that name at more than
the ordinary effect. -/
def Front.proposes (fr : Front) (n : String) : Bool :=
  fr.d.functions.any (fun c => c.name == n && (c.footprint, c.onThrow, c.resultFootprint) != (.top, false, .top)) ||
    fr.statesMore n


/-- **A selected unit's plans from the fragment alone** (mode 8): the front
of `fragmentClaims`, no import planned, each import read at its declared
type, at its stand-in's footprint, or at the footprint `qualified` gives it
(an import whose module's units establish it, `fragmentPlansWithModules`),
the module values typed by the initialization's walk, and each selected
group's units extracted over their computed types (`retypeFromFragment`),
the functions' footprints their own steps give (`PassProposals.proposals`). With
`closure`, the selected groups and every group they reach; with
`proposed`, of the selected functions those whose footprint is more than
the ordinary effect. -/
def fragmentPlansCore (ast : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget)
    (names : Option (List String)) (standIns : StandIns := {}) (force : List String := [])
    (imported : List (String × Footprints.Closed × Bool × Footprints.Closed) := [])
    (depends : List (String × List String) := []) (closure : Bool := false) (proposed : Bool := false)
    (front : Option (Json × Front) := none) (interfaceSlots : Bool := false) :
    Except String FilePlans := do
  let ast := ast.setObjVal! "modules" (Json.arr #[])
  -- A stand-in's footprint first; then the footprint the module's units
  -- establish.
  let given := standIns.imports.map fun s => (s.name, s.footprint, s.onThrow, s.resultFootprint)
  let qualified := given ++ imported.filter fun q => !given.any (·.1 == q.1)
  let depends := depends.filter fun d => !given.any (·.1 == d.1)
  -- (`front`: the claims and front `fileFront` gave with no qualified read
  -- and no stand-in, given again with these reads)
  let (claims, fr) ← match front with
    | some (claims, fr) =>
      if standIns.functions.isEmpty && standIns.imports.isEmpty then pure (claims, fr.withQualified qualified)
      else do
        let claims ← SinglePass.work "prepare: claims" (fileItem ast) fun _ => fragmentClaims ast fileKey standIns force
        pure (claims, ← SinglePass.work "prepare: file lowering" (fileItem ast) fun _ =>
          fileFront ast claims fileKey budget qualified (lenient := true))
    | none => do
      let claims ← SinglePass.work "prepare: claims" (fileItem ast) fun _ => fragmentClaims ast fileKey standIns force
      pure (claims, ← SinglePass.timedKind "lower: fileFront" fun _ =>
        SinglePass.work "prepare: file lowering" (fileItem ast) fun _ =>
        fileFront ast claims fileKey budget qualified (lenient := true))
  let fr := fr.withNeverImports
  -- (each typing of the initialization recorded as one, `SinglePass.work`)
  let initTyped := fun (g : Front) => SinglePass.work "prepare: initialization typing" s!"{fileItem ast}#init" fun _ =>
    g.withInitTypes force
  let wantedOf (fr : Front) (names : Option (List String)) : List Nat :=
    let selected := (fr.selected names).flatMap fr.group
    if closure then (selected ++ selected.flatMap fr.reach).eraseDups.flatMap fr.group |>.eraseDups else selected
  -- A function's member planned with the functions `sis` names at their
  -- footprints, as the plans below are: the proposals' runs read it.
  let planOf := fun (sis : List StandIn) (name : String) =>
      SinglePass.work "propose: member plans" (fr.nameItem name) fun _ => (do
    let fr' := initTyped (fr.withStandIns sis)
    let members := (fr'.selected (some [name])).flatMap fr'.group
    let (T, plans) := fr'.extractSome (members.foldl (·.insert ·) {}) (some (retypeFromFragment force))
      (some (instancesFromWalk force)) (some (writtenSchemes force))
    let F ← EquationStore.freeze T
    let f : FilePlans := ⟨⟨ast, withStandIns claims sis, qualified, [], depends⟩, fr', F,
      plans.map fun e => e.bind (FunctionPlan.over F), []⟩
    return f.withHeadFacts {} false (inferred := true) : Except String FilePlans)
  -- The functions' footprints their own steps establish, as stand-ins
  -- (`PassProposals.proposals`); the claims and the front again where any
  -- is found.
  let computed := if force.contains "callees" || force.contains "throws" then [] else
    SinglePass.timedKind "lower: declarations' footprints" fun _ =>
      PassProposals.proposals fr (wantedOf fr names) standIns force [] planOf
  -- Where the initialization calls a function proposed a returned
  -- function's footprint, the module values it types hold such functions:
  -- the proposals once more, every function not yet proposed again read
  -- at its first proposal.
  let returning := (computed.filter (·.resultFootprint != .top)).map (·.name)
  let computed := if returning.isEmpty || !(fr.init.flatMap stmtNames).any returning.contains then computed else
    SinglePass.timedKind "lower: declarations' footprints" fun _ =>
      PassProposals.proposals fr (wantedOf fr names) standIns force computed planOf
  let (claims, fr) := if computed.isEmpty then (claims, fr) else (withStandIns claims computed, fr.withStandIns computed)
  let fr := SinglePass.timedKind "lower: initialization's walk" fun _ => initTyped fr
  -- With `proposed`, the selected functions whose footprint is more than
  -- the ordinary effect alone, and what they reach.
  let names := if !proposed then names else names.map (·.filter fr.proposes)
  let wanted := wantedOf fr names
  let (T, plans) := SinglePass.timedKind "lower: extractAll" fun _ =>
    fr.extractSome (wanted.foldl (·.insert ·) {}) (some (retypeFromFragment force)) (some (instancesFromWalk force))
      (some (writtenSchemes force))
  -- With `interfaceSlots`, each ordinary function's type as its callers
  -- read it, lowered into the store: the module's interface types.
  let own := (fr.units.filterMap fun (g, tps, c) => if tps.isEmpty && c.isNone then some g.name else none).eraseDups
  let (T, slotTypes) := if !interfaceSlots then (T, []) else
    fr.moduleFunctions.foldl (init := (T, ([] : List (String × Ty Tree)))) fun (T, acc) v =>
      if !own.contains v.1 then (T, acc) else
      match runCompiler T [] (moduleValueType v) with
      | .ok (A, r) => (r.types, acc ++ [(v.1, A)])
      | .error _ => (T, acc)
  let F ← SinglePass.timedKind "lower: freeze" fun _ => SinglePass.work "prepare: freeze" (fileItem ast) fun _ =>
    EquationStore.freeze T
  let plans := SinglePass.timedKind "lower: plans over the store" fun _ =>
    SinglePass.work "prepare: plans over the store" (fileItem ast) fun _ => plans.map fun e => e.bind (FunctionPlan.over F)
  let slots := slotTypes.filterMap fun (n, A) =>
    ((fromJson? (toJson A) : Except String (Ty (EquationStore.CheckedLabel F.equations F.primitive))).toOption).map (n, ·)
  return ⟨⟨ast, claims, qualified, [], depends⟩, fr, F, plans, slots⟩

/-- A module unit's identity on the wire: `module:<location>#<unit>`. -/
def moduleUnitId (location unit : String) : String := s!"module:{location}#{unit}"

/-- A module unit's group checked in the importer's invocation
(`fragmentPlansWithModules`): its identity and its members' on the wire
(`moduleUnitId`), the check's lines, and its verdict, accepted with its
dependencies on the wire. -/
structure ModuleVerdict where
  unit : String
  members : List String
  lines : List String
  verdict : Except String (List String)

abbrev Established := List ((String × String) × (Footprints.Closed × Bool × Footprints.Closed) × String)

def readsOf (rs : List FragmentRead) (est : Established) :
    List ((String × Footprints.Closed × Bool × Footprints.Closed) × (String × List String)) :=
  rs.filterMap fun r => (est.lookup (r.location, r.name)).map fun (p, u) => ((r.localName, p), (r.localName, [u]))

/-- Complete module candidates and their resolved imports, independent of
selection and measurement stand-ins. -/
def interfaceNeeds (sc : ImportScope) : Except String (List ModuleNeed) := do
  sc.modules.mapM fun m => do
    let names ← (← jArr m.document "functions").mapM fun f => f.getObjValAs? String "name"
    return { module := m, names, reads := (moduleReads sc m ("init" :: names)).toOption.getD [] }

/-- Discover only modules reached by the importer, then close over each
complete module's reads. Selection changes the requested components, never
the candidates or inputs of a component check. -/
def requestedInterfaceNeeds (sc : ImportScope) (ast : Json) (names : Option (List String))
    (given fixed own : List String := []) : Except String (List ModuleNeed) := do
  let roots ← importerReads sc ast names given fixed
  let mut pending := (own ++ roots.map (·.location)).eraseDups
  let mut needs : List ModuleNeed := []
  for _ in sc.modules do
    if pending.isEmpty then break
    let batch := sc.modules.filter fun m => pending.contains m.location &&
      !needs.any (·.module.location == m.location)
    pending := []
    for m in batch do
      let ns ← (← jArr m.document "functions").mapM fun f => f.getObjValAs? String "name"
      let reads := (moduleReads sc m ("init" :: ns)).toOption.getD []
      needs := needs ++ [{ module := m, names := ns, reads }]
      pending := (pending ++ reads.map (·.location)).eraseDups
  return needs

/-- The SCC DAG in dependency order; lexicographic module identities break
all ties, including member order within a component. -/
def interfaceComponents (needs : List ModuleNeed) : List (List ModuleNeed) := Id.run do
  let sorted := needs.mergeSort (fun a b => a.module.location ≤ b.module.location)
  let reach := fun (start : String) => Id.run do
    let mut seen := [start]
    for _ in needs do
      seen := (seen ++ (needs.filter fun n => seen.contains n.module.location).flatMap
        (fun n => n.reads.map (·.location))).eraseDups
    return seen
  let mut left := sorted
  let mut components : List (List ModuleNeed) := []
  for n in sorted do
    if !left.any (·.module.location == n.module.location) then continue
    let component := left.filter fun m => (reach n.module.location).contains m.module.location &&
      (reach m.module.location).contains n.module.location
    components := components ++ [component]
    left := left.filter fun m => !component.any (·.module.location == m.module.location)
  let mut out : List (List ModuleNeed) := []
  let mut done : List String := []
  for _ in components do
    let some c := components.find? (fun c =>
      !c.any (fun n => done.contains n.module.location) &&
      c.all (fun n => n.reads.all (fun r => done.contains r.location || c.any (·.module.location == r.location))))
      | break
    out := out ++ [c]
    done := done ++ c.map (·.module.location)
  return out

/-- The plans with each unit's capture of an import read at an entry
checked: the store-map check from the entry's rows to the type the unit
reads it at (`importerRowsAgree`); a refused one refuses the unit. (An
import read at its entry: its slot the entry's reading, `importedArrow`; one
read otherwise, a never-returning import at its declared type, is read at
its declaration's contract.) The importer's reads (`fragmentPlansOfInterfaces`)
and a module's own reads of the entries published before it
(`establishStep`) alike. -/
def FilePlans.refuseRows (f : FilePlans) (reads : List FragmentRead) (established : Established)
    (tables : List (String × RowTable)) : FilePlans :=
  let atEntry := reads.filter fun r => match established.lookup (r.location, r.name),
      f.fr.imported.find? (·.1 == r.localName), f.fr.moduleFunctions.find? (·.1 == r.localName) with
    | some ((fp, ot, ret), _), some (_, _, U), some (_, _, .ok (.written J)) =>
      match importedArrow f.fr.d.types U fp ot ret with
      | .ok J' => J' == J
      | .error _ => false
    | _, _, _ => false
  if atEntry.isEmpty then f else
  { f with plans := f.plans.zipIdx.map fun (p, j) => p.bind fun plan =>
    match (f.captures j).find? fun (n, A) => atEntry.any fun r => r.localName == n &&
        !(match tables.lookup r.location with
          | some t => SinglePass.work "rows: importer check" (f.fr.nameItem n) fun _ => importerRowsAgree f.F.store t r.name A
          | none => false) with
    | some (n, _) => .error s!"signature rows differ: the import '{n}', its module's interface rows refused by the store-map check"
    | none => .ok plan }

/-- The groups of a module's prepared plans its step checks: every group the
selected functions whose claims propose more than the ordinary effect reach,
by leader. -/
def establishChecked (m : ModuleNeed) (fm : FilePlans) : List Nat :=
  let wanted := fm.fr.selected (some (m.names.filter fm.fr.proposes))
  let reach := (wanted ++ wanted.flatMap fm.fr.reach).eraseDups.filterMap fun j => (fm.fr.group j).head?
  fm.fr.leaders.filter reach.contains

/-- The units a step establishes: the least set holding each accepted unit
(with its dependencies on the wire) whose every dependency is in it or among
the units `earlier` established before, grown once per accepted unit. -/
def establishedUnits (accepted : List (String × List String)) (earlier : List String) : List String :=
  go (accepted.length + 1) []
where
  go : Nat → List String → List String
    | 0, ok => ok
    | n + 1, ok =>
      let next := accepted.filter fun (u, deps) => !ok.contains u &&
        deps.all fun d => ok.contains d || earlier.contains d
      if next.isEmpty then ok else go n (ok ++ next.map (·.1))

/-- A function's entry where its step publishes one: its unit's group a
leader whose identity is in `ok`, at the footprint the module's claim of the
function states, where that is more than the ordinary effect; else the note
saying why it has none. -/
def establishEntry (location : String) (fm : FilePlans) (ok : List String) (n : String) :
    Except String ((String × String) × (Footprints.Closed × Bool × Footprints.Closed) × String) :=
  match (List.range fm.fr.units.length).find? fun i => match fm.fr.units[i]? with
      | some (f, _, none) => f.name == n
      | _ => false with
  | none => .error s!"{location}#{n}: no unit"
  | some i => match (fm.fr.group i).head?, fm.fr.units[i]? with
    | some l, some f => match fm.fr.d.functions.find? fun c => c.name == n && c.namePos == f.1.namePos with
      | some c =>
        let u := moduleUnitId location (fm.fr.unitId l)
        let p := (c.footprint, c.onThrow, c.resultFootprint)
        if p == (.top, false, .top) && !fm.fr.statesMore n then .error s!"{location}#{n}: the ordinary effect"
        else if !ok.contains u then
          .error s!"{location}#{n}: proposed {(toJson p.1).compress} onThrow {p.2.1}, not established"
        else .ok ((location, n), p, u)
      | none => .error ""
    | _, _ => .error ""

/-- The goal of a code entry whose function is declared without `this`: the
signature's result, under its promise where it states one (the unit lane's
`PassUnit.receiverlessGoal`). -/
def receiverlessGoal {ι : Type} (c : CodeEntry ι) : ControlFlow.Goal ι :=
  match c.row.effect.promise with
  | some (.guards p) => .guards c.row.result p
  | some (.asserts p) => .asserts c.row.result p
  | none => .plain c.row.result

/-- **The plain row beside a promise row**: the signature `p` with the
result `R` and no promise, its receiver, actuals and every other part of its
effect kept. A guard's interface states it beside its promise row, both run
by the same code. -/
def promisePlain {ι : Type} (p : CallEffects.Arrow (Ty ι)) (R : Ty ι) : CallEffects.Arrow (Ty ι) :=
  { p with result := R, effect := { p.effect with promise := none } }

/-- **A plain result admits a promise's results**: `true` and `false` for a
guard's, `undefined` for an assertion's (`booleanMember`, `admitsUndef`). -/
def promiseAdmits {ι : Type} [DecidableEq ι] (G : PositiveGraphs.NormalGraph ι) (R : Ty ι) : CallEffects.TypePromise → Bool
  | .guards _ => BranchRefinement.booleanMember G R true && BranchRefinement.booleanMember G R false
  | .asserts _ => PromiseCalls.admitsUndef G R

/-- The slot map from a frame with a receiver in front to the frame past it
(the unit lane's `PassUnit.pastReceiver`). -/
def layoutPastReceiver (s : Nat) : Option Nat := if s = 0 then none else some (s - 1)

/-- A layout's verdict on one function on its own: the functions of its file
its code captures (`ok`), or why it is outside the laid-out set. -/
inductive LayoutOwn where
  | ok (callees : List String)
  | outside (why : String)

open LabelStore in
/-- **A function's own layout conditions** (`ModuleLayout`'s `shape`, the
unit lane's restated U3, but the callees' membership): unit `i`'s function
has one interface, the type its file's units capture it at, else its
interface slot; it presents one clause of signatures (`expand`) its code's
kind offers (`KindOffers`); its captures are its slots, each of a file
function read at that function's interface; and each signature row is
realized by some member `j` of the file (`RowRealized`): `j`'s plan is
unqualified, runs this function's code from its start at the row's frame
with its captures (`codeFrame`, or past the receiver for a function without
`this`), at the row's goal, postcondition (past the receiver,
`IndexFact.pastReceiver`), footprint, fresh and throw flags, with an entry separation
naming only captures that are no function of the file, the module cells
(`ModuleLayout.apart`), and the code's entry facts (renamed past the
receiver, each fact of the request one of `mapIndices pastReceiver`), and
the row conditions hold (`PassUnit.rowConditions`). -/
def FilePlans.layoutOwn (f : FilePlans) (i : Nat) : LayoutOwn := Id.run do
  let G := StoreView.graph f.F.store
  let fr := f.fr
  let own : List String := (fr.units.filterMap fun (fn, tps, c) =>
    if tps.isEmpty && c.isNone then some fn.name else none).eraseDups
  let captured := fun (j : Nat) => match f.plans[j]? with
    | some (.ok (.graph _ _ r)) =>
      let names := fr.captureNames j
      if names.length > r.inputs.length then none
      else some (r, names.zip (r.inputs.drop (r.inputs.length - names.length)))
    | _ => none
  let readers := (List.range fr.units.length).filterMap captured
  let ifaceOf := fun (n : String) => (readers.flatMap fun (_, cs) => cs.filter (·.1 == n)).map (·.2) |>.eraseDups
  let some (fn, tps, initClaims) := fr.units[i]? | return .outside "no unit"
  if initClaims.isSome then return .outside "the initialization"
  if !tps.isEmpty then return .outside "a generic function's interface is a scheme"
  let some (r, caps) := captured i | return .outside "its plan or its captures"
  if r.qualification.isSome then return .outside "a qualified request"
  let mut callees : List String := []
  for (n, A) in caps do
    if own.contains n then
      match ifaceOf n with
      | [B] => if A != B then return .outside s!"capture '{n}' at another type than its interface"
      | _ => return .outside s!"'{n}' read at {(ifaceOf n).length} types"
      callees := callees ++ [n]
  let iface ← match ifaceOf fn.name, f.slots.lookup fn.name with
    | [A], _ => pure A
    | [], some A => pure A
    | [], none => return .outside "no interface type"
    | _, _ => return .outside s!"'{fn.name}' read at {(ifaceOf fn.name).length} types"
  let some (L, Sg) := (match PositiveRules.expand G iface with
      | [.arrs L Sg] => some (L, Sg)
      | _ => none) | return .outside "its interface is not one clause of signatures"
  let kind := if fn.convertsReceiver then Invoke.sloppy else Invoke.call
  if !(offerRows L Sg).all (fun p => kindOffers G kind p.receiver) then
    return .outside "its code's kind does not offer its signatures"
  let captures := caps.map (·.2)
  let before := r.inputs.take (r.inputs.length - captures.length)
  let receiverless := !(fn.params.head?.any (·.name == "this"))
  let arity := if receiverless then before.length else before.length - 1
  let exprs := r.program.map (·.expression)
  let conts := r.program.map fun n => (n.continuation, n.handler)
  -- The members whose plans run this code: the candidates of each row.
  let members := (List.range fr.units.length).filterMap fun (j : Nat) => match f.plans[j]? with
    | some (.ok (.graph _ _ q)) =>
      if q.start == r.start && q.program.map (·.expression) == exprs &&
          q.program.map (fun n => (n.continuation, n.handler)) == conts then some q else none
    | _ => none
  -- A row is realized at its own goal, or, where it is the plain row beside
  -- a promise row of the clause (`promisePlain`) whose result admits the
  -- promise's results (`promiseAdmits`), through that promise row
  -- (`RowRealized`, `rowSpec_plain_of_promise`).
  let rows := (offerRows L Sg).map fun p =>
    match (offerRows L Sg).find? fun p' => match p'.effect.promise with
        | some π => p.effect.promise.isNone && promisePlain p' p.result == p && promiseAdmits G p.result π
        | none => false with
    | some p' => p'
    | none => p
  for p in rows do
    let e : CodeEntry _ := ⟨arity, exprs, conts, r.start, captures, p, none⟩
    let eff := p.effect
    if !(decide (arity ≤ p.arguments.length) && eff.belowRow arity && !eff.freshObject && eff.requires.isNone &&
        eff.elements.isNone && !eff.receiverGrows && eff.elementWrite.isNone) then
      return .outside "the code's conditions"
    -- A function declared without `this` states no postcondition of its
    -- receiver, in either state (`IndexFact.pastReceiver`).
    let receiverlessEnsures := eff.ensures.mapM HeapKnowledge.IndexFact.pastReceiver
    if receiverless && receiverlessEnsures.isNone then
      return .outside "a postcondition of the receiver"
    let goal := if receiverless then receiverlessGoal e else e.goal
    let facts := GraphCode.codeEntryIndices e
    let past := HeapKnowledge.mapIndices layoutPastReceiver facts
    -- The entry separation names module cells alone, by level: each capture
    -- that is no function of the file (`ModuleLayout.apart`).
    let cellLevel := fun (l : Nat) => l < captures.length &&
      match caps[captures.length - 1 - l]? with
      | some (n, _) => !own.contains n
      | none => false
    let sepOk := fun (q : SourceRequest _ _) => q.entrySeparation.facts.isEmpty ||
      q.entrySeparation.depth == q.inputs.length &&
        q.entrySeparation.facts.all fun a => cellLevel a.slot && a.partners.all fun pt => cellLevel pt.1
    let ensuresOk := fun (q : SourceRequest _ _) =>
      (if receiverless then receiverlessEnsures == some q.ensures else q.ensures == eff.ensures)
    let frameOk := fun (q : SourceRequest _ _) =>
      q.qualification.isNone &&
      q.inputs == (if receiverless then p.arguments.take arity ++ captures else codeFrame arity p captures none) &&
      sepOk q && ensuresOk q &&
      (if receiverless then q.entryIndices.all past.contains else q.entryIndices == facts) &&
      q.footprint == eff.footprint && q.fresh == eff.fresh && q.onThrow == eff.onThrow
    if !members.any fun q => frameOk q && q.toRequest.goal == goal then
      if members.any frameOk then return .outside "its goal"
      return .outside "no member realizes a signature row (its frame, entry facts or effect)"
  return .ok callees

/-- **The laid-out set** `D` (`ModuleLayout.D`): the greatest set of the
file's functions meeting their own conditions (`layoutOwn`) whose every
captured file function is in it, by unit; and each function outside it
with why. It refuses nothing: the units' verdicts do not depend on it. -/
def FilePlans.laidOut (f : FilePlans) : List String × List (String × String) :=
  let own := (List.range f.fr.units.length).filterMap fun i => match f.fr.units[i]? with
    | some (fn, _, none) => some (fn.name, f.layoutOwn i)
    | _ => none
  let start := own.filterMap fun (n, o) => match o with | .ok cs => some (n, cs) | .outside .. => none
  let rec shrink : Nat → List (String × List String) → List (String × List String)
    | 0, d => d
    | k + 1, d =>
      let d' := d.filter fun (_, cs) => cs.all fun c => d.any (·.1 == c)
      if d'.length == d.length then d else shrink k d'
  let D := (shrink (start.length + 1) start).map (·.1)
  let outside := own.filterMap fun (n, o) => match o with
    | .outside w => some (n, w)
    | .ok _ => if D.contains n then none else some (n, "a callee outside the laid-out set")
  (D.eraseDups, outside)

/-- **One module's step of the interface computation**: the module planned
over its document at its names, reading the entries `established` before it
(`fragmentPlansCore`), prepared (`prepare`); each group its proposals reach
checked (`check`); the entries it publishes (`establishEntry`) over the units
it establishes (`establishedUnits`); its verdicts and notes. It reads
`established` and nothing else of the steps before it. -/
def establishStep (budget : PositiveCertificates.SearchBudget) (force : List String)
    (prepare : String → FilePlans → FilePlans)
    (check : FilePlans → List Nat → List String × Except String (List String))
    (established : Established) (tables : List (String × RowTable)) (m : ModuleNeed) :
    Established × List ModuleVerdict × List String × List (String × RowTable) :=
  let location := m.module.location
  let foreign := m.reads.filter (·.location != location)
  let rs := readsOf foreign established
  let forced : StandIns := if force.contains "imports" then
      { functions := m.names.map fun n => { name := n, footprint := ⟨.keep, .keep⟩, onThrow := true } } else {}
  let planned := SinglePass.timedKind "lower: modules' plans" fun _ =>
    fragmentPlansCore m.module.document location budget (some m.names) forced force (rs.map (·.1)) (rs.map (·.2))
      (closure := true) (proposed := true) (interfaceSlots := true)
  match planned with
  | .error e => ([], [], [s!"{location}: its plans: {e.take 200}"], [])
  | .ok fm =>
    -- The module's own reads of entries published before it, checked by
    -- rows as an importer's are (`FilePlans.refuseRows`).
    let fm := (prepare location fm).refuseRows foreign established tables
    let toCheck := establishChecked m fm
    -- Each function checked, at the footprint its claim states.
    let checkedNotes := (toCheck.flatMap fm.fr.group).filterMap fun j => match fm.fr.units[j]? with
      | some (g, _, none) => (fm.fr.d.functions.find? fun c => c.name == g.name && c.namePos == g.namePos).map fun c =>
        s!"{location}#{g.name}: checked at {(toJson c.footprint).compress} onThrow {c.onThrow}"
      | _ => none
    -- Each group the reads reach, checked; accepted with its dependencies,
    -- each a group of the module or a module unit established before.
    let wire := fun (d : String) => if d.startsWith "module:" then d else moduleUnitId location d
    let verdicts := toCheck.map fun l =>
      let group := fm.fr.group l
      let (lines, v) := SinglePass.timedKind "modules: pass" fun _ => check fm group
      (⟨moduleUnitId location (fm.fr.unitId l), group.map (fun j => moduleUnitId location (fm.fr.unitId j)),
        lines, v.map (·.map wire)⟩ : ModuleVerdict)
    let accepted := verdicts.filterMap fun mv => match mv.verdict with
      | .ok deps => some (mv.unit, deps)
      | .error _ => none
    -- A group is established where it and, transitively, every group it
    -- depends on was accepted.
    let ok := establishedUnits accepted (established.map (·.2.2))
    let entries := m.names.map (establishEntry location fm ok)
    -- Each entry's interface type in the module's store, its rows a table
    -- of their own (`encodeRowTable`), decoded; an entry published where
    -- the store-map check relates the two (`moduleRowsAgree`).
    let candidates := entries.filterMap (·.toOption)
    let ifaces := candidates.filterMap fun e => (fm.slots.lookup e.1.2).map (e.1.2, ·)
    let table := let (rows, ifs) := encodeRowTable fm.F.store ifaces; decodeRowTable rows ifs
    -- An entry is published where its function is laid out (`laidOut`):
    -- the cross-module theorem's step layouts are about those.
    let (laid, outsideD) := fm.laidOut
    let checked := candidates.map fun e => if !laid.contains e.1.2 then
        Except.error s!"{location}#{e.1.2}: not laid out: {((outsideD.find? (·.1 == e.1.2)).map (·.2)).getD ""}"
      else match fm.slots.lookup e.1.2, table with
      | some I, .ok t => if SinglePass.work "rows: publication check" (fm.fr.nameItem e.1.2) fun _ =>
          moduleRowsAgree fm.F.store t e.1.2 I then Except.ok e
        else .error s!"{location}#{e.1.2}: its interface rows refused by the store-map check"
      | none, _ => .error s!"{location}#{e.1.2}: no interface type"
      | _, .error w => .error s!"{location}#{e.1.2}: its interface rows: {w}"
    let published := checked.filterMap (·.toOption)
    (published, verdicts, checkedNotes ++ (entries ++ checked).filterMap (fun
      | .error e => if e.isEmpty then none else some e
      | .ok _ => none), match table with
      | .ok t => if published.isEmpty then [] else [(location, t)]
      | .error _ => [])

/-- The steps over a component's modules in order, each reading the entries
published before it: the fold `establishModules` makes. -/
def establishFold (budget : PositiveCertificates.SearchBudget) (force : List String)
    (prepare : String → FilePlans → FilePlans)
    (check : FilePlans → List Nat → List String × Except String (List String))
    (prior : List (String × RowTable) := []) :
    List ModuleNeed → Established × List ModuleVerdict × List String × List (String × RowTable) →
      Established × List ModuleVerdict × List String × List (String × RowTable)
  | [], acc => acc
  | m :: ms, (est, vs, ns, ts) =>
    let (es, vs', ns', ts') := establishStep budget force prepare check est (prior ++ ts) m
    establishFold budget force prepare check prior ms (est ++ es, vs ++ vs', ns ++ ns', ts ++ ts')

/-- The canonical component computation. Every candidate's required groups
are checked without measurement stand-ins. Incoming footprints are closed
results of predecessor components. Each module is one step
(`establishStep`) over the entries published before it (`establishFold`). -/
def establishModules (needs : List ModuleNeed) (budget : PositiveCertificates.SearchBudget)
    (force : List String) (incoming : Established)
    (prepare : String → FilePlans → FilePlans)
    (check : FilePlans → List Nat → List String × Except String (List String))
    (incomingTables : List (String × RowTable) := []) :
    Except String (Established × List ModuleVerdict × List String × List (String × RowTable)) :=
  .ok (establishFold budget force prepare check incomingTables needs (incoming, [], [], []))

/-- A document's values by their local names, each with the module and name
of its declaration: its imports and the globals it reads. -/
def documentValues (document : Json) : List (String × String × String) :=
  ((jArr (document.getObjValD "declarations") "values").toOption.getD []).filterMap fun v => (do
    let local_ ← (← v.getObjVal? "binding").getObjValAs? String "local"
    let q ← v.getObjVal? "declaration"
    return (local_, ← q.getObjValAs? String "module", ← q.getObjValAs? String "name")).toOption

/-- **The names a module's document leaves unbound for a read of one of its
names**: where the document binds `name` nowhere (no function, no function
it could not lower, no name its top-level code binds), that name; else each
name the code the read reaches mentions (`name`'s functions, the functions
they mention, transitively, and the top-level code where one of them reads
a name it binds) that the document binds nowhere, its values included (its
imports and the globals it reads), each with the module it is read in. A
value the document imports from another module of the fragment is followed
there the same way. A module the fragment does not list (a declaration
alone) binds every name it declares. -/
def unboundReads (sc : ImportScope) (location name : String) : List (String × String) := Id.run do
  let mut pending : List (String × String) := [(location, name)]
  let mut seen : List (String × String) := []
  let mut out : List (String × String) := []
  for _ in [0:sc.modules.length * 64 + 1] do
    let some (l, n) := pending.head? | break
    pending := pending.drop 1
    if seen.contains (l, n) then continue
    seen := seen ++ [(l, n)]
    let some m := sc.modules.find? (·.location == l) | continue
    let some decoded := sc.code[l]? | continue
    let .ok dm := decoded.get | continue
    let (fs, init) := (dm.functions, dm.init)
    let values := documentValues m.document
    let owned := init.flatMap Fragment.Stmt.bound
    let own := fs.map (·.name) ++ m.absent.map (·.1) ++ owned
    if !own.contains n then
      out := out ++ [(l, n)]
      continue
    -- The code the read reaches: functions by name, the top-level code
    -- where a name it binds is reached.
    let intrinsic := fun (x : String) => x.startsWith "%" || x.startsWith "?" || x == "this"
    let mut set := [n]
    let mut withInit := owned.contains n
    let mut mentions : List String := []
    for _ in [0:fs.length + 2] do
      -- (a name the body declares at its top level binds the whole body,
      -- a closure reading it before its declaration included)
      let bodies := (fs.filter fun f => set.contains f.name).flatMap fun f =>
        (Fragment.stmtsFreeNames f.body).filter fun x =>
          !(f.params.map (·.name)).contains x && !(f.body.flatMap Fragment.Stmt.bound).contains x
      let found := ((if withInit then Fragment.stmtsFreeNames init else []) ++ bodies).eraseDups.filter
        (!intrinsic ·)
      let reachesInit := withInit || found.any owned.contains
      let next := (set ++ found.filter (fs.map (·.name)).contains).eraseDups
      let done := next.length == set.length && reachesInit == withInit
      set := next
      withInit := reachesInit
      mentions := found
      if done then break
    for x in mentions do
      if own.contains x then continue
      match values.find? (·.1 == x) with
      | some (_, l', n') => pending := pending ++ [(l', n')]
      | none => out := out ++ [(l, x)]
  return out.eraseDups

/-- Each import of the importer whose declaration names a module of the
fragment, by its local name, with the names that module's document leaves
unbound for it (`unboundReads`), where there are any. -/
def unboundImports (sc : ImportScope) (ast : Json) : List (String × List (String × String)) :=
  if sc.modules.isEmpty then [] else
  (documentValues ast).filterMap fun (local_, l, n) =>
    if !sc.modules.any (·.location == l) then none else
    match unboundReads sc l n with
    | [] => none
    | us => some (local_, us)

/-- The plans with each unit that reads an import of `unbound` refused, at
the first call of it in the unit's code, else at the unit: `unbound name
<name> in <module>, read through the import '<local>'`. -/
def FilePlans.refuseUnbound (f : FilePlans) (unbound : List (String × List (String × String))) : FilePlans :=
  if unbound.isEmpty then f else
  { f with plans := f.plans.zipIdx.map fun (p, j) =>
    match (f.fr.captureNames j).findSome? fun n => (unbound.lookup n).map (n, ·) with
    | none => p
    | some (n, us) =>
      let (l, x) := us.head?.getD ("", n)
      let reason := s!"unbound name {x} in {l}, read through the import '{n}'"
      let at_ := (f.fr.units[j]?).bind fun (fn, _, _) =>
        ((Fragment.stmtsCallees fn.body).find? (·.2.2.1 == n)).map (·.2.1)
      .error (match at_ with
        | some (a, b) => s!"source refusal at [{a},{b}): {reason}"
        | none => reason) }

/-- Importer planning from closed interfaces. No module is planned here. -/
def fragmentPlansOfInterfaces (ast : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget)
    (names : Option (List String)) (standIns : StandIns) (force : List String) (established : Established)
    (tables : List (String × RowTable)) : Except String FilePlans := do
  if established.isEmpty then
    return ← fragmentPlansCore ast fileKey budget names standIns force
  let sc ← ImportScope.of ast
  let reads ← importerReads sc ast names (standIns.imports.map StandIn.name) (standIns.functions.map StandIn.name)
  let rs := readsOf reads established
  let f ← fragmentPlansCore ast fileKey budget names standIns force (rs.map (·.1)) (rs.map (·.2))
  return f.refuseRows reads established tables

/-- Importer planning from closed interfaces (`fragmentPlansOfInterfaces`),
each unit reading an import whose module's document leaves a name its read
reaches unbound refused (`unboundImports`): the fragment's module documents
are the interfaces' (`decodeInterfaces` refuses another), so a module's
missing function is told from an entry not established on both paths. -/
def fragmentPlansFromInterfaces (ast : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget)
    (names : Option (List String)) (standIns : StandIns) (force : List String) (established : Established)
    (tables : List (String × RowTable) := []) :
    Except String FilePlans := do
  let unbound := unboundImports (← ImportScope.of ast) ast
  return (← fragmentPlansOfInterfaces ast fileKey budget names standIns force established tables).refuseUnbound unbound

/-- Direct invocation uses the same canonical component computation as
stored interfaces. Its result is local to this invocation. -/
def fragmentPlansWithModules (ast : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget)
    (names : Option (List String)) (standIns : StandIns := {}) (force : List String := [])
    (prepare : String → FilePlans → FilePlans := fun _ f => f)
    (check : FilePlans → List Nat → List String × Except String (List String) := fun _ _ => ([], .error "not checked")) :
    Except String (FilePlans × List ModuleVerdict × List String) := do
  let needs ← requestedInterfaceNeeds (← ImportScope.of ast) ast names
    (standIns.imports.map StandIn.name) (standIns.functions.map StandIn.name)
  -- The components in order, each established from the entries of those
  -- before it.
  let (established, verdicts, notes, tables) := (interfaceComponents needs).foldl (init := (([] : Established),
      ([] : List ModuleVerdict), ([] : List String), ([] : List (String × RowTable)))) fun (est, vs, ns, ts) component =>
    let (es, vs', ns', ts') := establishFold budget force prepare check ts component (est, [], [], [])
    (es, vs ++ vs', ns ++ ns', ts ++ ts')
  let f ← fragmentPlansFromInterfaces ast fileKey budget names standIns force established tables
  return (f, verdicts, notes)

/-- `fragmentPlansWithModules`' importer plans, its module units unchecked:
every import at its declared type or stand-in. -/
def fragmentPlans (ast : Json) (fileKey : String) (budget : PositiveCertificates.SearchBudget)
    (names : Option (List String)) (standIns : StandIns := {}) (force : List String := []) : Except String FilePlans :=
  fragmentPlansCore ast fileKey budget names standIns force

end Verification.SourceClaimJson
