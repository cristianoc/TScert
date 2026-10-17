import Verification.Source.Claims.Preparation
import Verification.Source.Claims.Sites
import Verification.Source.Claims.Plans
import Verification.Source.SourceExtraction
import Verification.Source.FlowJson
import Verification.Source.FragmentTypes

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)
section
variable {ι : Type} [Labels ι]

def extractPlans (ast claims : Json) (fileKey : String)
    (budget : PositiveCertificates.SearchBudget := {}) : Except String (EquationStore.State × List (FunctionPlan EquationStore.State Tree)) := do
  -- A source with arrays lists `ArrayProto`: its units see `Array.prototype`.
  let arrays := match (ast.getObjVal? "declarations").toOption.bind
      (fun doc => (doc.getObjVal? "definitions").toOption) with
    | some (.arr ds) => ds.any fun d =>
        ((d.getObjVal? "declaration").toOption.bind fun i => (i.getObjVal? "module").toOption) ==
          some (Json.str "tscert/array-prototype")
    | _ => false
  let ⟨ast, d, imported, generics, unitBinders, initBinders⟩ ← equationFront ast claims fileKey budget
  let functionJsons := ((ast.getObjVal? "functions").toOption.bind (·.getArr?.toOption)).getD #[]
  let all ← Fragment.decodeAstWithParams ast
  let fs := all.map Prod.fst
  if (fs.map (fun f => (f.name,f.namePos))).eraseDups.length != fs.length then throw "duplicate source function identities"
  let init ← Fragment.decodeInit ast
  -- A module whose only code is its initialization is checked through that
  -- unit alone; a module with neither runs nothing and states no claim.
  if fs.isEmpty && init.isEmpty then throw "no source code to verify: no function and no module initialization"
  -- A body reaches the file's other ordinary functions at their annotated
  -- signatures, and a function also reaches the module's constants at their
  -- annotations; each of those is established by its own unit.
  -- Imported values join them at the types their declarations state.
  -- A function's slot states the footprint its claim proposes, which its own
  -- unit certifies (`checkRequestResult`); an imported value states none.
  let footprintOf (g : Fragment.Fn) : Footprints.Closed :=
    ((d.functions.find? fun c => c.name == g.name && c.namePos == g.namePos).map (·.footprint)).getD .top
  let onThrowOf (g : Fragment.Fn) : Bool :=
    ((d.functions.find? fun c => c.name == g.name && c.namePos == g.namePos).map (·.onThrow)).getD false
  let moduleFunctions : List (SourceExtraction.ModuleValue Tree) :=
    (all.filterMap fun (g, tps) => if tps.isEmpty then
      some (g.name, g.namePos, (moduleArrow g (footprintOf g) (onThrowOf g)).map .written) else none) ++
    (imported.map fun (name, span, ty) => (name, span, .ok (.written ty))) ++
    (if arrays then [(SourceExtraction.arrayPrototypeName, (0, 0),
      Except.ok (.written (Json.mkObj [("top", toJson false), ("atoms", toJson [Json.mkObj
        [("a", toJson "graph"), ("label", toJson (StoreView.arrayProto d.types))]])])))] else [])
  -- Every immutable module value retains its initializer's checked claim and
  -- its annotation. The initialization unit checks both contracts; an
  -- annotation does not erase independently inferred facts such as call effects.
  -- A generic class is read at the instances its uses name, as a generic
  -- module function is (`generics`), not at its declaring unit's rows.
  let classNames := genericClassNames ((ast.getObjVal? "init").toOption.getD (.arr #[]))
  let moduleConstants : List (SourceExtraction.ModuleValue Tree) := init.flatMap fun
    | .constants _ bs => (bs.filter fun b => !classNames.contains b.name).map fun b =>
      (b.name, b.namePos, match (d.init.map (·.expressions)).getD [] |>.find? (·.pos == b.init.span) with
        | some e => .ok (.claimed e.type.ground b.annot)
        | none => .error s!"module constant '{b.name}' has no claimed initializer")
    | _ => []
  -- A class's instance members are closures created before the class value
  -- is bound, and run only once it is: they read it as its own binding
  -- (`Fragment.selfBindingOf`), which the initialization unit reads as a
  -- module value at the class's construct signature, the annotation its
  -- binding is checked at there, as a function reads a module constant. A
  -- generic class's is not one (the parser refuses its self-reads).
  let classSelves : List (SourceExtraction.ModuleValue Tree) := init.flatMap fun
    | .constants _ bs =>
      let ctors := bs.filterMap fun b => match b.init with
        | .ctor .. => some b.name
        | _ => none
      bs.filterMap fun b => match b.annot with
        | some ty =>
          if !classNames.contains b.name &&
              (ctors.contains b.name || ctors.contains (b.name ++ ".[[class]]")) then
            some (Fragment.selfBindingOf b.name, b.namePos, .ok (.written ty))
          else none
        | none => none
    | _ => []
  -- The initialization unit: the top-level code, as a body with no
  -- parameters that completes with `undefined`.
  let initUnit : List (Fragment.Fn × List Fragment.TypeParam × (Function Tree)) ← match init, d.init with
    | [], none => pure []
    | [], some _ => throw "module initialization claims for a source without initialization code"
    | _ :: _, none => throw "missing claims for the module initialization"
    | first :: _, some c =>
      let span := (first.pos.1, (init.getLast?.map (·.pos.2)).getD first.pos.2)
      let undefinedType := Json.mkObj [("top", toJson false),
        ("atoms", toJson [Json.mkObj [("a", toJson "undefined")]])]
      let binders ← classBinders ((ast.getObjVal? "init").toOption.getD (.arr #[]))
      if binders.map (·.name) != (initBinders.map (·.1)).filter (!·.endsWith "#pack") then
        throw "the module initialization's binders are not its generic classes'"
      -- Nothing calls the initialization unit with a receiver.
      pure [(⟨"", span, [], undefinedType, init, false, none⟩, binders,
        ⟨"", span, [], .labels [Labels.undef], c.entries, c.expressions, c.contracts, .top, false, c.arrows⟩)]
  -- Initialization order is the initialization unit's own obligation.
  if !initUnit.isEmpty then checkInitializationOrder d.types all init
  if all.length != d.functions.length then throw "function claim count mismatch"
  let units := all.map (fun (f, tps) => (f, tps, none)) ++
    initUnit.map (fun (f, tps, c) => (f, tps, some c))
  -- The units grow one store, in turn: a label one unit adds keeps its row
  -- for the next, so every request is over the store the last one leaves.
  let (T, plans) ← units.foldlM (init := (d.types, [])) fun (T, plans) (f,tps,initClaims) => do
    let d := { d with types := T }
    let module := if initClaims.isSome then moduleFunctions ++ classSelves
      else moduleFunctions ++ moduleConstants
    let mut c ← match initClaims with
      | some c => pure c
      | none => match d.functions.find? (fun c => c.name == f.name && c.namePos == f.namePos) with
        | some c => pure c
        | none => throw s!"missing claims for '{f.name}'"
    let mut module := module
    let mut d := d
    let mut f := f
    let unitSource := if initClaims.isSome then
        some (Json.mkObj [("body", (ast.getObjVal? "init").toOption.getD (.arr #[]))])
      else functionJsons.find? fun j =>
        (j.getObjValAs? String "name").toOption == some f.name &&
          (j.getObjValAs? Span "namePos").toOption == some f.namePos
    let owner := if initClaims.isSome then (0,0) else f.namePos
    let graph ← SourceFlow.build owner [] f.body
    let nested ← match unitSource with
      | some raw => SourceFlow.nestedGraphs raw
      | none => pure []
    let flowGraphs := graph :: nested
    let prologues ← prologueSites (unitSource.getD .null)
    checkPointSites flowGraphs prologues c.entries c.expressions c.contracts
    let sites := functionSites f
    let closures := (allFunctionSites f).2.2
    for a in c.arrows.getD [] do
      if !closures.contains a.pos then throw "per-arrow claims must name a source closure"
      for row in a.rows do
        checkPointSites flowGraphs prologues row.entries row.expressions row.contracts
        -- An expression body's entry is its prologue's, at the body's start.
        if !row.entries.all (fun e => (sites.1.contains e.start || prologues.any (·.1.1 == e.start)) &&
              a.pos.1 ≤ e.start && e.start < a.pos.2) ||
            !row.expressions.all (fun e => sites.2.contains e.pos && a.pos != e.pos &&
              a.pos.1 ≤ e.pos.1 && e.pos.2 ≤ a.pos.2) ||
            !row.contracts.all (fun c => a.pos.1 ≤ c.pos.1 && c.pos.2 ≤ a.pos.2) then
          throw "per-arrow claim site is outside its source closure"
    if c.hasScheme && tps.isEmpty && !(c.arrows.getD []).isEmpty then
      throw "per-arrow source claims are for ground closures, not quantified schemes"
    -- The unit's source tree, and the generic closures it creates, each
    -- graph code at its scheme row.
    let closures := match unitSource with
      | some j => Scheme.genericClosures ((j.getObjVal? "body").toOption.getD .null)
      | none => []
    let graphClosures := !closures.isEmpty
    -- The calls a scheme-typed local makes: a generic module value's calls
    -- name instances its slot holds (`Scheme.moduleInstances`) instead.
    let localCalls := (f.body.flatMap Fragment.Stmt.callees).filter fun call =>
      !generics.any (·.name == call.2.2.1)
    let mut sourceScheme : Option (SchemeRow Tree) := none
    if !tps.isEmpty then
      -- A generic unit is an ordinary graph request: each binder is read as
      -- its parameter row, a bounded one as its meet with its bound (an
      -- earlier binder's row, for a dependent bound), and the unit is
      -- certified at every assignment of those rows
      -- (`Parametricity.accepted_at`).
      let some source := unitSource
        | throw "a generic unit's source function is missing"
      if nestedBinders ((source.getObjVal? "body").toOption.getD .null) && !graphClosures then
        throw (sourceRefusal d.types f.namePos .genericValidation
          "a generic closure inside a generic body has binders of its own")
      let binders := if initClaims.isSome then initBinders else
        ((unitBinders.lookup (f.name, f.namePos)).getD [])
      if (binders.map (·.1)).filter (!·.endsWith "#pack") != tps.flatMap (fun p => ResolutionWire.ownedNames p.name p.resolution) then
        throw (sourceRefusal d.types f.namePos .genericValidation
          "a generic unit's binders are not the ones its declaration lowers")
      let resolution := ResolutionWire.groups (tps.map fun p => (p.name, p.resolution))
      if !resolution.isEmpty then
        sourceScheme := some {
          binders := binders.map (·.2.1)
          signatures := []
          bounds := binders.filterMap fun (n, p, B) =>
            if tps.any (·.name == n) then B.map (p, ·) else none
          resolution }
      let (T, rows) ← match binderRows d.types binders with
        | .ok r => pure r
        | .error reason => throw (sourceRefusal d.types f.namePos .genericValidation reason)
      let (T, atRows, scopes) ← if graphClosures || c.hasScheme then
          match Scheme.closureRows T rows closures localCalls c with
          | .ok r => pure r
          | .error reason => throw (sourceRefusal T f.namePos .schemeIntroduction reason)
        else
          let (T, atRows) := c.atRows T rows
          pure (T, atRows, [])
      d := { d with types := T }
      c := atRows
      let source := Scheme.annotationAtScopes T scopes rows source
      if initClaims.isSome then
        let body ← Fragment.decodeInit (Json.mkObj [("init", source.getObjValD "body")])
        f := { f with body }
      else
        f := (← Fragment.decodeFn source).1
    else if c.hasScheme then
      -- A scheme claim in a unit without binders of its own is a scheme row;
      -- a generic closure's code is graph code checked at its row's
      -- signatures.
      let some source := unitSource | throw "a unit's source function is missing"
      let (T, claims, scopes) ← match Scheme.closureRows d.types [] closures localCalls c with
        | .ok r => pure r
        | .error reason => throw (sourceRefusal d.types f.namePos .schemeIntroduction reason)
      d := { d with types := T }
      c := claims
      let source := Scheme.annotationAtScopes T scopes [] source
      if initClaims.isSome then
        let body ← Fragment.decodeInit (Json.mkObj [("init", source.getObjValD "body")])
        f := { f with body }
      else
        f := (← Fragment.decodeFn source).1
    let finish (d : Document EquationStore.State Tree) (module : List (SourceExtraction.ModuleValue Tree)) (c : Function Tree)
        (f : Fragment.Fn) : Except String (FunctionPlan EquationStore.State Tree) := do
      let mut d := d
      let mut module := module
      let mut c := c
      -- A generic module function this unit calls: its slot holds the instances
      -- the calls name, and those reads and calls are claimed at them. The
      -- unit's scheme claims are scheme rows by now (`Scheme.closureRows`).
      for g in generics.filter (fun g => !(initClaims.isSome && classNames.contains g.name)) do
        if (f.body.flatMap Fragment.Stmt.callees).any (·.2.2.1 == g.name) then
          match Scheme.moduleInstances d.types g f.body c sourceScheme
            (tps.flatMap fun p => ResolutionWire.ownedNames p.name p.resolution) with
          | .ok (T, slot, reads, calls) =>
            d := { d with types := T }
            -- The callee reads are claimed at the slot's type, which the
            -- source fixes; the producer's reading of them is not needed.
            let (A, T) ← match (Fragment.translate slot).run d.types with
              | .ok r => pure r
              | .error reason => throw (sourceRefusal d.types g.pos .schemeElimination reason)
            d := { d with types := T }
            module := module ++ [(g.name, g.pos, .ok (.written slot))]
            c := { c with expressions := c.expressions.map fun e =>
              if reads.contains e.pos then { e with type := .labels A }
              else if calls.contains e.pos then { e with instantiate := none } else e }
          | .error (.obligation failure, T) => throw (directFailure T failure)
          | .error (.exhausted failure limit rounds visited, T) =>
            throw (directFailure T failure (.exhausted limit rounds visited))
          | .error (.refusal pos role reason, _) => throw (sourceRefusal d.types pos role reason)
        -- A generic function or class the unit reads only as a value: its slot
        -- is its scheme.
        else if (Fragment.stmtsFreeNames f.body).contains g.name then
          match Scheme.moduleScheme d.types g with
          | .ok (T, slot) =>
            d := { d with types := T }
            module := module ++ [(g.name, g.pos, .ok (.written slot))]
          | .error reason => throw (sourceRefusal d.types g.pos .schemeIntroduction reason)
      let request ← extractNormalizedFn d.types f c.normalized module (SourceExtraction.sourceClasses init)
      return .graph f.name f.namePos { request with sourceScheme }
    -- A generic unit's graph extraction reports where it stops as a
    -- located refusal at the function, as the direct checker's do.
    let plan ← if tps.isEmpty then finish d module c f
      else tryCatch (finish d module c f) fun e =>
        throw (if (e.splitOn "obligation-diagnostic: ").length > 1 then e
          else sourceRefusal d.types f.namePos .genericValidation e)
    let .graph _ _ r := plan
    return (r.types, plans ++ [plan])
  return (T, plans)

end

end Verification.SourceClaimJson
