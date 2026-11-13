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

/-- A certified import's declared signatures: one plain signature, and
beside it a guard's promise at most, the promised signature of the same
actuals (`moduleArrow`'s guard). -/
def importedSignatures (T : EquationStore.State) (U : List Tree) :
    Except String (CallEffects.Arrow (List Tree) × Option Fragment.Guard) :=
  match PositiveRules.expand (SourceTypes.graph T) U with
  | [.arrs [a] []] => .ok (a, none)
  | [.arrs [a, g] []] => do
    let some p := g.effect.promise
      | throw "a certified import needs one fixed call signature and a guard's at most"
    if a.effect.promise.isSome || g.arguments != a.arguments || g.receiver != a.receiver ||
        ({ g.effect with promise := none } : CallEffects.Effect) != a.effect then
      throw "a certified import's guard is a signature of its plain one's actuals"
    let asserts : Bool := match p with
      | .asserts _ => true
      | .guards _ => false
    return (a, some { param := p.param, asserts, type := graphClaim g.result })
  | _ => throw "a certified import needs one fixed call signature"

/-- An import a certified unit stands for, read as the unit's module reads
the unit (`moduleArrow`): its declared signature, `U`'s one call signature,
with the unit's footprint and on-throw flag, its returned function's
signature with the footprint the unit proposes for it, and its extension
discarding further actuals, which the unit's code does. -/
def importedArrow (T : EquationStore.State) (U : List Tree) (footprint : Footprints.Closed) (onThrow : Bool)
    (result : Footprints.Closed) : Except String Json := do
  let (a, guard) ← importedSignatures T U
  if a.effect.promise.isSome then throw "a certified import's plain signature states no promise"
  let params : List Fragment.Param := a.arguments.zipIdx.map fun (A, i) => ⟨s!"p{i}", graphClaim A, false⟩
  let ret ← resultWithFootprint T (graphClaim a.result) result
  moduleArrow ⟨"", (0, 0), params, ret, [], false, guard, false, none, a.effect.pre, a.effect.ensures⟩
    footprint onThrow

/-- Whether a declaration's module is one with a body, whose functions a
module check certifies: a source file, not a declaration file. -/
def bodyModule (module : String) : Bool :=
  let ends := fun (x : String) => module.endsWith x
  (ends ".ts" || ends ".mts" || ends ".cts" || ends ".tsx" || ends ".js" || ends ".mjs" || ends ".cjs") &&
    !(ends ".d.ts" || ends ".d.mts" || ends ".d.cts")

/-- An effect stating nothing a caller may assume beyond the ordinary effect:
at most a precondition, which the caller discharges. -/
def assumesNothing (e : CallEffects.Effect) : Bool :=
  ({ e with pre := [], requires := none } : CallEffects.Effect) == CallEffects.Effect.ofFootprint .top

/-- **An import with a body read at its declared type, with no entry**
(`ordinaryImport`): what the declaration's signatures state of a call beyond
its precondition (a footprint, a postcondition, fresh results, a promise, a
throw bound, regions) its module's check certifies only through a published
entry (`importedArrow`), so without one each signature is read at the
ordinary effect, its precondition kept. A declared type whose signatures
assume nothing is read as written; one that is no clause of signatures, or
whose rest signatures assume something, is read as written where its
signatures assume nothing and refused otherwise. -/
def ordinaryImport (T : EquationStore.State) (U : List Tree) : Except String Json := do
  let claim (V : List Tree) : Json := Json.mkObj [("top", toJson false), ("atoms", Json.arr (V.map fun l =>
    Json.mkObj [("a", toJson "graph"), ("label", Tree.toJson l)]).toArray)]
  match PositiveRules.expand (SourceTypes.graph T) U with
  | [.arrs L S] =>
    if L.all (assumesNothing ·.effect) && S.all (assumesNothing ·.effect) then return graphClaim U
    if !S.all (assumesNothing ·.effect) || L.isEmpty then
      throw "an import with a body whose variadic signature states an effect is read only at its module's entry"
    let ordinary (e : CallEffects.Effect) : CallEffects.Effect :=
      { CallEffects.Effect.ofFootprint .top with pre := e.pre, requires := e.requires }
    let signature (a : CallEffects.Arrow (List Tree)) : Json :=
      Json.mkObj [("a", toJson "function"), ("this", claim a.receiver),
        ("params", toJson (a.arguments.map claim)), ("result", claim a.result), ("construct", toJson "unknown"),
        ("array", toJson "unknown"), ("effect", toJson (ordinary a.effect))]
    let atoms := L.map signature
    let atom := match atoms with
      | [a] => a
      | a :: rest => a.setObjVal! "and" (toJson rest)
      | [] => Json.null
    return Json.mkObj [("top", toJson false), ("atoms", toJson [atom])]
  | _ => return graphClaim U

/-- The units of one name are the overloads of one declaration: each runs the
implementation's code, so they share their parameters' names, their body,
their type parameters, their completion and their strictness. -/
def sameCodeOverloads (functionJsons : Array Json) : Except String Unit := do
  let named := functionJsons.toList.filterMap fun f => (f.getObjValAs? String "name").toOption.map (·, f)
  let names (j : Json) : List Json :=
    ((j.getObjValAs? (Array Json) "params").toOption.getD #[]).toList.map (·.getObjValD "name")
  for (name, f) in named do
    if let some (_, g) := named.find? (·.1 == name) then
      if ["body", "typeParams", "completion", "strict"].any (fun k => g.getObjValD k != f.getObjValD k) ||
          names g != names f then
        throw s!"the units of {name} are no overloads of one declaration's code"

/-- A module function's slot from its units' signatures (`moduleArrow`), one
unit's or, for a declaration with overloads, every overload's: one function
holding them all, as an imported declaration with overloads is read. -/
def overloadSlot (arrows : List Json) : Except String Json := do
  let atoms ← arrows.mapM fun a => match a.getObjValD "atoms" with
    | .arr #[atom] => pure atom
    | _ => throw "a module function's slot is one function"
  let conjuncts (atom : Json) : List Json := ((atom.getObjValAs? (Array Json) "and").toOption.getD #[]).toList
  let alone : Json → Json
    | .obj kvs => Json.mkObj (kvs.toList.filter (·.1 != "and"))
    | j => j
  match atoms with
  | [] => throw "a module function has a unit"
  | [_] => match arrows with
    | [a] => pure a
    | _ => throw "a module function's slot is one function"
  | first :: rest =>
    let extra := conjuncts first ++ rest.flatMap fun atom => alone atom :: conjuncts atom
    return Json.mkObj [("top", toJson false), ("atoms", toJson [(alone first).setObjVal! "and" (toJson extra)])]

/-- What a file's units share: its document and claims read once (the
equations, the module environment, the generic instances, the
initialization's claims and order), and its units, each a function or the
module's initialization with its claims. Every input a unit's extraction
reads beside its own code and claims is a field of the front. -/
structure Front where
  ast : Json
  d : Document EquationStore.State Tree
  functionJsons : Array Json
  init : List Fragment.Stmt
  generics : List Instantiable
  unitBinders : List ((String × Span) × List (String × Tree × Option (List Tree)))
  initBinders : List (String × Tree × Option (List Tree))
  classNames : List String
  freshConstructors : List (String × Span)
  moduleFunctions : List (SourceExtraction.ModuleValue Tree)
  moduleConstants : List (SourceExtraction.ModuleValue Tree)
  classSelves : List (SourceExtraction.ModuleValue Tree)
  /-- The units in order: the functions, then the initialization, with its
  claims. -/
  units : List (Fragment.Fn × List Fragment.TypeParam × Option (Function Tree))
  /-- The local names of the qualified reads. -/
  qualifiedNames : List String
  /-- The initialization order's refusal, the initialization unit's own. -/
  initOrder : Option String
  /-- The module cells whose objects the module owns
  (`SourceExtraction.ownedModuleCells`), over every unit's code. -/
  moduleOwned : List String
  /-- Each unit's units reached by name (`Front.edgesOf`), by its index. -/
  edgeTable : Array (List Nat)
  /-- Each unit's group (`Front.groupOf`), by its index. -/
  groupTable : Array (List Nat)
  /-- The imported values at their declared types, by local name and span,
  which `Front.withQualified` reads again. -/
  imported : List (String × Span × List Tree)

/-- A unit's identity on the wire: a function's name and its name's start,
or `init` for the module's initialization. -/
def Front.unitId (fr : Front) (i : Nat) : String :=
  match fr.units[i]? with
  | some (_, _, some _) => "init"
  | some (f, _, none) => s!"{f.name}@{f.namePos.1}"
  | none => ""

/-- A source's item in the work table (`SinglePass.work`): the first twelve
digits of its `sourceSha256`. -/
def fileItem (ast : Json) : String := ((ast.getObjValAs? String "sourceSha256").toOption.getD "").take 12 |>.toString

/-- A function's item in the work table: its source's, then its unit's
identity (`init` for the initialization, whose function has no name). -/
def Front.fnItem (fr : Front) (f : Fragment.Fn) : String :=
  s!"{fileItem fr.ast}#{if f.name.isEmpty then "init" else s!"{f.name}@{f.namePos.1}"}"

/-- Unit `i`'s item in the work table. -/
def Front.workItem (fr : Front) (i : Nat) : String := s!"{fileItem fr.ast}#{fr.unitId i}"

/-- The item of the function named `n` in the work table: its first unit's. -/
def Front.nameItem (fr : Front) (n : String) : String :=
  match (List.range fr.units.length).find? fun i => match fr.units[i]? with
      | some (f, _, none) => f.name == n
      | _ => false with
  | some i => fr.workItem i
  | none => s!"{fileItem fr.ast}#{n}"

/-- Every name a unit's code mentions, bound or not: its body's, its
parameter defaults' and its closures' (`stmtNames`). -/
def Front.mentions (fr : Front) (i : Nat) : List String :=
  match fr.units[i]? with
  | some (_, _, some _) => fr.init.flatMap stmtNames
  | some (f, _, none) => f.body.flatMap stmtNames
  | none => []

/-- The names the initialization owns: the bindings its statements declare,
the module constants and cells, the generic classes and the classes' self
bindings. -/
def Front.initNames (fr : Front) : List String :=
  fr.init.flatMap Fragment.Stmt.bound ++ fr.moduleConstants.map (·.1) ++ fr.classSelves.map (·.1) ++
    fr.classNames

/-- The units a unit's code reaches by name: a module function's unit for
its name, and the initialization for a name the initialization owns. -/
def Front.edgesOf (fr : Front) (i : Nat) : List Nat :=
  let names := fr.mentions i
  let owned := fr.initNames
  (List.range fr.units.length).filter fun j => j != i && match fr.units[j]? with
    | some (_, _, some _) => names.any owned.contains
    | some (g, _, none) => names.contains g.name
    | none => false

/-- The units a unit's code reaches by name, as `edgesOf` gives them,
computed once (`Front.indexed`). -/
def Front.edges (fr : Front) (i : Nat) : List Nat := fr.edgeTable.getD i []

/-- The units a unit reaches, transitively: its edges, grown by their
units' edges until none is added. -/
def Front.reach (fr : Front) (i : Nat) : List Nat := Id.run do
  let mut seen := fr.edges i
  for _ in List.range (fr.units.length + 1) do
    let grown := (seen ++ seen.flatMap fr.edges).eraseDups
    if grown.length == seen.length then break
    seen := grown
  return seen

/-- A unit's group: itself and every unit that reaches it and that it
reaches, in order. Its members are certified together. -/
def Front.groupOf (fr : Front) (reaches : Array (List Nat)) (i : Nat) : List Nat :=
  (List.range fr.units.length).filter fun j =>
    j == i || ((reaches.getD i []).contains j && (reaches.getD j []).contains i)

/-- The front with each unit's edges and group computed once. -/
def Front.indexed (fr : Front) : Front :=
  let fr := { fr with edgeTable := (List.range fr.units.length).toArray.map fr.edgesOf }
  let reaches := (List.range fr.units.length).toArray.map fr.reach
  { fr with groupTable := (List.range fr.units.length).toArray.map (fr.groupOf reaches) }

/-- A unit's group (`groupOf`), as `indexed` computed it. -/
def Front.group (fr : Front) (i : Nat) : List Nat := fr.groupTable.getD i []

/-- The groups' first members, in order: each group's identity. -/
def Front.leaders (fr : Front) : List Nat :=
  (List.range fr.units.length).filter fun i => (fr.group i).head? == some i

/-- A group's dependencies: the groups its members reach directly outside
it, each by its first member. -/
def Front.dependencies (fr : Front) (group : List Nat) : List Nat :=
  ((group.flatMap fr.edges).filter (!group.contains ·) |>.map fun j => ((fr.group j).head?).getD j).eraseDups

/-- The slots of the file's ordinary functions of the given names. A
function's slot states the footprint its claim proposes, which its own unit
certifies (`checkRequestResult`); its result states the footprint its claim
proposes for the function it returns, which its unit's returns establish
(`resultWithFootprint`). A declaration with overloads is one unit per
overload, each its code at that overload's signature (SOURCE-ELABORATION.md,
"Module functions"): the units of one name run one code, and its slot holds
every overload. -/
def ordinarySlots (d : Document EquationStore.State Tree) (ordinary : List Fragment.Fn) (names : List String) :
    List (SourceExtraction.ModuleValue Tree) :=
  let claimOf (g : Fragment.Fn) : Option (Function Tree) :=
    d.functions.find? fun c => c.name == g.name && c.namePos == g.namePos
  let returning (g : Fragment.Fn) : Except String Fragment.Fn := do
    return { g with ret := ← resultWithFootprint d.types g.ret (((claimOf g).map (·.resultFootprint)).getD .top) }
  -- A statement with store regions is certified by its unit's regional
  -- check (`regionalResult`): the slot states it.
  let slotOf (u : Fragment.Fn) : Except String Json := do
    let r ← returning u
    let c := claimOf u
    match u.stated.bind fun (s : CallEffects.Effect) => if s.regions.isEmpty then none else some s with
    | some s => moduleArrow r s.closed s.onThrow false s.regions
    | none =>
      let fresh := u.stated.any (·.fresh : CallEffects.Effect → Bool)
      moduleArrow r ((c.map (·.footprint)).getD .top) ((c.map (·.onThrow)).getD false) fresh
  names.filterMap fun name => do
    let units := ordinary.filter (·.name == name)
    let g ← units.head?
    some (name, g.namePos, (do overloadSlot (← units.mapM slotOf)).map .written)

/-- The front of a source's units. A qualified import, by its name, is read
at its certified unit's footprint and on-throw flag (`importedArrow`); every
other at its declared type. With `lenient` (mode 8), a qualified import
whose declared type `importedArrow` does not read is at its declared type. -/
def fileFront (ast claims : Json) (fileKey : String)
    (budget : PositiveCertificates.SearchBudget := {})
    (qualified : List (String × Footprints.Closed × Bool × Footprints.Closed) := []) (lenient : Bool := false) :
    Except String Front := do
  -- A source with arrays lists `ArrayProto`: its units see `Array.prototype`.
  let arrays := match (ast.getObjVal? "declarations").toOption.bind
      (fun doc => (doc.getObjVal? "definitions").toOption) with
    | some (.arr ds) => ds.any fun d =>
        EquationLowering.ImplicitDependency.arrayProto.selects (d.getObjValD "declaration")
    | _ => false
  -- The standard Error contract allocates an unpublished object identity.
  -- Own-location freshness alone permits a shared object with no own keys.
  let freshConstructors : List (String × Span) := (((ast.getObjVal? "declarations").toOption.bind
      (fun doc => (doc.getObjVal? "values").toOption.bind (·.getArr?.toOption))).getD #[]).toList.filterMap fun value => do
    let binding ← (value.getObjVal? "binding").toOption
    let declaration ← (value.getObjVal? "declaration").toOption
    if (binding.getObjValAs? String "specifier").toOption != some "global" ||
        (binding.getObjValAs? String "imported").toOption != some "Error" ||
        (declaration.getObjValAs? String "module").toOption != some "typescript/lib/lib.es5.d.ts" ||
        (declaration.getObjValAs? String "name").toOption != some "Error" then none else
      some (← (binding.getObjValAs? String "local").toOption,
        ← (fromJson? (binding.getObjValD "span") : Except String Span).toOption)
  -- The imported values whose declarations are in modules with a body.
  let bodyImports : List (String × Span) := (((ast.getObjVal? "declarations").toOption.bind
      (fun doc => (doc.getObjVal? "values").toOption.bind (·.getArr?.toOption))).getD #[]).toList.filterMap fun value => do
    let binding ← (value.getObjVal? "binding").toOption
    let declaration ← (value.getObjVal? "declaration").toOption
    let module ← (declaration.getObjValAs? String "module").toOption
    if !bodyModule module then none else
    some (← (binding.getObjValAs? String "local").toOption,
      ← (fromJson? (binding.getObjValD "span") : Except String Span).toOption)
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
  sameCodeOverloads functionJsons
  let ordinary := (all.filter (·.2.isEmpty)).map (·.1)
  let moduleFunctions : List (SourceExtraction.ModuleValue Tree) :=
    ordinarySlots d ordinary (ordinary.map (·.name)).eraseDups ++
    (imported.map fun (name, span, U) =>
      -- An import with a body, read at no entry, at the ordinary effect
      -- (`ordinaryImport`); a declaration-only import at its declaration.
      let declared : Except String (SourceExtraction.ModuleType Tree) :=
        if bodyImports.contains (name, span) then (ordinaryImport d.types U).map .written
        else .ok (.written (graphClaim U))
      (name, span, match qualified.lookup name with
      | some (footprint, onThrow, result) => match importedArrow d.types U footprint onThrow result with
        | .ok J => .ok (.written J)
        | .error e => if lenient then declared else .error e
      | none => declared)) ++
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
    -- A module cell, at the contract the initialization unit claims for it
    -- (SOURCE-ELABORATION.md, "Module cells").
    | .mutables _ bs => (bs.filter (·.early)).map fun b =>
      (b.name, b.namePos, match ((d.init.map (·.contracts)).getD []).find? (fun c => c.pos == b.init.span && c.name == b.name) with
        | some c => .ok (.cell c.type.ground)
        | none => .error s!"module cell '{b.name}' has no claimed storage contract")
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
      pure [(⟨"", span, [], undefinedType, init, false, none, false, none, [], []⟩, binders,
        ⟨"", span, [], .labels [Labels.undef], c.entries, c.expressions, c.contracts, .top, false, .top, c.arrows⟩)]
  -- Initialization order is the initialization unit's own obligation.
  let initOrder := if initUnit.isEmpty then none else match checkInitializationOrder d.types all init with
    | .ok () => none
    | .error reason => some reason
  if all.length != d.functions.length then throw "function claim count mismatch"
  let units := all.map (fun (f, tps) => (f, tps, none)) ++
    initUnit.map (fun (f, tps, c) => (f, tps, some c))
  return Front.indexed ⟨ast, d, functionJsons, init, generics, unitBinders, initBinders, classNames, freshConstructors,
    moduleFunctions, moduleConstants, classSelves, units, qualified.map (·.1), initOrder,
    SourceExtraction.ownedModuleCells init (all.map (·.1.body)) (← Fragment.decodeOmittedMentions ast),
    #[], #[], imported⟩

/-- The front `fileFront` gives with the qualified reads `qualified`, of a
front it gave with none (`lenient`, mode 8): each imported value the reads
name at its certified unit's footprint and on-throw flag
(`importedArrow`), else at its declared type. -/
def Front.withQualified (fr : Front)
    (qualified : List (String × Footprints.Closed × Bool × Footprints.Closed)) : Front :=
  { fr with
    moduleFunctions := fr.moduleFunctions.map fun v =>
      match fr.imported.find? (fun (n, span, _) => n == v.1 && span == v.2.1), qualified.lookup v.1 with
      | some (_, _, U), some (footprint, onThrow, result) => match importedArrow fr.d.types U footprint onThrow result with
        | .ok J => (v.1, v.2.1, .ok (.written J))
        | .error _ => v
      | _, _ => v
    qualifiedNames := qualified.map (·.1) }

/-- What replaces a unit's claims before its extraction, where one does:
its claims with the types a computation gives (`Synthesis.retypeUnit`), over
a grown store. -/
abbrev Retype := Front → EquationStore.State → Fragment.Fn → SourceClaims.Function Tree →
  List (SourceExtraction.ModuleValue Tree) → Option (SchemeRow Tree × List String) →
  Except String (EquationStore.State × SourceClaims.Function Tree)

/-- What states a unit's calls' type arguments before its generic module
values are instantiated, where a computation gives them: its claims with
each such call's, over a grown store. -/
abbrev Instances := Front → EquationStore.State → Fragment.Fn → Function Tree →
  List (SourceExtraction.ModuleValue Tree) → Option (SchemeRow Tree × List String) →
  Except String (EquationStore.State × Function Tree)

/-- What claims a unit's generic closures at their schemes where no claim
names them, before their scheme rows are made (`Scheme.closureRows`): from
the unit's source tree, over a grown store. -/
abbrev ClosureSchemes := EquationStore.State → Json →
  Except String (EquationStore.State × List (Expression Tree))

/-- One unit's plan, extracted from the front over the store `T`. -/
def extractMember (fr : Front) (T : EquationStore.State)
    (u : Fragment.Fn × List Fragment.TypeParam × Option (Function Tree)) (retype : Option Retype := none)
    (instances : Option Instances := none) (closureSchemes : Option ClosureSchemes := none) :
    Except String (EquationStore.State × FunctionPlan EquationStore.State Tree) := do
  let ⟨ast, d, functionJsons, init, generics, unitBinders, initBinders, classNames, freshConstructors,
    moduleFunctions, moduleConstants, classSelves, _, _, initOrder, moduleOwned, _, _, _⟩ := fr
  let (f, tps, initClaims) := u
  if let (some _, some reason) := (initClaims, initOrder) then throw reason
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
  -- The unit's source tree, and the generic closures it creates, each
  -- graph code at its scheme row.
  let closures := match unitSource with
    | some j => Scheme.genericClosures ((j.getObjVal? "body").toOption.getD .null)
    | none => []
  -- Per-arrow claims are a ground closure's, one set per signature it
  -- advertises; a generic closure is checked at its scheme row.
  if (c.arrows.getD []).any fun a => closures.any (·.span == a.pos) then
    throw "per-arrow source claims are for ground closures, not quantified schemes"
  let graphClosures := !closures.isEmpty
  -- A generic closure no claim names, claimed at its scheme where a hook
  -- states one (the claims-free front's, from its annotations).
  if let (some h, some j) := (closureSchemes, unitSource) then
    if closures.any fun gc => !c.expressions.any (·.pos == gc.span) then
      let (T, es) ← h d.types ((j.getObjVal? "body").toOption.getD .null)
      d := { d with types := T }
      c := { c with expressions := c.expressions ++ es.filter fun e => !c.expressions.any (·.pos == e.pos) }
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
  -- The calls' type arguments, where computed (`instances`).
  if let some h := instances then
    let (T, c') ← h fr d.types f c module (sourceScheme.map fun row =>
      (row, tps.flatMap fun p => ResolutionWire.ownedNames p.name p.resolution))
    d := { d with types := T }
    c := c'
  let finish (d : Document EquationStore.State Tree) (module : List (SourceExtraction.ModuleValue Tree)) (c : Function Tree)
      (f : Fragment.Fn) : Except String (FunctionPlan EquationStore.State Tree) := do
    let mut d := d
    let mut module := module
    let mut c := c
    -- A generic module function this unit calls: its slot holds the instances
    -- the calls name, and those reads and calls are claimed at them. The
    -- unit's scheme claims are scheme rows by now (`Scheme.closureRows`).
    for g in generics.filter (fun g => !(initClaims.isSome && classNames.contains g.name)) do
      let prepared : Except String (Document EquationStore.State Tree × List (SourceExtraction.ModuleValue Tree) × Function Tree) := do
        let mut d := d
        let mut module := module
        let mut c := c
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
        return (d, module, c)
      match prepared with
      | .ok (next, bindings, claims) =>
        d := next
        module := bindings
        c := claims
      | .error reason => throw reason
    let (types, claims) ← match retype with
      | some r => r fr d.types f c.normalized module (sourceScheme.map fun row =>
          (row, tps.flatMap fun p => ResolutionWire.ownedNames p.name p.resolution))
      | none => pure (d.types, c.normalized)
    let request ← extractNormalizedFn types f claims module (SourceExtraction.sourceClasses init) freshConstructors
      moduleOwned
    return .graph f.name f.namePos { request with sourceScheme }
  -- A generic unit's graph extraction reports where it stops as a
  -- located refusal at the function, as the direct checker's do.
  let plan ← if tps.isEmpty then finish d module c f
    else tryCatch (finish d module c f) fun e =>
      throw (if RequestJson.hasDiagnostic e then e
        else sourceRefusal d.types f.namePos .genericValidation e)
  let .graph _ _ r := plan
  return (r.types, plan)

/-- Whether a group's code mentions a qualified read. -/
def Front.readsQualified (fr : Front) (group : List Nat) : Bool :=
  group.any fun i => (fr.mentions i).any fr.qualifiedNames.contains

end

end Verification.SourceClaimJson
