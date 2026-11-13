import Verification.Source.Claims.Extraction
import Verification.Source.EffectJson

/-! Certified imports (SOURCE-CONTRACTS.md, "Certified imports"): which module
units the importer's claims read qualified, the structural correspondence of
the two readings of each one's signature, and the module documents the one
check certifies, each restricted to its certified set. -/
namespace Verification.SourceClaimJson
open Lean

/-- A module run the check certifies: its identity, its document restricted
to its certified set, its claims restricted alike, and its own qualified
reads, each with its unit's footprint and on-throw flag. -/
structure ModuleRun where
  location : String
  ast : Json
  claims : Json
  qualified : List (String × Footprints.Closed × Bool × Footprints.Closed)

/-- What certified imports give the check: the importer's document and claims
without modules, the importer's qualified reads by name, each with its unit's
footprint and on-throw flag, and the module runs. -/
structure ImportPlan where
  ast : Json
  claims : Json
  qualified : List (String × Footprints.Closed × Bool × Footprints.Closed)
  modules : List ModuleRun
  /-- The module units each qualified read's footprint rests on, by the
  read's local name: the units mode 8 checks in the same invocation
  (`fragmentPlansWithModules`). -/
  depends : List (String × List String)

section correspondence

/-- A term or definition with each symbol key, an index into its document's
`symbols`, replaced by that symbol's declaration identity. -/
partial def canonical (symbols : Array Json) : Json → Json
  | .arr xs => .arr (xs.map (canonical symbols))
  | .obj kvs => Json.mkObj (kvs.toArray.toList.map fun (k, v) =>
      (k, match k, v with
        | "symbol", .num n =>
          if n.exponent == 0 && n.mantissa ≥ 0 then (symbols[n.mantissa.toNat]?).getD v else v
        | _, _ => canonical symbols v))
  | j => j

/-- The declarations a term references, by identity. -/
partial def referenced : Json → List Json
  | .arr xs => xs.toList.flatMap referenced
  | j@(.obj _) =>
    let here := match j.getObjVal? "reference" with
      | .ok r => ((r.getObjVal? "target").toOption).toList
      | .error _ => []
    here ++ (match j with
      | .obj kvs => kvs.toArray.toList.flatMap fun (_, v) => referenced v
      | _ => [])
  | _ => []

/-- Whether a term or definition holds an array or tuple term, whose
lowering reads the document's `ArrayProto`. -/
partial def mentionsArray : Json → Bool
  | .arr xs => xs.any mentionsArray
  | j@(.obj kvs) =>
    (match j.getObjVal? "k" with | .ok (.str "array") | .ok (.str "tuple") => true | _ => false) ||
      kvs.toArray.any fun (_, v) => mentionsArray v
  | _ => false

/-- Whether a term or definition holds a resolution-qualified binder, whose
scheme's domain lowering takes relative to `%Stable%` and native `Promise`. -/
partial def mentionsResolution : Json → Bool
  | .arr xs => xs.any mentionsResolution
  | j@(.obj kvs) =>
    (match j.getObjVal? "resolution" with | .ok .null | .error _ => false | .ok _ => true) ||
      kvs.toArray.any fun (_, v) => mentionsResolution v
  | _ => false

/-- Whether lowering a term or definition reads the implicit dependency `d`. -/
def triggers : EquationLowering.ImplicitDependency → Json → Bool
  | .arrayProto, j => mentionsArray j
  | .stable, j | .promise, j => mentionsResolution j

/-- A declaration document's parts the comparison reads: its definitions,
its symbols and its written applications. -/
structure Reading where
  definitions : List Json
  symbols : Array Json
  applications : List Json

def Reading.of (declarations : Json) : Except String Reading := do
  return ⟨← jArr declarations "definitions", (← jArr declarations "symbols").toArray,
    ← jArr declarations "applications"⟩

def Reading.definition (r : Reading) (id : Json) : Option Json :=
  r.definitions.find? fun d => (d.getObjVal? "declaration").toOption == some id

/-- The identities of a reading's definitions lowering reads implicitly as `d`. -/
def Reading.implicit (r : Reading) (d : EquationLowering.ImplicitDependency) : List Json :=
  (r.definitions.map (·.getObjValD "declaration")).filter d.selects

/-- The written applications a reading lists in the declaration `site`
names (`module#name`), each with its symbol keys by identity and without its
span, which only the document whose own file it is written in has. -/
def Reading.applicationsAt (r : Reading) (site : String) : List Json :=
  (r.applications.filter fun a => (a.getObjValAs? String "site").toOption == some site).map fun a =>
    canonical r.symbols (a.setObjVal! "span" .null)

/-- The site name of a declaration identity. -/
def siteOf (id : Json) : String :=
  s!"{(id.getObjValAs? String "module").toOption.getD ""}#{(id.getObjValAs? String "name").toOption.getD ""}"

/-- **The two readings agree.** The terms `a` (the importer's) and `b` (the
module's) are equal once their symbol keys name declarations, and so,
recursively, is every declaration either reaches: its definition in each
reading, both present and equal, or both absent (a declaration neither
document defines, the standard library's, which both read alike). The
declarations lowering reads implicitly (`ImplicitDependency`) where a term
reached triggers them, `ArrayProto` for an array or tuple term, `%Stable%`
and native `Promise` for a resolution-qualified binder, are reached as an
explicit reference is, the same identities in both readings. In each declaration reached, and in the
`sites` given, both readings list the same written applications, whose
arguments and bounds reach declarations in turn. A visited set closes
recursive definitions; a mismatch is refused, never proved equivalent. -/
partial def sameReading (ra rb : Reading) (sites : List String) (pairs : List (Json × Json)) :
    Except String Unit := do
  let mut work : List Json := []
  let mut triggered : List EquationLowering.ImplicitDependency := []
  let trigger (ts : List EquationLowering.ImplicitDependency) (j : Json) :=
    ts ++ EquationLowering.ImplicitDependency.all.filter fun d => !ts.contains d && triggers d j
  for (a, b) in pairs do
    if canonical ra.symbols a != canonical rb.symbols b then
      throw "the importer's and the module's readings of an imported signature differ"
    work := work ++ referenced a ++ referenced b
    triggered := trigger (trigger triggered a) b
  let mut seen : List Json := []
  let mut siteWork := sites
  let mut seenSites : List String := []
  for _ in [0:100000] do
    if let site :: rest := siteWork then
      siteWork := rest
      if seenSites.contains site then continue
      seenSites := site :: seenSites
      let as := ra.applicationsAt site
      let bs := rb.applicationsAt site
      if as.length != bs.length || !as.all (fun x => as.count x == bs.count x) then
        throw s!"the importer's and the module's readings of the written applications in {site} differ"
      for x in as do
        work := work ++ referenced x
        triggered := trigger triggered x
      continue
    match work with
    | [] =>
      -- The implicit dependencies the terms reached trigger, by identity in
      -- each reading: the same declarations in both, reached in turn.
      let mut more : List Json := []
      for d in triggered do
        let ia := ra.implicit d
        let ib := rb.implicit d
        if ia.length != ib.length || !ia.all ib.contains then
          throw s!"a declaration one reading of an imported signature reads implicitly and the other lacks: {repr d}"
        more := more ++ ia.filter (!seen.contains ·)
      if more.isEmpty then return ()
      work := more
    | id :: rest =>
      work := rest
      if seen.contains id then continue
      seen := id :: seen
      siteWork := siteWork ++ [siteOf id]
      match ra.definition id, rb.definition id with
      | none, none => pure ()
      | some da, some db =>
        if canonical ra.symbols da != canonical rb.symbols db then
          throw s!"the importer's and the module's readings of a declaration differ: {id.compress}"
        work := work ++ referenced da
        triggered := trigger triggered da
      | _, _ => throw s!"a declaration one reading of an imported signature reaches and the other lacks: {id.compress}"
  throw "the readings of an imported signature reach too many declarations"

end correspondence

/-- Whether a span holds another. -/
private def within (inner outer : Span) : Bool := outer.1 ≤ inner.1 && inner.2 ≤ outer.2

/-- A module's code, decoded: its functions, then its top-level code. -/
private def decodeCode (m : Fragment.ModuleAst) : Except String (List Fragment.Fn × List Fragment.Stmt) := do
  let functions ← (← jArr m.document "functions").mapM fun f => do return (← Fragment.decodeFn f).1
  return (functions, ← Fragment.decodeInit m.document)

/-- Each module's code (`decodeCode`) by its location, the first module of
that location's, decoded at most once, where a read first asks for it. -/
abbrev ModuleCode := Std.HashMap String (Thunk (Except String (List Fragment.Fn × List Fragment.Stmt)))

def ModuleCode.of (fragmentModules : List Fragment.ModuleAst) : ModuleCode :=
  fragmentModules.foldl (init := {}) fun m mod => m.insertIfNew mod.location (Thunk.mk fun _ => decodeCode mod)

/-- The imported value a qualified read names, among a document's `values`. -/
private def importedValue (values : List Json) (q : Json) : Option Json :=
  values.find? fun v => (v.getObjVal? "declaration").toOption == some q

/-- A read of an import that names an eligible unit of its origin whose
two signature readings agree: the importer's binding of it and the unit's
fragment. The import `q`, a declaration identity, is an imported value of
the importer's declarations; its module is one the fragment lists; the unit
is a function of that module, its name the declaration's, its name within
the declaration's span; it has no binders, no rest and no receiver;
no code of its module writes its binding; the import is a function of one
fixed call signature of no rest, receiver, binders or promise, or, for a
unit with a guard, of that signature and beside it the promise signature
of the same actuals and effect stating the unit's promise (`guards k`,
`asserts k`: the pair `importedSignatures` reads); the import's signature
and the unit state the same precondition and postcondition; and the two
readings of its signature agree (`sameReading`), the promised type's
among them. -/
private def eligibleRead (importer : Reading) (values : List Json) (fragmentModules : List Fragment.ModuleAst)
    (code : ModuleCode) (q : Json) (location name : String) (span : Span) :
    Except String (String × Json) := do
  let some v := importedValue values q
    | throw s!"a qualified read names no imported value: {q.compress}"
  let binding ← jField v "binding"
  let localName ← jStr (← jField binding "local")
  let some m := fragmentModules.find? (·.location == location)
    | throw s!"a qualified read names a module the fragment does not list: {location}"
  let fs ← jArr m.document "functions"
  let some unit := fs.find? fun f => (f.getObjValAs? String "name").toOption == some name &&
      ((f.getObjValAs? Span "namePos").toOption.map (within · span)).getD false
    | throw s!"a qualified read names no unit of its origin: {location}#{name}"
  -- Eligible: no binders, no rest and no receiver, on both readings.
  let params ← jArr unit "params"
  if !(← jArr unit "typeParams").isEmpty ||
      params.any (fun p => (p.getObjVal? "rest").isOk || (p.getObjValAs? String "name").toOption == some "this") then
    throw s!"a qualified read names a unit that is not eligible: {location}#{name}"
  -- Stable: no code of the module the document holds writes the binding;
  -- the parser refuses a module whose code it does not lower writes it.
  let (functions, init) ← match code[location]? with
    | some decoded => decoded.get
    | none => decodeCode m
  if (init ++ functions.flatMap (·.body)).any (SourceExtraction.assignsStmt name) then
    throw s!"a qualified read names a unit whose module writes its binding: {location}#{name}"
  let declared ← jField v "type"
  if (v.getObjValD "construct") != .bool false || !(← jArr v "typeParams").isEmpty then
    throw s!"a qualified read names an import that is not eligible: {location}#{name}"
  -- The plain signature, and a guard's promise signature beside it: the
  -- same actuals, receiver and effect, stating the unit's promise.
  let guard := unit.getObjValD "guard"
  let (type, promised) ← match guard, declared.getObjValD "k" with
    | .null, _ => pure (declared, none)
    | _, .str "intersection" => match declared.getObjValD "parts" with
      | .arr #[a, g] => do
        let promise ← jField (← jField g "effect") "promise"
        let param ← jField guard "param"
        let asserts ← jField guard "asserts"
        let stated := Json.mkObj [((if asserts == .bool true then "asserts" else "guards"),
          Json.mkObj [("param", param)])]
        let unpromised := (← jField g "effect").setObjVal! "promise" .null
        if (g.getObjValD "k") != .str "function" || promise != stated || unpromised != (← jField a "effect") ||
            (g.getObjValD "params") != (a.getObjValD "params") || (g.getObjValD "rest") != (a.getObjValD "rest") ||
            (g.getObjValD "receiver") != (a.getObjValD "receiver") then
          throw s!"a qualified read names a guard whose declared signatures are not its plain and promise ones: {location}#{name}"
        pure (a, some ((← jField g "result"), (← jField guard "type")))
      | _ => throw s!"a qualified read names a guard whose declared type is not two signatures: {location}#{name}"
    | _, _ => throw s!"a qualified read names a guard whose declared type is not two signatures: {location}#{name}"
  if (type.getObjValD "k") != .str "function" || (type.getObjValD "rest") != .null ||
      (type.getObjValD "receiver") != .null then
    throw s!"a qualified read names an import that is not eligible: {location}#{name}"
  let effect ← jField type "effect"
  if (effect.getObjValD "promise") != .null then
    throw s!"a qualified read names an import with a promise: {location}#{name}"
  -- The importer's signature states the precondition the unit is checked
  -- assuming (`Request.entryIndices`), so each call establishes it.
  let pre : List HeapKnowledge.IndexFact ← fromJson? (← jField effect "pre")
  let requires : List HeapKnowledge.IndexFact ← fromJson? (← jField unit "requires")
  if pre != requires then
    throw s!"the importer's signature and the module's unit state different preconditions: {location}#{name}"
  -- Its postcondition too, which the unit certifies at each return.
  let ensures : List HeapKnowledge.IndexFact ← fromJson? (← jField effect "ensures")
  let stated : List HeapKnowledge.IndexFact ← fromJson? (← jField unit "ensures")
  if ensures != stated then
    throw s!"the importer's signature and the module's unit state different postconditions: {location}#{name}"
  let ps ← jArr type "params"
  if ps.length != params.length then
    throw s!"the importer's and the module's readings of an imported signature differ: {location}#{name}"
  let module ← Reading.of (← jField m.document "declarations")
  sameReading importer module [s!"{location}#{name}"] (((← jField type "result"), (← jField unit "retType")) ::
    promised.toList ++ (← (ps.zip params).mapM fun (a, p) => do return (a, ← jField p "type")))
  return (localName, unit)

/-- An import the fragment alone resolves to a unit of a module it lists
(`eligibleRead`): the importer's local name, the module's location, and the
unit's name and name position. -/
structure FragmentRead where
  localName : String
  location : String
  name : String
  namePos : Span
  deriving Repr, BEq

/-- **The fragment's reads of one document** (mode 8): each imported value
of its declarations whose declaration identity names a module the fragment
lists, resolved by that identity alone as a qualified read naming it is
(`eligibleRead`): a function of that module, its name the declaration's,
its name within the declaration's span, eligible, its two signature
readings agreeing, of the local names `wanted` holds. An import refused
there, and a local name two imports bind, resolve to no unit. -/
private def documentReads (fragmentModules : List Fragment.ModuleAst) (code : ModuleCode) (declarations : Json)
    (wanted : String → Bool := fun _ => true) : List FragmentRead := Id.run do
  let locations := fragmentModules.map (·.location)
  let some values := (jArr declarations "values").toOption | return []
  let some importer := (Reading.of declarations).toOption | return []
  let mut out : List FragmentRead := []
  for v in values do
    let some localName := (do (← v.getObjVal? "binding").getObjValAs? String "local").toOption | continue
    if !wanted localName then continue
    let some q := (v.getObjVal? "declaration").toOption | continue
    let some location := (q.getObjValAs? String "module").toOption | continue
    if !locations.contains location then continue
    let some name := (q.getObjValAs? String "name").toOption | continue
    let some span := (fromJson? (q.getObjValD "span") : Except String Span).toOption | continue
    match eligibleRead importer values fragmentModules code q location name span with
    | .ok (localName, unit) =>
      let some namePos := (fromJson? (unit.getObjValD "namePos") : Except String Span).toOption | continue
      out := out ++ [⟨localName, location, name, namePos⟩]
    | .error _ => continue
  let names := out.map (·.localName)
  return out.filter fun r => names.count r.localName == 1

/-- The names the code a set of a document's functions reaches mentions:
those functions', the functions they mention, transitively, and the
top-level code's where any of them mentions a name it binds (the
initialization unit, which the front's edges reach the same way,
`Front.edgesOf`), or where `init` is among the names. With `walked`, a
function reached but not among `start` adds its body's names only where
`walked` holds of it. -/
private def reachMentions (functions : List Fragment.Fn) (init : List Fragment.Stmt) (start : List String)
    (walked : Fragment.Fn → Bool := fun _ => true) : List String := Id.run do
  let names := functions.map (·.name)
  let owned := init.flatMap Fragment.Stmt.bound
  let initNames := Fragment.stmtsFreeNames init
  let mut set := start.eraseDups
  let mut withInit := start.contains "init"
  let mut out : List String := if withInit then initNames else []
  for _ in [0:functions.length + 2] do
    let bodies := (functions.filter fun f => set.contains f.name && (start.contains f.name || walked f)).flatMap
      fun f => Fragment.stmtsFreeNames f.body
    let seen := (out ++ bodies).eraseDups
    let reachesInit := withInit || seen.any owned.contains
    let seen := if reachesInit then (seen ++ initNames).eraseDups else seen
    let next := (set ++ seen.filter names.contains).eraseDups
    if next.length == set.length && reachesInit == withInit then return seen
    set := next
    withInit := reachesInit
    out := seen
  return out

/-- The modules a fragment lists, and their code decoded where first asked
(`ModuleCode`): what an importer's reads resolve against (`importerReads`,
`moduleReads`). -/
structure ImportScope where
  modules : List Fragment.ModuleAst
  code : ModuleCode

def ImportScope.of (ast : Json) : Except String ImportScope := do
  let modules ← (← jArr ast "modules").mapM Fragment.decodeModule
  return ⟨modules, ModuleCode.of modules⟩

/-- **What the importer's units read of the modules** (mode 8): the reads of
the importer's document the code `start` names reaches mentions (every
function's where none is given, `reachMentions`). The importer's reads of
the names `given` are left out (a stand-in states them). Of the importer's
functions reached, only those whose footprint the walk proposes
(`declarationEffects`) add the names their bodies mention: a function the
stand-ins name (`fixed`), or one keeping its footprint (async, generic, of a
rest or of a written effect), is read at that footprint, its body neither
walked nor checked for the selected units. -/
def importerReads (sc : ImportScope) (ast : Json) (start : Option (List String)) (given : List String := [])
    (fixed : List String := []) : Except String (List FragmentRead) := do
  if sc.modules.isEmpty then return []
  let decoded ← (← jArr ast "functions").mapM Fragment.decodeFn
  let functions := decoded.map (·.1)
  let kept := (decoded.filter fun (f, tps) => !tps.isEmpty || f.async || f.stated.isSome ||
    f.params.any (·.rest) || fixed.contains f.name).map (·.1.name)
  let init ← Fragment.decodeInit ast
  let own := reachMentions functions init (start.getD (functions.map (·.name))) (!kept.contains ·.name)
  return documentReads sc.modules sc.code (← jField ast "declarations") fun n => own.contains n && !given.contains n

/-- **A module's own reads** for the functions `names` of it an importer
reads: its imports the code those functions reach mentions, its top-level
code's where they read a name it binds (`reachMentions`), each resolved as
the importer's are (`documentReads`). -/
def moduleReads (sc : ImportScope) (m : Fragment.ModuleAst) (names : List String) : Except String (List FragmentRead) := do
  let (fs, mi) ← match sc.code[m.location]? with
    | some decoded => decoded.get
    | none => throw s!"a module the fragment does not list: {m.location}"
  let more := reachMentions fs mi names
  return documentReads sc.modules sc.code (← jField m.document "declarations") more.contains

/-- A module whose units an importer reads (`fragmentPlansWithModules`): the
module, the names of its functions read, and its own reads its read closure
mentions. -/
structure ModuleNeed where
  module : Fragment.ModuleAst
  names : List String
  reads : List FragmentRead

end Verification.SourceClaimJson
