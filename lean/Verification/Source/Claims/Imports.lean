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

/-- The functions of a module a set of its functions reads, with them,
closed under reads, its top-level code's reads included. -/
private def readClosure (functions : List Fragment.Fn) (init : List Fragment.Stmt) (start : List String) :
    List String := Id.run do
  let names := functions.map (·.name)
  let mut set := (start ++ (Fragment.stmtsFreeNames init).filter names.contains).eraseDups
  for _ in [0:functions.length + 1] do
    let more := (functions.filter (set.contains ·.name)).flatMap fun f =>
      (Fragment.stmtsFreeNames f.body).filter names.contains
    let next := (set ++ more).eraseDups
    if next.length == set.length then return set
    set := next
  return set

/-- The functions of a document whose names are in `keep`. -/
private def keepFunctions (doc : Json) (keep : String → Span → Bool) : Except String Json := do
  let fs ← jArr doc "functions"
  let kept := fs.filter fun f => match (f.getObjValAs? String "name").toOption, (f.getObjValAs? Span "namePos").toOption with
    | some n, some p => keep n p
    | _, _ => false
  return doc.setObjVal! "functions" (Json.arr kept.toArray)

/-- One qualified read: the importer's binding of it, and its unit's
footprint and on-throw flag, where the read names an eligible unit of its
origin whose two signature readings agree. -/
private def qualifiedRead (importer : Reading) (values : List Json) (fragmentModules : List Fragment.ModuleAst)
    (claimModules : List Json) (q : Json) (location name : String) (span : Span) :
    Except String (String × Footprints.Closed × Bool × Footprints.Closed) := do
  let some v := values.find? fun v => (v.getObjVal? "declaration").toOption == some q
    | throw s!"a qualified read names no imported value: {q.compress}"
  let binding ← jField v "binding"
  let localName ← jStr (← jField binding "local")
  let some m := fragmentModules.find? (·.location == location)
    | throw s!"a qualified read names a module the fragment does not list: {location}"
  let some c := claimModules.find? fun c => (c.getObjValAs? String "file").toOption == some location
    | throw s!"a qualified read names a module without claims: {location}"
  let fs ← jArr m.document "functions"
  let some unit := fs.find? fun f => (f.getObjValAs? String "name").toOption == some name &&
      ((f.getObjValAs? Span "namePos").toOption.map (within · span)).getD false
    | throw s!"a qualified read names no unit of its origin: {location}#{name}"
  -- Eligible: no binders, no rest, no receiver, no guard and no promise,
  -- on both readings.
  let params ← jArr unit "params"
  if !(← jArr unit "typeParams").isEmpty || (unit.getObjValD "guard") != .null ||
      params.any (fun p => (p.getObjVal? "rest").isOk || (p.getObjValAs? String "name").toOption == some "this") then
    throw s!"a qualified read names a unit that is not eligible: {location}#{name}"
  -- Stable: no code of the module the document holds writes the binding;
  -- the parser refuses a module whose code it does not lower writes it.
  let functions ← fs.mapM fun f => do return (← Fragment.decodeFn f).1
  let init ← Fragment.decodeInit m.document
  if (init ++ functions.flatMap (·.body)).any (SourceExtraction.assignsStmt name) then
    throw s!"a qualified read names a unit whose module writes its binding: {location}#{name}"
  let type ← jField v "type"
  if (v.getObjValD "construct") != .bool false || !(← jArr v "typeParams").isEmpty ||
      (type.getObjValD "k") != .str "function" || (type.getObjValD "rest") != .null ||
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
    (← (ps.zip params).mapM fun (a, p) => do return (a, ← jField p "type")))
  let namePos ← jField unit "namePos"
  let some uc := (← jArr c "functions").find? fun f =>
      (f.getObjValAs? String "name").toOption == some name && (f.getObjValD "namePos") == namePos
    | throw s!"a qualified read names a unit without claims: {location}#{name}"
  let footprint : Footprints.Closed ← fromJson? (← jField uc "footprint")
  let onThrow ← (← jField uc "onThrow").getBool?
  -- An async unit's footprint is `top` (`RequestJson.asyncEffects`), read
  -- from its own module's Fragment.
  let async ← Fragment.decodeCompletion (← jField unit "completion")
  if !RequestJson.asyncEffects async footprint then
    throw s!"a qualified read names an async unit claimed below `top`: {location}#{name}"
  -- A stated unit's claim lies within its statement, as its own module's
  -- run requires (`RequestJson.statedWithin`).
  if !RequestJson.statedWithin async footprint onThrow false (← Fragment.decodeStated (← jField unit "stated")) then
    throw s!"a qualified read names a unit claimed outside the effect its annotation states: {location}#{name}"
  -- The footprint the unit proposes for the function it returns, which its
  -- returns establish (`resultWithFootprint`).
  let result : Footprints.Closed ← fromJson? (← jField uc "resultFootprint")
  return (localName, footprint, onThrow, result)

/-- The qualified reads of one document: each read its claims list names an
imported value of its declarations and an eligible unit whose two readings
agree (`qualifiedRead`). Its importer's binding of each, with the unit's
footprint and on-throw flag, and the units, by module and name. -/
private def planReads (declarations claims : Json) (fragmentModules : List Fragment.ModuleAst)
    (claimModules : List Json) :
    Except String (List (String × Footprints.Closed × Bool × Footprints.Closed) × List (String × String)) := do
  let reads ← jArr claims "qualified"
  if reads.eraseDups.length != reads.length then throw "a qualified read is listed twice"
  let values ← jArr declarations "values"
  let importer ← Reading.of declarations
  let mut qualified : List (String × Footprints.Closed × Bool × Footprints.Closed) := []
  let mut units : List (String × String) := []
  for q in reads do
    fieldsExactly q ["module", "name", "span"]
    let location ← jStr (← jField q "module")
    let name ← jStr (← jField q "name")
    let span : Span ← fromJson? (← jField q "span")
    let read ← (qualifiedRead importer values fragmentModules claimModules q location name span).mapError
      (s!"certified import {location}#{name}: " ++ ·)
    qualified := qualified ++ [read]
    units := units ++ [(location, name)]
  let names := qualified.map (·.1)
  if names.eraseDups.length != names.length then throw "two qualified reads bind one name"
  return (qualified, units)

/-- Whether a graph over `nodes` has a cycle: no node is left once each node
whose edges all reach removed nodes is removed, repeatedly. -/
private def cyclic (nodes : List String) (edges : List (String × String)) : Option String := Id.run do
  let mut left := nodes
  for _ in [0:nodes.length + 1] do
    let sinks := left.filter fun n => edges.all fun (a, b) => a != n || !left.contains b
    if sinks.isEmpty then return left.head?
    left := left.filter (!sinks.contains ·)
  return left.head?

/-- **The import plan.** Each read a document's claims list qualified names
an imported value of that document's declarations and a unit of a module the
fragment lists: a function of that module, its name the declaration's, its
name within the declaration's span. The unit is eligible (no binders, no
rest, no receiver, no guard, no promise, a binding no code of its module
writes), its claims are in that module's claims document, about the
module's bytes, and the two readings of its signature agree (`sameReading`).
The documents planned are the importer's and, recursively, each module's a
planned read names; the qualified-dependency graph among the modules is
acyclic. Each planned module runs restricted to the read closure of the
units read qualified of it, its top-level code kept, at its own qualified
reads. -/
def planImports (ast claims : Json) : Except String ImportPlan := do
  let fragmentModules ← (← jArr ast "modules").mapM Fragment.decodeModule
  let locations := fragmentModules.map (·.location)
  if locations.eraseDups.length != locations.length then throw "a module is listed twice"
  let claimModules ← jArr claims "modules"
  let claimFiles ← claimModules.mapM fun c => do jStr (← jField c "file")
  if claimFiles.eraseDups.length != claimFiles.length then throw "a module's claims are listed twice"
  for c in claimModules do
    let file ← jStr (← jField c "file")
    let some m := fragmentModules.find? (·.location == file)
      | throw s!"claims for a module the fragment does not list: {file}"
    if (← jStr (← jField c "sourceSha256")) != m.sourceSha256 then
      throw s!"a module's claims are about other bytes: {file}"
  let claimsOf (location : String) : Except String Json :=
    match claimModules.find? fun c => (c.getObjValAs? String "file").toOption == some location with
    | some c => pure c
    | none => throw s!"a module without claims: {location}"
  let (qualified, importerUnits) ← planReads (← jField ast "declarations") claims fragmentModules claimModules
  -- The modules a planned read names, each planned once, its reads in turn.
  let mut units := importerUnits
  let mut planned : List (String × List (String × Footprints.Closed × Bool × Footprints.Closed)) := []
  let mut edges : List (String × String) := []
  for _ in [0:fragmentModules.length + 1] do
    let some location := (units.map (·.1)).find? fun l => !(planned.map (·.1)).contains l | break
    let some m := fragmentModules.find? (·.location == location)
      | throw s!"a qualified read names a module the fragment does not list: {location}"
    let (reads, more) ← (planReads (← jField m.document "declarations") (← claimsOf location)
      fragmentModules claimModules).mapError (s!"module {location}: " ++ ·)
    planned := planned ++ [(location, reads)]
    edges := edges ++ more.map fun (l, _) => (location, l)
    units := units ++ more
  if let some location := cyclic (planned.map (·.1)) edges then
    throw s!"module {location}: a cycle of qualified reads through it"
  let modules ← fragmentModules.filterMapM fun m => do
    let some (_, reads) := planned.find? (·.1 == m.location) | return none
    let start := (units.filter (·.1 == m.location)).map (·.2)
    let decoded ← (← jArr m.document "functions").mapM fun f => do return (← Fragment.decodeFn f).1
    let init ← Fragment.decodeInit m.document
    let keep := readClosure decoded init start
    let ast ← keepFunctions m.document fun n _ => keep.contains n
    let claims ← keepFunctions (← claimsOf m.location) fun n _ => keep.contains n
    return some ⟨m.location, ast, claims, reads⟩
  return ⟨ast.setObjVal! "modules" (Json.arr #[]), claims.setObjVal! "modules" (Json.arr #[]), qualified, modules⟩

/-- Each qualified read of one document `qualifiedRead` refuses, worded as
`planReads` words it, and the units of the reads it admits. -/
private def readRefusals (declarations claims : Json) (fragmentModules : List Fragment.ModuleAst)
    (claimModules : List Json) : Except String (List String × List (String × String)) := do
  let values ← jArr declarations "values"
  let importer ← Reading.of declarations
  let mut refused : List String := []
  let mut units : List (String × String) := []
  for q in ← jArr claims "qualified" do
    let location ← jStr (← jField q "module")
    let name ← jStr (← jField q "name")
    let span : Span ← fromJson? (← jField q "span")
    match qualifiedRead importer values fragmentModules claimModules q location name span with
    | .ok _ => units := units ++ [(location, name)]
    | .error e => refused := refused ++ [s!"certified import {location}#{name}: {e}"]
  return (refused, units)

/-- **The plan's refusals**, for withdrawing reads: every qualified read of
the importer, and of each module an admitted read names, that
`qualifiedRead` refuses, a module's prefixed `module <location>: ` as
`planImports` prefixes it. Each read is checked on its own. A diagnostic:
the check plans by `planImports`. -/
def planRefusals (ast claims : Json) : Except String (List String) := do
  let fragmentModules ← (← jArr ast "modules").mapM Fragment.decodeModule
  let claimModules ← jArr claims "modules"
  let (importerRefused, importerUnits) ← readRefusals (← jField ast "declarations") claims fragmentModules
    claimModules
  let mut refused := importerRefused
  let mut units := importerUnits
  let mut planned : List String := []
  for _ in [0:fragmentModules.length + 1] do
    let some location := (units.map (·.1)).find? fun l => !planned.contains l | break
    planned := planned ++ [location]
    let some m := fragmentModules.find? (·.location == location) | continue
    let some c := claimModules.find? fun c => (c.getObjValAs? String "file").toOption == some location
      | continue
    match do readRefusals (← jField m.document "declarations") c fragmentModules claimModules with
    | .ok (more, reached) =>
      refused := refused ++ more.map (s!"module {location}: " ++ ·)
      units := units ++ reached
    | .error e => refused := refused ++ [s!"module {location}: {e}"]
  return refused

end Verification.SourceClaimJson
