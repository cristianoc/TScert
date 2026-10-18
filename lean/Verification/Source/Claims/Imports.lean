import Verification.Source.Claims.Extraction
import Verification.Source.EffectJson

/-! Certified imports (SOURCE-MODEL.md, "Certified imports"): which module
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
  qualified : List (String × Footprints.Closed × Bool)

/-- What certified imports give the check: the importer's document and claims
without modules, the importer's qualified reads by name, each with its unit's
footprint and on-throw flag, and the module runs. -/
structure ImportPlan where
  ast : Json
  claims : Json
  qualified : List (String × Footprints.Closed × Bool)
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

/-- A declaration document's parts the comparison reads: its definitions
and its symbols. -/
structure Reading where
  definitions : List Json
  symbols : Array Json

def Reading.of (declarations : Json) : Except String Reading := do
  return ⟨← jArr declarations "definitions", (← jArr declarations "symbols").toArray⟩

def Reading.definition (r : Reading) (id : Json) : Option Json :=
  r.definitions.find? fun d => (d.getObjVal? "declaration").toOption == some id

/-- **The two readings agree.** The terms `a` (the importer's) and `b` (the
module's) are equal once their symbol keys name declarations, and so,
recursively, is every declaration either reaches: its definition in each
reading, both present and equal, or both absent (a declaration neither
document defines, the standard library's, which both read alike). A visited
set closes recursive definitions; a mismatch is refused, never proved
equivalent. -/
partial def sameReading (ra rb : Reading) (pairs : List (Json × Json)) : Except String Unit := do
  let mut work : List Json := []
  for (a, b) in pairs do
    if canonical ra.symbols a != canonical rb.symbols b then
      throw "the importer's and the module's readings of an imported signature differ"
    work := work ++ referenced a ++ referenced b
  let mut seen : List Json := []
  for _ in [0:100000] do
    match work with
    | [] => return ()
    | id :: rest =>
      work := rest
      if seen.contains id then continue
      seen := id :: seen
      match ra.definition id, rb.definition id with
      | none, none => pure ()
      | some da, some db =>
        if canonical ra.symbols da != canonical rb.symbols db then
          throw s!"the importer's and the module's readings of a declaration differ: {id.compress}"
        work := work ++ referenced da
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
    Except String (String × Footprints.Closed × Bool) := do
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
  let ps ← jArr type "params"
  if ps.length != params.length then
    throw s!"the importer's and the module's readings of an imported signature differ: {location}#{name}"
  let module ← Reading.of (← jField m.document "declarations")
  sameReading importer module (((← jField type "result"), (← jField unit "retType")) ::
    (← (ps.zip params).mapM fun (a, p) => do return (a, ← jField p "type")))
  let namePos ← jField unit "namePos"
  let some uc := (← jArr c "functions").find? fun f =>
      (f.getObjValAs? String "name").toOption == some name && (f.getObjValD "namePos") == namePos
    | throw s!"a qualified read names a unit without claims: {location}#{name}"
  let footprint : Footprints.Closed ← fromJson? (← jField uc "footprint")
  let onThrow ← (← jField uc "onThrow").getBool?
  return (localName, footprint, onThrow)

/-- The qualified reads of one document: each read its claims list names an
imported value of its declarations and an eligible unit whose two readings
agree (`qualifiedRead`). Its importer's binding of each, with the unit's
footprint and on-throw flag, and the units, by module and name. -/
private def planReads (declarations claims : Json) (fragmentModules : List Fragment.ModuleAst)
    (claimModules : List Json) :
    Except String (List (String × Footprints.Closed × Bool) × List (String × String)) := do
  let reads ← jArr claims "qualified"
  if reads.eraseDups.length != reads.length then throw "a qualified read is listed twice"
  let values ← jArr declarations "values"
  let importer ← Reading.of declarations
  let mut qualified : List (String × Footprints.Closed × Bool) := []
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
  let mut planned : List (String × List (String × Footprints.Closed × Bool)) := []
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

end Verification.SourceClaimJson
