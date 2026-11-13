import Verification.Source.Claims.Extraction
import Verification.Source.EffectJson

/-! Certified imports (SOURCE-CONTRACTS.md, "Certified imports"): the origin
each import of a module the fragment lists resolves to, and the module
documents the one check certifies, each restricted to its certified set. -/
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


/-- Whether a span holds another. -/
private def within (inner outer : Span) : Bool := outer.1 ≤ inner.1 && inner.2 ≤ outer.2

/-- A module's code, decoded once: its functions, its top-level code, and
**the stability of its function bindings**: the names of its functions no
statement of its top-level code or of any of its function bodies assigns
(`assignsStmt`). A function binding is stable when no code of its module
writes it; the parser refuses a module whose code it does not lower writes
it. Stability is a property of the binding, established once per module
for every function binding it declares, and read by every read of one. -/
structure DecodedModule where
  functions : List Fragment.Fn
  init : List Fragment.Stmt
  stable : List String

private def decodeCode (m : Fragment.ModuleAst) : Except String DecodedModule := do
  let functions ← (← jArr m.document "functions").mapM fun f => do return (← Fragment.decodeFn f).1
  let init ← Fragment.decodeInit m.document
  let code := init ++ functions.flatMap (·.body)
  let names := (functions.map (·.name)).eraseDups
  return ⟨functions, init, names.filter fun n => !code.any (SourceExtraction.assignsStmt n)⟩

/-- Each module's code (`decodeCode`) by its location, the first module of
that location's, decoded at most once, where a read first asks for it. -/
abbrev ModuleCode := Std.HashMap String (Thunk (Except String DecodedModule))

def ModuleCode.of (fragmentModules : List Fragment.ModuleAst) : ModuleCode :=
  fragmentModules.foldl (init := {}) fun m mod => m.insertIfNew mod.location (Thunk.mk fun _ => decodeCode mod)

/-- The imported value a qualified read names, among a document's `values`. -/
private def importedValue (values : List Json) (q : Json) : Option Json :=
  values.find? fun v => (v.getObjVal? "declaration").toOption == some q

/-- **An import's origin** (`resolveRead`): the import `q`, a declaration
identity, is an imported value of the importer's declarations; its module is
one the fragment lists. Where a function of that module binds the
declaration's name within the declaration's span and that binding is stable
(`DecodedModule.stable`), the import resolves to that function: its unit
(its first, for overloads). Its declared contract and the function's entry
correspond where the store-map checks relate the entry's rows and the type
the importer reads the import at (`FilePlans.refuseRows`); a refused check
refuses each unit reading it. Where no function binds the name, or its
binding is written, the module's initialization holds it: no function's
entry states it, and the import is read at its declared contract. -/
private def resolveRead (values : List Json) (fragmentModules : List Fragment.ModuleAst)
    (code : ModuleCode) (q : Json) (location name : String) (span : Span) :
    Except String (Option (String × Json)) := do
  let some v := importedValue values q
    | throw s!"a qualified read names no imported value: {q.compress}"
  let localName ← jStr (← jField (← jField v "binding") "local")
  let some m := fragmentModules.find? (·.location == location)
    | throw s!"a qualified read names a module the fragment does not list: {location}"
  let some unit := (← jArr m.document "functions").find? fun f =>
      (f.getObjValAs? String "name").toOption == some name &&
        ((f.getObjValAs? Span "namePos").toOption.map (within · span)).getD false
    | return none
  let decoded ← match code[location]? with
    | some decoded => decoded.get
    | none => decodeCode m
  if !decoded.stable.contains name then return none
  return some (localName, unit)

/-- An import the fragment alone resolves to a function of a module it lists
(`resolveRead`): the importer's local name, the module's location, and the
unit's name and name position. -/
structure FragmentRead where
  localName : String
  location : String
  name : String
  namePos : Span
  deriving Repr, BEq

/-- **The fragment's reads of one document** (mode 8): each imported value
of its declarations whose declaration identity names a module the fragment
lists, of the local names `wanted` holds, resolved by that identity alone
(`resolveRead`) to a function of that module. An import of a module the
fragment does not list is
read at its declaration (its stated contract), and one the module's
initialization holds at its declared contract; a local name two imports
bind resolves to neither. -/
private def documentReads (fragmentModules : List Fragment.ModuleAst) (code : ModuleCode) (declarations : Json)
    (wanted : String → Bool := fun _ => true) : List FragmentRead := Id.run do
  let locations := fragmentModules.map (·.location)
  let some values := (jArr declarations "values").toOption | return []
  let mut out : List FragmentRead := []
  for v in values do
    let some localName := (do (← v.getObjVal? "binding").getObjValAs? String "local").toOption | continue
    if !wanted localName then continue
    let some q := (v.getObjVal? "declaration").toOption | continue
    let some location := (q.getObjValAs? String "module").toOption | continue
    if !locations.contains location then continue
    let some name := (q.getObjValAs? String "name").toOption | continue
    let some span := (fromJson? (q.getObjValD "span") : Except String Span).toOption | continue
    match resolveRead values fragmentModules code q location name span with
    | .ok (some (localName, unit)) =>
      let some namePos := (fromJson? (unit.getObjValD "namePos") : Except String Span).toOption | continue
      out := out ++ [⟨localName, location, name, namePos⟩]
    | .ok none | .error _ => continue
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
  let decoded ← match sc.code[m.location]? with
    | some decoded => decoded.get
    | none => throw s!"a module the fragment does not list: {m.location}"
  let more := reachMentions decoded.functions decoded.init names
  return documentReads sc.modules sc.code (← jField m.document "declarations") more.contains

/-- A module whose units an importer reads (`fragmentPlansWithModules`): the
module, the names of its functions read, and its own reads its read closure
mentions. -/
structure ModuleNeed where
  module : Fragment.ModuleAst
  names : List String
  reads : List FragmentRead

end Verification.SourceClaimJson
