import Verification.Source.Claims.ModuleInterfaces

/-! The source inputs of a fresh group plan. The worker compares a plan over
these inputs with its ordinary plan before reporting a shadow hit. -/
namespace Verification.GroupProjection
open Lean SourceClaimJson

def footprint (f : Footprints.Closed) : Json := toJson
  [EffectJson.changeName f.value, EffectJson.changeName f.array, EffectJson.changeName f.view]

def answersWire (answers : List (String × Option StandIn)) : Json :=
  toJson (answers.map fun (n, s) => (n, s.map fun (v : StandIn) => Json.mkObj [
    ("name", toJson v.name), ("normal", toJson (v.summary.normal.map footprint)),
    ("exceptional", toJson (v.summary.exceptional.map footprint)),
    ("result", footprint v.resultFootprint), ("alias", toJson v.returnAlias)]))

/-- Canonical source offsets and their inverse, including the zero sentinel. -/
structure Sites where
  offsets : Std.HashMap Nat Nat
  ranks : Std.HashMap Nat Nat
  /-- Physical coordinates for a correspondence that requires the original sites. -/
  physical : Bool := false

private def spanField (k : String) := k == "pos" || k == "namePos" || k == "span"

/-- A declaration identity has its own source coordinate system. -/
private def external (j : Json) := (j.getObjVal? "module").isOk

private partial def collect (j : Json) (s : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  match j with
  | .arr a => return a.foldl (fun s v => collect v s) s
  | .obj kv =>
    if external j then return s
    return kv.foldl (fun s k v =>
      if spanField k then match (fromJson? v : Except String (Nat × Nat)) with
        | .ok (a,b) => (s.insert a).insert b
        | .error _ => collect v s
      else collect v s) s
  | _ => return s

private def Sites.ofPairs (pairs : Array (Nat × Nat)) : Sites :=
  ⟨pairs.foldl (fun m (n,i) => m.insert i n) {}, pairs.foldl (fun m (n,i) => m.insert n i) {}, false⟩

def Sites.of (j : Json) : Sites :=
  Sites.ofPairs (((collect j (({} : Std.HashSet Nat).insert 0)).toArray.qsort (· < ·)).zipIdx)

/-- Each declaration starts a new interval. A change in its number of sites
leaves the coordinates of other declarations alone. The stride bounds every
interval even on a file larger than the ordinary one-million-site stride. -/
private def fileSites (code bindings : Json) (anchors : Std.HashSet Nat) : Sites := Id.run do
  let offsets := (collect (.arr #[code, bindings]) (({} : Std.HashSet Nat).insert 0)).toArray.qsort (· < ·)
  let stride := max 1048576 (offsets.size + 1)
  let mut pairs := #[]
  let mut block := 0
  let mut index := 0
  for n in offsets do
    if n != 0 && anchors.contains n then
      block := block + 1
      index := 0
    pairs := pairs.push (n, block * stride + index)
    index := index + 1
  return Sites.ofPairs pairs

def Sites.inFile (group file : Sites) : Sites :=
  Sites.ofPairs (group.offsets.toArray.map fun (i,n) => (file.offsets.getD n n, i))

partial def Sites.relative (s : Sites) (j : Json) : Json := Id.run do
  if s.physical then return j
  match j with
  | .arr a => return .arr (a.map s.relative)
  | .obj kv =>
    if external j then return j
    return Json.mkObj (kv.toList.map fun (k,v) => (k,
      if spanField k then match (fromJson? v : Except String (Nat × Nat)) with
        | .ok (a,b) => toJson (s.ranks.getD a a, s.ranks.getD b b)
        | .error _ => s.relative v
      else s.relative v))
  | _ => return j

/-- Lower the store at relative sites too. Source type terms occur verbatim
inside intern keys and head names. Reusing the lowering gives negative
lookups the same spelling as positive ones. Imported declaration identities
retain their full module, name and declaration span. -/
def fileProgram (ast : Json) : Json × Sites := Id.run do
  let functions := (ast.getObjValAs? (Array Json) "functions").toOption.getD #[]
  let init := (ast.getObjValAs? (Array Json) "init").toOption.getD #[]
  let code := Json.mkObj [("functions", .arr functions), ("init", .arr init)]
  let anchors := (functions.map (·.getObjValD "namePos") ++ init.map (·.getObjValD "pos")).foldl (fun a v =>
    match (fromJson? v : Except String (Nat × Nat)) with | .ok (n,_) => a.insert n | .error _ => a) ({} : Std.HashSet Nat)
  let doc := ast.getObjValD "declarations"
  let rows := fun k => (doc.getObjValAs? (Array Json) k).toOption.getD #[]
  let bindings := (rows "roots" ++ rows "values").map (·.getObjValD "binding")
  let sites := fileSites code (.arr bindings) anchors
  let mut doc := doc
  for k in ["roots", "values"] do
    doc := doc.setObjVal! k (.arr ((rows k).map fun v =>
      v.setObjVal! "binding" (sites.relative (v.getObjValD "binding"))))
  return (ast.setObjVal! "functions" (.arr (functions.map sites.relative))
    |>.setObjVal! "init" (.arr (init.map sites.relative)) |>.setObjVal! "declarations" doc, sites)

def Sites.unit (s : Sites) (id : String) (inverse : Bool) : String := Id.run do
  if id.startsWith "module:" then return id
  let [name, n] := id.splitOn "@" | return id
  let some n := n.toNat? | return id
  let some m := if inverse then s.offsets.get? n else s.ranks.get? n | return id
  return s!"{name}@{m}"

/-- Located refusal text carries half-open source spans. Other text, including
external identities, must correspond exactly for the projected check to qualify. -/
private def Sites.locate (s : Sites) (v : String) : String :=
  let parts := v.splitOn "["
  parts.headD "" ++ String.join (parts.tail.map fun suffix => Id.run do
    let a := suffix.takeWhile Char.isDigit
    let rest := suffix.drop a.toString.length
    let b := (rest.drop 1).takeWhile Char.isDigit
    let some i := a.toString.toNat? | return "[" ++ suffix
    let some j := b.toString.toNat? | return "[" ++ suffix
    let tail := rest.drop (b.toString.length + 1)
    if !rest.startsWith "," || !tail.startsWith ")" then return "[" ++ suffix
    let some x := s.offsets.get? i | return "[" ++ suffix
    let some y := s.offsets.get? j | return "[" ++ suffix
    return s!"[{x},{y}{tail}")

private def Sites.absoluteSpan (s : Sites) (v : Json) : Json := Id.run do
  let .ok (a,b) := (fromJson? v : Except String (Nat × Nat)) | return v
  let some x := s.offsets.get? a | return v
  let some y := s.offsets.get? b | return v
  return toJson (x,y)

/-- A temporary's origin in the expression and binding plans. Its final
component identifies a slot inside the plan and keeps its local number. -/
private def Sites.temporary (s : Sites) (name : String) : String := Id.run do
  let [kind, suffix] := name.splitOn "@" | return name
  if !name.startsWith "%" || !suffix.endsWith "%" then return name
  let parts := (suffix.dropEnd 1).toString.splitOn ":"
  let absolute := fun t => do let n ← String.toNat? t; toString <$> s.offsets.get? n
  match parts with
  | [a,b,slot] =>
    let some x := absolute a | return name
    let some y := absolute b | return name
    return s!"{kind}@{x}:{y}:{slot}%"
  | [a] =>
    let some x := absolute a | return name
    return s!"{kind}@{x}%"
  | _ => return name

/-- Structured source maps in a diagnostic carry spans, temporary names and
the entry offset. Sequent labels and store projections have their own indices. -/
private partial def Sites.diagnostic (s : Sites) (j : Json) : Json := Id.run do
  match j with
  | .arr xs => return .arr (xs.map s.diagnostic)
  | .obj fields =>
    if external j then return j
    return Json.mkObj (fields.toList.map fun (k,v) => (k, Id.run do
      if spanField k || k == "subject" then return s.absoluteSpan v
      if k == "environmentStart" then
        if let .ok n := v.getNat? then return toJson (s.offsets.getD n n)
      if k == "name" then
        if let .ok n := v.getStr? then return toJson (s.temporary n)
      if k == "id" && j.getObjValD "phase" == .str "request-validation" then
        if let .ok id := v.getStr? then
          if let kind :: pos :: rest := id.splitOn ":" then
            if let some n := pos.toNat? then
              return toJson (String.intercalate ":" (kind :: toString (s.offsets.getD n n) :: rest))
      return s.diagnostic v))
  | _ => return j

private def Sites.refusal (s : Sites) (text : String) : String :=
  let marker := "\nobligation-diagnostic: "
  let parts := text.splitOn marker
  String.intercalate marker (s.locate (parts.headD "") :: parts.tail.map fun record =>
    match Json.parse record with
    | .ok j => (s.diagnostic j).compress
    | .error _ => s.locate record)

def Sites.materialize (s : Sites) (line : String) : Except String String := do
  if s.physical then return line
  let j ← Json.parse line
  let mut j := j.setObjVal! "unit" (toJson (s.unit (← j.getObjValAs? String "unit") true))
  for field in ["members", "depends"] do
    if let .ok (ids : List String) := j.getObjValAs? (List String) field then
      j := j.setObjVal! field (toJson (ids.map (s.unit · true)))
  for field in ["refusal", "elaboration"] do
    if let .ok reason := j.getObjValAs? String field then
      j := j.setObjVal! field (toJson (s.refusal reason))
  return j.compress

open EquationLowering

private instance [ToJson α] : ToJson (Except String α) where
  toJson
    | .ok a => Json.mkObj [("ok", toJson a)]
    | .error e => Json.mkObj [("error", toJson e)]

deriving instance ToJson for HeadKind, EquationLowering.Binding, Ctx, Job, Definition, Obligation, ArrayParts, ProducerRows
deriving instance ToJson for EquationGraphs.Binder, Draft, GenericType, GenericValue

section
open EquationGraphs EquationLowering PositiveNormalization

/-- Restricting the intern index to demanded spellings preserves the answer
for each demand, including a missing key. The heads used to spell the
query and the argument vector of the resulting application stay fixed. -/
theorem lookup_filter_keys (s : EquationStore.State) (wanted : String → Bool)
    (cs : List (Clause (List Tree))) (h : wanted (internKey s.heads cs).1 = true) :
    EquationStore.lookup { s with keys := s.keys.filter fun key _ => wanted key } cs =
      EquationStore.lookup s cs := by
  simp only [EquationStore.lookup, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter']
  cases s.keys[(internKey s.heads cs).1]? <;> simp [h]

private def BaseReadsHead (i : Nat) : Tree → Prop
  | .app head _ | .bound head _ _ => i = head
  | _ => False

/-- Whether a row query reads draft head `i`. A meet reads the base row of each part. -/
def RowReadsHead (i : Nat) : Tree → Prop
  | .meet parts => ∃ t ∈ parts.toList, BaseReadsHead i t
  | t => BaseReadsHead i t

private theorem baseRow_eq_of_heads (a b : EquationStore.State) (t : Tree)
    (h : ∀ i, BaseReadsHead i t → a.heads[i]? = b.heads[i]?) :
    EquationStore.baseRow a t = EquationStore.baseRow b t := by
  cases t <;> try rfl
  case app | bound =>
    simp only [BaseReadsHead, forall_eq] at h
    simp only [EquationStore.baseRow, h]

theorem rowOf_eq_of_heads (a b : EquationStore.State) (t : Tree)
    (h : ∀ i, RowReadsHead i t → a.heads[i]? = b.heads[i]?) :
    EquationStore.rowOf a t = EquationStore.rowOf b t := by
  cases t <;> try rfl
  case app | bound =>
    simp only [RowReadsHead, BaseReadsHead, forall_eq] at h
    simp only [EquationStore.rowOf, EquationStore.baseRow, h]
  case meet parts =>
    unfold EquationStore.rowOf
    congr 1
    apply List.map_congr_left
    intro t ht
    rw [baseRow_eq_of_heads a b t (fun i hi => h i ⟨t, ht, hi⟩)]

end

/-- Initialization typing contributes its grown store and its module binding
answers to the front at this prior, including binding-specific refusals. -/
theorem withInitTypes_eq (fr : Front) (force : List String) :
    let typed := fr.withInitTypes force
    typed = { fr with d := { fr.d with types := typed.d.types }, moduleConstants := typed.moduleConstants } := by
  dsimp only
  unfold Front.withInitTypes
  simp only [Id.run, pure, Bind.bind]
  split <;> try rfl
  repeat' first | split | rfl

/-- Declaration identities occurring in a term, including references inside
bounds, method signatures and inherited rows. -/
private partial def identities (term : Json) (seen : Std.HashSet Json) : Std.HashSet Json :=
  match term with
  | .obj fields => if external term then seen.insert term else
      fields.foldl (fun acc _ child => identities child acc) seen
  | .arr terms => terms.foldl (fun acc child => identities child acc) seen
  | _ => seen

/-- Restrict the declaration document before assigning equation head numbers.
Written application obligations and the document's canonical symbol identities
survive the restriction. Definitions keep their original relative order. -/
private def sliceDeclarations (document code : Json) (names : List String) : Except String Json := do
  let bindingRead := fun (row : Json) =>
    ((row.getObjValD "binding").getObjValAs? String "local").toOption.any names.contains
  let roots := (← arr document "roots").filter bindingRead
  let values := (← arr document "values").filter bindingRead
  let defs ← arr document "definitions"
  let mut needed := identities (.arr #[code, .arr roots, .arr values, ← field document "applications"]) {}
  for row in defs do
    let id := row.getObjValD "declaration"
    if ImplicitDependency.all.any (·.selects id) then needed := needed.insert id
  let mut expanded : Std.HashSet Json := {}
  for _ in [:defs.size + 1] do
    let fresh := defs.filter fun row =>
      let id := row.getObjValD "declaration"
      needed.contains id && !expanded.contains id
    if fresh.isEmpty then break
    for row in fresh do
      expanded := expanded.insert (row.getObjValD "declaration")
      needed := identities row needed
  return document.setObjVal! "roots" (.arr roots) |>.setObjVal! "values" (.arr values)
    |>.setObjVal! "definitions" (.arr (defs.filter fun row => needed.contains (row.getObjValD "declaration")))

/-- Close the group's executable source over module reads. A group containing
initialization executes the entire initializer. Other groups retain the
statements defining the bindings they read, transitively. -/
def sliceProgram (ast : Json) (fr : Front) (i : Nat) (order : List Nat) : Except String Json := do
  let functions ← arr ast "functions"
  let init ← arr ast "init"
  let members := fr.group i
  let wholeInit := (members ++ order).any fun j => (fr.group j).any fr.isInitialization
  let mut names := (members ++ order).eraseDups.filterMap fun j => fr.units[j]?.map (·.1.name)
  for _ in [:functions.size + init.size + 2] do
    let mut reads := names
    for (fn, _, initClaim) in fr.units do
      if initClaim.isNone && names.contains fn.name then
        reads := reads ++ SourceElaboration.moduleReadNames fn.body
    for stmt in fr.init do
      if wholeInit || stmt.bound.any names.contains then
        reads := reads ++ SourceElaboration.moduleReadNames [stmt]
    reads := reads.eraseDups
    if reads.length == names.eraseDups.length then break
    names := reads
  let fs := functions.filter fun f => (f.getObjValAs? String "name").toOption.any names.contains
  let ss := (init.zip fr.init.toArray).filterMap fun (raw, stmt) =>
    if wholeInit || stmt.bound.any names.contains then some raw else none
  let declarations ← sliceDeclarations (← field ast "declarations") (.arr #[.arr fs, .arr ss]) names
  return ast.setObjVal! "functions" (.arr fs) |>.setObjVal! "init" (.arr ss)
    |>.setObjVal! "declarations" declarations |>.setObjVal! "modules" (.arr #[])

/-- The equation document's standard encoder contains the rows. Planning
also consults the intern index, declaration identity index, draft kinds,
builtins and search policy. Enumerating the complete maps preserves absence.
The omitted thunk vector is determined by the heads (`State.nullary_eq`). -/
def storeFields (s : EquationStore.State) : Json :=
  let ⟨budget, doc, identities, packings, packs, heads, _, _, keys, jobs, processing,
    excluded, arrays, obligations, meets, scopes, units, sourceRows, names, fresh, proto,
    stable, arrayAnnotations, rows, tags⟩ := s
  Json.mkObj [("budget", toJson (budget.rounds,budget.select,budget.rerun)),
    ("doc", toJson doc), ("identities", toJson (identities.toList.mergeSort (fun a b => a.1.compress ≤ b.1.compress))),
    ("packings", toJson packings), ("packs", toJson packs), ("heads", toJson heads),
    ("keys", toJson (keys.toList.mergeSort (fun a b => a.1 ≤ b.1))), ("jobs", toJson jobs),
    ("processing", toJson processing), ("excluded", toJson excluded), ("arrays", toJson arrays),
    ("obligations", toJson obligations), ("meets", toJson meets), ("scopes", toJson scopes),
    ("units", toJson units), ("sourceRows", toJson sourceRows), ("names", toJson names),
    ("fresh", toJson fresh), ("proto", toJson proto), ("stable", toJson stable),
    ("arrayAnnotations", toJson arrayAnnotations), ("producerRows", toJson rows), ("tags", toJson tags)]

/-- The source annotations in the group program already contain their
lowered labels. These are the remaining inputs to `prepareEquationFront`. -/
structure Equations where
  store : EquationStore.State
  values : List (String × (Nat × Nat) × EquationLowering.Union)
  generics : List GenericValue
  units : List (String × List (String × EquationGraphs.Tree × Option EquationLowering.Union))
  initBinders : List (String × EquationGraphs.Tree × Option EquationLowering.Union)
  claims : Json

def Equations.lowering (e : Equations) : SourceLowering :=
  ⟨e.store, [], [], e.values, e.generics, e.units, e.initBinders, e.claims⟩

/-- Members and potential second-round callees are numbered within the
group input. The interleaving preserves the declaration order read when
building slots and ordered stand-ins. -/
inductive FunctionRef where
  | member (index : Nat)
  | callee (index : Nat)
  | signature (index : Nat)
  deriving ToJson

structure Functions where
  members : Array Json := #[]
  callees : Array Json := #[]
  signatures : Array Json := #[]
  order : Array FunctionRef := #[]

def Functions.of (fs : Array Json) (members reachable : List Nat) : Functions := Id.run do
  let mut out : Functions := {}
  for (f, i) in fs.zipIdx do
    if members.contains i then
      out := { out with members := out.members.push f, order := out.order.push (.member out.members.size) }
    else if reachable.contains i then
      out := { out with callees := out.callees.push f, order := out.order.push (.callee out.callees.size) }
    else
      out := { out with signatures := out.signatures.push f, order := out.order.push (.signature out.signatures.size) }
  return out

def Functions.ordered (fs : Functions) : Array Json :=
  fs.order.map fun
    | .member i => fs.members[i]!
    | .callee i => fs.callees[i]!
    | .signature i => fs.signatures[i]!

/-- A fresh computation has no access to the original front, answer memo,
or worker. Its validated store determines positive and negative lookups.
Initialization and proposal settling can run at either prior. -/
structure Input where
  common : Json
  functions : Functions
  equations : Equations
  claims : Json
  leader : String
  owned : List String
  initOrder : Option String
  demand : Bool
  below : List (String × Option StandIn)
  imports : Except String GroupImports
  established : Established
  tables : List (String × RowTable)
  force : List String
  fuel : Nat
  budget : PositiveCertificates.SearchBudget
  counting : Bool

def Input.program (g : Input) : Json := g.common.setObjVal! "functions" (.arr g.functions.ordered)

def groupEnvironment (captures : List String) (imports : Except String GroupImports) (est : Established)
    (tables : List (String × RowTable)) : Except String GroupImports × Established × List (String × RowTable) := Id.run do
  let imports := imports.map fun r => { r with unbound := r.unbound.filter (captures.contains ·.1) }
  let reads := (imports.toOption.map (·.reads)).getD []
  let est := reads.filterMap fun r => (est.lookup (r.location, r.name)).map ((r.location,r.name), ·)
  let tables := (reads.map (·.location)).eraseDups.filterMap fun loc => do
    let t ← tables.lookup loc
    let names := (reads.filter (·.location == loc)).map (·.name)
    return (loc, { t with interfaces := t.interfaces.filter (names.contains ·.1) })
  return (imports, est, tables)

def Input.ofFile (ast claims : Json) (L : SourceLowering) (fr : Front) (i : Nat) (demand : Bool)
    (below : List (String × Option StandIn)) (imports : Except String GroupImports)
    (est : Established) (tables : List (String × RowTable)) (force : List String)
    (fuel : Nat) (budget : PositiveCertificates.SearchBudget) (counting : Bool) (physical := false) : Input × Sites := Id.run do
  let selected := (fr.selected (some [memberName (fr.unitId i)])).flatMap fr.group
  let belowMembers := (selected ++ selected.flatMap fr.reach).eraseDups
  let inferredNames := belowMembers.map fun j => memberName (fr.unitId j)
  let reachable := if physical then List.range fr.units.length else
    (belowMembers ++ (fr.selected (some inferredNames)).flatMap fr.group).eraseDups
  let funcs := fr.functionJsons
  -- Other declarations supply signatures. Both proposal rounds can replan
  -- any reachable body, even a callee whose ordinary proposal is known.
  let funcs := funcs.zipIdx.map fun (f, j) => if reachable.contains j then f else f.setObjVal! "body" (.arr #[])
  let code := Json.mkObj [("functions", .arr funcs), ("init", fr.ast.getObjValD "init")]
  let declarations := ast.getObjValD "declarations"
  -- The import binding is in the current file. The identity and its type
  -- annotation belong to the declaring file and keep their own coordinates.
  let declValues := (declarations.getObjValAs? (Array Json) "values").toOption.getD #[]
  let sites := if physical then (⟨{}, {}, true⟩ : Sites) else Sites.of (.arr #[code, claims, L.claims,
    .arr (declValues.map (·.getObjValD "binding"))])
  let span := fun (p : Nat × Nat) => (sites.ranks.getD p.1 p.1, sites.ranks.getD p.2 p.2)
  let identity := fun (j : Json) => if physical then
      (j.setObjVal! "file" (ast.getObjValD "file")).setObjVal! "sourceSha256" (ast.getObjValD "sourceSha256")
    else j.setObjVal! "file" "group.ts"
    |>.setObjVal! "sourceSha256" (toJson (String.ofList (List.replicate 64 '0')))
  let equations : Equations := {
    store := L.store
    values := L.values.map fun (n, p, u) => (n, span p, u)
    generics := L.generics.map fun v => { v with pos := span v.pos }
    units := L.units
    initBinders := L.initBinders
    claims := identity (sites.relative L.claims) }
  -- fileFrontFrom reads the definitions for ArrayProto and the declarations
  -- and bindings of values. The validated store holds their lowered types.
  let defs := (declarations.getObjValAs? (Array Json) "definitions").toOption.getD #[]
  let bindings := Json.mkObj [("definitions", .arr (defs.map fun d =>
    Json.mkObj [("declaration", d.getObjValD "declaration")])),
    ("values", .arr (declValues.map fun v => Json.mkObj [
      ("declaration", v.getObjValD "declaration"), ("binding", sites.relative (v.getObjValD "binding"))]))]
  let functions := Functions.of (funcs.map sites.relative) (fr.group i) reachable
  let common := identity ((Json.mkObj [("init", sites.relative (fr.ast.getObjValD "init"))]).setObjVal! "declarations" bindings
    |>.setObjVal! "omittedMentions" (ast.getObjValD "omittedMentions") |>.setObjVal! "modules" (.arr #[]))
  let (imports, est, tables) := groupEnvironment (selected.flatMap fr.captureNames) imports est tables
  return (⟨common, functions, equations, identity (sites.relative claims), sites.unit (fr.unitId i) false, fr.moduleOwned, fr.initOrder, demand, below,
    imports, est, tables, force, fuel, budget, counting⟩, sites)

private def effectWire (q : QualifiedEffect) := Json.mkObj [
  ("regions", toJson (q.1.regions.map fun r => (r.position,r.path,r.key,EffectJson.changeName r.change))),
  ("result", footprint q.2),
  ("closed", footprint q.1.closed), ("throw", toJson q.1.onThrow),
  ("fresh", toJson q.1.fresh), ("alias", toJson q.1.retAlias)]

def importFields (answer : Except String GroupImports) (established : Established)
    (tables : List (String × RowTable)) : List (String × Json) :=
  let imports := match answer with
    | .error e => toJson e
    | .ok v => Json.mkObj [
        ("reads", toJson (v.reads.map fun r => (r.localName, r.location, r.name, r.namePos))),
        ("qualified", toJson (v.qualified.map fun (n,q) => (n, effectWire q))),
        ("depends", toJson v.depends), ("unbound", toJson v.unbound)]
  [("imports", imports),
   ("established", toJson (established.map fun (key,q,id) => (key,effectWire q,id))),
   ("tables", toJson (tables.map fun (l,t) => (l,t.rowsWire,t.interfaces)))]

/-- Ordered fields for comparing two runs. Field hashes are diagnostics. -/
def Input.fields (g : Input) : List (String × Json) :=
  [("members", .arr g.functions.members), ("callees", .arr g.functions.callees),
   ("init", g.common.getObjValD "init"), ("signatures", .arr g.functions.signatures),
   ("order", toJson g.functions.order),
   ("store", storeFields g.equations.store), ("bindings", toJson g.equations.values),
   ("generics", toJson g.equations.generics), ("binders", toJson (g.equations.units,g.equations.initBinders)),
   ("claims", g.claims), ("loweredClaims", g.equations.claims), ("declarations", g.common.getObjValD "declarations"),
   ("omittedMentions", g.common.getObjValD "omittedMentions"),
   ("file", g.common.getObjValD "file"), ("sourceSha256", g.common.getObjValD "sourceSha256"),
   ("leader", toJson g.leader), ("owned", toJson g.owned), ("initOrder", toJson g.initOrder),
   ("demand", toJson g.demand), ("below", answersWire g.below)] ++ importFields g.imports g.established g.tables ++ [
   ("controls", toJson (g.force,g.fuel,g.budget.rounds,g.budget.select,g.budget.rerun,g.counting))]

/-- Raw program and explicit whole-file answers for one independent lowering.
The member list identifies the group even when the slice renumbers the units. -/
structure Slice where
  proposalOrder : List String
  resultConsumers : List String
  ast : Json
  members : List String
  owned : List String
  initOrder : Option String
  demand : Bool
  below : List (String × Option StandIn)
  imports : Except String GroupImports
  established : Established
  tables : List (String × RowTable)
  force : List String
  fuel : Nat
  budget : PositiveCertificates.SearchBudget
  counting : Bool

def Slice.relative (s : Slice) : Slice × Sites :=
  let (ast, sites) := fileProgram s.ast
  let ast := ast.setObjVal! "file" "group.ts" |>.setObjVal! "sourceSha256" (toJson (String.ofList (List.replicate 64 '0')))
  ({ s with ast, members := s.members.map (sites.unit · false), proposalOrder := s.proposalOrder.map (sites.unit · false) }, sites)

/-- Splitting the functions by membership for diagnostics retains their
interleaving and every other input field, including errors and controls. -/
def Slice.fields (s : Slice) : List (String × Json) :=
  let ⟨proposalOrder, resultConsumers, ast, members, owned, initOrder, demand, below, imports, est, tables, force, fuel, budget, counting⟩ := s
  let fs := (ast.getObjValAs? (Array Json) "functions").toOption.getD #[]
  let member := fun (f : Json) =>
    let name := (f.getObjValAs? String "name").toOption.getD ""
    let pos := (f.getObjValAs? (Nat × Nat) "namePos").toOption.getD (0,0)
    members.contains s!"{name}@{pos.1}"
  [("members", toJson (fs.filter member)), ("callees", toJson (fs.filter (!member ·))),
   ("order", toJson (fs.map member)), ("init", ast.getObjValD "init"),
   ("declarations", ast.getObjValD "declarations"), ("omittedMentions", ast.getObjValD "omittedMentions"),
   ("file", ast.getObjValD "file"), ("sourceSha256", ast.getObjValD "sourceSha256"),
   ("group", toJson members), ("owned", toJson owned), ("initOrder", toJson initOrder),
   ("demand", toJson demand), ("resultConsumers", toJson resultConsumers),
   ("proposalOrder", toJson proposalOrder), ("below", answersWire below),
   ("controls", toJson (force, fuel, budget.rounds, budget.select, budget.rerun, counting))] ++
   importFields imports est tables

end Verification.GroupProjection
