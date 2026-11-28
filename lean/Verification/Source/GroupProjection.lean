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

private def decodeFootprint (j : Json) : Except String Footprints.Closed := do
  let [v,a,w] := (← j.getArr?).toList | throw "expected three footprint changes"
  return ⟨← EffectCodec.changeOf v, ← EffectCodec.changeOf a, ← EffectCodec.changeOf w⟩

def decodeAnswers (wire : Json) : Except String (List (String × Option StandIn)) := do
  let entries ← fromJson? (α := List (String × Option Json)) wire
  let answers ← entries.mapM fun (name, proposal) => do
    let value ← proposal.mapM fun j => do
      let exit := fun k => do
        let f ← j.getObjVal? k
        if f.isNull then return none
        return some (← decodeFootprint f)
      return (⟨← j.getObjValAs? String "name", ⟨← exit "normal", ← exit "exceptional"⟩,
        ← decodeFootprint (← j.getObjVal? "result"), ← j.getObjValAs? (Option Nat) "alias"⟩ : StandIn)
    return (name, value)
  unless answersWire answers == wire do throw "invalid group proposal encoding"
  return answers

/-- Canonical source offsets and their inverse, including the zero sentinel. -/
structure Sites where
  offsets : Std.HashMap Nat Nat
  ranks : Std.HashMap Nat Nat
  /-- Physical coordinates for a correspondence that requires the original sites. -/
  physical : Bool := false
  declarations : Std.HashMap Json Json := {}

private def spanField (k : String) := k == "pos" || k == "namePos" || k == "span"

/-- A declaration identity has its own source coordinate system. -/
private def external (j : Json) := (j.getObjVal? "module").isOk &&
  (j.getObjVal? "span").isOk && (j.getObjVal? "name").isOk

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
  ⟨pairs.foldl (fun m (n,i) => m.insert i n) {}, pairs.foldl (fun m (n,i) => m.insert n i) {}, false, {}⟩

def Sites.of (j : Json) : Sites :=
  Sites.ofPairs (((collect j (({} : Std.HashSet Nat).insert 0)).toArray.qsort (· < ·)).zipIdx)

/-- Each declaration starts a new interval. A change in its number of sites
leaves the coordinates of other declarations alone. The stride bounds every
interval even on a file larger than the ordinary one-million-site stride. -/
private def fileSites (code bindings : Json) (anchors : Std.HashSet Nat) (scale : Nat := 1) : Sites := Id.run do
  let offsets := (collect (.arr #[code, bindings]) (({} : Std.HashSet Nat).insert 0)).toArray.qsort (· < ·)
  let stride := max 1048576 (offsets.size + 1)
  let mut pairs := #[]
  let mut block := 0
  let mut index := 0
  for n in offsets do
    if n != 0 && anchors.contains n then
      block := block + 1
      index := 0
    pairs := pairs.push (n, scale * (block * stride + index))
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
def fileProgram (ast : Json) (scale : Nat := 1) : Json × Sites := Id.run do
  let functions := (ast.getObjValAs? (Array Json) "functions").toOption.getD #[]
  let init := (ast.getObjValAs? (Array Json) "init").toOption.getD #[]
  let code := Json.mkObj [("functions", .arr functions), ("init", .arr init)]
  let anchors := (functions.map (·.getObjValD "namePos") ++ init.map (·.getObjValD "pos")).foldl (fun a v =>
    match (fromJson? v : Except String (Nat × Nat)) with | .ok (n,_) => a.insert n | .error _ => a) ({} : Std.HashSet Nat)
  let doc := ast.getObjValD "declarations"
  let rows := fun k => (doc.getObjValAs? (Array Json) k).toOption.getD #[]
  let bindings := (rows "roots" ++ rows "values").map (·.getObjValD "binding")
  let sites := fileSites code (.arr bindings) anchors scale
  let mut doc := doc
  for k in ["roots", "values"] do
    doc := doc.setObjVal! k (.arr ((rows k).map fun v =>
      v.setObjVal! "binding" (sites.relative (v.getObjValD "binding"))))
  return (ast.setObjVal! "functions" (.arr (functions.map sites.relative))
    |>.setObjVal! "init" (.arr (init.map sites.relative)) |>.setObjVal! "declarations" doc, sites)

def Sites.unit (s : Sites) (id : String) (inverse : Bool) : String := Id.run do
  if id.startsWith "module:" then return id
  let n :: names := (id.splitOn "@").reverse | return id
  if names.isEmpty then return id
  let name := String.intercalate "@" names.reverse
  let some n := n.toNat? | return id
  let some m := if inverse then s.offsets.get? n else s.ranks.get? n | return id
  return s!"{name}@{m}"

/-- Substitute whole declaration identities. Their module distinguishes the
coordinate systems of two declarations with equal source spans. -/
private partial def replaceIdentities (ids : Std.HashMap Json Json) (j : Json) : Json :=
  match j with
  | .arr a => .arr (a.map (replaceIdentities ids))
  | .obj kv => if external j then ids.getD j j else
      Json.mkObj (kv.toList.map fun (k,v) => (k, replaceIdentities ids v))
  | _ => j

def Sites.materialize (s : Sites) (line : String) : Except String String := do
  if s.physical then return line
  let j ← Json.parse line
  -- Refusals and elaboration diagnostics contain opaque text produced by
  -- lowering and proof search, including generated binding and head names.
  unless (j.getObjValD "refusal").isNull && (j.getObjValD "elaboration").isNull do
    throw "physical diagnostic required"
  let unit := fun id => do
    if id == "init" || id.startsWith "module:" then return id
    let some n := ((id.splitOn "@").getLast?).bind String.toNat? | throw "missing unit position"
    unless s.offsets.contains n do throw "missing current unit position"
    return s.unit id true
  let mut j := j.setObjVal! "unit" (toJson (← unit (← j.getObjValAs? String "unit")))
  for field in ["members", "depends"] do
    let ids ← j.getObjValAs? (List String) field
    j := j.setObjVal! field (toJson (← ids.mapM unit))
  let contracts ← j.getObjValAs? (Array Json) "contracts"
  let contracts ← contracts.mapM fun read => do
    let .ok member := read.getObjVal? "member" | return read
    let id ← member.getObjVal? "declaration"
    let some current := s.declarations.get? id | throw "missing current declaration identity"
    return read.setObjVal! "member" (member.setObjVal! "declaration" current)
  let contracts := contracts.qsort (·.compress < ·.compress)
  return (j.setObjVal! "contracts" (.arr contracts)).compress

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

/-- Positions preserve document order in the selected rows, including
multiple bindings of one name and multiple definitions of an identity. -/
structure DeclarationIndex where
  document : Json
  roots : Std.HashMap String (List (Nat × Json))
  values : Std.HashMap String (List (Nat × Json))
  definitions : Std.HashMap Json (List (Nat × Json))
  references : Std.HashMap Json (List Json)
  required : Std.HashSet Json

def DeclarationIndex.of (document : Json) : Except String DeclarationIndex := do
  let bindings := fun (rows : Array Json) => Id.run do
    let mut index : Std.HashMap String (List (Nat × Json)) := {}
    for (row, i) in rows.zipIdx do
      if let .ok name := (row.getObjValD "binding").getObjValAs? String "local" then
        index := index.insert name ((i, row) :: index.getD name [])
    return index
  let roots := bindings (← arr document "roots")
  let values := bindings (← arr document "values")
  let mut required := identities (← field document "applications") {}
  let mut definitions := {}
  let mut references := {}
  for (row, i) in (← arr document "definitions").zipIdx do
    let id := row.getObjValD "declaration"
    definitions := definitions.insert id ((i, row) :: definitions.getD id [])
    references := references.insert id ((identities row {}).toList ++ references.getD id [])
    if ImplicitDependency.all.any (·.selects id) then required := required.insert id
  return ⟨document, roots, values, definitions, references, required⟩

/-- The definitions reached by this code, the selected bindings and the
document's implicit reads. Each reached definition contributes its own
references once. Written application obligations and symbol identities
survive the restriction. -/
def DeclarationIndex.slice (index : DeclarationIndex) (code : Json) (names : List String) : Json := Id.run do
  let ordered := fun (rows : List (Nat × Json)) =>
    Json.arr ((rows.mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd).toArray
  let names := (Std.HashSet.ofList names).toList
  let roots := ordered (names.flatMap (index.roots.getD · []))
  let values := ordered (names.flatMap (index.values.getD · []))
  let initial := identities (.arr #[code, roots, values]) index.required
  let mut seen := initial
  let mut definitions := []
  -- Only identities in the index have outgoing edges.
  let mut active := initial.toList.filter index.definitions.contains
  for _ in [:index.definitions.size] do
    let some id := active.head? | break
    active := active.tail
    definitions := index.definitions.getD id [] ++ definitions
    for child in index.references.getD id [] do
      if !seen.contains child && index.definitions.contains child then
        seen := seen.insert child
        active := child :: active
  return index.document.setObjVal! "roots" roots |>.setObjVal! "values" values
    |>.setObjVal! "definitions" (ordered definitions)

/-- Member bodies, external signatures and the initializer statements that
type the module bindings read by the members. Local indices follow file order. -/
def sliceProgram (ast : Json) (index : DeclarationIndex) (bodies signatures statements : List Nat) (reads : List String) : Except String Json := do
  let functions ← arr ast "functions"
  let init ← arr ast "init"
  let fs ← ((bodies ++ signatures).eraseDups.mergeSort (· ≤ ·)).mapM fun j => do
    let some fn := functions[j]? | throw "missing function declaration"
    return if bodies.contains j then fn else fn.setObjVal! "body" (.arr #[])
  let ss ← statements.mapM fun j => do
    let some stmt := init[j]? | throw "missing initializer statement"
    return stmt
  let code := Json.arr #[.arr fs.toArray, .arr ss.toArray]
  let declarations := index.slice code reads
  return ast.setObjVal! "functions" (.arr fs.toArray) |>.setObjVal! "init" (.arr ss.toArray)
    |>.setObjVal! "declarations" declarations |>.setObjVal! "modules" (.arr #[])

/-- Reconstruct the transitive program used to produce physical diagnostics.
The declaration, function and statement order determines equation head names. -/
def diagnosticProgram (ast : Json) (fr : Front) (i : Nat) (order : List Nat) : Except String Json := do
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
  let index ← DeclarationIndex.of (← field ast "declarations")
  let declarations := index.slice (.arr #[.arr fs, .arr ss]) names
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
  let sites := if physical then (⟨{}, {}, true, {}⟩ : Sites) else Sites.of (.arr #[code, claims, L.claims,
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
  externalGroups : List (List String)
  dependencies : List String
  inheritedReturn : Bool
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

/-- Only a local declarator and its identifier uses can be renamed together.
A matching string anywhere else in the function reserves its spelling,
including literal values, property keys and names in annotations. -/
private structure LocalNames where
  binders : Std.HashMap String Nat := {}
  reserved : Std.HashSet String := {}

private def shadowBase (name : String) : Option String := do
  let [base, suffix] := name.splitOn "@" | none
  let [line, col] := suffix.splitOn ":" | none
  guard ((← line.toNat?) > 0 && (← col.toNat?) > 0)
  return base

private partial def localNames (j : Json) (s : LocalNames) : LocalNames := Id.run do
  match j with
  | .arr xs => return xs.foldl (fun acc v => localNames v acc) s
  | .obj fields =>
    return fields.foldl (fun acc k v => Id.run do
      let acc := { acc with reserved := acc.reserved.insert k }
      if k == "name" then
        if let .ok name := v.getStr? then
          if (shadowBase name).isSome then
            if j.getObjValD "k" == .str "id" then return acc
            if (j.getObjVal? "early").isOk && (j.getObjVal? "init").isOk then
              if let .ok (pos, _) := j.getObjValAs? (Nat × Nat) "namePos" then
                return { acc with binders := acc.binders.insert name pos }
      return localNames v acc) s
  | .str name => return { s with reserved := s.reserved.insert name }
  | _ => return s

private partial def renameStrings (names : Std.HashMap String String) (j : Json) : Json :=
  match j with
  | .arr a => .arr (a.map (renameStrings names))
  | .obj kv => Json.mkObj (kv.toList.map fun (k,v) => (k, renameStrings names v))
  | .str n => .str (names.getD n n)
  | _ => j

private def relativeLocals (fn : Json) : Json := Id.run do
  let names := localNames fn {}
  let ordered := names.binders.toArray.qsort (fun a b => a.2 < b.2 || (a.2 == b.2 && a.1 < b.1))
  let mut renames := {}
  for ((old,_), i) in ordered.zipIdx do
    let some base := shadowBase old | continue
    let fresh := s!"{base}@0:{i}"
    unless names.reserved.contains old || names.reserved.contains fresh do
      renames := renames.insert old fresh
  return if renames.isEmpty then fn else renameStrings renames fn

/-- File preparation shares the normalized rows used by each slice. A
declaration identity is distinguished within its module and name. Canonical
symbol numbers on module interfaces require the symbol's physical identity. -/
structure DeclarationSites where
  rows : Std.HashMap Json Json
  physicalIds : Std.HashMap Json Json
  definitions : EquationLowering.DefinitionCache

def DeclarationSites.of (ast : Json) : DeclarationSites := Id.run do
  let ast := ast.setObjVal! "modules" (.arr #[])
  let doc := ast.getObjValD "declarations"
  let rows := fun k => (doc.getObjValAs? (Array Json) k).toOption.getD #[]
  let key := fun (id : Json) => (id.getObjValD "module", id.getObjValD "name")
  let symbols := Std.HashSet.ofArray ((rows "symbols").map key)
  let span := fun (id : Json) => (id.getObjValAs? (Nat × Nat) "span").toOption.getD (0,0)
  let ordered := (identities ast {}).toArray.qsort (fun a b => (span a).1 < (span b).1 || ((span a).1 == (span b).1 && (span a).2 < (span b).2))
  let mut counts : Std.HashMap (Json × Json) Nat := {}
  let mut relative := {}
  let mut physical := {}
  for id in ordered do
    let k := key id
    let i := counts.getD k 0 + 1
    counts := counts.insert k i
    let canonical := if symbols.contains k || span id == (0,0) then id else id.setObjVal! "span" (toJson (i,i))
    relative := relative.insert id canonical
    physical := physical.insert canonical id
  let subst := replaceIdentities relative
  let mut replacements := {}
  let mut defs := #[]
  let mut occupied : Std.HashSet Nat := {}
  for k in ["definitions", "values", "roots"] do
    for row in rows k do
      let binding := row.getObjVal? "binding"
      let body := if binding.isOk then row.setObjVal! "binding" .null else row
      let id := row.getObjValD "declaration"
      let ownerKey := toJson (k, relative.getD id id, (row.getObjValD "binding").getObjValD "local")
      -- Start at the same slot when an unrelated declaration is inserted.
      -- Check occupancy: even colliding hashes get different intervals.
      let mut owner := (hash ownerKey).toNat % 65536
      for _ in [:occupied.size] do
        if !occupied.contains owner then break
        owner := owner + 1
      occupied := occupied.insert owner
      let sites := Sites.of body
      -- Executable sites are even. Each row has its own disjoint positive
      -- odd sites, ordered by the distinct offsets within that row.
      let sites := Sites.ofPairs (sites.offsets.toArray.map fun (rank,n) =>
        (n, if n == 0 then 0 else (owner + rank) * (owner + rank + 1) + 2 * owner + 1))
      let normalized := subst (sites.relative body)
      let normalized := if let .ok b := binding then normalized.setObjVal! "binding" b else normalized
      replacements := replacements.insert row normalized
      if k == "definitions" then defs := defs.push normalized
  for fn in (ast.getObjValAs? (Array Json) "functions").toOption.getD #[] do
    replacements := replacements.insert fn (relativeLocals (subst fn))
    let signature := fn.setObjVal! "body" (.arr #[])
    replacements := replacements.insert signature (relativeLocals (subst signature))
  for k in ["init", "applications"] do
    let source := if k == "init" then ast else doc
    for row in (source.getObjValAs? (Array Json) k).toOption.getD #[] do
      replacements := replacements.insert row (subst row)
  return ⟨replacements, physical, EquationLowering.DefinitionCache.ofDocument
    (Json.mkObj [("definitions", .arr defs)])⟩

def Slice.relative (s : Slice) (decls : DeclarationSites) : Slice × Sites := Id.run do
  let replace := fun (doc : Json) (k : String) =>
    doc.setObjVal! k (.arr (((doc.getObjValAs? (Array Json) k).toOption.getD #[]).map fun row =>
      decls.rows.getD row row))
  let doc := ["values","definitions","roots","applications"].foldl replace (s.ast.getObjValD "declarations")
  let ast := replace (replace s.ast "functions") "init" |>.setObjVal! "declarations" doc
  let (ast, sites) := fileProgram ast 2
  let sites := { sites with declarations := decls.physicalIds }
  let ast := ast.setObjVal! "file" "group.ts" |>.setObjVal! "sourceSha256" (toJson (String.ofList (List.replicate 64 '0')))
  return ({ s with ast
                   externalGroups := s.externalGroups.map (·.map (sites.unit · false))
                   dependencies := s.dependencies.map (sites.unit · false), members := s.members.map (sites.unit · false), proposalOrder := s.proposalOrder.map (sites.unit · false) }, sites)

/-- The complete input of the stored operation, including the entire slice
Fragment. Field hashes in the shadow report are for comparisons only. -/
def Slice.wire (s : Slice) : String :=
  let ⟨externalGroups, dependencies, inheritedReturn, order, consumers, ast, members, owned, initOrder, demand, below, imports, est, tables,
    force, fuel, budget, counting⟩ := s
  let program := Json.mkObj ([("ast", ast), ("externalGroups", toJson externalGroups), ("dependencies", toJson dependencies),
    ("inheritedReturn", toJson inheritedReturn), ("group", toJson members), ("owned", toJson owned), ("initOrder", toJson initOrder),
    ("demand", toJson demand), ("resultConsumers", toJson consumers), ("proposalOrder", toJson order),
    ("controls", toJson (force, fuel, budget.rounds, budget.select, budget.rerun, counting))] ++
    importFields imports est tables)
  String.intercalate "\n" (program.compress :: below.map (fun answer => (answersWire [answer]).compress))

/-- Splitting the functions by membership for diagnostics retains their
interleaving and every other input field, including errors and controls. -/
def Slice.fields (s : Slice) : List (String × Json) :=
  let ⟨externalGroups, dependencies, inheritedReturn, proposalOrder, resultConsumers, ast, members, owned, initOrder, demand, below, imports, est, tables, force, fuel, budget, counting⟩ := s
  let fs := (ast.getObjValAs? (Array Json) "functions").toOption.getD #[]
  let member := fun (f : Json) =>
    let name := (f.getObjValAs? String "name").toOption.getD ""
    let pos := (f.getObjValAs? (Nat × Nat) "namePos").toOption.getD (0,0)
    members.contains s!"{name}@{pos.1}"
  [("externalGroups", toJson externalGroups), ("dependencies", toJson dependencies), ("inheritedReturn", toJson inheritedReturn),
   ("members", toJson (fs.filter member)), ("callees", toJson (fs.filter (!member ·))),
   ("order", toJson (fs.map member)), ("init", ast.getObjValD "init"),
   ("declarations", ast.getObjValD "declarations"), ("omittedMentions", ast.getObjValD "omittedMentions"),
   ("file", ast.getObjValD "file"), ("sourceSha256", ast.getObjValD "sourceSha256"),
   ("group", toJson members), ("owned", toJson owned), ("initOrder", toJson initOrder),
   ("demand", toJson demand), ("resultConsumers", toJson resultConsumers),
   ("proposalOrder", toJson proposalOrder), ("below", answersWire below),
   ("controls", toJson (force, fuel, budget.rounds, budget.select, budget.rerun, counting))] ++
   importFields imports est tables

end Verification.GroupProjection
