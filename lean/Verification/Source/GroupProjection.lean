import Verification.Source.Claims.ModuleInterfaces

/-! The source inputs of a fresh group plan. The worker compares a plan over
these inputs with its ordinary plan before reporting a shadow hit. -/
namespace Verification.GroupProjection
open Lean SourceClaimJson EquationLowering

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

/-- The current file's interpretation of executable sites and declarations. -/
structure Sites where
  points : Std.HashMap SourcePoint Nat := {}
  declarations : Std.HashMap Json Json := {}
  symbols : Array Nat := #[]
  moduleUnits : Std.HashMap String String := {}

private def spanField (k : String) := k == "pos" || k == "namePos" || k == "span" || k == "at"

/-- A declaration identity has its own source coordinate system. -/
private def external (j : Json) := (j.getObjVal? "module").isOk &&
  (j.getObjVal? "span").isOk && (j.getObjVal? "name").isOk

private def collectEndpoints (seen : Std.HashSet Nat) (span : Nat × Nat) : Std.HashSet Nat :=
  if span == (0, 0) then seen else (seen.insert span.1).insert span.2

private partial def collect (j : Json) (s : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  match j with
  | .arr a => return a.foldl (fun s v => collect v s) s
  | .obj kv =>
    if external j then return s
    return kv.foldl (fun s k v =>
      if spanField k then match (fromJson? v : Except String (Nat × Nat)) with
        | .ok span => collectEndpoints s span
        | .error _ => collect v s
      else collect v s) s
  | _ => return s

/-- Walk a Fragment row in a fixed order. A declaration reference has its
own scope, and a source range is one occurrence. -/
private partial def mapSites [Monad m] (site : Nat × Nat → m Json)
    (references : Std.HashMap Json Json) (j : Json) : m Json := do
  match j with
  | .arr items => return .arr (← items.mapM (mapSites site references))
  | .obj fields =>
    if external j then return references.getD j j
    let fields ← fields.toList.mapM fun (k, v) => do
      if spanField k then
        if let .ok span := (fromJson? v : Except String (Nat × Nat)) then
          return (k, ← site span)
      if k == "arguments" && (j.getObjVal? "target").isOk then
        -- TypeScript compares these ranges while producing the fragment.
        -- Equation lowering consumes the applied type terms in `args`.
        return (k, .arr #[])
      return (k, ← mapSites site references v)
    return Json.mkObj fields
  | _ => return j

/-- Type occurrences in a declaration row. Repeated uses of the same
source range in its translated type denote the same occurrence. -/
private def nameTypeSites (owner : Json) (references : Std.HashMap Json Json) (row : Json) : Json :=
  let visit := fun (span : Nat × Nat) => do
    if span == (0,0) then return toJson span
    let seen ← get
    if let some i := seen.get? span then return toJson (owner, i)
    let i := seen.size
    set (seen.insert span i)
    return toJson (owner, i)
  (mapSites (m := StateM (Std.HashMap (Nat × Nat) Nat)) visit references row).run' {}

/-- A point-specific proposal control is written against the current file. Resolve
its selection in the same table as the expression it targets. -/
private def pointControl (names : Std.HashMap Nat SourcePoint) (control : String) : String := Id.run do
  unless control.startsWith "point@" do return control
  let [start, stop] := (control.drop 6).toString.splitOn "-" | return control
  let some a := start.toNat? | return control
  let some b := stop.toNat? | return control
  let point := fun n => names.getD n (SourcePoint.offset n)
  return s!"point@{point a}-{point b}"

/-- Number the lexical endpoints within each declaration. Overload signatures
can share the same implementation body. Their common syntax has one owner. -/
private def nameExecutableSites (ast : Json) (controls : List String) : Json × Sites × List String := Id.run do
  let functions := (ast.getObjValAs? (Array Json) "functions").toOption.getD #[]
  let doc := ast.getObjValD "declarations"
  let rows := fun k => (doc.getObjValAs? (Array Json) k).toOption.getD #[]
  let mut owners : Std.HashMap String (Std.HashSet Nat) := {}
  for fn in functions do
    let owner := (toJson ("function", fn.getObjValD "name")).compress
    owners := owners.insert owner (collect fn (owners.getD owner {}))
  let init := ast.getObjValD "init"
  owners := owners.insert "init" (collect init {})
  for row in rows "roots" ++ rows "values" do
    let binding := row.getObjValD "binding"
    let owner := (toJson ("binding", binding.getObjValD "local")).compress
    owners := owners.insert owner (collect binding (owners.getD owner {}))
  let mut names : Std.HashMap Nat SourcePoint := {}
  let mut sites : Sites := {}
  for (owner, offsets) in owners.toArray.qsort (fun a b => a.1 < b.1) do
    let sorted := offsets.toArray.qsort (· < ·)
    for (offset, i) in sorted.zipIdx do
      let point := SourcePoint.occurrence owner i
      names := names.insertIfNew offset point
      sites := {sites with points := sites.points.insert point offset}
  let point := fun n => names.getD n (SourcePoint.offset n)
  let range := fun (span : Nat × Nat) =>
    if span == (0,0) then toJson span else toJson (point span.1, point span.2)
  let name := fun j => Id.run (mapSites (pure ∘ range) {} j)
  let mut doc := doc
  for k in ["roots", "values"] do
    doc := doc.setObjVal! k (.arr ((rows k).map fun v =>
      v.setObjVal! "binding" (name (v.getObjValD "binding"))))
  return (ast.setObjVal! "functions" (.arr (functions.map name))
    |>.setObjVal! "init" (name init) |>.setObjVal! "declarations" doc, sites, controls.map (pointControl names))

/-- The Fragment, effect and equation-row encodings of symbol keys and literals. -/
private partial def symbolEdits [Monad m] (number : Nat → m Nat) (j : Json) : m (Option Json) := do
  match j with
  | .arr xs =>
    let mut changed := none
    for h : i in [:xs.size] do
      if let some v ← symbolEdits number xs[i] then changed := some ((changed.getD xs).set! i v)
    return changed.map Json.arr
  | .obj fields =>
    let mut changed := none
    for (k, v) in fields do
      let key := if k == "symbol" then v.getNat?.toOption else none
      let literal := if k == "sym" || k == "symbolLit" then (v.getObjValAs? Nat "id").toOption else none
      let next ← match key, literal with
        | some n, _ => do
          let i ← number n
          pure (if i == n then none else some (toJson i))
        | _, some n => do
          let i ← number n
          pure (if i == n then none else some (v.setObjVal! "id" (toJson i)))
        | _, _ => symbolEdits number v
      if let some v' := next then changed := some ((changed.getD fields).insert k v')
    return changed.map Json.obj
  | _ => return none

private def mapSymbols [Monad m] (number : Nat → m Nat) (j : Json) : m Json := do
  return (← symbolEdits number j).getD j

/-- Resolve the contract declarations of a stored verdict for the worker wire. -/
def Sites.printContracts (s : Sites) (j : Json) : Except String String := do
  let contracts ← j.getObjValAs? (Array Json) "contracts"
  let contracts ← contracts.mapM fun read => do
    let .ok member := read.getObjVal? "member" | return read
    let id ← member.getObjVal? "declaration"
    let some current := s.declarations.get? id | throw "missing current declaration identity"
    let key ← mapSymbols (fun i => pure (s.symbols[i]?.getD i)) (member.getObjValD "key")
    return read.setObjVal! "member" ((member.setObjVal! "declaration" current).setObjVal! "key" key)
  let contracts := contracts.qsort (·.compress < ·.compress)
  return (j.setObjVal! "contracts" (.arr contracts)).compress

open EquationLowering

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

private partial def reaches (test : Json → Bool) (j : Json) : Bool :=
  match j with
  | .arr xs => xs.any (reaches test)
  | .obj fs => test j || fs.any fun _ v => reaches test v
  | _ => false

/-- Array annotations, allocation and positive array-test refinement read the
prototype equation. The last two reads also occur in unannotated expressions. -/
private def reachesPrototype := reaches fun j => match kindOf j with
  | some "array" | some "tuple" | some "arrayLit" | some "arrayTest" => true
  | _ => false

private def reachesResolution := reaches fun j => !(j.getObjValD "resolution").isNull

/-- Positions preserve document order in the selected rows, including
multiple bindings of one name and multiple definitions of an identity. -/
structure DeclarationIndex where
  document : Json
  roots : Std.HashMap String (List (Nat × Json))
  values : Std.HashMap String (List (Nat × Json))
  definitions : Std.HashMap Json (List (Nat × Json))
  references : Std.HashMap Json (List Json)
  resolution : List Json
  usesResolution : Std.HashSet Json

def DeclarationIndex.of (document : Json) : Except String DeclarationIndex := do
  let bindings := fun (rows : Array Json) => Id.run do
    let mut index : Std.HashMap String (List (Nat × Json)) := {}
    for (row, i) in rows.zipIdx do
      if let .ok name := (row.getObjValD "binding").getObjValAs? String "local" then
        index := index.insert name ((i, row) :: index.getD name [])
    return index
  let roots := bindings (← arr document "roots")
  let values := bindings (← arr document "values")
  let rows ← arr document "definitions"
  let resolution := rows.toList.map (·.getObjValD "declaration") |>.filter fun id =>
    ImplicitDependency.stable.selects id || ImplicitDependency.promise.selects id
  let mut definitions := {}
  let mut references := {}
  let mut usesResolution := {}
  for (row, i) in rows.zipIdx do
    let id := row.getObjValD "declaration"
    definitions := definitions.insert id ((i, row) :: definitions.getD id [])
    let edges := identities row {}
    let edges := if reachesPrototype row then edges.insert arrayProtoIdentity else edges
    let readsResolution := reachesResolution row
    if readsResolution then usesResolution := usesResolution.insert id
    let implied := if readsResolution then resolution else []
    references := references.insert id (implied ++ edges.toList ++ references.getD id [])
  return ⟨document, roots, values, definitions, references, resolution, usesResolution⟩

/-- Failed external reads of the declaration environment. The selected rows
in the fragment carry the successful answers. -/
structure MissingReads where
  definitions : List Json
  roots : List String
  values : List String
  resolution : List ImplicitDependency
  deriving ToJson, Inhabited

/-- The definitions reached by this code, the selected bindings and the
implicit reads. The second result names every requested definition absent
from the document, including absent references of reached definitions. -/
def DeclarationIndex.slice (index : DeclarationIndex) (code : Json) (names : List String)
    (readBuiltins := false) (captured : List String := []) : Json × MissingReads := Id.run do
  let ordered := fun (rows : List (Nat × Json)) =>
    Json.arr ((rows.mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd).toArray
  let early := Fragment.throwUninitializedName
  let names := if names.contains early && !captured.contains early &&
      !(reaches (fun j => j.getObjValD "early" == .bool true || j.getObjValD "name" == .str early) code)
    then names.erase early else names
  let names := (Std.HashSet.ofList names).toList
  let roots := ordered (names.flatMap (index.roots.getD · []))
  let values := ordered (names.flatMap (index.values.getD · []))
  -- Preparation checks every written type argument before publishing any unit.
  let inputs := Json.arr #[code, roots, values]
  let initial := identities inputs {}
  let mut resolutionRead := reachesResolution inputs
  let initial := if resolutionRead then index.resolution.foldl (·.insert ·) initial else initial
  let initial := if readBuiltins || reachesPrototype inputs then initial.insert arrayProtoIdentity else initial
  let mut seen := initial
  let mut definitions := []
  -- Only identities in the index have outgoing edges.
  let mut active := initial.toList.filter index.definitions.contains
  for _ in [:index.definitions.size] do
    let some id := active.head? | break
    active := active.tail
    definitions := index.definitions.getD id [] ++ definitions
    resolutionRead := resolutionRead || index.usesResolution.contains id
    for child in index.references.getD id [] do
      if !seen.contains child then
        seen := seen.insert child
        if index.definitions.contains child then active := child :: active
  let doc := index.document.setObjVal! "roots" roots |>.setObjVal! "values" values
    |>.setObjVal! "definitions" (ordered definitions) |>.setObjVal! "applications" (.arr #[])
  let missingResolution := if resolutionRead then
      [ImplicitDependency.stable, .promise].filter (!index.resolution.any ·.selects) else []
  return (doc, ⟨seen.toList.filter (!index.definitions.contains ·),
    (names.filter (!index.roots.contains ·)).mergeSort,
    (names.filter (!index.values.contains ·)).mergeSort,
    missingResolution⟩)

/-- Lowering queries ownership for a captured sibling, a variable access or
an early binding when setting up its cell. Each query names a source binding. -/
def ownedIn (owned reads : List String) (code : Json) : List String :=
  owned.filter fun n => reads.contains n || reaches (fun j =>
    j.getObjValD "name" == .str n &&
      (kindOf j == some "id" || j.getObjValD "early" == .bool true)) code

/-- Member bodies, external signatures and the initializer statements that
type the module bindings read by the members. Local indices follow file order. -/
def sliceProgram (ast : Json) (bodies signatures statements : List Nat) : Except String Json := do
  let functions ← arr ast "functions"
  let init ← arr ast "init"
  let fs ← ((bodies ++ signatures).eraseDups.mergeSort (· ≤ ·)).mapM fun j => do
    let some fn := functions[j]? | throw "missing function declaration"
    return if bodies.contains j then fn else fn.setObjVal! "body" (.arr #[])
  let ss ← statements.mapM fun j => do
    let some stmt := init[j]? | throw "missing initializer statement"
    return stmt
  return ast.setObjVal! "functions" (.arr fs.toArray) |>.setObjVal! "init" (.arr ss.toArray)
    |>.setObjVal! "modules" (.arr #[]) |>.setObjVal! "omittedMentions" (.arr #[])

def groupEnvironment (captures : List String) (imports : Except String GroupImports) (est : Established)
    (tables : List (String × RowTable)) : Except String GroupImports × Established × List (String × RowTable) := Id.run do
  let imports := imports.map fun r => { r with unbound := r.unbound.filter (captures.contains ·.1) }
  let reads := (imports.toOption.map (·.reads)).getD []
  let est := reads.filterMap fun r => (est.lookup (r.location, r.name)).map ((r.location,r.name), ·)
  let tables := (reads.map (·.location)).eraseDups.filterMap fun loc => do
    let t ← tables.lookup loc
    let names := (reads.filter (·.location == loc)).map (·.name)
    return (loc, t.restrict names)
  return (imports, est, tables)

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
        ("reads", toJson (v.reads.map fun r => (r.localName, r.location, r.name))),
        ("qualified", toJson (v.qualified.map fun (n,q) => (n, effectWire q))),
        ("depends", toJson v.depends), ("unbound", toJson v.unbound)]
  [("imports", imports),
   ("established", toJson (established.map fun (key,q,id) => (key,effectWire q,id))),
   ("tables", toJson (tables.map fun (l,t) => (l,t.rowsWire,t.interfaces)))]

structure UnitNames where
  references : Array UnitRef
  wire : Std.HashMap UnitRef String
  fromWire : Std.HashMap String UnitRef

def UnitNames.ofFront (fr : Front) : UnitNames := Id.run do
  let references := fr.unitReferences
  let mut names : UnitNames := ⟨references, {}, {}⟩
  for ((fn, _, init), ref) in fr.units.zip references.toList do
    let wire := if init.isSome then "init" else s!"{fn.name}@{fn.namePos.1}"
    names := { names with wire := names.wire.insert ref wire, fromWire := names.fromWire.insert wire ref }
  return names

/-- Translate the unit fields of a verdict. Dependencies supplied by a
module interface belong to that module's name space. -/
private def mapVerdictUnits (resolve : Json → Except String Json) (j : Json) : Except String Json := do
  let mut line := j.setObjVal! "unit" (← resolve (← j.getObjVal? "unit"))
  for field in ["members", "depends"] do
    if field == "members" || (j.getObjVal? field).isOk then
      let units ← j.getObjValAs? (List Json) field
      line := line.setObjVal! field (toJson (← units.mapM fun u =>
        if field == "depends" && u.getStr?.toOption.any (·.startsWith "module:") then pure u else resolve u))
  return line

def UnitNames.nameVerdict (names : UnitNames) := mapVerdictUnits fun j => do
  let wire ← j.getStr?
  let some ref := names.fromWire.get? wire | throw s!"unknown unit {wire}"
  return toJson ref

def UnitNames.printVerdict (names : UnitNames) := mapVerdictUnits fun j => do
  let ref ← fromJson? j
  let some wire := names.wire.get? ref | throw s!"unknown declaration {repr ref}"
  return toJson wire

open EquationGraphs

/-- An initialization supplies the types of the bindings a member reads.
Head numbers here are local to the ordered roots and their template operands. -/
inductive BindingKind where
  | written | claimed | cell
  deriving ToJson, BEq, Inhabited

structure BindingEnvironment where
  slots : List (String × BindingKind × List Tree)
  heads : Array Draft
  origins : Array (Option Json)

deriving instance ToJson for HeadKind

def BindingEnvironment.wire (env : BindingEnvironment) : Json :=
  toJson (env.slots, env.origins, env.heads.map fun d =>
    (d.name, toJson d.kind, toJson d.kinds,
      d.binders.map (fun (b : EquationGraphs.Binder) => (b.name,toJson b.kind)), toJson d.body, toJson d.defaults))

/-- Heads rebuilt by the reader's lowering refer to their declarations.
Only a structural template carries its operands across the boundary. -/
private def HeadKind.structural : HeadKind → Bool
  | .literal | .scheme | .primitive => true
  | .declaration _ | .proto | .array _ | .method .. | .unit _ => false

def bindingEnvironment (fr : Front) (reads : List String) : Option BindingEnvironment := do
  let T := fr.d.types
  let mut roots := []
  for v in fr.moduleConstants do
    unless reads.contains v.1 do continue
    let (kind, A) ← match v.2.2 with
      | .ok (.claimed (.ok A) _) => some (BindingKind.claimed, A)
      | .ok (.cell (.ok A)) => some (.cell, A)
      | .ok (.written _) => some (.written, [])
      | _ => none
    roots := (v.1, kind, A) :: roots
  roots := roots.reverse
  let push := fun (st : Std.HashMap Nat Nat × Array Nat) (hs : List Nat) =>
    hs.foldl (fun (s : Std.HashMap Nat Nat × Array Nat) h =>
      if s.1.contains h then s else (s.1.insert h s.2.size, s.2.push h)) st
  let mut queue := push ({}, #[]) (roots.flatMap fun (_, _, A) => A.flatMap Tree.dependencyHeads)
  let mut heads := #[]
  let mut origins := #[]
  for i in [:T.heads.size] do
    let some h := queue.2[i]? | break
    let d ← T.heads[h]?
    let row ← d.body
    if let .unit _ := d.kind then failure
    let parent := match d.kind with | .method o _ => [o] | _ => []
    let binder := match row with | .param t .. => t.dependencyHeads | _ => []
    let children := ((row.operands ++ d.defaults.map Prod.snd).flatten.flatMap Tree.dependencyHeads)
    queue := push queue (if HeadKind.structural d.kind then binder ++ children else parent)
    let f := (queue.1.getD · 0)
    let rename := treeRename f
    let origin ← match d.kind with
      | .declaration j => some <$> (T.doc[j]?.map (·.identity))
      | _ => pure none
    let kind := match d.kind with
      | .declaration _ => HeadKind.declaration 0
      | .method o k => HeadKind.method (f o) k
      | k => k
    heads := heads.push { d with
      kind, name := match kind with | .literal => "type" | _ => d.name
      body := if HeadKind.structural kind then some (row.map rename (·.map rename)) else none
      defaults := if HeadKind.structural kind then d.defaults.map fun (j,A) => (j,A.map rename) else [] }
    origins := origins.push origin
  guard (heads.size == queue.2.size)
  -- Free variables are indexed in the elaborator's lexical environment.
  -- Template arguments and locals are bound by their own head.
  guard (!reaches (fun j => (j.getObjVal? "var").isOk && (j.getObjVal? "owner").isOk)
    (toJson (roots, heads.map fun d => (toJson d.body, toJson d.defaults))))
  return ⟨roots.map (fun (n,c,A) => (n,c,A.map (treeRename (queue.1.getD · 0)))), heads, origins⟩

/-- Rebuild the binding types in an independently lowered group. Nominal
heads resolve in that group's declarations. Structural heads share the
same template equality as equation compaction. -/
def BindingEnvironment.install (env : BindingEnvironment) (fr : Front) : Except String Front := do
  let T := fr.d.types
  let decl := fun (i : Nat) => env.origins[i]?.join.bind fun id => do
    let [j] := T.identities.getD id [] | none
    T.keys.get? s!"decl|{j}"
  let owner := fun i => match (env.heads[i]?).map Draft.kind with
    | some (.declaration _) => decl i
    | some .proto => T.proto
    | some (.array ro) => T.keys.get? s!"array|{ro}"
    | _ => none
  let mut numbers : Array Nat := #[]
  let mut next := T.heads.size
  for (d,i) in env.heads.zipIdx do
    if HeadKind.structural d.kind then
      numbers := numbers.push next
      next := next + 1
    else
      let target := match d.kind with
        | .method o k => (owner o).bind fun h => T.keys.get? s!"method|{h}|{k}"
        | _ => owner i
      let some h := target | throw "binding type owner is absent from the reader"
      numbers := numbers.push h
  let renameDraft := fun (f : Nat → Nat) (d : Draft) =>
    let rn := treeRename f
    { d with
      body := d.body.map (·.map rn (·.map rn)), kind := match d.kind with | .method owner k => .method (f owner) k | k => k,
      defaults := d.defaults.map fun (i,A) => (i,A.map rn) }
  let mut combined := T.heads
  for (d, i) in env.heads.zipIdx do
    if numbers[i]! ≥ T.heads.size then combined := combined.push (renameDraft (numbers[·]!) d)
  let rep := hashCons combined
  let mut installed := T.heads
  let mut positions := Array.range T.heads.size
  for i in [T.heads.size:combined.size] do
    if rep[i]! == i then
      positions := positions.push installed.size
      installed := installed.push combined[i]!
    else positions := positions.push positions[rep[i]!]!
  let translate := fun i => positions[numbers[i]!]!
  let mut keys := T.keys
  for i in [T.heads.size:installed.size] do
    let d := renameDraft (positions[·]!) installed[i]!
    installed := installed.set! i d
    if let some (.clauses cs) := d.body then
      if d.kinds.isEmpty then keys := keys.insertIfNew s!"ground|{spelling cs}" i
  -- The intern index merges equal rows. Defaults are additional planning
  -- input and must agree even when the row has an existing representative.
  for (d, i) in env.heads.zipIdx do
    if HeadKind.structural d.kind then
      let expected := renameDraft translate d
      let actual := installed[translate i]!
      unless expected.kinds == actual.kinds && expected.binders == actual.binders &&
          expected.body == actual.body && expected.defaults == actual.defaults do
        throw "binding template differs in the reader"
  let T := {T with heads := installed, keys, nullary := nullaryOf installed, nullary_eq := rfl}
  let slots ← env.slots.mapM fun (n,kind,A) => do
    let some binder := fr.init.findSome? (fun stmt => match stmt with
      | .constants _ bs | .mutables _ bs => bs.find? (·.name == n)
      | _ => none) | throw "missing initialization binding"
    let A := normUnion (A.map (treeRename translate))
    let slot ← match kind with
      | .written => do
        let some annot := binder.annot | throw "missing written binding type"
        pure (SourceElaboration.ModuleType.written annot)
      | .cell => pure (.cell (.ok A))
      | .claimed => pure (.claimed (.ok A) binder.annot)
    return (n, binder.namePos, Except.ok slot)
  return { fr with d := {fr.d with types := T}, moduleConstants := slots, init := [] }

/-- Raw program and explicit whole-file answers for one independent lowering.
The member list identifies the group even when the slice renumbers the units. -/
structure Slice where
  externalGroups : List (List UnitRef)
  dependencies : List UnitRef
  inheritedReturn : Bool
  proposalOrder : List UnitRef
  resultConsumers : List String
  ast : Json
  members : List UnitRef
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
  missing : MissingReads := default
  bindings : Option BindingEnvironment := none

/-- The checked source range belongs to the refusal. Its endpoints resolve in
the file that prints the worker line. -/
structure StoredMessage where
  heading : String
  site : Span
  reason : String
  raw : String
  projection : Option NodeRecord := none
  deriving ToJson, FromJson

inductive StoredFailure where
  | text (message : String)
  | located (message : StoredMessage)
  | expression (unit : UnitRef) (index : Nat) (exhausted : Bool)
  | elaboration (unit : UnitRef)
  | planning (reason : String)
  deriving ToJson, FromJson

def StoredFailure.ofFailure : PassDiagnostic → StoredFailure
  | .expression unit index exhausted _ => .expression unit index exhausted
  | .before unit _ => .elaboration unit
  | .located msg raw record => .located ⟨msg.heading, msg.pos, msg.reason, raw, record.map (·.node)⟩
  | .text msg => .text msg

def StoredFailure.readsPlan : StoredFailure → Bool
  | .text _ => false
  | .located msg => msg.projection.isSome
  | .elaboration _ | .expression .. | .planning _ => true

def Sites.offset (s : Sites) : SourcePoint → Except String Nat
  | .offset n => pure n
  | .occurrence o i d => do
    let some n := s.points.get? (.occurrence o i) | throw "missing diagnostic occurrence"
    return n + d

def StoredMessage.print (m : StoredMessage) (sites : Sites)
    (project : NodeRecord → Except String (List (String × Json))) : Except String String := do
  let pos : Span := (.offset (← sites.offset m.site.1), .offset (← sites.offset m.site.2))
  let text := (PassDiagnostic.located ⟨m.heading, pos, m.reason⟩ m.raw none).render
  let some node := m.projection | return text
  let resolve := fun j => Id.run (mapSymbols (pure ∘ fun i => sites.symbols[i]?.getD i) j)
  let witness := resolve node.witness.2
  let node : NodeRecord := {node with edge := node.edge.map fun (e : EdgeRecord) => {e with required := resolve e.required}}
  return RequestJson.withDiagnostic text (← project { node with witness := (node.witness.1, witness) })

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

private def localRenames (fn : Json) : Std.HashMap String String := Id.run do
  let names := localNames fn {}
  let ordered := names.binders.toArray.qsort (fun a b => a.2 < b.2 || (a.2 == b.2 && a.1 < b.1))
  let mut renames := {}
  for ((old,_), i) in ordered.zipIdx do
    let some base := shadowBase old | continue
    let fresh := s!"{base}@0:{i}"
    unless names.reserved.contains old || names.reserved.contains fresh do
      renames := renames.insert old fresh
  return renames

/-- File preparation shares the normalized rows used by each slice. A
declaration identity is distinguished within its module and name. Canonical
symbol numbers on module interfaces require the symbol's physical identity. -/
structure DeclarationSites where
  rows : Std.HashMap Json Json
  physicalIds : Std.HashMap Json Json
  symbols : Array Json
  localNames : Std.HashMap String String

def DeclarationSites.of (ast : Json) : DeclarationSites := Id.run do
  let symbols := (Fragment.symbolIdentities [ast]).eraseDups.toArray
  let ast := ast.setObjVal! "modules" (.arr #[])
  let doc := ast.getObjValD "declarations"
  let rows := fun k => (doc.getObjValAs? (Array Json) k).toOption.getD #[]
  let key := fun (id : Json) => (id.getObjValD "module", id.getObjValD "name")
  let span := fun (id : Json) => (id.getObjValAs? (Nat × Nat) "span").toOption.getD (0,0)
  let ordered := (identities ast (.ofArray symbols)).toArray.qsort (fun a b => (span a).1 < (span b).1 || ((span a).1 == (span b).1 && (span a).2 < (span b).2))
  let multiplicities := ordered.foldl (fun (m : Std.HashMap (Json × Json) Nat) id =>
    m.insert (key id) (m.getD (key id) 0 + 1)) {}
  let mut counts : Std.HashMap (Json × Json) Nat := {}
  let mut relative := {}
  let mut physical := {}
  for id in ordered do
    let k := key id
    let i := counts.getD k 0 + 1
    counts := counts.insert k i
    let named := Json.mkObj [("module", k.1), ("name", k.2)]
    -- Distinct declarations can share a spelling in the input document.
    -- Keep the ordinal only where lookup needs the distinction.
    let canonical := if span id == (0,0) then id
      else if multiplicities.getD k 0 == 1 then named
      else named.setObjVal! "occurrence" (toJson i)
    relative := relative.insert id canonical
    physical := physical.insert canonical id
  let subst := fun row => Id.run (mapSites (pure ∘ toJson) relative row)
  let mut replacements := relative
  let mut occurrences : Std.HashMap Json Nat := {}
  for k in ["definitions", "values", "roots"] do
    for row in rows k do
      let binding := row.getObjVal? "binding"
      let body := if binding.isOk then row.setObjVal! "binding" .null else row
      let id := row.getObjValD "declaration"
      let ownerKey := toJson (k, relative.getD id id, (row.getObjValD "binding").getObjValD "local")
      let occurrence := occurrences.getD ownerKey 0
      occurrences := occurrences.insert ownerKey (occurrence + 1)
      let normalized := nameTypeSites (toJson (ownerKey, occurrence)) relative body
      let normalized := if let .ok b := binding then normalized.setObjVal! "binding" b else normalized
      replacements := replacements.insert row normalized
  let mut locals := {}
  for fn in (ast.getObjValAs? (Array Json) "functions").toOption.getD #[] do
    let body := subst fn
    let renames := localRenames body
    replacements := replacements.insert fn (if renames.isEmpty then body else renameStrings renames body)
    let owner := fn.getObjValD "name"
    for (old, named) in renames do
      locals := locals.insert old (toJson (owner, named)).compress
    let signature := fn.setObjVal! "body" (.arr #[])
    replacements := replacements.insert signature (subst signature)
  for row in (ast.getObjValAs? (Array Json) "init").toOption.getD #[] do
    replacements := replacements.insert row (subst row)
  return ⟨replacements, physical, symbols, locals⟩

def Slice.relative (s : Slice) (decls : DeclarationSites) : Except String (Slice × Sites) := do
  let replace := fun (doc : Json) (k : String) =>
    doc.setObjVal! k (.arr (((doc.getObjValAs? (Array Json) k).toOption.getD #[]).map fun row =>
      decls.rows.getD row row))
  let doc := ["values","definitions","roots"].foldl replace (s.ast.getObjValD "declarations")
  let ast := replace s.ast "functions"
  let ast := if s.bindings.isSome then
      ast.setObjVal! "init" (Id.run (mapSites (pure ∘ toJson) decls.rows (ast.getObjValD "init")))
    else replace ast "init"
  let ast := ast.setObjVal! "declarations" doc
  -- The file worker has resolved document indices to interface numbers. Give
  -- symbols reached by this group local indices and carry their declarations.
  let symbols := decls.symbols
  let mut sitesSymbols := #[]
  let mut tables := s.tables
  let mut imports := s.imports
  let mut established := s.established
  -- Several exported declarations can depend on the same provider unit.
  -- Name that unit by the least reached declaration that refers to it.
  let mut providerNames : Std.HashMap String String := {}
  for (key, _, wire) in established do
    let ref := "module:" ++ (toJson key).compress
    providerNames := providerNames.insert wire (min ref (providerNames.getD wire ref))
  let moduleUnits := Std.HashMap.ofList (providerNames.toList.map Prod.swap)
  let provider := fun wire => providerNames.getD wire wire
  established := established.map fun (key, q, wire) => (key, q, provider wire)
  imports := imports.map fun r => {r with depends := r.depends.map fun (n, ds) => (n, ds.map provider)}
  let mut bindings := s.bindings.map fun env => {env with
    origins := env.origins.map (·.map fun id => decls.rows.getD id id) }
  let mut numbered := ast
  if !symbols.isEmpty then
    let without := ast.setObjVal! "declarations" (doc.setObjVal! "symbols" (.arr #[]))
    let fields := importFields imports established []
    let rowInputs := tables.map fun (n,t) => (n,t,t.rows.map toJson,SourceClaimJson.builtinsWire t.builtins)
    let scan : Nat → StateM (Std.HashSet Nat) Nat := fun n => do modify (fun (seen : Std.HashSet Nat) => seen.insert n); pure n
    let scanInput := Json.arr #[without, Json.mkObj fields, toJson (rowInputs.map fun (_,_,rows,b) => (rows,b)),
      toJson (bindings.map (·.heads.map fun d => toJson d.body))]
    let used := ((symbolEdits scan scanInput).run {}).2
    let reached := (symbols.filter (fun id => used.contains (symbolNumber id))).map fun id =>
      (decls.rows.getD id id, symbolNumber id)
    let reached := reached.qsort (fun a b => a.1.compress < b.1.compress)
    sitesSymbols := reached.map Prod.snd
    let numbers := Std.HashMap.ofList sitesSymbols.toList.zipIdx
    let number := fun n => numbers.getD n n
    let rename := fun j => Id.run (mapSymbols (pure ∘ number) j)
    numbered := rename without
    numbered := numbered.setObjVal! "declarations" ((numbered.getObjValD "declarations").setObjVal! "symbols"
      (.arr (reached.map Prod.fst)))
    let key : PropKey → PropKey := fun | .sym i => .sym (number i) | k => k
    let effect := fun (q : QualifiedEffect) =>
      ({q.1 with regions := q.1.regions.map fun r => {r with key := r.key.map key}}, q.2)
    imports := imports.map fun r => {r with qualified := r.qualified.map fun (n,q) => (n, effect q)}
    established := established.map fun (n,q,id) => (n, effect q, id)
    bindings ← bindings.mapM fun env => do
      let heads ← env.heads.mapM fun d => do
        let body ← d.body.mapM fun row => do
          match Id.run (symbolEdits (pure ∘ number) (toJson row)) with
          | none => pure row
          | some changed => fromJson? changed
        return {d with body}
      return {env with heads}
    tables ← rowInputs.mapM fun (n,t,wire,_) => do
      let mut rows := t.rows
      for h : i in [:wire.size] do
        if let some changed := Id.run (symbolEdits (pure ∘ number) wire[i]) then
          rows := rows.set! i (← fromJson? changed)
      let builtins := t.builtins.map fun b => {b with keys := b.keys.map key}
      return (n, {t with rows, builtins})
  let (ast, sites, force) := nameExecutableSites numbered s.force
  let functions := (ast.getObjValAs? (List Json) "functions").toOption.getD []
  let ordered := functions.mergeSort fun a b =>
    (a.getObjValAs? String "name").toOption.getD "" ≤ (b.getObjValAs? String "name").toOption.getD ""
  let ast := ast.setObjVal! "functions" (toJson ordered)
  let sites := { sites with declarations := decls.physicalIds, symbols := sitesSymbols, moduleUnits }
  let ast := ast.setObjVal! "file" "group.ts" |>.setObjVal! "sourceSha256" (toJson (String.ofList (List.replicate 64 '0')))
  let definitions := (s.missing.definitions.map fun id => decls.rows.getD id id).mergeSort (fun a b => a.compress ≤ b.compress)
  let names := fun (ns : List String) => (ns.map fun n => decls.localNames.getD n n).mergeSort
  let missing := { s.missing with definitions, roots := names s.missing.roots, values := names s.missing.values }
  return ({ s with ast, force, tables, imports, established, missing, bindings }, sites)

/-- Splitting the functions by membership for diagnostics retains their
interleaving and every other input field, including errors and controls. -/
def Slice.fields (s : Slice) : List (String × Json) :=
  let ⟨externalGroups, dependencies, inheritedReturn, proposalOrder, resultConsumers, ast, members, owned, initOrder, demand, below, imports, est, tables, force, fuel, budget, counting, missing, bindings⟩ := s
  let fs := (ast.getObjValAs? (Array Json) "functions").toOption.getD #[]
  let (_, membership) := fs.foldl (fun (acc : Std.HashMap String Nat × Array Bool) f =>
    let name := (f.getObjValAs? String "name").toOption.getD ""
    let i := acc.1.getD name 0
    (acc.1.insert name (i+1), acc.2.push (members.contains (.declaration name i)))) ({}, #[])
  let parts := fs.zip membership
  [("bindings", toJson (bindings.map BindingEnvironment.wire)), ("missing", toJson missing), ("externalGroups", toJson externalGroups), ("dependencies", toJson dependencies), ("inheritedReturn", toJson inheritedReturn),
   ("members", toJson (parts.filterMap (fun (f,m) => if m then some f else none))), ("callees", toJson (parts.filterMap (fun (f,m) => if m then none else some f))),
   ("order", toJson membership), ("init", ast.getObjValD "init"),
   ("declarations", ast.getObjValD "declarations"), ("omittedMentions", ast.getObjValD "omittedMentions"),
   ("file", ast.getObjValD "file"), ("sourceSha256", ast.getObjValD "sourceSha256"),
   ("group", toJson members), ("owned", toJson owned), ("initOrder", toJson initOrder),
   ("demand", toJson demand), ("resultConsumers", toJson resultConsumers),
   ("proposalOrder", toJson proposalOrder), ("below", answersWire below),
   ("controls", toJson (force, fuel, budget.rounds, budget.select, budget.rerun, counting))] ++
   importFields imports est tables

end Verification.GroupProjection
