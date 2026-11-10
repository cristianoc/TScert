import Verification.Source.SourceClaims
import Verification.Source.SourceRequests
import Verification.Source.Equations.Store

/-! Strict producer-independent claims documents. A document carries its producer's
rows, which its row labels index, and label trees name what only the verifier
lowers: declarations' applications, intersections, arrays and binders
(SOURCE-CLAIMS, "Encoding"). The verifier lowers the document with the
source's declarations to recursive equations (RECURSIVE-EQUATIONS §8), and a
checked request is over those equations' graph. The external parser
supplies the source fingerprint; this module checks agreement, not hashing or
the parser's semantic correctness. Saved statuses are not part of the
schema. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)
/-- A rigid name refers to the enclosing source function's binder. It is never
interpreted as a ground graph label or replaced with its upper bound. -/
inductive ClaimType (ι : Type) where
  | labels : List ι → ClaimType ι
  | union : List (ClaimType ι) → ClaimType ι
  | param : String → ClaimType ι
  | array : ClaimType ι → ClaimType ι
  /-- Binders, receiver, parameters, rest element and result. -/
  | scheme : List (ResolutionWire.Binder (ClaimType ι)) → ClaimType ι → List (ClaimType ι) → Option (ClaimType ι) →
      ClaimType ι → CallEffects.Effect → ClaimType ι
  | unavailable : String → ClaimType ι
  deriving Repr, BEq, Inhabited
instance : Coe (List ι) (ClaimType ι) := ⟨ClaimType.labels⟩

private partial def ClaimType.toJson [ToJson ι] : ClaimType ι → Json
  | .labels A => Lean.toJson A
  | .union ts => Json.mkObj [("union", Lean.toJson (ts.map ClaimType.toJson))]
  | .array e => Json.mkObj [("array", e.toJson)]
  | .param name => Json.mkObj [("param", Lean.toJson name)]
  | .scheme typeParams receiver params rest result effect => Json.mkObj [("scheme", Json.mkObj [
      ("typeParams", Lean.toJson (typeParams.map fun p => Json.mkObj [
        ("name", Lean.toJson p.name), ("bound", p.bound.map ClaimType.toJson |>.getD Json.null),
        ("resolution", Lean.toJson p.resolution)])),
      ("this", ClaimType.toJson receiver),
      ("params", Lean.toJson (params.map ClaimType.toJson)),
      ("rest", rest.map ClaimType.toJson |>.getD Json.null),
      ("result", ClaimType.toJson result), ("effect", Lean.toJson effect)])]
  | .unavailable reason => Json.mkObj [("unavailable", Lean.toJson reason)]

instance [ToJson ι] : ToJson (ClaimType ι) where
  toJson := ClaimType.toJson

private partial def ClaimType.fromJson [FromJson ι] (j : Json) : Except String (ClaimType ι) :=
  match j with
  | .arr _ => ClaimType.labels <$> Lean.fromJson? j
  | _ => do
    if let .ok reason := j.getObjValAs? String "unavailable" then
      if j != Json.mkObj [("unavailable", Lean.toJson reason)] || reason.isEmpty then
        throw "invalid unavailable claim"
      return .unavailable reason
    if let .ok _ := j.getObjVal? "union" then
      fieldsExactly j ["union"]
      return .union (← (← jArr j "union").mapM ClaimType.fromJson)
    if let .ok e := j.getObjVal? "array" then
      fieldsExactly j ["array"]
      return .array (← ClaimType.fromJson e)
    if let .ok s := j.getObjVal? "scheme" then
      fieldsExactly j ["scheme"]
      fieldsExactly s ["typeParams", "this", "params", "rest", "result", "effect"]
      let typeParams ← (← jArr s "typeParams").mapM fun p => do
        fieldsExactly p ["name", "bound", "resolution"]
        let name ← jStr (← jField p "name")
        let bound ← jField p "bound"
        let bound ← if bound == .null then pure none else do
          pure (some (← ClaimType.fromJson bound))
        let rawResolution ← jField p "resolution"
        let resolution ← if rawResolution == .null then pure none else some <$> fromJson? rawResolution
        return (⟨name, bound, resolution⟩ : ResolutionWire.Binder (ClaimType ι))
      ResolutionWire.validateOwnership (typeParams.map fun p => (p.name, p.resolution))
      let receiver ← ClaimType.fromJson (← jField s "this")
      let params ← (← jArr s "params").mapM ClaimType.fromJson
      let rest ← jField s "rest"
      let rest ← if rest == .null then pure none else some <$> ClaimType.fromJson rest
      return .scheme typeParams receiver params rest (← ClaimType.fromJson (← jField s "result"))
        (← Lean.fromJson? (← jField s "effect"))
    let name ← jStr (← jField j "param")
    if j != Json.mkObj [("param", Lean.toJson name)] || name.isEmpty then
      throw "invalid rigid parameter claim"
    return .param name

instance [FromJson ι] : FromJson (ClaimType ι) where
  fromJson? := ClaimType.fromJson
partial def ClaimType.ground [Labels ι] : ClaimType ι → Except String (Ty ι)
  | .union ts => do
      let arms ← ts.mapM ClaimType.ground
      return (arms.flatten.eraseDups.mergeSort Labels.le)
  | .labels A => .ok A
  | .array _ => .error "array over a rigid parameter requires scheme checking"
  | .param _ => .error "rigid parameter outside generic function"
  | .scheme .. => .error "quantified callable requires scheme checking"
  | .unavailable reason => .error reason

/-- Proposed current property-read results, path by path: a nonempty list
of fields read in turn from the point's value. Optional fields include the
absent-key result. A point that names no record carries none. A path of two
fields or more is a statement entry's witness of a member path
(HOST-FAMILIES.md, "Entries"). -/
abbrev CurrentFields (ι : Type) := List (List PropKey × List ι)

structure Binding (ι : Type) where
  name : String
  type : ClaimType ι
  current : Option (CurrentFields ι) := none
  deriving ToJson, FromJson
/-- A bound at a statement entry: the binding `index` holds an array index at
most the length of the array the binding `array` holds, below it where
`strict`. -/
structure Bound where
  array : String
  index : String
  strict : Bool
  deriving ToJson, FromJson
/-- A term of a linear fact the producer proposes: what the binding `name`
holds, its named data fields `path` read from it in turn, read as `term` says
(`HeapKnowledge.Term.Kind`): the safe integer it is, the length of its array
store, or the length of its typed array; with an integer
coefficient. -/
structure FactTerm where
  name : String
  path : List String
  term : HeapKnowledge.Term.Kind
  coefficient : Int
  deriving ToJson, FromJson
/-- A guard of a fact the producer proposes (ARITHMETIC.md, "Guarded
clauses"): the named data fields `path` read from what the binding `name`
holds give the value `tag` names, or the guarded fact holds. -/
structure FactGuard where
  name : String
  path : List String
  tag : HeapKnowledge.GuardTag
  deriving ToJson, FromJson
/-- A linear fact the producer proposes at a statement entry: where none of
its guards, in order, reads its tag's value, the sum of the terms is at most
`bound`; every term denotes an integer. -/
structure LinearFactClaim where
  guards : List FactGuard
  terms : List FactTerm
  bound : Int
  deriving ToJson, FromJson
inductive Fact where
  | linear (fact : LinearFactClaim)
  | either (left right : Fact)

partial def Fact.fromJson (j : Json) : Except String Fact := do
  if let .ok e := j.getObjVal? "either" then
    fieldsExactly j ["either"]
    fieldsExactly e ["left", "right"]
    return .either (← Fact.fromJson (← jField e "left")) (← Fact.fromJson (← jField e "right"))
  fieldsExactly j ["guards", "terms", "bound"]
  return .linear (← Lean.fromJson? j)

instance : FromJson Fact := ⟨Fact.fromJson⟩

def Fact.toJson : Fact → Json
  | .linear f => Lean.toJson f
  | .either left right => Json.mkObj [("either", Json.mkObj [("left", left.toJson), ("right", right.toJson)])]
instance : ToJson Fact := ⟨Fact.toJson⟩

def Fact.claim : Fact → SourceClaims.ClauseClaim
  | .linear f => .linear (f.guards.map fun g => (g.name, g.path, g.tag))
      (f.terms.map fun t => (t.name, t.path, t.term, t.coefficient)) f.bound
  | .either left right => .either left.claim right.claim

/-- A term a proposed quantified fact names: what the binding `name` holds,
its named data fields `path` read from it in turn, read as `term` says. -/
structure TermRef where
  name : String
  path : List String
  term : HeapKnowledge.Term.Kind
  deriving ToJson, FromJson
/-- A variable of a quantified fact's body: `"index"`, `"elem"`, or
`{"term": TermRef}` (ARITHMETIC.md, "Quantified clauses"). -/
inductive BodyVariable where
  | index
  | elem
  | offset (delta : Nat)
  | project (kind : HeapKnowledge.Term.Kind) (path : List String)
  | term (ref : TermRef)
  deriving ToJson, FromJson
/-- A fact of a quantified fact's body: the sum of the terms is at most `bound`. -/
structure LinearBodyFact where
  terms : List (BodyVariable × Int)
  bound : Int
  deriving ToJson, FromJson
inductive BodyFact where
  | linear (fact : LinearBodyFact)
  | either (left right : BodyFact)

private def bodyFactJson : BodyFact → Json
  | .linear f => toJson f
  | .either A B => Json.mkObj [("either", Json.mkObj [("left", bodyFactJson A), ("right", bodyFactJson B)])]

instance : ToJson BodyFact := ⟨bodyFactJson⟩

private partial def bodyFactOf (j : Json) : Except String BodyFact := do
  let f ← match j.getObjVal? "either" with
    | .ok b => do pure (.either (← bodyFactOf (← b.getObjVal? "left")) (← bodyFactOf (← b.getObjVal? "right")))
    | .error _ => BodyFact.linear <$> fromJson? j
  if toJson f != j then throw "a body fact has exactly its constructor's fields"
  pure f

instance : FromJson BodyFact := ⟨bodyFactOf⟩

private def BodyFact.claim : BodyFact → SourceClaims.BodyClaim
  | .linear b => .linear (b.terms.map fun (v,c) => ((match v with
      | .index => .index
      | .elem => .elem
      | .offset d => .offset d
      | .project k p => .project k p
      | .term r => .term r.name r.path r.term : SourceClaims.BodyRef), c)) b.bound
  | .either A B => .either A.claim B.claim

/-- A quantified fact the producer proposes at a statement entry: for every
index below `stop` of the array the path `path` reads from what the binding
`name` holds, each body fact holds. -/
structure Quantified where
  name : String
  path : List String
  stop : TermRef
  body : List BodyFact
  deriving ToJson, FromJson
/-- A region fact the producer proposes at a statement entry: the regions of
the arrays the value bindings `name` and `other` hold share no location
(FOOTPRINTS.md, "Element regions"). -/
structure Apart where
  name : String
  other : String
  deriving ToJson, FromJson
/-- A store separation the producer proposes at a statement entry: where
none of its guards, in order, reads its tag's value ("Guarded clauses"), the
arrays the paths `path` and `otherPath` read from what the value bindings
`name` and `other` hold have different stores (ARITHMETIC.md, "Store
separation"). -/
structure StoresApart where
  guards : List FactGuard
  name : String
  path : List String
  other : String
  otherPath : List String
  deriving ToJson, FromJson
structure Entry (ι : Type) where
  point : String
  start : Nat
  bindings : List (Binding ι)
  bounds : List Bound
  facts : List Fact
  quantified : List Quantified
  apart : List Apart
  storesApart : List StoresApart
  deriving ToJson, FromJson
/-- The type arguments one call supplies for a scheme's binders. It is the
producer's proposed elimination, re-checked here; it is never itself evidence. -/
structure Instantiation (ι : Type) where
  name : String
  type : ClaimType ι
  resolution : Option ResolutionWire.Instance
  deriving ToJson, BEq

instance [FromJson ι] : FromJson (Instantiation ι) where
  fromJson? j := do
    fieldsExactly j ["name", "type", "resolution"]
    let name ← jStr (← jField j "name")
    if name.isEmpty then throw "empty instantiation binder"
    let rawResolution ← jField j "resolution"
    let resolution ← if rawResolution == .null then pure none else some <$> fromJson? rawResolution
    return ⟨name, ← fromJson? (← jField j "type"), resolution⟩

structure Expression (ι : Type) where
  point : String
  pos : Span
  type : ClaimType ι
  current : Option (CurrentFields ι) := none
  instantiate : Option (List (Instantiation ι)) := none
  deriving FromJson

/-- `current` is required and explicitly `null`, because silence about a
record's contents is itself an assertion. Absence of `instantiate` asserts
nothing: the site simply calls no quantified callable, so it is omitted rather
than stated, and no producer has to write it at every expression. -/
instance [ToJson ι] : ToJson (Expression ι) where
  toJson e := Json.mkObj ([("point", toJson e.point), ("pos", toJson e.pos), ("type", toJson e.type),
    ("current", toJson e.current)] ++
    (match e.instantiate with
     | none => []
     | some xs => [("instantiate", toJson xs)]))
/-- A proposed lifetime contract for one mutable declaration. -/
structure StorageContract (ι : Type) where
  pos : Span
  name : String
  type : ClaimType ι
  deriving ToJson, FromJson

/-- Interior claims for one closure, one set per signature of its claimed
callable type, in that order. A closure advertising several signatures has one
body and a different obligation at each: the producer states the claims that
body has under each, as scheme compilation states them under each checked
instantiation. -/
structure ArrowRow (ι : Type) where
  contracts : List (StorageContract ι)
  expressions : List (Expression ι)
  entries : List (Entry ι) := []
  deriving ToJson, FromJson
structure ArrowClaims (ι : Type) where
  pos : Span
  rows : List (ArrowRow ι)
  deriving ToJson, FromJson
structure Function (ι : Type) where
  name : String
  namePos : Span
  params : List (Binding ι)
  result : ClaimType ι
  entries : List (Entry ι)
  expressions : List (Expression ι)
  contracts : List (StorageContract ι)
  /-- The footprint the producer proposes for the declaration's signature,
  which the unit's graph must certify. Its annotation states none. -/
  footprint : Footprints.Closed
  /-- Whether the footprint is proposed on a throw too, which the unit's
  graph must certify as well. -/
  onThrow : Bool
  /-- The footprint the producer proposes for the signatures of the function
  the declaration returns, which the unit's returns must certify. -/
  resultFootprint : Footprints.Closed
  /-- Omitted by a document whose closures each advertise one signature. -/
  arrows : Option (List (ArrowClaims ι)) := none
  deriving FromJson

/-- Absence asserts nothing: a document whose closures each advertise one
signature states no per-arrow claims, and no producer writes an empty list. -/
instance [ToJson ι] : ToJson (Function ι) where
  toJson f := Json.mkObj ([("name", toJson f.name), ("namePos", toJson f.namePos),
    ("params", toJson f.params), ("result", toJson f.result),
    ("entries", toJson f.entries), ("expressions", toJson f.expressions),
    ("contracts", toJson f.contracts), ("footprint", toJson f.footprint), ("onThrow", toJson f.onThrow),
    ("resultFootprint", toJson f.resultFootprint)] ++
    (match f.arrows with
     | none | some [] => []
     | some rows => [("arrows", toJson rows)]))
/-- Claims for the module's initialization: the code unit that runs the
file's top-level code. It has no parameters, and completes with `undefined`. -/
structure InitClaims (ι : Type) where
  entries : List (Entry ι)
  expressions : List (Expression ι)
  contracts : List (StorageContract ι)
  arrows : Option (List (ArrowClaims ι)) := none
  deriving FromJson
instance [ToJson ι] : ToJson (InitClaims ι) where
  toJson i := Json.mkObj ([("entries", toJson i.entries), ("expressions", toJson i.expressions),
    ("contracts", toJson i.contracts)] ++
    (match i.arrows with
     | none | some [] => []
     | some rows => [("arrows", toJson rows)]))
/-- Whether no two of `xs` are equal (`xs.eraseDups.length == xs.length`),
decided in one pass. -/
private def allDistinct {α : Type} [BEq α] [Hashable α] (xs : List α) : Bool :=
  (xs.foldlM (init := ({} : Std.HashSet α)) fun (seen : Std.HashSet α) x =>
    if seen.contains x then none else some (seen.insert x)).isSome

/-- A document with every label a row: the wire's once `FiniteLayout.finite`
has given its label trees rows, or one whose producer names only rows. -/
structure Document (σ ι : Type) where
  file : String
  sourceSha256 : String
  types : σ
  functions : List (Function ι)
  /-- Present exactly when the source has module initialization code. -/
  init : Option (InitClaims ι) := none
  deriving FromJson

section
variable {ι : Type} [Labels ι]

private def pointData (entries : List (Entry ι)) (expressions : List (Expression ι)) :
    SourceClaims.PointData ι :=
  { envs := entries.map (fun e => (e.start,e.bindings.map (fun b => (b.name,b.type.ground))))
    exprs := expressions.map (fun e => (e.pos,e.type.ground))
    entryCurrent := entries.map (fun e => (e.start,e.bindings.filterMap fun b => b.current.map (b.name,·)))
    entryBounds := entries.map (fun e => (e.start,e.bounds.map fun b => (b.array, b.index, b.strict)))
    entryFacts := entries.map (fun e => (e.start,e.facts.map Fact.claim))
    entryEvery := entries.map (fun e => (e.start,e.quantified.map fun q =>
      ((q.name, q.path), (q.stop.name, q.stop.path, q.stop.term), q.body.map BodyFact.claim)))
    entryApart := entries.map (fun e => (e.start, e.apart.map fun r => (r.name, r.other)))
    entryStoresApart := entries.map (fun e => (e.start, e.storesApart.map fun r =>
      (r.guards.map fun g => (g.name, g.path, g.tag), (r.name, r.path), (r.other, r.otherPath))))
    -- An expression's assertion is of one field each (`validCurrent`).
    exprCurrent := expressions.filterMap (fun e => e.current.map fun fs =>
      (e.pos, fs.filterMap fun (p, A) => match p with | [k] => some (k, A) | _ => none)) }

/-- `xs` grouped by `point`, each group in order. -/
private def byPoint {α : Type} (xs : List α) (point : α → String) : Std.HashMap String (Array α) :=
  xs.foldl (init := {}) fun m x => m.insert (point x) ((m.getD (point x) #[]).push x)

/-- Each point's entries and expressions, in order, by the point's first
occurrence: `pointData` of `entries.filter (·.point == id)` and
`expressions.filter (·.point == id)` for each distinct `id`, grouped in one
pass. -/
private def pointTable (entries : List (Entry ι)) (expressions : List (Expression ι)) :
    List (String × SourceClaims.PointData ι) :=
  let ids := (entries.map (·.point) ++ expressions.map (·.point)).foldl (init := (({} : Std.HashSet String), #[]))
    fun (seen, out) id => if seen.contains id then (seen, out) else (seen.insert id, out.push id)
  let es := byPoint entries (·.point)
  let xs := byPoint expressions (·.point)
  ids.2.toList.map fun id => (id, pointData (es.getD id #[]).toList (xs.getD id #[]).toList)

private def storageContracts (contracts : List (StorageContract ι)) : SourceClaims.Contracts ι :=
  contracts.map fun c => ((c.pos,c.name),c.type.ground)

def Function.normalized (f : Function ι) : SourceClaims.Function ι :=
  let sites := pointData f.entries f.expressions
  { name := f.name, namePos := f.namePos, params := f.params.map (fun b => (b.name,b.type.ground))
    ret := f.result.ground, envs := sites.envs, exprs := sites.exprs
    entryCurrent := sites.entryCurrent, exprCurrent := sites.exprCurrent, entryBounds := sites.entryBounds
    entryFacts := sites.entryFacts
    entryEvery := sites.entryEvery
    entryApart := sites.entryApart
    entryStoresApart := sites.entryStoresApart
    points := pointTable f.entries f.expressions, contracts := storageContracts f.contracts
    footprint := f.footprint
    onThrow := f.onThrow
    resultFootprint := f.resultFootprint
    arrowClaims := (f.arrows.getD []).map fun a => (a.pos, a.rows.map fun row =>
      { toPointData := pointData row.entries row.expressions
        points := pointTable row.entries row.expressions
        contracts := storageContracts row.contracts }) }

private partial def validType (T : EquationStore.State) : ClaimType Tree → Bool
  | .union ts => !ts.isEmpty && ts.all (validType T)
  | .array e => validType T e
  | .param name => !name.isEmpty
  | .scheme typeParams receiver params rest result _effect =>
      -- With no binders of its own this is a callable that mentions an
      -- enclosing rigid parameter, such as a returned `() => T`.
      (ResolutionWire.validateOwnership (typeParams.map fun p => (p.name, p.resolution))).isOk &&
      typeParams.all (fun p => p.bound.all (validType T)) &&
      validType T receiver && params.all (validType T) && rest.all (validType T) &&
      validType T result
  | .unavailable reason => !reason.isEmpty
  | .labels A => validTy (StoreView.valid T) A && A == A.mergeSort Labels.le && A.eraseDups == A
/-- Every asserted path is nonempty and asserted at most once, its first
field one the point's own record contract names, at a type this table has.
A path of two fields or more only at a statement entry (`paths`), whose
lowering reads its later fields. The asserted type need not be finite: a
field the extractor cannot turn into a literal assertion becomes an obligation
that the storage contract already implies it. -/
private def validCurrent (T : EquationStore.State) (A : ClaimType Tree) (current : Option (CurrentFields Tree))
    (paths : Bool := false) : Bool :=
  match current with
  | none => true
  | some fs =>
    !fs.isEmpty && allDistinct (fs.map Prod.fst) &&
    fs.all (fun p => !p.1.isEmpty && (paths || p.1.length == 1)) &&
    -- Every record arm names the first field, required or optional, or is a
    -- dictionary whose string index reaches it.
    let firsts := fs.filterMap (·.1.head?)
    (match PositiveRules.expand (SourceTypes.graph T) (A.ground.toOption.getD []) with
      | [] => false
      | cs => cs.all fun
        | .refs contract [] vs os _ _ _ => firsts.all (fun k => (contract.lookup k).isSome ||
            (vs.lookup k).isSome || os.any (fun o => o.key == k))
        | .dict _ _ _ ds _ _ _ cells _ => firsts.all (fun k => (ds ++ cells).any (HeapExpressionRules.stringIndex · k))
        | _ => false) &&
    fs.all (fun p => validType T (.labels p.2))
private def validBindings (T : EquationStore.State) (bs : List (Binding Tree)) : Bool :=
  allDistinct (bs.map (·.name)) &&
    bs.all (fun b => !b.name.isEmpty && validType T b.type && validCurrent T b.type b.current (paths := true))
private def validSpan (p : Span) : Bool := p.1 < p.2
private def validInterior (T : EquationStore.State) (entries : List (Entry Tree))
    (expressions : List (Expression Tree)) : Bool :=
  allDistinct (entries.map (fun e => (e.point,e.start))) &&
  allDistinct (expressions.map (fun e => (e.point,e.pos))) &&
  entries.all (fun e => validBindings T e.bindings) &&
  expressions.all (fun e => validSpan e.pos && validType T e.type && validCurrent T e.type e.current &&
    e.instantiate.all (fun is => allDistinct (is.map (·.name)) &&
      is.all (fun i => !i.name.isEmpty && validType T i.type)))
private def validContracts (T : EquationStore.State) (cs : List (StorageContract Tree)) : Bool :=
  allDistinct (cs.map (fun c => (c.pos,c.name))) &&
  cs.all (fun c => validSpan c.pos && !c.name.isEmpty && validType T c.type)
private def validFunction (T : EquationStore.State) (f : Function Tree) : Bool :=
  !f.name.isEmpty && validSpan f.namePos && validBindings T f.params &&
  f.params.all (fun b => b.current.isNone) && validType T f.result &&
  validInterior T f.entries f.expressions && validContracts T f.contracts &&
  let arrows := f.arrows.getD []
  allDistinct (arrows.map (·.pos)) &&
  arrows.all (fun a => validSpan a.pos && !a.rows.isEmpty && a.rows.all (fun row =>
    validInterior T row.entries row.expressions && validContracts T row.contracts &&
    -- These are ground overload rows. Quantified eliminations are checked by
    -- the scheme gate, never silently discarded during ground normalization.
    row.expressions.all (fun e => e.instantiate.isNone)))

/-- The claims document over a store: its label lists already the store's
labels. Unknown and missing fields are refused, and every label is one the
store holds. -/
def decodeDocument (T : EquationStore.State) (claims : Json) : Except String (Document EquationStore.State Tree) := do
  fieldsExactly claims (["file", "sourceSha256", "types", "functions", "modules", "qualified"] ++
    if (claims.getObjVal? "init").isOk then ["init"] else [])
  -- A module's claims and the qualified reads are read by `planImports`;
  -- a document checked here has its modules' read apart.
  if !(← jArr claims "modules").isEmpty then throw "a document's module claims are read apart from it"
  let _ ← jArr claims "qualified"
  let functions : List (Function Tree) ← decodeStrict "claims.functions" (← jField claims "functions")
  let init : Option (InitClaims Tree) ← match claims.getObjVal? "init" with
    | .ok j => some <$> decodeStrict "claims.init" j
    | .error _ => pure none
  let d : Document EquationStore.State Tree := ⟨← jStr (← jField claims "file"), ← jStr (← jField claims "sourceSha256"),
    T, functions, init⟩
  if d.sourceSha256.length != 64 || !d.sourceSha256.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    throw "invalid source fingerprint"
  -- A statement entry's current contents name a field of every record arm
  -- of the binding's type: the first such claim that does not is located.
  for f in d.functions do
    for e in f.entries do
      for b in e.bindings do
        if validType d.types b.type && !validCurrent d.types b.type b.current (paths := true) then
          throw s!"invalid source claims: invalid current-contents field of '{b.name}' at the entry at {e.start}: a field some arm of its type does not name, or an invalid path"
  if !d.functions.all (validFunction d.types) then
    throw "invalid source claims: duplicate identity, span, binding or type labels"
  if !allDistinct (d.functions.map (fun f => (f.name,f.namePos))) then
    throw "duplicate function claims"
  if let some i := d.init then
    if !validInterior d.types i.entries i.expressions || !validContracts d.types i.contracts then
      throw "invalid source claims: duplicate identity, span, binding or type labels"
  return d


end

end Verification.SourceClaimJson
