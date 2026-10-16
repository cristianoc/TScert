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

/-- Proposed current property-read results, field by field. Optional fields
include the absent-key result. A point that names no record carries none. -/
abbrev CurrentFields (ι : Type) := List (PropKey × List ι)

structure Binding (ι : Type) where
  name : String
  type : ClaimType ι
  current : Option (CurrentFields ι) := none
  deriving ToJson, FromJson
structure Entry (ι : Type) where
  point : String
  start : Nat
  bindings : List (Binding ι)
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
  /-- Omitted by a document whose closures each advertise one signature. -/
  arrows : Option (List (ArrowClaims ι)) := none
  deriving FromJson

/-- Absence asserts nothing: a document whose closures each advertise one
signature states no per-arrow claims, and no producer writes an empty list. -/
instance [ToJson ι] : ToJson (Function ι) where
  toJson f := Json.mkObj ([("name", toJson f.name), ("namePos", toJson f.namePos),
    ("params", toJson f.params), ("result", toJson f.result),
    ("entries", toJson f.entries), ("expressions", toJson f.expressions),
    ("contracts", toJson f.contracts)] ++
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
    exprCurrent := expressions.filterMap (fun e => e.current.map (e.pos,·)) }

private def pointTable (entries : List (Entry ι)) (expressions : List (Expression ι)) :
    List (String × SourceClaims.PointData ι) :=
  (entries.map (·.point) ++ expressions.map (·.point)).eraseDups.map fun id =>
    (id, pointData (entries.filter (·.point == id)) (expressions.filter (·.point == id)))

private def storageContracts (contracts : List (StorageContract ι)) : SourceClaims.Contracts ι :=
  contracts.map fun c => ((c.pos,c.name),c.type.ground)

def Function.normalized (f : Function ι) : SourceClaims.Function ι :=
  let sites := pointData f.entries f.expressions
  { name := f.name, namePos := f.namePos, params := f.params.map (fun b => (b.name,b.type.ground))
    ret := f.result.ground, envs := sites.envs, exprs := sites.exprs
    entryCurrent := sites.entryCurrent, exprCurrent := sites.exprCurrent
    points := pointTable f.entries f.expressions, contracts := storageContracts f.contracts
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
/-- Every asserted field is one the point's own record contract names, each at
most once, at a type this table has. The asserted type need not be finite: a
field the extractor cannot turn into a literal assertion becomes an obligation
that the storage contract already implies it. -/
private def validCurrent (T : EquationStore.State) (A : ClaimType Tree) (current : Option (CurrentFields Tree)) : Bool :=
  match current with
  | none => true
  | some fs =>
    !fs.isEmpty && (fs.map Prod.fst).eraseDups.length == fs.length &&
    -- Every record arm names the field, required or optional.
    (match PositiveRules.expand (SourceTypes.graph T) (A.ground.toOption.getD []) with
      | [] => false
      | cs => cs.all fun
        | .refs contract [] vs os _ _ => fs.all (fun p => (contract.lookup p.1).isSome ||
            (vs.lookup p.1).isSome || os.any (fun o => o.key == p.1))
        | _ => false) &&
    fs.all (fun p => validType T (.labels p.2))
private def validBindings (T : EquationStore.State) (bs : List (Binding Tree)) : Bool :=
  (bs.map (·.name)).eraseDups.length == bs.length &&
    bs.all (fun b => !b.name.isEmpty && validType T b.type && validCurrent T b.type b.current)
private def validSpan (p : Span) : Bool := p.1 < p.2
private def validInterior (T : EquationStore.State) (entries : List (Entry Tree))
    (expressions : List (Expression Tree)) : Bool :=
  (entries.map (fun e => (e.point,e.start))).eraseDups.length == entries.length &&
  (expressions.map (fun e => (e.point,e.pos))).eraseDups.length == expressions.length &&
  entries.all (fun e => validBindings T e.bindings) &&
  expressions.all (fun e => validSpan e.pos && validType T e.type && validCurrent T e.type e.current &&
    e.instantiate.all (fun is => (is.map (·.name)).eraseDups.length == is.length &&
      is.all (fun i => !i.name.isEmpty && validType T i.type)))
private def validContracts (T : EquationStore.State) (cs : List (StorageContract Tree)) : Bool :=
  (cs.map (fun c => (c.pos,c.name))).eraseDups.length == cs.length &&
  cs.all (fun c => validSpan c.pos && !c.name.isEmpty && validType T c.type)
private def validFunction (T : EquationStore.State) (f : Function Tree) : Bool :=
  !f.name.isEmpty && validSpan f.namePos && validBindings T f.params &&
  f.params.all (fun b => b.current.isNone) && validType T f.result &&
  validInterior T f.entries f.expressions && validContracts T f.contracts &&
  let arrows := f.arrows.getD []
  (arrows.map (·.pos)).eraseDups.length == arrows.length &&
  arrows.all (fun a => validSpan a.pos && !a.rows.isEmpty && a.rows.all (fun row =>
    validInterior T row.entries row.expressions && validContracts T row.contracts &&
    -- These are ground overload rows. Quantified eliminations are checked by
    -- the scheme gate, never silently discarded during ground normalization.
    row.expressions.all (fun e => e.instantiate.isNone)))

/-- The claims document over a store: its label lists already the store's
labels. Unknown and missing fields are refused, and every label is one the
store holds. -/
def decodeDocument (T : EquationStore.State) (claims : Json) : Except String (Document EquationStore.State Tree) := do
  fieldsExactly claims (["file", "sourceSha256", "types", "functions"] ++
    if (claims.getObjVal? "init").isOk then ["init"] else [])
  let functions : List (Function Tree) ← decodeStrict (← jField claims "functions")
  let init : Option (InitClaims Tree) ← match claims.getObjVal? "init" with
    | .ok j => some <$> decodeStrict j
    | .error _ => pure none
  let d : Document EquationStore.State Tree := ⟨← jStr (← jField claims "file"), ← jStr (← jField claims "sourceSha256"),
    T, functions, init⟩
  if d.sourceSha256.length != 64 || !d.sourceSha256.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    throw "invalid source fingerprint"
  if !d.functions.all (validFunction d.types) then
    throw "invalid source claims: duplicate identity, span, binding or type labels"
  if (d.functions.map (fun f => (f.name,f.namePos))).eraseDups.length != d.functions.length then
    throw "duplicate function claims"
  if let some i := d.init then
    if !validInterior d.types i.entries i.expressions || !validContracts d.types i.contracts then
      throw "invalid source claims: duplicate identity, span, binding or type labels"
  return d


end

end Verification.SourceClaimJson
