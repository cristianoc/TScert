import Lean.Data.Json
import Verification.Types.Claim
import Verification.Types.GraphRows
import Verification.Programs.Parametricity
import Verification.Programs.GraphCode
import Verification.Source.LabelStore
import Verification.Source.EffectJson

/-! In-memory JSON boundary for the stateful consumer: a unit's request, over
the labels of a store, and its evidence, as separate inputs. No unsupported
type is approximated. `decodeStrict` requires every field and rejects any
other, so a document either has the current shape or is refused. -/
namespace Verification.RequestJson
open Lean ProgramTyping PositiveNormalization PositiveGraphs PositiveRules
open ProgramCertificates PointClaims ControlFlow CertificateProducer
open CallEffects (Arrow RestArrow Contract Effect)
open LabelStore

deriving instance ToJson, FromJson for Tag
deriving instance ToJson, FromJson for Arith
deriving instance ToJson, FromJson for Invoke
deriving instance ToJson, FromJson for Target
deriving instance ToJson, FromJson for Continuation
deriving instance ToJson, FromJson for Tm, CallCode

/-- A code's kind is left out of its JSON when it is `call`, the kind of every
arrow and method, and graph code's rest when it collects none: that is the one
spelling of each, so strict decoding, which re-encodes and compares, refuses an
explicit `"call"` or `false`, and a code without them reads with these defaults.
Code nests anywhere in a term, so the spelling applies at every depth. -/
private partial def codeDefaults (restore : Bool) : Json → Json
  | .arr xs => .arr (xs.map (codeDefaults restore))
  | .obj kvs => Json.mkObj (kvs.toArray.toList.map fun (k, v) =>
      let v := codeDefaults restore v
      let defaults : List (String × Json) := match k with
        | "graph" => [("kind", toJson Invoke.call), ("rest", toJson false)]
        | _ => []
      match v with
      | .obj fields =>
        (k, defaults.foldl (fun v (field, dflt) =>
          if restore then
            if fields.contains field then v else v.setObjVal! field dflt
          else if (v.getObjVal? field).toOption == some dflt then
            match v with
            | .obj fs => Json.mkObj (fs.toArray.toList.filter (·.1 != field))
            | v => v
          else v) v)
      | _ => (k, v))
  | j => j

private def derivedTmToJson : Tm → Json := toJson
private def derivedTmFromJson : Json → Except String Tm := fromJson?

instance (priority := high) : ToJson Tm := ⟨fun t => codeDefaults false (derivedTmToJson t)⟩
instance (priority := high) : FromJson Tm := ⟨fun j => derivedTmFromJson (codeDefaults true j)⟩
deriving instance ToJson, FromJson for ArrayPresence
deriving instance ToJson, FromJson for PositiveNormalization.Tuple
deriving instance ToJson, FromJson for Contract
deriving instance ToJson, FromJson for MethodMembers.Sig
deriving instance ToJson, FromJson for StorageRole

/-- A storage position, a field's or a writable index's, is the flat array
`[key, role, contents]`, the key a property key or an index's key class, the
role its constructor's name (`"field"`, `"cell"`, `"arrayStore"`,
`"viewStore"`). -/
instance (priority := high) {κ α : Type} [ToJson κ] [ToJson α] : ToJson (κ × StorageRole × α) :=
  ⟨fun p => .arr #[toJson p.1, toJson p.2.1, toJson p.2.2]⟩

instance (priority := high) {κ α : Type} [FromJson κ] [FromJson α] : FromJson (κ × StorageRole × α) :=
  ⟨fun j => do
    let xs ← j.getArr?
    let #[k, s, a] := xs | throw s!"expected [key, role, contents], got {j.compress}"
    pure (← fromJson? k, ← fromJson? s, ← fromJson? a)⟩

deriving instance ToJson, FromJson for OptionalField
deriving instance ToJson, FromJson for KeyBound
deriving instance ToJson, FromJson for IndexKeys
deriving instance ToJson, FromJson for Clause

/-- The clause fields that are left out of JSON when empty: a call clause's
variadic signatures, a class value's static fields, a record's optional
fields, methods, key bounds and stable keys, a callable object's methods, and
a dictionary's writable index contracts.
Absence is the one spelling of none, so strict decoding, which re-encodes and
compares, still refuses an explicit empty list, and a clause without them reads
as it always has. -/
private def omittedWhenEmpty : List (String × String) :=
  [("arrs", "variadic"), ("callable", "variadic"), ("callable", "methods"), ("ctors", "variadic"), ("ctors", "first"),
   ("ctors", "rest"), ("ctors", "views"), ("refs", "optional"),
   ("dict", "optional"), ("refs", "methods"), ("dict", "methods"), ("refs", "bounds"),
   ("dict", "bounds"), ("dict", "cells"), ("refs", "stable"), ("dict", "stable")]

private def withoutEmptyVariadic (j : Json) : Json :=
  omittedWhenEmpty.foldl (fun j (key, name) =>
    match j.getObjVal? key with
    | .ok body@(.obj _) =>
      match body.getObjVal? name with
      | .ok (.arr xs) =>
        if xs.isEmpty then
          let fields := match body.getObj? with
            | .ok kvs => kvs.toArray.toList.filter (·.1 != name)
            | .error _ => []
          j.setObjVal! key (Json.mkObj fields)
        else j
      | _ => j
    | _ => j) j

private def withEmptyVariadic (j : Json) : Json :=
  omittedWhenEmpty.foldl (fun j (key, name) =>
    match j.getObjVal? key with
    | .ok body@(.obj _) =>
      if (body.getObjVal? name).toOption.isSome then j
      else j.setObjVal! key (body.setObjVal! name (.arr #[]))
    | _ => j) j

private def derivedClauseToJson [ToJson α] : Clause α → Json := toJson
private def derivedClauseFromJson [FromJson α] : Json → Except String (Clause α) := fromJson?

instance (priority := high) [ToJson α] : ToJson (Clause α) :=
  ⟨fun c => withoutEmptyVariadic (derivedClauseToJson c)⟩
/-- A tag set's list is sorted, distinct and of at least two elements: its one
spelling (HOST-FAMILIES.md, "Tag sets"). -/
def canonicalSet [LT β] [DecidableRel (α := β) (· < ·)] (xs : List β) : Bool :=
  xs.length ≥ 2 && (xs.zip xs.tail).all fun (a, b) => decide (a < b)

instance (priority := high) [FromJson α] : FromJson (Clause α) :=
  ⟨fun j => do
    let c ← derivedClauseFromJson (withEmptyVariadic j)
    match c with
    | .numIn bs => unless canonicalSet bs do
        throw "a number set lists two or more bit patterns, sorted and distinct"
    | .strIn ss => unless canonicalSet ss do
        throw "a string set lists two or more strings, sorted and distinct"
    | _ => pure ()
    return c⟩
instance : ToJson ParameterKind := ⟨fun
  | .value => .str "value"
  | .arguments => .str "arguments"
  | .packed => .str "packed"⟩

instance : FromJson ParameterKind := ⟨fun j => do
  match ← j.getStr? with
  | "value" => return .value
  | "arguments" => return .arguments
  | "packed" => return .packed
  | _ => throw "expected parameter kind value, arguments or packed"⟩

/-- Resolution groups retain positions among the scheme's binders. -/
instance : ToJson ResolutionSlots := ⟨fun s => Json.mkObj [
  ("input", toJson s.input), ("observation", toJson s.observation), ("result", toJson s.result)]⟩

instance : FromJson ResolutionSlots := ⟨fun j => do
  fieldsExactly j ["input", "observation", "result"]
  return ⟨← fromJson? (← jField j "input"), ← fromJson? (← jField j "observation"),
    ← fromJson? (← jField j "result")⟩⟩

/-- A clause row is spelled as its array of clauses, as every row was before
scheme rows; a scheme row as
`{"scheme": {"binders", "signatures", "bounds", "variadic", "resolution"}}`,
its bounds, variadic signatures and resolution groups left out when empty, a parameter row as
`{"param": label, "name": name, "kind": "value" | "arguments"}`, and a meet
row as `{"meet": binder, "clauses": [...]}`, whatever the labels are. -/
instance [ToJson ι] [ToJson α] : ToJson (GraphRow ι α) := ⟨fun
  | .clauses cs => toJson cs
  | .scheme bs sigs bounds rests resolution construct => Json.mkObj [("scheme",
      Json.mkObj ([("binders", toJson bs), ("signatures", toJson sigs)] ++
        (if bounds.isEmpty then [] else [("bounds", toJson bounds)]) ++
        (if rests.isEmpty then [] else [("variadic", toJson rests)]) ++
        (if resolution.isEmpty then [] else [("resolution", toJson resolution)]) ++
        (if construct then [("construct", toJson true)] else [])))]
  | .param l n k => Json.mkObj [("param", toJson l), ("name", toJson n), ("kind", toJson k)]
  | .meet p cs ps => Json.mkObj ([("meet", toJson p), ("clauses", toJson cs)] ++
      (if ps.isEmpty then [] else [("also", toJson ps)]))⟩

instance [FromJson ι] [FromJson α] : FromJson (GraphRow ι α) := ⟨fun j =>
  match j with
  | .arr _ => GraphRow.clauses <$> fromJson? j
  | _ => match j.getObjVal? "scheme", j.getObjVal? "param", j.getObjVal? "meet" with
    | .error _, .error _, .ok p => do
      fieldsExactly j (["meet", "clauses"] ++ ["also"].filter (fun k => (j.getObjVal? k).isOk))
      return .meet (← fromJson? p) (← fromJson? (← j.getObjVal? "clauses"))
        (← match j.getObjVal? "also" with
          | .ok v => fromJson? v
          | .error _ => pure [])
    | .ok b, .error _, .error _ => do
      fieldsExactly j ["scheme"]
      let optional := ["bounds", "variadic", "resolution", "construct"].filter (fun k => (b.getObjVal? k).isOk)
      fieldsExactly b (["binders", "signatures"] ++ optional)
      return .scheme (← fromJson? (← b.getObjVal? "binders"))
        (← fromJson? (← b.getObjVal? "signatures"))
        (← match b.getObjVal? "bounds" with
          | .ok v => fromJson? v
          | .error _ => pure [])
        (← match b.getObjVal? "variadic" with
          | .ok v => fromJson? v
          | .error _ => pure [])
        (← match b.getObjVal? "resolution" with
          | .ok v => fromJson? v
          | .error _ => pure [])
        (← match b.getObjVal? "construct" with
          | .ok (.bool true) => pure true
          | .ok _ => throw "a scheme's construct field, when present, is true"
          | .error _ => pure false)
    | .error _, .ok l, .error _ => do
      fieldsExactly j ["param", "name", "kind"]
      return .param (← fromJson? l) (← fromJson? (← j.getObjVal? "name"))
        (← fromJson? (← j.getObjVal? "kind"))
    | _, _, _ => .error "expected a clause array, a scheme row, a parameter row or a meet row"⟩

/-- A diagnostic's `types` field, and its `names` field when there are any. -/
@[nospecialize] def _root_.Verification.LabelStore.Projection.fields {ι : Type} (p : Projection ι) :
    List (String × Json) :=
  ("types", toJson p.rows) :: (if p.names.isEmpty then [] else [("names", toJson p.names)])

/-! ### The built-in arrays -/

/-- A key a declaration may not name: one the model keeps for itself (the
array store, the prototype, every other name in double brackets), or one its
representation of keys moves (`escapedSpelling`), so that a declared key is
the key a computed one of the same spelling is. -/
def reservedKey : PropKey → Bool
  | .str s => escapedSpelling s.toList
  | .sym _ => false

/-- The keys an ordinary array cannot own: its prototype's declared keys,
`constructor`, `then` and `toJSON`. These preserve standard species
construction, the array's non-thenable contract during native promise
resolution, and `JSON.stringify`'s calling no hook of an array.
Sorted, each once, with the model's reserved keys aside. -/
def arrayExcludedKeys (ks : List PropKey) : List PropKey :=
  (((PropKey.str "constructor" :: PropKey.str "then" :: PropKey.str "toJSON" :: ks).filter fun k => !reservedKey k).eraseDups).mergeSort PropKey.before

/-- The excluded array keys: `constructor`, `then`, `toJSON` and the prototype row's fields', views', optional fields'
and methods', the reserved keys aside. -/
@[nospecialize] def arrayExcludedKeysOf : List (Clause (List ι)) → List PropKey
  | [.refs a bs vs os ms _ _] =>
    arrayExcludedKeys ((a :: bs).flatten.map (·.1) ++ vs.map (·.1) ++ os.map (·.key) ++ ms.map (·.key))
  | _ => arrayExcludedKeys []

deriving instance ToJson for Node
deriving instance ToJson, FromJson for PositiveCertificates.Instance
deriving instance ToJson, FromJson for PositiveCertificates.SubtypeChoices
deriving instance ToJson for Sequent
deriving instance ToJson, FromJson for Rule
deriving instance ToJson for ValueSets.Lit
deriving instance ToJson for ValueSets.Literal
deriving instance ToJson for ValueSets.ValueSet
deriving instance ToJson for HeapFacts.Fact
deriving instance ToJson for HeapLinks.Link
deriving instance ToJson for HeapSeparation.Fact
deriving instance ToJson for HeapSeparation.Separation
deriving instance ToJson for CallEffects.ElemPred
deriving instance ToJson for HeapKnowledge.ElemAtom
deriving instance ToJson, FromJson for HeapKnowledge.IndexAtom
deriving instance ToJson for HeapKnowledge.Knowledge
deriving instance ToJson, FromJson for PointClaim
deriving instance ToJson, FromJson for CodeEntry

/-- Graph code a request creates, at one signature it offers, with the point
claims of its graph, and whether its definition is async, as the source
states (`Fragment.Expr.lambda`). Nested code comes before the code creating
it. -/
structure CodeRequest (ι : Type) where
  entry : CodeEntry ι
  claims : List (PointClaim ι)
  async : Bool
  deriving ToJson, FromJson

/-- A request over a store `σ` of labels `ι`: its program, point claims,
result and inputs are typed by the store's labels. -/
structure Request (σ ι : Type) where
  types : σ
  program : Program
  claims : List (PointClaim ι)
  result : Ty ι
  start : Nat
  /-- External argument contract, in slot order; independent of point claims. -/
  inputs : List (Ty ι)
  /-- The graph code the program creates, each at each signature it offers. -/
  codes : List (CodeRequest ι) := []
  /-- A guard's promise about the input in a slot: whether an assertion
  function's, the slot, and the promise's type. -/
  promise : Option (Bool × Nat × Ty ι) := none
  /-- What the request assumes apart in its inputs, beside their types: a
  unit's module cells (SOURCE-ELABORATION.md, "Module cells"). The entry may
  know it, and the safety theorems assume it of the environment. -/
  entrySeparation : HeapSeparation.Separation := {}
  /-- The index facts the request assumes of its inputs: the
  precondition of the function it checks (ARITHMETIC.md, 
  "Preconditions"). The entry may know them, and the safety theorems assume
  them of the environment. -/
  entryIndices : List HeapKnowledge.IndexAtom := []

/-- What a request's returns establish: its result, or its promise. -/
def Request.goal {σ ι : Type} (r : Request σ ι) : ControlFlow.Goal ι :=
  match r.promise with
  | none => .plain r.result
  | some (false, slot, T) => .guards T slot
  | some (true, slot, T) => .asserts T slot

structure Response (ι : Type) where
  certificate : ControlFlow.Certificate ι
  /-- One certificate per code request, in its order. -/
  codes : List (ControlFlow.Certificate ι) := []
  /-- The request's read summaries, each checked once; a derivation node
  `readSummary` names one by its index. -/
  readSummaries : List (ReadSummary ι) := []

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

@[nospecialize] def graph (r : Request σ ι) : NormalGraph ι := StoreView.graph r.types

@[nospecialize] def validTy (ok : ι → Bool) (A : Ty ι) : Bool := A.all ok

/-- Use the clause language's operand traversal for boundary validation too. -/
@[nospecialize] def clauseTypes : Clause (Ty ι) → List (Ty ι) := Clause.operands

@[nospecialize] def validClaim (ok : ι → Bool) (c : PointClaim ι) : Bool :=
  (c.type :: c.context).all (validTy ok)

/-- The total Lean graph's out-of-range default must not become an accidental
meaning for an invalid serialized type reference. -/
@[nospecialize] def validRequest (r : Request σ ι) : Bool :=
  let ok := StoreView.valid r.types
  StoreView.wellFormed r.types &&
  r.claims.all (validClaim ok) && validTy ok r.result &&
  r.promise.all (fun (_, _, T) => validTy ok T) &&
  r.inputs.all (validTy ok) &&
  r.codes.all fun q => q.claims.all (validClaim ok) &&
    (q.entry.row.operands ++ q.entry.captures ++
      q.entry.store.toList).all
      (validTy ok)

@[nospecialize] def instanceTypes (c : PositiveCertificates.Instance ι) : List (Ty ι) :=
  c.domain :: c.instances ++ c.free.flatMap (fun p => [[p.1], p.2]) ++
    c.table.flatMap (fun e => [e.1] :: e.2.2 :: e.2.1.flatMap (fun p => [[p.1], p.2]))

@[nospecialize] def subtypeChoiceTypes (p : PositiveCertificates.SubtypeChoices ι) : List (Ty ι) :=
  p.instantiation.toList.flatMap instanceTypes ++ p.members.flatMap (fun k => k.1 ::
    k.2.1.flatMap Arrow.operands ++
    k.2.2.1.flatMap RestArrow.operands ++ instanceTypes k.2.2.2)

@[nospecialize] def validEvidence (ok : ι → Bool) : ProgramCertificates.Evidence ι → Bool
  | .node j r ps =>
    (j.type :: j.context).all (validTy ok) &&
    (match r with
      | .sub p => (subtypeChoiceTypes p).all (validTy ok)
      | .bindMember ps rs vs => (ps.all fun p =>
          (p.1.flatMap subtypeChoiceTypes ++ subtypeChoiceTypes p.2).all (validTy ok)) && (rs.all fun p =>
          (p.1.flatMap subtypeChoiceTypes ++ subtypeChoiceTypes p.2.1 ++ subtypeChoiceTypes p.2.2).all (validTy ok)) &&
          vs.all fun p => (subtypeChoiceTypes p).all (validTy ok)
      | .ifBoolVar T F => validTy ok T && validTy ok F
      | .funGraph As | .callableGraph As => As.all (validTy ok)
      | .ctorGraph U => validTy ok U
      | .callRest _ _ _ _ E => validTy ok E
      | .arrParts E _ => validTy ok E
      | .constructRest _ _ P => validTy ok P
      | .callPacked _ _ t P => validTy ok [t] && validTy ok P
      | .readProto P => validTy ok P
      | .elemOpt U | .elemAny U => validTy ok U
      | .elemStr T U => validTy ok T && validTy ok U
      | _ => true) &&
    ps.attach.all (fun p => validEvidence ok p.val)
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem p.property
  simp only [ProgramCertificates.Evidence.node.sizeOf_spec]
  omega

@[nospecialize] def validEffect (ok : ι → Bool) : HeapExpressionRules.StepEvidence ι → Bool
  | .ordinary e | .pure e | .reading e | .created e | .allocated e | .typedRead _ e | .written _ _ _ e =>
    validEvidence ok e
  | .slicedRead _ _ _ e p => validEvidence ok e && (subtypeChoiceTypes p).all (validTy ok)
  | .observedRead _ _ | .knownValue _ _ => true
  | .linkedRead _ _ p | .boundedWrite _ _ _ p => (subtypeChoiceTypes p).all (validTy ok)

@[nospecialize] def validCertificate (ok : ι → Bool) (C : ControlFlow.Certificate ι) : Bool :=
  C.all (fun n =>
    validEvidence ok n.expression &&
    (n.effect.map (validEffect ok)).getD true &&
    (n.edges.flatMap id |>.flatMap subtypeChoiceTypes).all (validTy ok))

/-- A read summary's labels: its receiver, its result, and each arm's view
and comparison. -/
@[nospecialize] def validSummary (ok : ι → Bool) (s : ReadSummary ι) : Bool :=
  validTy ok s.receiver && validTy ok s.result && s.arms.all fun a =>
    validTy ok a.view && ((a.proof.map subtypeChoiceTypes).getD []).all (validTy ok)

@[nospecialize] def validResponse (r : Request σ ι) (c : Response ι) : Bool :=
  validCertificate (StoreView.valid r.types) c.certificate &&
    c.codes.all (validCertificate (StoreView.valid r.types)) &&
    c.readSummaries.all (validSummary (StoreView.valid r.types))

end

/-- Semantic JSON equality for strict field checking, independent of object
field order. Re-encoding rejects unknown fields and defaulted omissions. -/
partial def sameJson (a b : Json) : Bool :=
  match a, b with
  | .arr xs, .arr ys => xs.size == ys.size && (xs.toList.zip ys.toList).all (fun (x,y) => sameJson x y)
  | .obj xs, .obj ys => xs.toList.length == ys.toList.length && xs.toList.all (fun (k,v) =>
      match b.getObjVal? k with | .ok w => sameJson v w | .error _ => false)
  | _, _ => a == b

/-- The first place, under the path `p`, where a document and its
re-encoding differ: a field the re-encoding drops (unknown, or a default
whose spelling is its omission), a field it adds (one the document left
implicit), or a value it spells otherwise. -/
partial def firstDifference (p : String) (a b : Json) : Option String :=
  match a, b with
  | .arr xs, .arr ys =>
      if xs.size != ys.size then some s!"`{p}` does not re-encode to itself"
      else (xs.toList.zip ys.toList).zipIdx.findSome? fun ((x, y), i) => firstDifference s!"{p}[{i}]" x y
  | .obj xs, .obj ys =>
      (xs.toList.findSome? fun (k, v) => match b.getObjVal? k with
        | .ok w => firstDifference s!"{p}.{k}" v w
        | .error _ => some s!"`{p}.{k}` is a field the calculus protocol does not take there (unknown, or a default spelled out)") <|>
      (ys.toList.findSome? fun (k, _) => match a.getObjVal? k with
        | .ok _ => none
        | .error _ => some s!"`{p}.{k}` is missing: every field of the calculus protocol is explicit")
  | _, _ => if a == b then none else some s!"`{p}` does not re-encode to itself"

/-- Decode `j`, the value at path `p` of a document, refusing it unless it
re-encodes to itself; the refusal names the first field that differs. -/
def decodeStrict [FromJson α] [ToJson α] (p : String) (j : Json) : Except String α := do
  let a ← fromJson? j
  if sameJson j (toJson a) then return a
  throw ((firstDifference p j (toJson a)).getD s!"`{p}` does not re-encode to itself")

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- Async code is certified at the footprint letting every location change:
an async call returns normally where its body throws, so a footprint its
body meets on normal return is no footprint of the call (L6 of the method
effects design; SOURCE-CONTRACTS.md, "Async functions and await"). -/
def asyncEffects (async : Bool) (footprint : Footprints.Closed) : Bool :=
  !async || footprint == .top

/-- A declaration's claim within the effect its result annotation states
(`Modifies<P, T>`; SOURCE-ELABORATION.md, "Stated effects"): a statement adds a
guarantee (a footprint below `top`, a fresh result, or store regions); the
claim's footprint is within the statement's, on a throw too where the
statement says so, and promises a fresh result where the statement does; an
async declaration states none. A statement with store regions is established
by the unit's regional check (`SourceRequests.regionalResult`), whatever its
claim. Unstated, any claim. -/
def statedWithin (async : Bool) (footprint : Footprints.Closed) (onThrow fresh : Bool) :
    Option CallEffects.Effect → Bool
  | none => true
  | some s => !async && (s.footprint != .top || s.fresh || !s.regions.isEmpty) &&
      (!s.regions.isEmpty || footprint.le s.footprint) && (!s.regions.isEmpty || !s.onThrow || onThrow) &&
      (!s.fresh || fresh)

/-- The request's async code at `top`, then its read summaries, each checked
once, then its graph code, checked in order against its claims, as a table
of what was checked. -/
@[nospecialize] def codeTableResult (r : Request σ ι) (c : Response ι) :
    ProgramCertificates.CheckResult ι (List (CodeEntry ι)) :=
  (ProgramCertificates.CheckResult.ofBool
    (r.codes.all fun q => asyncEffects q.async q.entry.row.effect.footprint)).bind fun _ =>
  (ProgramCertificates.CheckResult.ofBool (r.codes.length == c.codes.length &&
    (r.codes.zip c.codes).all (fun (q, C) => C.map signature == q.claims))).bind fun _ =>
  (ProgramCertificates.checkReadSummariesResult (graph r) (StoreView.images r.types) c.readSummaries).bind fun _ =>
  GraphCode.checkCodesResult (graph r) (StoreView.images r.types) c.readSummaries
    ((r.codes.map (·.entry)).zip c.codes)

end

section
variable {ι : Type} [DecidableEq ι]

/-- A qualified body's executable check and its enclosing descriptor contract.
The ordinary graph assignment also has a proof for this same check. -/
structure QualifiedBody (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G) where
  source : SchemeRow ι
  stable : Fam
  capabilities : ResolutionDescriptors.Capabilities (excOf G) stable
  domain : G.domain = ResolutionDescriptors.descriptorDomain capabilities
  body : BodySubtyping G
  /-- Labels the body reads as one another, each pair denoting the same
  values within the declared bounds (`ProgramCertificates.AliasesSound`). -/
  aliases : List (ι × ι)
  aliases_sound : ProgramCertificates.AliasesSound G source aliases
  check_eq : body.check = ProgramCertificates.lexicalBodyCheck G images source aliases

/-- Source instances satisfy both the descriptor contract and the declared
bounds. Each bound is interpreted in the enclosing assignment. -/
def QualifiedBody.Admits {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (q : QualifiedBody G images) (η : MixedAssignment ι) : Prop :=
  ∃ θ As, As.length = q.source.binders.length ∧ G.domain.allowed q.source As ∧
    (∀ n, Bounded (mixedMeaning G) θ q.source As n) ∧
    η = assign θ q.source.binders As

/-- The body's rule admits every ordinary comparison. -/
theorem QualifiedBody.ordinary {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (q : QualifiedBody G images) {A B p}
    (h : PositiveCertificates.checkUsing G images A B p = true) : q.body.check A B p = true := by
  rw [q.check_eq]
  exact ProgramCertificates.lexicalBodyCheck_ordinary h

@[nospecialize] def QualifiedBody.checker {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (q : QualifiedBody G images) :
    HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.withSubtyping G images q.body q.ordinary

end

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- Validate a request and retain its checked code table for supplemental obligations. -/
@[nospecialize] def verifyResult (r : Request σ ι) (c : Response ι)
    (checker : HeapExpressionRules.Checker (graph r) (StoreView.images r.types) :=
      HeapExpressionRules.Checker.ordinary (graph r) (StoreView.images r.types)) :
    ProgramCertificates.CheckResult ι (List (CodeEntry ι)) :=
  (ProgramCertificates.CheckResult.ofBool (validRequest r && validResponse r c)).bind fun _ =>
  (codeTableResult r c).bind fun table =>
    (CertificateProducer.acceptResult (checker := checker) (sums := c.readSummaries) (graph r)
      (StoreView.images r.types) r.goal r.program
      r.claims c.certificate r.start r.inputs (GraphCode.admits table) r.entrySeparation r.entryIndices).map
        fun _ => table

end

/-! ## Source maps

A source map says how to describe the graph in the words of the source it was
lowered from: one entry per graph label, and within an entry one descriptor per
context binding. Lowering is the only pass that knows both sides, so it is the
only pass that can record this.

Source maps are explanatory. They have no decoder, never reach a request or a
certificate, and cannot affect acceptance; a wrong descriptor mislabels a
message and nothing else. -/

/-- How one context binding is named in the source: a source binding it is
addressable by, the expression whose value it holds, or both. At least one is
present — a context this cannot describe is an extraction error, not a slot
number shown to a reader. -/
structure Descriptor where
  name : String := ""
  span : Option (Nat × Nat) := none
  deriving ToJson, Repr, DecidableEq

def Descriptor.describes (d : Descriptor) : Bool := d.name != "" || d.span.isSome

/-- One graph label's source map entry. `context` runs in context order. -/
structure SourceMapEntry where
  pos : Nat × Nat
  role : String := "node-typing"
  environmentStart : Option Nat := none
  context : List Descriptor := []
  deriving ToJson

/-- The source map for a whole graph: one entry per label, absent where a node
has no source counterpart. -/
abbrev SourceMap := List (Option SourceMapEntry)

/-- A diagnostic distinguishes completed search from unfinished resource work. -/
inductive DiagnosticOutcome where
  | notEstablished
  | exhausted (limit rounds visited : Nat)

def DiagnosticOutcome.toJson : DiagnosticOutcome → Json
  | .notEstablished => Json.mkObj [("kind",Lean.toJson "not-established")]
  | .exhausted limit rounds visited => Json.mkObj [("kind",Lean.toJson "exhausted"),
      ("resource",Json.mkObj [("kind",Lean.toJson "subtype-frontier"),("limit",Lean.toJson limit),
        ("rounds",Lean.toJson rounds),("visited",Lean.toJson visited)])]

instance : ToJson DiagnosticOutcome := ⟨DiagnosticOutcome.toJson⟩

/-- One machine-readable record on stderr, following the human-readable error.
This transport leaves successful evidence JSON and the proof protocol unchanged. -/
def withDiagnostic (message : String) (fields : List (String × Json)) : String :=
  message ++ "\nobligation-diagnostic: " ++ (Json.mkObj fields).compress

/-- A message carrying a diagnostic (`withDiagnostic`). -/
def hasDiagnostic (message : String) : Bool :=
  (message.splitOn "\nobligation-diagnostic: ").length > 1

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- A point claim as a diagnostic shows it, through the store's projection. -/
@[nospecialize] def PointClaim.shown (p : Projection ι) (c : PointClaim ι) : PointClaim Nat :=
  ⟨c.context.map p.shown, p.shown c.type⟩

/-- The labels a point claim mentions. -/
@[nospecialize] def PointClaim.mentions (c : PointClaim ι) : List ι := c.type ++ c.context.flatten

/-- A graph failure as a diagnostic: its types are the store's projection
(`StoreView.project`) onto the labels the record mentions. -/
@[nospecialize] def failureDiagnostic (r : Request σ ι) (fuel : Nat)
    (sourceMap : SourceMap) (e : Failure ι)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := [])
    (phaseOverride : Option String := none) (leftOut : List CertificateProducer.LeftOut := []) :
    List (String × Json) := Id.run do
  let claimAt := fun l => (r.claims[l]? : Option (PointClaim ι))
  let mentionedAt := fun l => ((claimAt l).map PointClaim.mentions).getD []
  let mentioned := match e with
    | .expression label => mentionedAt label
    | .exhaustedExpression label stop => mentionedAt label ++ stop.source ++ stop.target
    | .exhaustedEdge source destination _ stop => mentionedAt source ++ mentionedAt destination ++ stop.source ++ stop.target
    | .edge source destination _ => mentionedAt source ++ mentionedAt destination
    | .promise label actual promised => mentionedAt label ++ actual ++ promised
    | .claimCount | .rejected => []
  let p := StoreView.projection r.types (r.result ++ mentioned).eraseDups
  let atNode := fun l => Json.mkObj [
    ("label",toJson l), ("sourceMap",toJson ((sourceMap[l]?).bind id)),
    ("node",toJson r.program[l]?), ("claim",toJson ((claimAt l).map (PointClaim.shown p))),
    ("requiredKnowledge",toJson (requirements.lookup l))]
  let phase := phaseOverride.getD (match e with
    | .rejected => "certificate-check"
    | .claimCount => "request-validation"
    | .expression .. | .edge .. | .exhaustedExpression .. | .exhaustedEdge .. | .promise .. => "proof-search")
  let outcome := match e with
    | .exhaustedExpression _ stop | .exhaustedEdge _ _ _ stop =>
      DiagnosticOutcome.exhausted stop.limit stop.rounds stop.visited
    | .expression .. | .edge .. | .promise .. | .rejected | .claimCount => .notEstablished
  -- Each candidate the search left out: its statement entry, the node whose
  -- edge into it does not establish it (the entry itself at the graph's
  -- entry), and the fact, over the entry's slots.
  let dropped := leftOut.map fun d => Json.mkObj [
    ("label",toJson d.cut), ("sourceMap",toJson ((sourceMap[d.cut]?).bind id)),
    ("edgeFrom",toJson d.source), ("edgeSourceMap",toJson ((sourceMap[d.source]?).bind id)),
    ("fact",toJson d.fact)]
  let common := [("phase",toJson phase),("outcome",toJson outcome),
    ("fuel",toJson fuel),("requiredResult",toJson (p.shown r.result)),
    ("candidatesLeftOut",Json.arr dropped.toArray)] ++ p.fields
  match e with
  | .expression label =>
    let goal := do
      let node ← r.program[label]?
      let c ← claimAt label
      pure (Sequent.mk (c.context.map p.shown) node.expression (p.shown c.type))
    return common ++ [("kind",toJson "node-typing"),("id",toJson s!"node:{label}"),
      ("source",atNode label),("sequent",toJson goal)]
  | .edge source destination index =>
    let transfer := do
      let node ← r.program[source]?
      let c := PointClaim.shown p (← claimAt source)
      let (available, target, observation) ← (match node.continuation with
        | .bind t => some (c.type :: c.context, t, (none : Option Bool))
        | .effect t => some (c.context, t, none)
        | .branch y n => some (c.context, if index == 0 then y else n, none)
        | .branchBind y n => some (c.type :: c.context, if index == 0 then y else n, some (index == 0))
        | .tagBind _ y n => some (c.type :: c.context, if index == 0 then y else n, none)
        | .ret => none)
      pure (Json.mkObj [("available",toJson available),("target",toJson target),
        ("booleanObservation",toJson observation),
        ("tagObservation",match node.continuation with
          | .tagBind t _ _ => Json.mkObj [("test",toJson t),("answer",toJson (index == 0)),("slot",toJson (0 : Nat))]
          | _ => Json.null)])
    return common ++ [("kind",toJson "edge-coverage"),("id",toJson s!"edge:{source}:{index}"),
      ("edgeIndex",toJson index),("source",atNode source),("destination",atNode destination),
      ("transfer",toJson transfer)]
  | .exhaustedExpression label stop | .exhaustedEdge _ label _ stop =>
    let origin := (sourceMap[label]?).bind id
    let subject := origin.map (·.pos) |>.getD (0, 0)
    return common ++ [("kind",toJson "direct-obligation"),("id",toJson s!"subtype:{label}"),
      ("sourceMap",toJson { (origin.getD (SourceMapEntry.mk subject "node-typing" none [])) with context := [] }),
      ("judgment",Json.mkObj [("kind",toJson "subtyping"),("subject",toJson subject),
        ("actual",toJson (p.shown stop.source)),("expected",toJson (p.shown stop.target))])]
  | .promise label actual promised =>
    let origin := (sourceMap[label]?).bind id
    let subject := origin.map (·.pos) |>.getD (0, 0)
    return common ++ [("kind",toJson "direct-obligation"),("id",toJson s!"promise:{label}"),
      ("sourceMap",toJson { (origin.getD (SourceMapEntry.mk subject "node-typing" none [])) with context := [] }),
      ("judgment",Json.mkObj [("kind",toJson "subtyping"),("subject",toJson subject),
        ("actual",toJson (p.shown actual)),("expected",toJson (p.shown promised))])]
  | .claimCount | .rejected => return common ++ [("kind",toJson "production-failure"),("failure",toJson (reprStr e))]

/-- A code request as a request of its own: its graph, from the frame its
signature describes, at the signature's result. What it may create is the
table checked before it, not part of this request. -/
@[nospecialize] def CodeRequest.asRequest (r : Request σ ι) (q : CodeRequest ι) : Request σ ι :=
  { types := r.types, program := GraphCode.program q.entry.exprs q.entry.conts, claims := q.claims,
    result := q.entry.row.result, start := q.entry.start,
    inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.store, codes := [],
    entryIndices := GraphCode.codeEntryIndices q.entry }

/-- Search one graph's certificate, the codes of `table` admitted, in the
producer's graph `G` and image check `I`: the request's own, built once by the
producer's caller for every search it makes (`produceResponseUsing`). -/
@[nospecialize] def produceGraphUsing (G : NormalGraph ι) (I : PositiveCertificates.InstanceImageCheck G)
    (r : Request σ ι) (fuel : Nat) (labels : List ι)
    (suggestions : List (ProgramCertificates.Sequent ι)) (known : List (ProgramCertificates.Evidence ι))
    (sourceMap : SourceMap) (requirements : List (Nat × HeapKnowledge.Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.IndexAtom))
    (table : List (CodeEntry ι))
    (checker : HeapExpressionRules.Checker G I := HeapExpressionRules.Checker.ordinary G I)
    (aliases : List (ι × ι) := []) (goal : Option (ControlFlow.Goal ι) := none)
    (answers : CertificateProducer.Answered G := {})
    (recheck : Option ((i : PositiveCertificates.InstanceImageCheck G) → HeapExpressionRules.Checker G i) := none)
    (unchecked : Bool := false) :
    Except String (ControlFlow.Certificate ι × CertificateProducer.Answered G) :=
  let entry := (requirements.lookup r.start).getD {}
  let requirements := (r.start, { entry with indices := (entry.indices ++ r.entryIndices).eraseDups }) ::
    requirements.filter (fun p => p.1 != r.start)
  match CertificateProducer.produceUsing G I labels fuel (goal.getD r.goal)
      r.program r.claims r.start [] r.inputs suggestions known
      requirements cuts (GraphCode.admits table) checker aliases answers recheck r.entrySeparation r.entryIndices
      candidates (unchecked := unchecked) with
  | (.ok c, answers, _) => pure (c, answers)
  | (.error e, _, leftOut) =>
    let location := match e with
      | .expression label | .exhaustedExpression label _ | .promise label .. => match (sourceMap[label]?).bind id with
        | some o => s!"source expression obligation at [{o.pos.1},{o.pos.2}): "
        | none => ""
      | .edge _ destination _ | .exhaustedEdge _ destination _ _ => match (sourceMap[destination]?).bind id with
        | some o => s!"source incoming edge obligation at [{o.pos.1},{o.pos.2}): "
        | none => ""
      | _ => ""
    -- Name what could not be established; the structured record below says
    -- with which claims, and the reader phrases it in source terms.
    let what := match e with
      | .expression label | .exhaustedExpression label _ => match (sourceMap[label]?).bind id with
        | some o => s!"no derivation of its {o.role} claim"
        | none => s!"no derivation of the claim of node {label}"
      | .edge source _ _ | .exhaustedEdge source _ _ _ => s!"the edge from node {source} does not establish the claims at this point"
      | .promise .. => "the promised argument is not within the promise at this return"
      | _ => reprStr e
    throw (withDiagnostic s!"{location}evidence search failed: {what}"
      (failureDiagnostic r fuel sourceMap e requirements (leftOut := leftOut)))

/-- What search knows of a code request beyond the request: its source map, its
points' required knowledge, its statement entries' candidates and its cuts,
as for a unit. -/
structure CodeHints where
  sourceMap : SourceMap := []
  requirements : List (Nat × HeapKnowledge.Knowledge) := []
  candidates : List (Nat × List HeapKnowledge.IndexAtom) := []
  cuts : List Nat := []

/-- Render the retained validation outcome in the graph whose check exhausted. -/
@[nospecialize] def validationFailure (r : Request σ ι) (fuel : Nat)
    (sourceMap : SourceMap) (codeHints : List CodeHints) (stop : Exhaustion ι) : String := Id.run do
  let (request, origins) := match stop.frames with
    | .code index :: _ => match r.codes[index]? with
      | some q => (q.asRequest r, ((codeHints[index]?).getD {}).sourceMap)
      | none => (r, sourceMap)
    | [] | .node _ :: _ | .obligation _ :: _ | .request _ :: _ => (r, sourceMap)
  let label := stop.nodeLabel.getD request.start
  return withDiagnostic "subtype search exhausted during certificate validation; result is inconclusive"
    (failureDiagnostic request fuel origins (.exhaustedExpression label stop) [] (some "certificate-check"))

/-- Search a request's evidence: each code's certificate, then the graph's,
checked as the consumer checks them. Fuel bounds search only; it is not
part of the certified request. Search runs in the producer's graph `G` and
image check `I`, which the caller builds once and shares between the
requests whose stores give the same graph and image check, under the search
checker `searchChecker`; the response is checked under the request's own
`checker`, as acceptance checks it. `searched` states that `G`, `I` and
`searchChecker` are the request's own graph, image check and checker. -/
@[nospecialize] def produceResponseUsing (G : NormalGraph ι) (I : PositiveCertificates.InstanceImageCheck G)
    (searchChecker : HeapExpressionRules.Checker G I) (r : Request σ ι) (fuel : Nat)
    (suggestions : List (ProgramCertificates.Sequent ι) := [])
    (known : List (ProgramCertificates.Evidence ι) := [])
    (sourceMap : SourceMap := [])
    (searchLabels : Option (List ι) := none)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := [])
    (candidates : List (Nat × List HeapKnowledge.IndexAtom) := [])
    (codeHints : List CodeHints := [])
    (checker : HeapExpressionRules.Checker (graph r) (StoreView.images r.types) :=
      HeapExpressionRules.Checker.ordinary (graph r) (StoreView.images r.types))
    (aliases : List (ι × ι) := []) (answers : CertificateProducer.Answered G := {})
    (searched : Bool := false)
    (recheck : Option ((i : PositiveCertificates.InstanceImageCheck G) → HeapExpressionRules.Checker G i) := none)
    (unchecked : Bool := false) :
    Except String (Response ι × CertificateProducer.Answered G) := do
  let labels := searchLabels.getD (StoreView.labels r.types)
  -- Each code against the table of those before it, as `codeTable` checks.
  let mut answers := answers
  let mut table : List (CodeEntry ι) := []
  let mut certificates : List (ControlFlow.Certificate ι) := []
  for (q, i) in r.codes.zipIdx do
    let hints := (codeHints[i]?).getD {}
    let (C, next) ← produceGraphUsing G I (q.asRequest r) fuel labels suggestions known hints.sourceMap
      hints.requirements hints.cuts hints.candidates table (goal := some q.entry.goal) (answers := answers)
      (recheck := recheck.map fun _ => HeapExpressionRules.Checker.ordinary G)
    answers := next
    certificates := certificates ++ [C]
    -- Search may use only definitions whose complete certificate checks,
    -- including their effect. Otherwise the defining expression must fail at
    -- its ordinary source obligation, rather than borrowing an unchecked code
    -- entry and failing only at the final generic certificate check.
    -- Retain every certificate: `verifyResult` still checks the entire code list.
    -- Under the search's own checks (`recheck`), the inclusions search
    -- established are answered from their proofs.
    let checked := match recheck with
      | some _ => GraphCode.codeCheckedResult G (answers.images I) answers.summaries.toList table q.entry C
      | none => GraphCode.codeCheckedResult (graph r) (StoreView.images r.types) answers.summaries.toList
          table q.entry C
    if checked.accepted then table := table ++ [q.entry]
    else if let some stop := checked.exhaustion then
      let label := stop.nodeLabel.getD q.entry.start
      throw (withDiagnostic "subtype search exhausted during code admission; result is inconclusive"
        (failureDiagnostic (q.asRequest r) fuel hints.sourceMap (.exhaustedExpression label stop)))
  let (C, final) ← produceGraphUsing G I r fuel labels suggestions known sourceMap requirements cuts candidates table
    searchChecker aliases (answers := answers) (recheck := recheck) (unchecked := unchecked)
  let response := Response.mk C certificates final.summaries.toList
  -- Where the search checked under the request's own checker (`searched`)
  -- and admitted every code, `verifyResult` repeats those checks: its code
  -- table is the loop's, each code checked against the codes before it, and
  -- its graph check is the one the graph's search accepted. Only its
  -- request and response checks remain.
  if searched && table.length == r.codes.length && validRequest r && validResponse r response &&
      (r.codes.zip response.codes).all (fun (q, C) => C.map signature == q.claims) then
    return (response, final)
  let checked := verifyResult r response checker
  if checked.accepted then return (response, final)
  throw (match checked.exhaustion with
    | some stop => validationFailure r fuel sourceMap codeHints stop
    | none => "the certificate does not justify the actual program and supplied claims")

end

end Verification.RequestJson
