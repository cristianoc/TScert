import Lean.Data.Json
import Verification.Semantics.CallEffects

/-! The one JSON form of a call signature's effect, read and written by the
Fragment's declaration document, the claims document and the evidence: a
closed `footprint`, `{"value", "store"}`; a `promise`, `null` or
`{"guards": {"param": p}}` or `{"asserts": {"param": p}}`; the Booleans
`fresh`, `receiverStore`, `onThrow`, `receiverOwn` and `freshObject`; and the
element predicates `requires` and `elements`, each `null` or its kinds in
order; the index-fact lists `pre` and `ensures`; the Boolean
`receiverGrows`; and `elementWrite`, `null`, `"stores"` or `"exact"`. Each decoder
re-encodes what it read and refuses a document that differs, so a field
outside these, a `grow` on `value` or an `init` or `scalar` on `store`, is refused. -/
namespace Verification.EffectJson
open Lean CallEffects

/-- An element write's wire name. -/
def elementWriteName : ElementWrite → String
  | .stores => "stores"
  | .exact => "exact"

private def elementWriteOf (name : String) : Except String ElementWrite :=
  match [ElementWrite.stores, .exact].find? (elementWriteName · == name) with
  | some w => pure w
  | none => throw s!"invalid element write '{name}'"

/-- A change's wire name. -/
def changeName : Footprints.Change → String
  | .keep => "keep"
  | .init => "init"
  | .scalar => "scalar"
  | .grow => "grow"
  | .any => "any"

private def changeOf (allowed : List Footprints.Change) (name : String) : Except String Footprints.Change :=
  match allowed.find? (changeName · == name) with
  | some d => pure d
  | none => throw s!"invalid footprint change '{name}'"

instance : ToJson Footprints.Closed :=
  ⟨fun c => Json.mkObj [("value", toJson (changeName c.value)), ("store", toJson (changeName c.store))]⟩

/-- On a value `grow` is `scalar`, so `value` is `keep`, `init`, `scalar` or
`any`; on a store `init` and `scalar` are `keep`, so `store` is `keep`,
`grow` or `any`. -/
instance : FromJson Footprints.Closed := ⟨fun j => do
  let c : Footprints.Closed := ⟨← changeOf [.keep, .init, .scalar, .any] (← j.getObjValAs? String "value"),
    ← changeOf [.keep, .grow, .any] (← j.getObjValAs? String "store")⟩
  if toJson c != j then throw "a closed footprint has exactly the fields value and store"
  pure c⟩

instance : ToJson TypePromise := ⟨fun
  | .guards p => Json.mkObj [("guards", Json.mkObj [("param", toJson p)])]
  | .asserts p => Json.mkObj [("asserts", Json.mkObj [("param", toJson p)])]⟩

instance : FromJson TypePromise := ⟨fun j => do
  let p ← match j.getObjVal? "guards", j.getObjVal? "asserts" with
    | .ok g, .error _ => pure (TypePromise.guards (← g.getObjValAs? Nat "param"))
    | .error _, .ok a => pure (TypePromise.asserts (← a.getObjValAs? Nat "param"))
    | _, _ => throw "a promise is a guard's or an assertion function's"
  if toJson p != j then throw "a promise has exactly one field, and its parameter"
  pure p⟩

/-- An elements predicate is the list of the kinds it admits, in this order. -/
def predKinds (R : ElemPred) : List String :=
  [("null", R.nul), ("undefined", R.undef), ("boolean", R.bool), ("number", R.num), ("string", R.str),
    ("bigint", R.big), ("symbol", R.sym), ("object", R.obj)].filterMap fun (k, b) => if b then some k else none

def predOfKinds (ks : List String) : ElemPred :=
  ⟨ks.contains "null", ks.contains "undefined", ks.contains "boolean", ks.contains "number",
    ks.contains "string", ks.contains "bigint", ks.contains "symbol", ks.contains "object"⟩

private def predJson : Option ElemPred → Json
  | none => Json.null
  | some R => toJson (predKinds R)

private def predOf : Json → Except String (Option ElemPred)
  | .null => pure none
  | j => do pure (some (predOfKinds (← fromJson? j)))

-- An index fact, in a precondition at the call's positions (`0` the
-- receiver, `i + 1` the `i`-th actual), in a postcondition at the return's
-- positions (`0` the result, `i + 1` the call's position `i`) and in
-- diagnostics' knowledge: its
-- constructor's name holding its fields; a linear term is `{"kind", "slot",
-- "path"}`, its kind's name, its root and its fields.
deriving instance ToJson, FromJson for HeapKnowledge.Term.Kind
deriving instance ToJson, FromJson for HeapKnowledge.Term
deriving instance ToJson, FromJson for HeapKnowledge.Bound
deriving instance ToJson, FromJson for Linear.Fact
private def clauseJson [ToJson V] : HeapKnowledge.LinearClause V → Json
  | .atom F => toJson F
  | .either A B => Json.mkObj [("either", Json.mkObj [("left", clauseJson A), ("right", clauseJson B)])]

instance [ToJson V] : ToJson (HeapKnowledge.LinearClause V) := ⟨clauseJson⟩

private partial def clauseOf [ToJson V] [FromJson V] (j : Json) : Except String (HeapKnowledge.LinearClause V) := do
  let c ← match j.getObjVal? "either" with
    | .ok b => do pure (.either (← clauseOf (← b.getObjVal? "left")) (← clauseOf (← b.getObjVal? "right")))
    | .error _ => HeapKnowledge.LinearClause.atom <$> fromJson? j
  if toJson c != j then throw "a linear clause has exactly its constructor's fields"
  pure c

instance [ToJson V] [FromJson V] : FromJson (HeapKnowledge.LinearClause V) := ⟨clauseOf⟩

-- A guard's tag is a nullish or Boolean literal; a guarded fact is
-- `{"guarded": {"slot", "path", "tag", "body"}}`.
instance : ToJson HeapKnowledge.GuardTag := ⟨fun
  | .null => "null"
  | .undef => "undefined"
  | .tru => "true"
  | .fls => "false"⟩
instance : FromJson HeapKnowledge.GuardTag := ⟨fun
  | .str "null" => pure .null
  | .str "undefined" => pure .undef
  | .str "true" => pure .tru
  | .str "false" => pure .fls
  | _ => throw "a guard's tag is a nullish or Boolean literal"⟩
deriving instance ToJson, FromJson for HeapKnowledge.IndexFact

/-- An effect is its footprint, its promise, `null` when there is none,
whether its result's array store is fresh, whether its footprint excepts its
receiver's store, whether the footprint also holds on a throw, whether it
excepts its receiver's own locations, and whether its result is an object
every own location of which is fresh, its precondition on the receiver's
elements and its elements promise, its precondition on the call's values
(`pre`) and the facts a normal return states (`ensures`), and, where it
states any, its frame's store regions, each a position and a path
(`regions`). Its footprint is the frame's closed bound. -/
instance : ToJson Effect := ⟨fun e => Json.mkObj [("footprint", toJson e.closed),
  ("promise", match e.promise with | some p => toJson p | none => Json.null),
  ("fresh", toJson e.fresh), ("receiverStore", toJson e.receiverStore), ("onThrow", toJson e.onThrow),
  ("receiverOwn", toJson e.receiverOwn), ("freshObject", toJson e.freshObject),
  ("requires", predJson e.requires), ("elements", predJson e.elements), ("pre", toJson e.pre),
  ("ensures", toJson e.ensures), ("receiverGrows", toJson e.receiverGrows),
  ("elementWrite", match e.elementWrite with | some w => toJson (elementWriteName w) | none => Json.null)] |>.mergeObj
  (if e.regions.isEmpty then Json.mkObj [] else
    Json.mkObj [("regions", Json.arr (e.regions.map fun r =>
      Json.mkObj [("position", toJson r.position), ("path", toJson r.path)]).toArray)])⟩

instance : FromJson Effect := ⟨fun j => do
  let footprint ← j.getObjValAs? Footprints.Closed "footprint"
  let promise ← match ← j.getObjVal? "promise" with
    | .null => pure none
    | p => some <$> fromJson? p
  let e : Effect := ⟨footprint, promise, ← j.getObjValAs? Bool "fresh", ← j.getObjValAs? Bool "receiverStore",
    ← j.getObjValAs? Bool "onThrow", ← j.getObjValAs? Bool "receiverOwn", ← j.getObjValAs? Bool "freshObject",
    ← predOf (← j.getObjVal? "requires"), ← predOf (← j.getObjVal? "elements"),
    ← fromJson? (← j.getObjVal? "pre"), ← fromJson? (← j.getObjVal? "ensures"),
    ← j.getObjValAs? Bool "receiverGrows", ← match ← j.getObjVal? "elementWrite" with
      | .null => pure none
      | w => do some <$> elementWriteOf (← w.getStr?), ← match j.getObjVal? "regions" with
      | .ok rs => do
          let rs ← rs.getArr?
          rs.toList.mapM fun r => do
            pure (⟨← r.getObjValAs? Nat "position", ← r.getObjValAs? (List String) "path"⟩ :
              Footprints.ArgumentStoreRegion)
      | .error _ => pure []⟩
  if toJson e != j then
    throw ("an effect has exactly the fields footprint, promise, fresh, receiverStore, onThrow, receiverOwn, " ++
      "freshObject, requires, elements, a predicate its kinds in order, pre, ensures, receiverGrows and elementWrite, " ++
      "and regions where its frame states store regions")
  pure e⟩

end Verification.EffectJson
