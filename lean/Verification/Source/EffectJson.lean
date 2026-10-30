import Lean.Data.Json
import Verification.Semantics.CallEffects

/-! The one JSON form of a call signature's effect, read and written by the
Fragment's declaration document, the claims document and the evidence: a
closed footprint, `{"value", "store"}`, a promise, `null` or
`{"guards": {"param": p}}` or `{"asserts": {"param": p}}`, and the Booleans
`fresh` and `receiverStore`. Each decoder
re-encodes what it read and refuses a document that differs, so a field
outside these, or a `grow` on `value`, is refused. -/
namespace Verification.EffectJson
open Lean CallEffects

/-- A change's wire name. -/
def changeName : Footprints.Change → String
  | .keep => "keep"
  | .grow => "grow"
  | .any => "any"

private def changeOf (allowed : List Footprints.Change) (name : String) : Except String Footprints.Change :=
  match allowed.find? (changeName · == name) with
  | some d => pure d
  | none => throw s!"invalid footprint change '{name}'"

instance : ToJson Footprints.Closed :=
  ⟨fun c => Json.mkObj [("value", toJson (changeName c.value)), ("store", toJson (changeName c.store))]⟩

/-- On a value `grow` is `keep`, so `value` is `keep` or `any`. -/
instance : FromJson Footprints.Closed := ⟨fun j => do
  let c : Footprints.Closed := ⟨← changeOf [.keep, .any] (← j.getObjValAs? String "value"),
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

/-- An effect is its footprint, its promise, `null` when there is none,
whether its result's array store is fresh, whether its footprint excepts its
receiver's store, whether the footprint also holds on a throw, whether it
excepts its receiver's own locations, and whether its result is an object
every own location of which is fresh. -/
instance : ToJson Effect := ⟨fun e => Json.mkObj [("footprint", toJson e.footprint),
  ("promise", match e.promise with | some p => toJson p | none => Json.null),
  ("fresh", toJson e.fresh), ("receiverStore", toJson e.receiverStore), ("onThrow", toJson e.onThrow),
  ("receiverOwn", toJson e.receiverOwn), ("freshObject", toJson e.freshObject),
  ("requires", predJson e.requires), ("elements", predJson e.elements)]⟩

instance : FromJson Effect := ⟨fun j => do
  let footprint ← j.getObjValAs? Footprints.Closed "footprint"
  let promise ← match ← j.getObjVal? "promise" with
    | .null => pure none
    | p => some <$> fromJson? p
  let e : Effect := ⟨footprint, promise, ← j.getObjValAs? Bool "fresh", ← j.getObjValAs? Bool "receiverStore",
    ← j.getObjValAs? Bool "onThrow", ← j.getObjValAs? Bool "receiverOwn", ← j.getObjValAs? Bool "freshObject",
    ← predOf (← j.getObjVal? "requires"), ← predOf (← j.getObjVal? "elements")⟩
  if toJson e != j then
    throw ("an effect has exactly the fields footprint, promise, fresh, receiverStore, onThrow, receiverOwn, " ++
      "freshObject, requires and elements, a predicate its kinds in order")
  pure e⟩

end Verification.EffectJson
