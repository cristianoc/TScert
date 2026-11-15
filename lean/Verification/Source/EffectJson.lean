import Lean.Data.Json
import Verification.Semantics.CallEffects

/-! The one JSON form of a call signature's effect, read and written by the
Fragment's declaration document, the claims document and the evidence: a
closed `footprint`, `{"value", "store"}`; a `promise`, `null` or
`{"guards": {"param": p}}` or `{"asserts": {"param": p}}`; the Booleans
`fresh`, `receiverStore`, `onThrow`, `receiverOwn` and `freshObject`; and the
element predicates `requires` and `elements`, each `null` or its kinds in
order; the index-fact lists `pre` and `ensures`; the Boolean
`receiverGrows`; and `elementWrite`, `null`, `"stores"` or the exact write of an element type,
`"exactUint8"`, `"exactUint16"`, `"exactInt32"` or `"exactFloat64"`, whose
precondition states the value's range (`ElementKind.preFacts`, which
`ElementKind.takes_of_requires` reads as the range `ExactWrite` states). Each decoder
re-encodes what it read and refuses a document that differs, so a field
outside these, a `grow` on `value` or an `init` or `scalar` on `store`, is refused. -/
namespace Verification.EffectJson
open Lean CallEffects

/-- An element write's wire name. -/
def elementWriteName : ElementWrite → String
  | .stores => "stores"
  | .assign => "assign"
  | .exact .uint8 => "exactUint8"
  | .exact .uint16 => "exactUint16"
  | .exact .int32 => "exactInt32"
  | .exact .float64 => "exactFloat64"

private def elementWriteOf (name : String) : Except String ElementWrite :=
  match [ElementWrite.stores, .assign, .exact .uint8, .exact .uint16, .exact .int32, .exact .float64].find?
      (elementWriteName · == name) with
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
  ⟨fun c => Json.mkObj [("value", toJson (changeName c.value)), ("store", toJson (changeName c.stores))]⟩

/-- On a value `grow` is `scalar`, so `value` is `keep`, `init`, `scalar` or
`any`; on a store `init` and `scalar` are `keep`, so `store` is `keep`,
`grow` or `any`. The wire's `store` is the change of both store components
(`Footprints.Closed.ofStores`), and a closed footprint is written with its
store bound (`Footprints.Closed.stores`). -/
instance : FromJson Footprints.Closed := ⟨fun j => do
  let c : Footprints.Closed := .ofStores (← changeOf [.keep, .init, .scalar, .any] (← j.getObjValAs? String "value"))
    (← changeOf [.keep, .grow, .any] (← j.getObjValAs? String "store"))
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
-- "path"}`, its kind's name, its root and its fields, and an entry term
-- `old(t)` (the note "Tolerant frames", section 6) also `"atEntry": true`,
-- its root a position of the entry's.
deriving instance ToJson, FromJson for HeapKnowledge.Term.Kind
instance : ToJson HeapKnowledge.Term where
  toJson t := Json.mkObj ([("kind", toJson t.kind), ("slot", toJson t.slot), ("path", toJson t.path)] ++
    if t.atEntry then [("atEntry", toJson true)] else [])
instance : FromJson HeapKnowledge.Term where
  fromJson? j := do
    let kind ← j.getObjValAs? HeapKnowledge.Term.Kind "kind"
    let slot ← j.getObjValAs? Nat "slot"
    let path ← j.getObjValAs? (List String) "path"
    let atEntry ← match j.getObjVal? "atEntry" with
      | .ok v => fromJson? v
      | .error _ => pure false
    return if atEntry then .old kind slot path else .now kind slot path
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

/-! ## The wire form of an effect

The document's fields of an effect are their own datatype (`WireEffect`).
A value of it read from a document is elaborated into the effect it states
(`WireEffect.elaborate`); an effect is written only where it is exactly
the elaboration of a valid wire value (`Representable`, `encodeOld`), so
writing never weakens an effect. -/

/-- **An effect as the documents write it**: its footprint, its promise,
`null` when there is none, whether its result's array store is fresh,
whether its footprint excepts its receiver's store, whether the footprint
also holds on a throw, whether it excepts its receiver's own locations, and
whether its result is an object every own location of which is fresh, its
precondition on the receiver's elements and its elements promise, its
precondition on the call's values (`pre`) and the facts a normal return
states (`ensures`), whether it grows its receiver's store, its element
write, and, where it states any, its frame's store regions, each a position
and a path (`regions`). Its footprint is the frame's closed bound. -/
structure WireEffect where
  closed : Footprints.Closed
  promise : Option TypePromise
  fresh : Bool
  receiverStore : Bool
  onThrow : Bool
  receiverOwn : Bool
  freshObject : Bool
  requires : Option ElemPred
  elements : Option ElemPred
  pre : List HeapKnowledge.IndexFact
  ensures : List HeapKnowledge.IndexFact
  receiverGrows : Bool
  elementWrite : Option ElementWrite
  regions : List Footprints.ArgumentStoreRegion
  deriving Repr, DecidableEq

/-- **A valid wire value**: its footprint is one the wire writes (a value
change `keep`, `init`, `scalar` or `any`, one store change `keep`, `grow`
or `any` for both stores, `Footprints.Closed.ofStores`), and an exact
element write states its value's range in its precondition
(`ElementKind.preFacts`, which `ElementKind.takes_of_requires` reads). -/
def WireEffect.valid (w : WireEffect) : Bool :=
  Footprints.Closed.ofStores w.closed.value w.closed.stores == w.closed &&
    [Footprints.Change.keep, .init, .scalar, .any].contains w.closed.value &&
    [Footprints.Change.keep, .grow, .any].contains w.closed.stores &&
    match w.elementWrite with
    | some (.exact k) => k.preFacts.all w.pre.contains
    | _ => true

def WireEffect.Valid (w : WireEffect) : Prop := w.valid = true

/-- **The effect a wire value states.** -/
def WireEffect.elaborate (w : WireEffect) : Effect :=
  ⟨w.closed, w.promise, w.fresh, w.receiverStore, w.onThrow, w.receiverOwn, w.freshObject, w.requires,
    w.elements, w.pre, w.ensures, w.receiverGrows, w.elementWrite, w.regions⟩

/-- **An effect the wire represents exactly**: the elaboration of a valid
wire value. -/
def Representable (e : Effect) : Prop := ∃ w : WireEffect, w.Valid ∧ w.elaborate = e

/-- The wire value whose elaboration an effect is, where it is one. -/
def wireOf (e : Effect) : WireEffect :=
  ⟨e.closed, e.promise, e.fresh, e.receiverStore, e.onThrow, e.receiverOwn, e.freshObject, e.requires,
    e.elements, e.pre, e.ensures, e.receiverGrows, e.elementWrite, e.regions⟩

theorem wireOf_elaborate (w : WireEffect) : wireOf w.elaborate = w := rfl

/-- **The encoder**: the wire value an effect is the elaboration of, where
it is valid; refused otherwise. -/
def encodeOld (e : Effect) : Except String WireEffect :=
  if (wireOf e).valid && decide ((wireOf e).elaborate = e) then .ok (wireOf e)
  else .error "an effect the documents' format does not represent exactly"

/-- **What the encoder writes states the effect** (proved). -/
theorem encodeOld_sound {e : Effect} {w : WireEffect} (h : encodeOld e = .ok w) : w.Valid ∧ w.elaborate = e := by
  unfold encodeOld at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc
  · cases h

/-- **The encoder writes every representable effect** (proved). -/
theorem encodeOld_complete {e : Effect} (h : Representable e) : encodeOld e = .ok (wireOf e) := by
  obtain ⟨w, hv, rfl⟩ := h
  unfold encodeOld
  rw [wireOf_elaborate]
  simp only [WireEffect.Valid] at hv
  simp [hv]

instance : ToJson WireEffect := ⟨fun e => Json.mkObj [("footprint", toJson e.closed),
  ("promise", match e.promise with | some p => toJson p | none => Json.null),
  ("fresh", toJson e.fresh), ("receiverStore", toJson e.receiverStore), ("onThrow", toJson e.onThrow),
  ("receiverOwn", toJson e.receiverOwn), ("freshObject", toJson e.freshObject),
  ("requires", predJson e.requires), ("elements", predJson e.elements), ("pre", toJson e.pre),
  ("ensures", toJson e.ensures), ("receiverGrows", toJson e.receiverGrows),
  ("elementWrite", match e.elementWrite with | some w => toJson (elementWriteName w) | none => Json.null)] |>.mergeObj
  (if e.regions.isEmpty then Json.mkObj [] else
    Json.mkObj [("regions", Json.arr (e.regions.map fun r =>
      Json.mkObj [("position", toJson r.position), ("path", toJson r.path)]).toArray)])⟩

/-- A document's effect as the wire value its fields state. -/
private def parseWire (j : Json) : Except String WireEffect := do
  let footprint ← j.getObjValAs? Footprints.Closed "footprint"
  let promise ← match ← j.getObjVal? "promise" with
    | .null => pure none
    | p => some <$> fromJson? p
  return ⟨footprint, promise, ← j.getObjValAs? Bool "fresh", ← j.getObjValAs? Bool "receiverStore",
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

/-- A parsed wire value, kept where it re-encodes to the document read and
is valid. -/
private def checkWire (j : Json) (e : WireEffect) : Except String WireEffect :=
  if toJson e != j then
    .error ("an effect has exactly the fields footprint, promise, fresh, receiverStore, onThrow, receiverOwn, " ++
      "freshObject, requires, elements, a predicate its kinds in order, pre, ensures, receiverGrows and elementWrite, " ++
      "and regions where its frame states store regions")
  else if !e.valid then
    match e.elementWrite with
    | some (.exact k) =>
      .error s!"an exact element write '{elementWriteName (.exact k)}' states its value's range in its precondition"
    | _ => .error "an effect's footprint is one the documents write"
  else .ok e

/-- **The decoder**: a document's effect as a wire value, refused unless it
re-encodes to exactly the document read and is valid. -/
def decodeOld (j : Json) : Except String WireEffect := parseWire j >>= checkWire j

/-- **What the decoder reads is valid and re-encodes to the document read**
(proved; Json's equality). -/
theorem decodeOld_sound {j : Json} {w : WireEffect} (h : decodeOld j = .ok w) :
    w.Valid ∧ (toJson w == j) = true := by
  unfold decodeOld at h
  cases hp : parseWire j with
  | error _ => rw [hp] at h; cases h
  | ok e =>
    rw [hp] at h
    change checkWire j e = .ok w at h
    unfold checkWire at h
    split at h
    · cases h
    · split at h
      · split at h <;> cases h
      · cases h
        rename_i hj hv
        refine ⟨by simpa [WireEffect.Valid] using hv, ?_⟩
        simpa [bne] using hj

/-- An effect is read through its wire value (`decodeOld`), and is the
effect that value states (`WireEffect.elaborate`): natives and library
declarations arrive through it. -/
instance : FromJson Effect := ⟨fun j => WireEffect.elaborate <$> decodeOld j⟩

/-- **An effect is written through the encoder** (`encodeOld`): refused where
the documents' format does not represent it exactly. -/
def effectJson (e : Effect) : Except String Json := toJson <$> encodeOld e

/-- **An effect inside a derived document** (a types table, evidence, a
diagnostic, a claim): the encoder's wire value (`encodeOld`), or, where the
encoder refuses, an object naming the refusal, `{"unrepresentable":
reason}`, which no decoder reads (`decodeOld` requires every field of the
wire). It writes no effect other than the one it is given. A writer that
can refuse uses `effectJson`. -/
instance : ToJson Effect := ⟨fun e => match encodeOld e with
  | .ok w => toJson w
  | .error msg => Json.mkObj [("unrepresentable", toJson msg)]⟩

/-- **Reading and writing are inverse on what is read** (proved): an effect
read from a document is written back as that document (Json's equality). -/
theorem effectJson_decode {j : Json} {w : WireEffect} (h : decodeOld j = .ok w) :
    ∃ j', effectJson w.elaborate = .ok j' ∧ (j' == j) = true := by
  obtain ⟨hv, hj⟩ := decodeOld_sound h
  refine ⟨toJson w, ?_, hj⟩
  rw [effectJson, encodeOld_complete ⟨w, hv, rfl⟩, wireOf_elaborate]
  rfl

/-- **An effect as a declaration's result annotation states it**
(`Modifies<P, T>`, the Fragment's and the request's `stated`): a closed
footprint, whether it also bounds a throw, whether the result's array store
is fresh, and the store regions it excepts. This is the documents' shape;
the effect it states is `StatedEffect.effect`. -/
structure StatedEffect where
  closed : Footprints.Closed
  onThrow : Bool
  fresh : Bool
  regions : List Footprints.ArgumentStoreRegion
  deriving Repr, DecidableEq

/-- **The effect a statement states** (`Effect.ofStated`), with the
precondition `pre` its declaration states and no promise. -/
def StatedEffect.effect (s : StatedEffect) (pre : List HeapKnowledge.IndexFact := []) : Effect :=
  Effect.ofStated s.closed none s.onThrow s.fresh pre [] s.regions

/-- The closed bound a statement gives its unit's claim: its closed footprint
without store regions, `top` with them. -/
def StatedEffect.footprint (s : StatedEffect) : Footprints.Closed :=
  if s.regions.isEmpty then s.closed else .top

/-- An exact element write is decoded with its value's range in its
precondition, and refused without it. -/
private def decodes (e : Effect) : Bool :=
  match effectJson e with
  | .ok j => match (fromJson? j : Except String Effect) with
    | .ok d => d == e
    | .error _ => false
  | .error _ => false

#guard decodes { Effect.ordinary with elementWrite := some (.exact .uint8), pre := ElementKind.preFacts .uint8 }
#guard decodes { Effect.ordinary with elementWrite := some (.exact .float64), pre := ElementKind.preFacts .float64 }
#guard !decodes { Effect.ordinary with elementWrite := some (.exact .uint8) }
#guard !decodes { Effect.ordinary with elementWrite := some (.exact .int32), pre := ElementKind.preFacts .uint8 }

end Verification.EffectJson
