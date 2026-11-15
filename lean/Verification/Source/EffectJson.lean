import Lean.Data.Json
import Verification.Semantics.CallEffects
import Verification.Source.EffectCodec

/-! The JSON instances of an effect and of the values documents share with
it: an effect is read and written in its one serialized form
(`EffectCodec`, the request protocol's grammar), an index fact and a linear
term in the same codec wherever they occur, a closed footprint as
`{"value", "store"}` and a promise as `{"guards": {"param"}}` or
`{"asserts": {"param"}}`. A declaration's statement is its exits in the
same codec (`StatedEffect`). -/
namespace Verification.EffectJson
open Lean CallEffects

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

-- An index fact, in a precondition at the call's positions (`0` the
-- receiver, `i + 1` the `i`-th actual), in a postcondition at the return's
-- positions and in diagnostics' knowledge, and a linear term (with
-- `"atEntry": true` for an entry term `old(t)`, the note "Tolerant frames",
-- section 6): the serialized effect's codec, read exactly.
instance : ToJson HeapKnowledge.Term.Kind := ⟨EffectCodec.kindJ⟩
instance : FromJson HeapKnowledge.Term.Kind := ⟨EffectCodec.kindOf⟩
instance : ToJson HeapKnowledge.GuardTag := ⟨EffectCodec.guardJ⟩
instance : FromJson HeapKnowledge.GuardTag := ⟨EffectCodec.guardOf⟩
instance : ToJson HeapKnowledge.Term := ⟨EffectCodec.termJ⟩
instance : FromJson HeapKnowledge.Term := ⟨EffectCodec.exactly EffectCodec.termJ EffectCodec.termOf⟩
instance : ToJson HeapKnowledge.IndexFact := ⟨EffectCodec.factJ⟩
instance : FromJson HeapKnowledge.IndexFact :=
  ⟨EffectCodec.exactly EffectCodec.factJ (EffectCodec.factOf EffectCodec.nestingLimit)⟩

/-! ## Effects -/

/-- **An effect is admitted as a contract**: read in its serialized form
(`EffectCodec.decode`), and refused unless every exact view write it states
has its range among its preconditions (`Effect.exactWritesRequired`, whose
theorem `Effect.exactWrite_pre` the exact write's rule reads). Natives and
library declarations arrive through it. -/
def admit (j : Json) : Except String Effect := do
  let e ← EffectCodec.decode j
  if !e.exactWritesRequired then
    throw "an exact element write states its range among its preconditions"
  pure e

instance : FromJson Effect := ⟨admit⟩

/-- **An effect is written in its serialized form** where it serializes
(`EffectCodec.checked`); a writer that can refuse uses this. -/
def effectJson (e : Effect) : Except String Json := (·.encode) <$> EffectCodec.checked e

/-- **An effect inside a document is its writing** (`EffectCodec.encode`); a
writer of a document holding effects writes it through
`EffectCodec.document`, which refuses the whole document, naming the
place, where an effect does not read back as one. -/
instance : ToJson Effect := ⟨EffectCodec.encode⟩

/-- A callable's exits (a statement's, a claim's), read exactly. -/
instance : FromJson (Exits ExitSchema) := ⟨EffectCodec.decodeExits⟩
instance : ToJson (Exits ExitSchema) := ⟨EffectCodec.exitsJ⟩

/-- **An effect as a declaration's result annotation states it**
(`Modifies<P, T>`, the Fragment's and the request's `stated`): a closed
footprint, whether it also bounds a throw, whether the result's array store
is fresh, and the store regions it excepts. The documents write its exits
(`StatedEffect.exits`); the effect it states is `StatedEffect.effect`. -/
structure StatedEffect where
  closed : Footprints.Closed
  onThrow : Bool
  fresh : Bool
  regions : List Footprints.ArgumentStoreRegion
  deriving Repr, DecidableEq

/-- **The exits a statement states** (`Exits.ofStated`). -/
def StatedEffect.exits (s : StatedEffect) : Exits ExitSchema :=
  Exits.ofStated s.closed s.onThrow s.fresh [] s.regions

/-- **The effect a statement states** (`Effect.ofStated`), with the
precondition `pre` its declaration states and no promise. -/
def StatedEffect.effect (s : StatedEffect) (pre : List HeapKnowledge.IndexFact := []) : Effect :=
  Effect.ofStated s.closed none s.onThrow s.fresh pre [] s.regions

theorem StatedEffect.effect_exits (s : StatedEffect) (pre : List HeapKnowledge.IndexFact) :
    (s.effect pre).exits = s.exits := rfl

/-- The argument store region an entry of a frame states, where it is one
(`ArgumentStoreRegion.entry`). -/
def storeRegionOf : Footprints.Region × Footprints.Change → Option Footprints.ArgumentStoreRegion
  | (.path p path k, .any) => if k = arrayStoreKey then some ⟨p, path⟩ else none
  | _ => none

/-- **The statement whose exits these are**, where there is one: the normal
frame's class bound and store regions, the fresh result, and a throw within
the frame where the exceptional exit is the normal frame and the frame is no
`⊤`. A statement is exactly such exits (checked: the statement's exits are
the exits read); others are refused. -/
def StatedEffect.ofExits (x : Exits ExitSchema) : Except String StatedEffect :=
  let Φ := x.normal.frame
  let s : StatedEffect := ⟨Φ.classBound, decide (x.exceptional = ⟨Φ, []⟩) && !decide (Φ = Parity.topEffect),
    decide (Parity.FormulaF.operation (.freshStore 0) ∈ x.normal.ensures), Φ.filterMap storeRegionOf⟩
  if s.exits = x then .ok s
  else .error "a statement states a closed frame with store regions, a throw within it or none, and a fresh result"

theorem StatedEffect.ofExits_exits {x : Exits ExitSchema} {s : StatedEffect} (h : StatedEffect.ofExits x = .ok s) :
    s.exits = x := by
  unfold StatedEffect.ofExits at h
  dsimp only at h
  split at h
  · cases h; assumption
  · cases h

/-- The closed bound a statement gives its unit's claim: its closed footprint
without store regions, `top` with them. -/
def StatedEffect.footprint (s : StatedEffect) : Footprints.Closed :=
  if s.regions.isEmpty then s.closed else .top

/-- **A claim's exits**: a closed frame on a normal return, and on a throw
the same frame where `onThrow`, `⊤` otherwise (`Exits.ofClosed`). -/
def classExits (c : Footprints.Closed) (onThrow : Bool) : Exits ExitSchema := Exits.ofClosed c onThrow

/-- **The closed frame and throw flag of a claim's exits**, where they are
such exits (checked: `classExits` of the result is the exits read); a throw
flag at the frame `⊤`, which states no exit of its own, reads as unset. -/
def classOfExits (x : Exits ExitSchema) : Except String (Footprints.Closed × Bool) :=
  let c := x.normal.frame.classBound
  let t := decide (x.exceptional = x.normal) && !decide (c = .top)
  if classExits c t = x then .ok (c, t)
  else .error "a claim states a closed frame, and a throw within it or none"

theorem classOfExits_sound {x : Exits ExitSchema} {c : Footprints.Closed} {t : Bool}
    (h : classOfExits x = .ok (c, t)) : classExits c t = x := by
  unfold classOfExits at h
  dsimp only at h
  split at h
  · cases h; assumption
  · cases h

end Verification.EffectJson
