import Verification.Source.EffectJson
import Verification.Types.Decode

/-! # A component family on the wire

The fragment's `components` (`tools/fragment.mts`, `ComponentsAst`): the
family of components the checked file's code lies in, and the proposals of
the read-only frame (docs/drafts/readonly-handles.md) about it, each fact at
the module and span of the code it is of. The decoder requires every object's
fields exactly and every index in range, and a family laminar by
construction: each component's parent an earlier component, a package's none,
a module's none or a package, a class's a module or a class. Each code's
innermost component is the ghost tag its frames carry (`ComponentTag`,
`Components.tagAt`). Nothing here is evidence: the read-only frame's checks
read these proposals and check them. -/
namespace Verification.ComponentWire
open Lean

inductive Kind where
  | package
  | module
  | klass
  deriving DecidableEq, Repr

/-- An entry of a component's interface: the code it names, by its module
and span, under the name the interface gives it. -/
structure Entry where
  name : String
  module : String
  pos : Span
  deriving Repr

/-- A component's interface: every entry, or why it is not known. -/
inductive Interface where
  | known (entries : List Entry)
  | unknown (reason : String)
  deriving Repr

structure Component where
  kind : Kind
  location : String
  pos : Option Span
  parent : Option Nat
  interface : Interface
  deriving Repr

/-- A component's mark for one of its allocation sites, in the order
`local ⊑ internal ⊑ exposed ⊑ released`. -/
inductive Mark where
  | local
  | internal
  | exposed
  | released
  deriving DecidableEq, Repr

def Mark.rank : Mark → Nat
  | .local => 0
  | .internal => 1
  | .exposed => 2
  | .released => 3

instance : LE Mark := ⟨fun a b => a.rank ≤ b.rank⟩
instance (a b : Mark) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.rank ≤ b.rank))

inductive SiteKind where
  | object
  | array
  | closure
  | instance
  | native
  deriving DecidableEq, Repr

structure Code where
  module : String
  pos : Span
  component : Nat
  deriving Repr

structure Site where
  module : String
  pos : Span
  kind : SiteKind
  keys : List String
  anyKey : Bool
  marks : List (Nat × Mark)
  deriving Repr

/-- A value's possible sites, by index, and the components it may enter
from outside. -/
structure Value where
  module : String
  pos : Span
  sites : List Nat
  incoming : List Nat
  deriving Repr

/-- The position a crossing passes its value at, the owner of its type. -/
inductive Position where
  | parameter (code : Span) (index : Nat)
  | receiver (code : Span)
  | result (code : Span)
  | argument (call : Span) (index : Nat)
  | callResult (call : Span)
  | thrown
  | caught
  | field (key : Option String)
  | binding (name : String)
  deriving Repr

inductive Direction where
  | into
  | out
  deriving DecidableEq, Repr

structure Crossing where
  module : String
  place : Span
  component : Nat
  direction : Direction
  position : Position
  readOnly : Bool
  value : Option Nat
  deriving Repr

inductive Via where
  | result
  | argument
  | throw
  | store
  deriving DecidableEq, Repr

structure Escape where
  module : String
  code : Span
  component : Nat
  via : Via
  place : Span
  deriving Repr

/-- The client obligation an exported type states: `@clients P` where
`stated`, else read-only (`[]`), a frame over `this` at position 0. -/
structure Clients where
  module : String
  name : String
  pos : Span
  stated : Bool
  frame : Footprints.Footprint

/-- A guarantee candidate: a type invariant, its facts of `this` at
position 0. -/
structure Guarantee where
  module : String
  name : String
  pos : Span
  facts : List HeapKnowledge.IndexFact

structure Components where
  components : List Component
  codes : List Code
  sites : List Site
  values : List Value
  crossings : List Crossing
  escapes : List Escape
  clients : List Clients
  guarantees : List Guarantee

/-- The empty family: no component. -/
def Components.empty : Components := ⟨[], [], [], [], [], [], [], []⟩

/-- **The family's nesting**: `inner` is nested in `outer` when `outer` is
on `inner`'s chain of parents, itself included. A parent is an earlier
component, so the chain is at most the family's length. -/
def Components.nested (F : Components) (inner outer : Nat) : Bool :=
  go F.components.length inner
where
  go : Nat → Nat → Bool
    | 0, c => c == outer
    | n + 1, c => c == outer || match (F.components[c]?).bind (·.parent) with
      | some p => go n p
      | none => false

/-- **The ghost tag of a code's frames**: the innermost component of the
code at `module` and `pos`, `none` for code the family does not describe. -/
def Components.tagAt (F : Components) (module : String) (pos : Span) : ComponentTag :=
  (F.codes.find? fun c => c.module == module && c.pos == pos).map (·.component)

/-! ## The decoder -/

def jSpanAt (j : Json) : Except String Span := do
  let a ← j.getArr?
  if h : a.size = 2 then return (← a[0].getNat?, ← a[1].getNat?)
  else throw "a span is a [start, end] pair"

def jNatList (j : Json) (k : String) : Except String (List Nat) := do
  (← jArr j k).mapM fun x => x.getNat?

def jBoolAt (j : Json) (k : String) : Except String Bool := do (← jField j k).getBool?

def jOptNat (j : Json) (k : String) : Except String (Option Nat) := do
  let v ← jField j k
  if v == .null then return none
  return some (← v.getNat?)

def kindOf (s : String) : Except String Kind :=
  match s with
  | "package" => pure .package
  | "module" => pure .module
  | "class" => pure .klass
  | _ => throw s!"no component kind '{s}'"

def markOf (s : String) : Except String Mark :=
  match s with
  | "local" => pure .local
  | "internal" => pure .internal
  | "exposed" => pure .exposed
  | "released" => pure .released
  | _ => throw s!"no mark '{s}'"

def siteKindOf (s : String) : Except String SiteKind :=
  match s with
  | "object" => pure .object
  | "array" => pure .array
  | "closure" => pure .closure
  | "instance" => pure .instance
  | "native" => pure .native
  | _ => throw s!"no site kind '{s}'"

def viaOf (s : String) : Except String Via :=
  match s with
  | "result" => pure .result
  | "argument" => pure .argument
  | "throw" => pure .throw
  | "store" => pure .store
  | _ => throw s!"no escape '{s}'"

def decodeEntry (j : Json) : Except String Entry := do
  fieldsExactly j ["name", "module", "pos"]
  return ⟨← jStr (← jField j "name"), ← jStr (← jField j "module"), ← jSpanAt (← jField j "pos")⟩

def decodeInterface (j : Json) : Except String Interface := do
  match j.getObjVal? "known" with
  | .ok k =>
    fieldsExactly j ["known"]
    fieldsExactly k ["entries"]
    return .known (← (← jArr k "entries").mapM decodeEntry)
  | .error _ =>
    fieldsExactly j ["unknown"]
    let u ← jField j "unknown"
    fieldsExactly u ["reason"]
    return .unknown (← jStr (← jField u "reason"))

def decodeComponent (j : Json) : Except String Component := do
  fieldsExactly j ["kind", "location", "pos", "parent", "interface"]
  let pos ← jField j "pos"
  return ⟨← kindOf (← jStr (← jField j "kind")), ← jStr (← jField j "location"),
    ← if pos == .null then pure none else some <$> jSpanAt pos, ← jOptNat j "parent",
    ← decodeInterface (← jField j "interface")⟩

def decodeCode (j : Json) : Except String Code := do
  fieldsExactly j ["module", "pos", "component"]
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "pos"), ← jNat j "component"⟩

def decodeSite (j : Json) : Except String Site := do
  fieldsExactly j ["module", "pos", "kind", "keys", "anyKey", "marks"]
  let marks ← (← jArr j "marks").mapM fun m => do
    fieldsExactly m ["component", "mark"]
    return (← jNat m "component", ← markOf (← jStr (← jField m "mark")))
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "pos"), ← siteKindOf (← jStr (← jField j "kind")),
    ← (← jArr j "keys").mapM jStr, ← jBoolAt j "anyKey", marks⟩

def decodeValue (j : Json) : Except String Value := do
  fieldsExactly j ["module", "pos", "sites", "incoming"]
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "pos"), ← jNatList j "sites", ← jNatList j "incoming"⟩

def decodePosition (j : Json) : Except String Position := do
  match j with
  | .str "thrown" => pure .thrown
  | .str "caught" => pure .caught
  | .obj _ =>
    if let .ok p := j.getObjVal? "parameter" then
      fieldsExactly j ["parameter"]
      fieldsExactly p ["code", "index"]
      return .parameter (← jSpanAt (← jField p "code")) (← jNat p "index")
    if let .ok p := j.getObjVal? "receiver" then
      fieldsExactly j ["receiver"]
      fieldsExactly p ["code"]
      return .receiver (← jSpanAt (← jField p "code"))
    if let .ok p := j.getObjVal? "result" then
      fieldsExactly j ["result"]
      fieldsExactly p ["code"]
      return .result (← jSpanAt (← jField p "code"))
    if let .ok p := j.getObjVal? "argument" then
      fieldsExactly j ["argument"]
      fieldsExactly p ["call", "index"]
      return .argument (← jSpanAt (← jField p "call")) (← jNat p "index")
    if let .ok p := j.getObjVal? "callResult" then
      fieldsExactly j ["callResult"]
      fieldsExactly p ["call"]
      return .callResult (← jSpanAt (← jField p "call"))
    if let .ok p := j.getObjVal? "field" then
      fieldsExactly j ["field"]
      fieldsExactly p ["key"]
      let k ← jField p "key"
      return .field (← if k == .null then pure none else some <$> jStr k)
    if let .ok p := j.getObjVal? "binding" then
      fieldsExactly j ["binding"]
      fieldsExactly p ["name"]
      return .binding (← jStr (← jField p "name"))
    throw "no crossing position"
  | _ => throw "no crossing position"

def decodeCrossing (j : Json) : Except String Crossing := do
  fieldsExactly j ["module", "at", "component", "direction", "position", "readOnly", "value"]
  let direction ← match ← jStr (← jField j "direction") with
    | "in" => pure Direction.into
    | "out" => pure Direction.out
    | d => throw s!"no direction '{d}'"
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "at"), ← jNat j "component", direction,
    ← decodePosition (← jField j "position"), ← jBoolAt j "readOnly", ← jOptNat j "value"⟩

def decodeEscape (j : Json) : Except String Escape := do
  fieldsExactly j ["module", "code", "component", "via", "at"]
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "code"), ← jNat j "component",
    ← viaOf (← jStr (← jField j "via")), ← jSpanAt (← jField j "at")⟩

def decodeClients (j : Json) : Except String Clients := do
  fieldsExactly j ["module", "name", "pos", "stated", "frame"]
  return ⟨← jStr (← jField j "module"), ← jStr (← jField j "name"), ← jSpanAt (← jField j "pos"),
    ← jBoolAt j "stated", ← EffectCodec.frameOf EffectCodec.nestingLimit (← jField j "frame")⟩

def decodeGuarantee (j : Json) : Except String Guarantee := do
  fieldsExactly j ["module", "name", "pos", "facts"]
  return ⟨← jStr (← jField j "module"), ← jStr (← jField j "name"), ← jSpanAt (← jField j "pos"),
    ← fromJson? (← jField j "facts")⟩

/-- **The family well formed**: each parent an earlier component, of the
kind that nests it (a package none, a module none or a package, a class a
module or a class), a span exactly where it is a class; every index of a
code, a site's mark, a value, a crossing and an escape in range. -/
def Components.wellFormed (F : Components) : Except String Unit := do
  let n := F.components.length
  for (c, i) in F.components.zipIdx do
    let parentKind : Option Kind := (c.parent.bind (F.components[·]?)).map (·.kind)
    match c.kind, parentKind, c.pos with
    | .package, none, none => pure ()
    | .module, none, none | .module, some .package, none => pure ()
    | .klass, some .module, some _ | .klass, some .klass, some _ => pure ()
    | _, _, _ => throw s!"component {i} is not nested as its kind is"
    if c.parent.any (· ≥ i) then throw s!"component {i}'s parent is not an earlier component"
  let inRange (what : String) (k bound : Nat) : Except String Unit :=
    if k < bound then pure () else throw s!"{what} {k} is out of range"
  for c in F.codes do inRange "a code's component" c.component n
  for s in F.sites do for (c, _) in s.marks do inRange "a site's mark's component" c n
  for v in F.values do
    for s in v.sites do inRange "a value's site" s F.sites.length
    for c in v.incoming do inRange "a value's incoming component" c n
  for x in F.crossings do
    inRange "a crossing's component" x.component n
    for v in x.value do inRange "a crossing's value" v F.values.length
  for e in F.escapes do inRange "an escape's component" e.component n

/-- **The fragment's family**, decoded and well formed. -/
def decode (j : Json) : Except String Components := do
  fieldsExactly j ["components", "codes", "sites", "values", "crossings", "escapes", "clients", "guarantees"]
  let F : Components := ⟨← (← jArr j "components").mapM decodeComponent, ← (← jArr j "codes").mapM decodeCode,
    ← (← jArr j "sites").mapM decodeSite, ← (← jArr j "values").mapM decodeValue,
    ← (← jArr j "crossings").mapM decodeCrossing, ← (← jArr j "escapes").mapM decodeEscape,
    ← (← jArr j "clients").mapM decodeClients, ← (← jArr j "guarantees").mapM decodeGuarantee⟩
  F.wellFormed
  return F

/-- The empty family on the wire. -/
def emptyJson : Json := Json.mkObj [("components", .arr #[]), ("codes", .arr #[]), ("sites", .arr #[]),
  ("values", .arr #[]), ("crossings", .arr #[]), ("escapes", .arr #[]), ("clients", .arr #[]),
  ("guarantees", .arr #[])]

end Verification.ComponentWire
