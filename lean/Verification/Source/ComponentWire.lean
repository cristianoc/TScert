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

/-- **A declared type's shape** (`TypeShapeAst`): what decides whether a
position of that type is read-only throughout. A record's members are each
`(readonly, field, type)`, a field a property or an index signature; a
named type is the family's, by its index in `types`. -/
inductive Shape where
  | primitive
  | unknown
  | function
  | sealed
  | other
  | readonlyArray (e : Shape)
  | array (e : Shape)
  | tuple (readonly : Bool) (es : List Shape)
  | record (ms : List (Bool × Bool × Shape))
  | union (ps : List Shape)
  | inter (ps : List Shape)
  | named (i : Nat)
  deriving Repr, Inhabited

/-- A named type of the family: its module, name, span and definition. -/
structure TypeRow where
  module : String
  name : String
  pos : Span
  definition : Shape
  deriving Repr

/-- A code of the family: its innermost component, its closure's site, its
parameters' values with their spans, its receiver's and result's values,
and whether it is an arrow function, which has no receiver of its own. -/
structure Code where
  module : String
  pos : Span
  component : Nat
  site : Option Nat
  params : List (Nat × Span × Option Shape)
  receiver : Nat
  result : Nat
  resultType : Option Shape
  arrow : Bool
  deriving Repr

/-- An allocation site: its kind, its records' keys, its contents' value,
and its mark for each component enclosing its code, innermost first. -/
structure Site where
  module : String
  pos : Span
  kind : SiteKind
  keys : List String
  anyKey : Bool
  contents : Nat
  marks : List (Nat × Mark)
  deriving Repr

/-- What a value of the flow includes: a site's storage, another value, what
a value's storage holds, or a value entering a component from outside. -/
inductive Source where
  | site (s : Nat)
  | value (v : Nat)
  | read (v : Nat)
  | incoming (c : Nat)
  | incomingReadOnly (c : Nat)
  deriving Repr, BEq

/-- A value's possible sites, by index, the components it may enter from
outside at a writable position (`incoming`) and reached read-only from a
crossing in at a read-only type (`incomingReadOnly`), and what the code's
statements make it include. -/
structure Value where
  module : String
  pos : Span
  sites : List Nat
  incoming : List Nat
  incomingReadOnly : List Nat
  sources : List Source
  deriving Repr

/-- A store: the value written (`none` a primitive) into the receiver's
fields at `key` (`none` a computed key; `element` an array's element or a
native's write); `initial` a field's initial value in the record it
allocates. -/
structure Store where
  module : String
  place : Span
  component : Nat
  receiver : Nat
  key : Option String
  element : Bool
  stored : Option Nat
  initial : Bool
  deriving Repr

structure Arg where
  value : Nat
  spread : Bool
  place : Span
  type : Option Shape
  deriving Repr

/-- A native's result site, the values its arguments pass, which it may
write into its receiver, the values it is given, its receiver's among them,
and those it may return. -/
structure Native where
  site : Nat
  passed : Nat
  given : Nat
  all : Nat
  member : Bool
  fresh : Bool
  primitiveElements : Bool
  deriving Repr

/-- A call: its callee's, receiver's, arguments' and result's values, the
codes it may run, the instance a `new` allocates, a native's values. -/
structure Call where
  module : String
  place : Span
  component : Nat
  callee : Nat
  receiver : Option Nat
  args : List Arg
  result : Nat
  targets : List Nat
  inst : Option Nat
  native : Option Native
  deriving Repr

/-- A value thrown or caught, a binding a module or a closure holds (its
holder the component), at its place. -/
structure Place where
  module : String
  place : Span
  component : Nat
  value : Nat
  name : String
  deriving Repr

/-- A module binding a module exports, out of each of `components`. -/
structure Export where
  module : String
  place : Span
  name : String
  components : List Nat
  value : Nat
  type : Option Shape
  deriving Repr

inductive SuspensionKind where
  | await
  | yield
  | async
  | generator
  deriving DecidableEq, Repr

structure Suspension where
  module : String
  place : Span
  component : Nat
  kind : SuspensionKind
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
  deriving Repr, BEq

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
  stores : List Store
  calls : List Call
  throws : List Place
  catches : List Place
  holds : List Place
  exports : List Export
  thrown : Option Nat
  suspensions : List Suspension
  types : List TypeRow
  escapes : List Escape
  clients : List Clients
  guarantees : List Guarantee

/-- The empty family: no component. -/
def Components.empty : Components := ⟨[], [], [], [], [], [], [], [], [], [], [], none, [], [], [], [], []⟩

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

/-- A shape, its nesting bounded by `fuel`. -/
def decodeShape : Nat → Json → Except String Shape
  | 0, _ => throw "a type's shape nests too deeply"
  | n + 1, j => do
    match j with
    | .str "primitive" => pure .primitive
    | .str "unknown" => pure .unknown
    | .str "function" => pure .function
    | .str "sealed" => pure .sealed
    | .str "other" => pure .other
    | .obj _ =>
      if let .ok e := j.getObjVal? "readonlyArray" then
        fieldsExactly j ["readonlyArray"]; return .readonlyArray (← decodeShape n e)
      if let .ok e := j.getObjVal? "array" then
        fieldsExactly j ["array"]; return .array (← decodeShape n e)
      if let .ok t := j.getObjVal? "tuple" then
        fieldsExactly j ["tuple"]
        fieldsExactly t ["readonly", "elements"]
        return .tuple (← (← jField t "readonly").getBool?) (← (← jArr t "elements").mapM (decodeShape n))
      if let .ok r := j.getObjVal? "record" then
        fieldsExactly j ["record"]
        let ms ← (← r.getArr?).toList.mapM fun m => do
          fieldsExactly m ["readonly", "field", "type"]
          return ((← (← jField m "readonly").getBool?), (← (← jField m "field").getBool?), ← decodeShape n (← jField m "type"))
        return .record ms
      if let .ok u := j.getObjVal? "union" then
        fieldsExactly j ["union"]; return .union (← (← u.getArr?).toList.mapM (decodeShape n))
      if let .ok u := j.getObjVal? "intersection" then
        fieldsExactly j ["intersection"]; return .inter (← (← u.getArr?).toList.mapM (decodeShape n))
      if let .ok i := j.getObjVal? "named" then
        fieldsExactly j ["named"]; return .named (← i.getNat?)
      throw "no type shape"
    | _ => throw "no type shape"

def shapeLimit : Nat := 64

def jOptShape (j : Json) (k : String) : Except String (Option Shape) := do
  let v ← jField j k
  if v == .null then return none
  return some (← decodeShape shapeLimit v)

def decodeCode (j : Json) : Except String Code := do
  fieldsExactly j ["module", "pos", "component", "site", "params", "receiver", "result", "resultType", "arrow"]
  let params ← (← jArr j "params").mapM fun p => do
    fieldsExactly p ["value", "at", "type"]
    return (← jNat p "value", ← jSpanAt (← jField p "at"), ← jOptShape p "type")
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "pos"), ← jNat j "component", ← jOptNat j "site", params,
    ← jNat j "receiver", ← jNat j "result", ← jOptShape j "resultType", ← jBoolAt j "arrow"⟩

def decodeSite (j : Json) : Except String Site := do
  fieldsExactly j ["module", "pos", "kind", "keys", "anyKey", "contents", "marks"]
  let marks ← (← jArr j "marks").mapM fun m => do
    fieldsExactly m ["component", "mark"]
    return (← jNat m "component", ← markOf (← jStr (← jField m "mark")))
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "pos"), ← siteKindOf (← jStr (← jField j "kind")),
    ← (← jArr j "keys").mapM jStr, ← jBoolAt j "anyKey", ← jNat j "contents", marks⟩

def decodeSource (j : Json) : Except String Source := do
  match j.getObjVal? "site", j.getObjVal? "value", j.getObjVal? "read", j.getObjVal? "incoming",
      j.getObjVal? "incomingReadOnly" with
  | .ok s, _, _, _, _ => fieldsExactly j ["site"]; return .site (← s.getNat?)
  | _, .ok v, _, _, _ => fieldsExactly j ["value"]; return .value (← v.getNat?)
  | _, _, .ok v, _, _ => fieldsExactly j ["read"]; return .read (← v.getNat?)
  | _, _, _, .ok c, _ => fieldsExactly j ["incoming"]; return .incoming (← c.getNat?)
  | _, _, _, _, .ok c => fieldsExactly j ["incomingReadOnly"]; return .incomingReadOnly (← c.getNat?)
  | _, _, _, _, _ => throw "no source of a value"

def decodeValue (j : Json) : Except String Value := do
  fieldsExactly j ["module", "pos", "sites", "incoming", "incomingReadOnly", "from"]
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "pos"), ← jNatList j "sites", ← jNatList j "incoming",
    ← jNatList j "incomingReadOnly", ← (← jArr j "from").mapM decodeSource⟩

def jOptStr (j : Json) (k : String) : Except String (Option String) := do
  let v ← jField j k
  if v == .null then return none
  return some (← jStr v)

def decodeStore (j : Json) : Except String Store := do
  fieldsExactly j ["module", "at", "component", "receiver", "key", "element", "stored", "initial"]
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "at"), ← jNat j "component", ← jNat j "receiver",
    ← jOptStr j "key", ← jBoolAt j "element", ← jOptNat j "stored", ← jBoolAt j "initial"⟩

def decodeCall (j : Json) : Except String Call := do
  fieldsExactly j ["module", "at", "component", "callee", "receiver", "args", "result", "targets", "instance", "native"]
  let args ← (← jArr j "args").mapM fun a => do
    fieldsExactly a ["value", "spread", "at", "type"]
    return (⟨← jNat a "value", ← jBoolAt a "spread", ← jSpanAt (← jField a "at"), ← jOptShape a "type"⟩ : Arg)
  let n ← jField j "native"
  let native ← if n == .null then pure none else do
    fieldsExactly n ["site", "passed", "given", "all", "member", "fresh", "primitiveElements"]
    pure (some (⟨← jNat n "site", ← jNat n "passed", ← jNat n "given", ← jNat n "all", ← jBoolAt n "member",
      ← jBoolAt n "fresh", ← jBoolAt n "primitiveElements"⟩ : Native))
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "at"), ← jNat j "component", ← jNat j "callee",
    ← jOptNat j "receiver", args, ← jNat j "result", ← jNatList j "targets", ← jOptNat j "instance", native⟩

/-- A thrown or caught value (`named` false, no name) or a held binding. -/
def decodePlace (named : Bool) (j : Json) : Except String Place := do
  fieldsExactly j (["module", "at", "component", "value"] ++ if named then ["name"] else [])
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "at"), ← jNat j "component", ← jNat j "value",
    ← if named then jStr (← jField j "name") else pure ""⟩

def decodeExport (j : Json) : Except String Export := do
  fieldsExactly j ["module", "at", "name", "components", "value", "type"]
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "at"), ← jStr (← jField j "name"), ← jNatList j "components",
    ← jNat j "value", ← jOptShape j "type"⟩

def decodeTypeRow (j : Json) : Except String TypeRow := do
  fieldsExactly j ["module", "name", "pos", "definition"]
  return ⟨← jStr (← jField j "module"), ← jStr (← jField j "name"), ← jSpanAt (← jField j "pos"),
    ← decodeShape shapeLimit (← jField j "definition")⟩

def decodeSuspension (j : Json) : Except String Suspension := do
  fieldsExactly j ["module", "at", "component", "kind"]
  let kind ← match ← jStr (← jField j "kind") with
    | "await" => pure SuspensionKind.await
    | "yield" => pure .yield
    | "async" => pure .async
    | "generator" => pure .generator
    | k => throw s!"no suspension '{k}'"
  return ⟨← jStr (← jField j "module"), ← jSpanAt (← jField j "at"), ← jNat j "component", kind⟩

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
  let nv := F.values.length
  let ns := F.sites.length
  for c in F.codes do
    inRange "a code's component" c.component n
    for s in c.site do inRange "a code's site" s ns
    for (v, _, _) in c.params do inRange "a code's parameter" v nv
    inRange "a code's receiver" c.receiver nv
    inRange "a code's result" c.result nv
  for s in F.sites do
    for (c, _) in s.marks do inRange "a site's mark's component" c n
    inRange "a site's contents" s.contents nv
  for v in F.values do
    for s in v.sites do inRange "a value's site" s ns
    for c in v.incoming ++ v.incomingReadOnly do inRange "a value's incoming component" c n
    for x in v.sources do
      match x with
      | .site s => inRange "a source's site" s ns
      | .value w | .read w => inRange "a source's value" w nv
      | .incoming c | .incomingReadOnly c => inRange "a source's component" c n
  for x in F.crossings do
    inRange "a crossing's component" x.component n
    for v in x.value do inRange "a crossing's value" v nv
  for s in F.stores do
    inRange "a store's component" s.component n
    inRange "a store's receiver" s.receiver nv
    for v in s.stored do inRange "a store's value" v nv
  for c in F.calls do
    inRange "a call's component" c.component n
    for v in [c.callee, c.result] ++ c.receiver.toList ++ c.args.map (·.value) ++
        (c.native.map fun x => [x.passed, x.given, x.all]).getD [] do inRange "a call's value" v nv
    for t in c.targets do inRange "a call's target" t F.codes.length
    for s in c.inst.toList ++ (c.native.map (·.site)).toList do inRange "a call's site" s ns
  for p in F.throws ++ F.catches ++ F.holds do
    inRange "a place's component" p.component n
    inRange "a place's value" p.value nv
  for e in F.exports do
    for c in e.components do inRange "an export's component" c n
    inRange "an export's value" e.value nv
  for v in F.thrown do inRange "the thrown value" v nv
  for x in F.suspensions do inRange "a suspension's component" x.component n
  for e in F.escapes do inRange "an escape's component" e.component n

/-- **The fragment's family**, decoded and well formed. -/
def decode (j : Json) : Except String Components := do
  fieldsExactly j ["components", "codes", "sites", "values", "crossings", "stores", "calls", "throws", "catches", "holds",
    "exports", "thrown", "suspensions", "types", "escapes", "clients", "guarantees"]
  let F : Components := ⟨← (← jArr j "components").mapM decodeComponent, ← (← jArr j "codes").mapM decodeCode,
    ← (← jArr j "sites").mapM decodeSite, ← (← jArr j "values").mapM decodeValue,
    ← (← jArr j "crossings").mapM decodeCrossing, ← (← jArr j "stores").mapM decodeStore,
    ← (← jArr j "calls").mapM decodeCall, ← (← jArr j "throws").mapM (decodePlace false),
    ← (← jArr j "catches").mapM (decodePlace false), ← (← jArr j "holds").mapM (decodePlace true),
    ← (← jArr j "exports").mapM decodeExport, ← jOptNat j "thrown", ← (← jArr j "suspensions").mapM decodeSuspension,
    ← (← jArr j "types").mapM decodeTypeRow,
    ← (← jArr j "escapes").mapM decodeEscape,
    ← (← jArr j "clients").mapM decodeClients, ← (← jArr j "guarantees").mapM decodeGuarantee⟩
  F.wellFormed
  return F

/-- The empty family on the wire. -/
def emptyJson : Json := Json.mkObj [("components", .arr #[]), ("codes", .arr #[]), ("sites", .arr #[]),
  ("values", .arr #[]), ("crossings", .arr #[]), ("stores", .arr #[]), ("calls", .arr #[]), ("throws", .arr #[]),
  ("catches", .arr #[]), ("holds", .arr #[]), ("exports", .arr #[]), ("thrown", .null), ("suspensions", .arr #[]), ("types", .arr #[]),
  ("escapes", .arr #[]), ("clients", .arr #[]), ("guarantees", .arr #[])]

end Verification.ComponentWire
