import Verification.Types.CellUnion

/-! # Fragment type terms

The translation of the Fragment's source type terms, which travel as JSON
alongside the tree, into the labels of the type graph. Cell annotations and
claims use the same bounded contract decoder. -/
namespace Verification.Fragment
open Lean ProgramTyping PositiveRules LabelStore
open EquationGraphs (Tree)
open EquationStore (State)

/-- Validate a free required-parameter signature without projecting away object
requirements: the receiver contract, the parameters, the result, and the
contract of each further actual, for a signature that takes any number of
them. Every signature states its receiver; one indifferent to it states
`unknown`. -/
private def callableShape (a : Json) : Except String (Json × List Json × Json × Option Json × CallEffects.Effect) := do
  let rest := (a.getObjVal? "rest").toOption
  let effect := (a.getObjVal? "effect").toOption
  fieldsExactly a
    (["a","this","params","result","construct","array"] ++ (if rest.isSome then ["rest"] else []) ++
      (if effect.isSome then ["effect"] else []))
  if (← jStr (← jField a "a")) != "function" then throw "expected a function atom"
  for key in ["construct","array"] do
    let mode ← jStr (← jField a key)
    if mode != "unknown" && mode != "absent" then throw "unsupported function object mode"
  let args ← jArr a "params"
  let effect ← match effect with
    | some e => fromJson? e
    | none => pure .ordinary
  return (← jField a "this", args, ← jField a "result", rest, effect)

/-- The positions a rest parameter stands for: the required elements of its
tuple contract. A contract with optional or unbounded positions is not a fixed
number of further arguments, which is what the callable signature has to say,
so it is refused here rather than approximated. -/
def tupleRequired (j : Json) : Except String (List Json) := do
  fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then
    throw "a rest parameter needs a tuple contract of required positions"
  match ← jArr j "atoms" with
  | [atom] =>
    fieldsExactly atom ["a","required","optional","rest","readonly","presence"]
    if (← jStr (← jField atom "a")) != "array" then
      throw "a rest parameter needs a tuple contract of required positions"
    if !(← jArr atom "optional").isEmpty || (← jField atom "rest") != Json.null then
      throw "a rest parameter needs a tuple contract of required positions"
    jArr atom "required"
  | _ => throw "a rest parameter needs a tuple contract of required positions"

/-- The element of an array contract `T[]`, and with `readonly` of a
`readonly T[]` too; none for any other contract. A rest parameter's contract
may be either: the array a call collects is fresh, a `T[]`, and viewing it as
`readonly T[]` gives up only writes. -/
def arrayElement (j : Json) (readonly : Bool := false) : Option Json := do
  let .ok false := (← (j.getObjVal? "top").toOption).getBool? | none
  let .ok [atom] := (← (j.getObjVal? "atoms").toOption).getArr?.map (·.toList) | none
  let .ok "array" := (← (atom.getObjVal? "a").toOption).getStr? | none
  let .ok r := (← (atom.getObjVal? "readonly").toOption).getBool? | none
  if r && !readonly then none
  let .ok [] := (← (atom.getObjVal? "required").toOption).getArr?.map (·.toList) | none
  let .ok [] := (← (atom.getObjVal? "optional").toOption).getArr?.map (·.toList) | none
  let rest ← (atom.getObjVal? "rest").toOption
  if rest == .null then none else some rest

/-- Whether a record claim names an optional field. -/
private def hasOptional (atom : Json) : Bool :=
  match atom.getObjVal? "fields" with
  | .ok (.arr fs) => fs.any fun f => (f.getObjVal? "optional").toOption == some (.bool true)
  | _ => false

section
variable {ι : Type} [Labels ι]

mutual
/-- Callable operands recursively use the same value contracts as receivers
and record fields. Every union and overload arm is checked. -/
partial def callableType (j : Json) : SourceTypes.Lowering (Ty Tree) := do
  fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then return [← SourceTypes.use .source]
  let arms ← (← jArr j "atoms").mapM fun atom => do
    if (← jStr (← jField atom "a")) == "graph" then
      fieldsExactly atom ["a", "label"]
      let label : Tree ← fromJson? (← jField atom "label")
      if !StoreView.valid (← get) label then throw "graph label is absent"
      return [label]
    else if (← jStr (← jField atom "a")) == "function" then
      let signatures ← (← CellClaims.conjuncts atom).mapM fun a => do
        let (recv, args, result, rest, effect) ← callableShape a
        return (← callableType recv, ← args.mapM callableType, ← rest.mapM callableType,
          ← callableType result, effect)
      -- Fixed and variadic signatures of one value sit in one clause: each
      -- says which receivers and actual lists a caller may write.
      let fixed := signatures.filterMap fun (Rc, Ds, E, R, effect) =>
        if E.isNone then some ⟨Rc, Ds, R, effect⟩ else none
      -- A rest's type is the pack of any number of actuals at its element.
      let variadic ← signatures.filterMapM fun (Rc, Ds, E, R, effect) => E.mapM fun E => do
        return ⟨Rc, (Ds, [← SourceTypes.use (.pack ⟨[], [], some E, false, .dense⟩ [])]), R, effect⟩
      return [← SourceTypes.use (.arrs fixed.eraseDups variadic.eraseDups)]
    else if (← jStr (← jField atom "a")) == "constructor" then
      -- A construct signature: what a class meets and no plain function does.
      -- A generic class's instances form one conjunction: each is a signature.
      -- A generic class's static fields, the same in each, name none of its
      -- binders: the first's are the class value's. A signature without an
      -- effect states the ordinary one, as a function atom's does.
      let parts ← (← CellClaims.conjuncts atom).mapM fun a => do
        let hasStatics := (a.getObjVal? "statics").isOk
        let effect := (a.getObjVal? "effect").toOption
        fieldsExactly a (["a", "params", "result"] ++ (if hasStatics then ["statics"] else []) ++
          (if effect.isSome then ["effect"] else []))
        let effect : CallEffects.Effect ← match effect with
          | some e => fromJson? e
          | none => pure .ordinary
        let statics ← if !hasStatics then pure [] else (← jArr a "statics").mapM fun f => do
          let readonly := (f.getObjVal? "readonly").isOk
          fieldsExactly f (["name", "type"] ++ (if readonly then ["readonly"] else []))
          return (← PropKey.decode (← jField f "name"), readonly, ← callableType (← jField f "type"))
        return ((⟨(), ← (← jArr a "params").mapM callableType, ← callableType (← jField a "result"),
          effect⟩ : CallEffects.MethodArrow (Ty Tree)), statics)
      let statics := (parts.head?.map (·.2)).getD []
      if parts.any (·.2 != statics) then throw "a class value's instances state the same static fields"
      -- A class value is an ordinary object: a static field's role is `field`.
      let fields : List (Stored (Ty Tree)) :=
        statics.filterMap fun (k, r, t) => if r then none else some (k, .field, t)
      let views := statics.filterMap fun (k, r, t) => if r then some (k, t) else none
      return [← SourceTypes.use (.ctors (parts.map (·.1)) [] fields [] views)]
    else if ["array", "store"].contains (← jStr (← jField atom "a")) then
      return [← arrayType atom]
    else if (← jStr (← jField atom "a")) == "record" &&
        (atom.getObjVal? "indexSignature").toOption.isSome then
      fieldsExactly atom
        ["a", "fields", "indexes", "indexSignature", "call", "construct", "array"]
      -- Keep named invariants and readonly views alongside the index view in
      -- one clause. A mutable named field has one lifetime contract; a
      -- readonly named field contributes no write capability.
      let fields ← (← jArr atom "fields").mapM fun field => do
        fieldsExactly field ["name", "optional", "read", "write"]
        let name ← jStr (← jField field "name")
        if name == SourceTypes.storeField then
          throw "the array store is internal, not a source property"
        if ← (← jField field "optional").getBool? then
          throw "optional named fields with a string index signature are not yet in the source fragment"
        let read ← callableType (← jField field "read")
        let write ← jField field "write"
        if write == Json.mkObj [("top", toJson false), ("atoms", toJson ([] : List Json))] then
          return (name, read, false)
        let written ← callableType write
        if read != written then
          throw "a mutable named field needs one fixed read/write contract"
        return (name, read, true)
      if (fields.map fun (name, _, _) => name).eraseDups.length != fields.length then
        throw "duplicate named field in an indexed object"
      let index ← jField atom "indexSignature"
      fieldsExactly index ["read", "write"]
      -- A writable index has one fixed contract, as a mutable field has.
      let write ← jField index "write"
      let writable := write != Json.mkObj [("top", toJson false), ("atoms", toJson ([] : List Json))]
      if writable && write != (← jField index "read") then
        throw "a mutable string index signature needs one fixed read/write contract"
      for key in ["call", "construct", "array"] do
        let mode ← jStr (← jField atom key)
        if mode != "unknown" && mode != "absent" then
          throw "unsupported indexed object mode"
      let indexes ← jField atom "indexes"
      fieldsExactly indexes ["string", "number", "symbol"]
      for key in ["string", "number", "symbol"] do
        let mode ← jStr (← jField indexes key)
        if mode != "absent" && mode != "synthetic" then
          throw "unsupported synthetic index marker"
      let element ← callableType (← jField index "read")
      -- A TypeScript record type describes ordinary objects: role `field`.
      let invariant : List (Stored (Ty Tree)) := fields.filterMap fun (name, A, writable) =>
        if writable then some (name, .field, A) else none
      let views := fields.filterMap fun (name, A, writable) =>
        if writable then none else some (name, A)
      return [← SourceTypes.use (.dict invariant [] views [(.strings, element)] [] [] []
        (if writable then [(.strings, .field, element)] else []))]
    else if (← jStr (← jField atom "a")) == "record" && hasOptional atom then
      return [← optionalRecord atom]
    else if (← jStr (← jField atom "a")) == "record" then
      if (atom.getObjVal? "and").toOption.isSome then
        throw "a callable operand contract is one record, not a conjunction"
      let fields ← CellClaims.decodeShapes
        (Json.mkObj [("top", toJson false), ("atoms", toJson [atom])])
      let lowered ← fields.mapM fun (name, read, write) => do
        return (name, ← callableType read, ← callableType write)
      -- A TypeScript record type describes ordinary objects: role `field`.
      let invariant : List (Stored (Ty Tree)) :=
        lowered.filterMap fun (n, r, w) => if r == w then some (n, .field, w) else none
      let views := lowered.filterMap fun (n, r, w) => if r == w then none else some (n, r)
      return [← SourceTypes.use (.refs invariant [] views)]
    else
      let single := Json.mkObj [("top",toJson false),("atoms",toJson [atom])]
      -- The callable table grows as this walks it, so a numeric parameter or
      -- result is interned rather than refused for being outside the four
      -- fixed labels.
      SourceTypes.translateArm (← CellClaims.primitive single)
  return arms.flatten.mergeSort Labels.le |>.eraseDups

/-- An array type: a tuple contract on a store, held by an object in its store
field, invariantly or, for a readonly array, as a view. Element types are
lowered as callable operands are. -/
partial def arrayType (atom : Json) : SourceTypes.Lowering Tree := do
  fieldsExactly atom ["a","required","optional","rest","readonly","presence"]
  let required ← (← jArr atom "required").mapM callableType
  let optional ← (← jArr atom "optional").mapM callableType
  let restJson ← jField atom "rest"
  let rest ← if restJson == .null then pure none else do pure (some (← callableType restJson))
  let readonly ← (← jField atom "readonly").getBool?
  let presence ← fromJson? (← jField atom "presence")
  let store ← SourceTypes.use (.list ⟨required, optional, rest, readonly, presence⟩ [])
  if (← jStr (← jField atom "a")) == "store" then pure store
  else SourceTypes.use (SourceTypes.arrayOf (← get) store readonly)

/-- A record with optional fields. A field whose read and write agree is
writable under that one contract; any other is readonly, read at its read
type, as in a plain record. A required field is an invariant field or a view;
an optional one constrains its key only where the object has it, writable or
readonly. Absorption does not apply to these records. -/
partial def optionalRecord (atom : Json) : SourceTypes.Lowering Tree := do
  let fields ← CellClaims.decodeFields
    (Json.mkObj [("top",toJson false),("atoms",toJson [atom])])
  let lowered ← fields.mapM fun (name, read, write, optional) => do
    let r ← callableType read
    return (name, r, r != (← callableType write), optional)
  -- A TypeScript record type describes ordinary objects: role `field`.
  let invariant : List (Stored (Ty Tree)) :=
    lowered.filterMap fun (n, t, ro, o) => if o || ro then none else some (n, .field, t)
  let views := lowered.filterMap fun (n, t, ro, o) => if !o && ro then some (n, t) else none
  let optional := lowered.filterMap fun (n, t, ro, o) =>
    if o then some (⟨n, ro, .field, t⟩ : OptionalField (Ty Tree)) else none
  SourceTypes.use (.refs invariant [] views optional)

end

/-- Required record fields recursively admit value contracts. Decode both
capabilities through the same table before checking invariance, field by field. -/
private def cellContract (atom : Json) : SourceTypes.Lowering (CellUnion.Contract Tree) := do
  let fields ← CellClaims.decodeShapes
    (Json.mkObj [("top",toJson false),("atoms",toJson [atom])])
  fields.mapM fun (name, read, write) => do
    return ⟨name, ← callableType read, ← callableType write⟩

/-- Fields in canonical order, each once: conjunction is commutative and
idempotent, so two spellings of one contract intern as one label. -/
private def canonicalFields (fs : List (PropKey × Ty ι)) : List (PropKey × Ty ι) :=
  (fs.mergeSort fun a b => CellClaims.beforeFields [a] [b]).eraseDups

/-- Storage positions in canonical order, by key, role and label, each
once. -/
private def canonicalStored (fs : List (Stored (Ty ι))) : List (Stored (Ty ι)) :=
  (fs.mergeSort fun a b => CellClaims.beforeStored [a] [b]).eraseDups

/-- One object under every conjunct. Each conjunct is a record with views, as
a plain record arm is (`CellUnion.lower`): its invariant fields and its
readonly fields as views. The conjunction is their meet, the one a
declaration's intersection gets (`PositiveNormalization.meetLists`, POSITIVE-TYPES.md
"Conjunction and normalization"): one record operand holding every conjunct's invariant fields, and
every conjunct's views. -/
private def cellConjunction (atom : Json) : SourceTypes.Lowering Tree := do
  let clauses ← (← CellClaims.conjuncts atom).mapM fun part => do
    let c ← cellContract part
    if !CellUnion.viewed c then
      throw "cell read and write types do not describe the same invariant"
    let fields : List (Stored (Ty Tree)) :=
      (c.filter fun f => !CellUnion.readonly f).map fun f => (f.name, .field, f.read)
    let views := (c.filter CellUnion.readonly).map fun f => (f.name, f.read)
    return [(.refs fields [] views : PositiveNormalization.Clause (Ty Tree))]
  let some last := clauses.getLast? | throw "an empty conjunction is not a contract"
  match clauses.dropLast.foldr PositiveNormalization.meetLists last with
  | [.refs fields [] views [] [] []] =>
    SourceTypes.use (.refs (canonicalStored fields) [] (canonicalFields views))
  | _ => throw "a record conjunction meets as one record"

/-- A callable bag is one value satisfying both contracts, never a union. -/
private def callableObject (atom : Json) : SourceTypes.Lowering Tree := do
  fieldsExactly atom ["a","function","bag"]
  let fn ← jField atom "function"
  let (recv,args,result,rest,_) ← callableShape fn
  let Rc ← callableType recv
  let Ds ← args.mapM callableType
  let E ← rest.mapM callableType
  let R ← callableType result
  let c ← cellContract (← jField atom "bag")
  if !CellUnion.invariant c then
    throw "callable field requires an invariant read/write contract"
  -- A callable object's bag is an ordinary object's: role `field`.
  let bag : List (Stored (Ty Tree)) := c.map fun f => (f.name, .field, f.write)
  match E with
  | none => SourceTypes.use (.callable bag [] [⟨Rc,Ds,R,.ordinary⟩] [])
  | some E => SourceTypes.use (.callable bag [] [] [⟨Rc,(Ds,E),R,.ordinary⟩])

/-- Validate every union arm. Record alternatives may absorb a redundant
read/write contract into an existing invariant alternative (CellUnion.normalize_exact).
Other unsupported arms reject the whole type; no projection is allowed.
Record fields and arrow operands use the same recursive contract decoder. -/
def translate (j : Json) : SourceTypes.Lowering (Ty Tree) := do
  if j == Json.mkObj [("unsupported", toJson true)] then
    throw "type claim unavailable from producer"
  fieldsExactly j ["top","atoms"]
  -- `unknown` is semantic top: every value, and no operation through it.
  if ← (← jField j "top").getBool? then return [← SourceTypes.use .source]
  let atoms ← jArr j "atoms"
  let tagged ← atoms.mapM fun atom => do return (← jStr (← jField atom "a"),atom)
  -- A conjunction is one arm of the union, not a union of its own, so each
  -- contributes a single label. Absorption applies to the plain arms, which is
  -- where two contracts can subsume one another.
  let (conjoined, plain) :=
    ((tagged.filter (fun p => p.1 == "record")).map (·.2)).partition
      (fun a => (a.getObjVal? "and").toOption.isSome)
  let (indexed, plain) := plain.partition
    (fun a => (a.getObjVal? "indexSignature").toOption.isSome)
  let (withOptional, plain) := plain.partition hasOptional
  let optionals ← withOptional.mapM fun a => do return [← optionalRecord a]
  let records ← CellUnion.lower (← plain.mapM cellContract)
  let dictionaries ← indexed.mapM fun atom =>
    callableType (Json.mkObj [("top", toJson false), ("atoms", toJson [atom])])
  let conjunctions ← conjoined.mapM fun a => do return [← cellConjunction a]
  let arms ← (tagged.filter (fun p => p.1 != "record")).mapM fun (_,atom) => do
    let single := Json.mkObj [("top",toJson false),("atoms",toJson [atom])]
    match ← jStr (← jField atom "a") with
    | "graph" =>
      fieldsExactly atom ["a", "label"]
      let label : Tree ← fromJson? (← jField atom "label")
      if !StoreView.valid (← get) label then throw "graph label is absent"
      return [label]
    | "callable" => return [← callableObject atom]
    | "constructor" => callableType single
    | "array" | "store" => return [← arrayType atom]
    | "function" => callableType single
    -- A number or string arm is interned, so `1` and `number` are separate
    -- labels and the singleton is below the family by the ordinary clause rules.
    | "number" | "numberlit" | "string" | "stringlit" | "void" | "bigint" | "bigintlit" | "symbol" =>
      SourceTypes.numberLabels (← CellClaims.primitive single)
    | _ => SourceTypes.translate (← CellClaims.primitive single)
  return (records ++ optionals ++ dictionaries ++ conjunctions ++ arms).flatten.mergeSort Labels.le |>.eraseDups

end

end Verification.Fragment
