import Verification.Source.Equations.Annotations

/-! Section references follow `RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-! ### Lowering a source for the source path -/

/-- A generic module value's type, its binders their name placeholders: a
function's signature (receiver, parameters, rest element and result), a
construct signature (parameters and result), or any other type. -/
inductive GenericType where
  | function (receiver : Option Union) (params : List Union) (rest : Option Union) (result : Union)
  /-- A generic class: its construct signatures, each its parameters, result
  and effect, every instance meeting all of them, and its static fields,
  each readonly or not, which name none of its binders. -/
  | construct (signatures : List (List Union × Union × CallEffects.Effect))
      (statics : List (PropKey × Bool × Union) := [])
  | other (type : Union)

def GenericType.map (f : Union → Union) : GenericType → GenericType
  | .function r ps e res => .function (r.map f) (ps.map f) (e.map f) (f res)
  | .construct ss fs => .construct (ss.map fun (ps, res, e) => (ps.map f, f res, e))
      (fs.map fun (k, r, t) => (k, r, f t))
  | .other t => .other (f t)

/-- A generic module value: a generic module function, a generic class or a
generic imported value. Its type and its binders' bounds have the binders
as their name placeholders; an instance substitutes them
(`EquationStore.rebind`). -/
structure GenericValue where
  name : String
  pos : Nat × Nat
  binders : List String
  resolution : List ResolutionSlots
  type : Except String GenericType
  bounds : List (String × Option Union)
  /-- The binders typing both a value and a rest's argument lists: each one's
  rest is its packed name's placeholder, which an instance gives the argument
  lists of the binder's array (`packedName`). -/
  packed : List String := []

/-- A source lowered for the source path. -/
structure SourceLowering where
  refusals : List (Span × String) := []
  /-- The store the units grow: the heads, hash-consed and compacted. -/
  store : State
  /-- Each annotation, by its path in the function tree. -/
  annotations : List (String × Union)
  /-- Each array or tuple annotation's parts, by its path. -/
  arrays : List (String × ArrayParts)
  /-- Each imported value's type, by its local name, with its span. -/
  values : List (String × (Nat × Nat) × Union)
  generics : List GenericValue
  /-- Each generic unit's binders, by its path: an owned parameter of the
  unit's head, with its declared bound over those parameters (`enterUnit`). -/
  units : List (String × List (String × Tree × Option Union))
  /-- The module initialization's binders: every generic class's, one per
  name, the first class's. -/
  initBinders : List (String × Tree × Option Union)
  /-- The claims document, its label lists spelled as trees (§9.2). -/
  claims : Json

/-- A generic value's type term: a function or construct signature by its
parts, so that several instances conjoin as one callable; any other type
whole. A rest is the pack of its element (`lowerRest`). -/
def genericType (ctx : Ctx) (term : Json) : M GenericType := do
  match (term.getObjValAs? String "k").toOption with
  | some "function" =>
    fieldsExactly term ["k", "receiver", "params", "rest", "result", "effect", "span"]
    let effect : CallEffects.Effect ← fromJson? (← field term "effect")
    if effect != .ordinary then return .other (← lowerType ctx term)
    let recv ← field term "receiver"
    let receiver ← if recv == .null then pure none else some <$> lowerType ctx recv
    let params ← (← arr term "params").toList.mapM (lowerType ctx)
    let restTerm ← field term "rest"
    -- A rest is its element's claim; a pack binder has no claim form.
    if kindOf restTerm == some "pack" then return .other (← lowerType ctx term)
    let rest ← if restTerm == .null then pure none else some <$> lowerType ctx restTerm
    return .function receiver params rest (← lowerType ctx (← field term "result"))
  | some "constructor" => constructorType term
  -- Several construct signatures of one generic class, under its binders:
  -- each a construct signature, all with the same static fields.
  | some "intersection" =>
    let parts ← arr term "parts"
    if parts.isEmpty || !parts.all (kindOf · == some "constructor") then return .other (← lowerType ctx term)
    fieldsExactly term ["k", "parts", "span"]
    let forms ← parts.toList.mapM constructorType
    let mut signatures := []
    let mut statics : Option (List (PropKey × Bool × Union)) := none
    for form in forms do
      match form with
      | .construct ss fs =>
        if statics.isSome && statics != some fs then
          throw s!"{ctx.site}: a generic class's construct signatures state the same static fields"
        statics := some fs
        signatures := signatures ++ ss
      | _ => return .other (← lowerType ctx term)
    return .construct signatures (statics.getD [])
  | _ => return .other (← lowerType ctx term)
where
  constructorType (term : Json) : M GenericType := do
    let hasStatics := (term.getObjVal? "statics").isOk
    fieldsExactly term (["k", "params", "rest", "result", "effect", "span"] ++
      (if hasStatics then ["statics"] else []))
    let effect : CallEffects.Effect ← fromJson? (← field term "effect")
    if (← field term "rest") != .null then return .other (← lowerType ctx term)
    let params ← (← arr term "params").toList.mapM (lowerType ctx)
    let statics ← if !hasStatics then pure [] else (← arr term "statics").toList.mapM fun f => do
      let readonly := (f.getObjVal? "readonly").isOk
      fieldsExactly f (["name", "type"] ++ (if readonly then ["readonly"] else []))
      if readonly then
        if (← field f "readonly") != .bool true then
          throw s!"{ctx.site}: a static field's readonly mark is `true`, left out otherwise"
      return (← PropKey.decode (← field f "name"), readonly, ← lowerType ctx (← field f "type"))
    return .construct [(params, ← lowerType ctx (← field term "result"), effect)] statics

/-- A type term with each rest typed by one of `names` typed by its packed
name instead. A nested scheme binding the name hides it. -/
partial def renamePacks (names : List String) (j : Json) : Json :=
  if names.isEmpty then j else
  match j with
  | .obj kvs =>
    if kindOf j == some "pack" then
      let operand := j.getObjValD "of"
      match kindOf operand, operand.getObjValAs? String "name" with
      | some "binder", .ok n =>
        if names.contains n then j.setObjVal! "of" (operand.setObjVal! "name" (.str (packedName n))) else j
      | _, _ => j.setObjVal! "of" (renamePacks names operand)
    else
      let hidden := if kindOf j == some "scheme" then
        ((j.getObjValAs? (Array Json) "binders").toOption.getD #[]).toList.filterMap
          fun b => (b.getObjValAs? String "name").toOption
        else []
      let inner := names.filter (!hidden.contains ·)
      Json.mkObj (kvs.toList.map fun (k, v) => (k, renamePacks inner v))
  | .arr xs => .arr (xs.map (renamePacks names))
  | j => j

/-- A module function's rest typed by one of its own type parameters,
`...args: T` (`{"k":"pack","of":{"k":"binder","name":"T"}}`): that parameter's
name and declared bound. -/
def packRest (f : Json) : Option (String × Json) := do
  let .ok params := f.getObjValAs? (Array Json) "params" | none
  let p ← params.back?
  if !(p.getObjVal? "rest").isOk then none
  let ty := p.getObjValD "type"
  if kindOf ty != some "pack" then none
  let of := ty.getObjValD "of"
  if kindOf of != some "binder" then none
  let .ok n := of.getObjValAs? String "name" | none
  let .ok tps := f.getObjValAs? (Array Json) "typeParams" | none
  let tp ← tps.find? fun tp => tp.getObjValD "name" == .str n
  return (n, tp.getObjValD "bound")

/-- A module function as its body sees it: a rest typed by its own type
parameter is the array the call collects at that parameter's bound, the
elements every instance's argument list has (PROGRAM-TYPING.md, "Judgments
and constructor views"). Its signature keeps the pack. -/
def restView (f : Json) : Json :=
  match packRest f, f.getObjValAs? (Array Json) "params" with
  | some (_, bound), .ok params =>
    let last := params.back!
    f.setObjVal! "params" (.arr (params.pop.push (last.setObjVal! "type" bound)))
  | _, _ => f

/-- Lower a generic module value's pieces with its binders as placeholders.
Its declared bounds are checked at each instance a call names
(`Scheme.moduleInstances`), not here. -/
private def genericOf (name : String) (pos : Nat × Nat) (path : String) (node : Json) (tps : Array Json)
    (type : List (String × Binding) → M GenericType) (packed : List String := []) : M GenericValue := do
  let (scope, _) ← bindNames [] [] node tps
  let scope := (← packed.mapM fun n => do
    return (packedName n, ({ pack := true, value := [← placeholder (packedName n) .arguments] } : Binding))) ++ scope
  let parameters ← sourceParameters tps
  let binders := parameters.flatMap fun (n, r) => ResolutionWire.ownedNames n r
  let t ← tryCatch (do return Except.ok (← type scope)) fun e => pure (.error e)
  let bounds ← tps.toList.mapM fun p => do
    let n ← (str p "name" : Except String String)
    let b := p.getObjValD "bound"
    let ctx : Ctx := { binders := scope, site := s!"{path}: the bound of {n}" }
    if (scope.lookup n).any (·.pack) then
      if b == .null then throw s!"{path}: an argument pack needs its bound"
      return (n, some (← packBound ctx b))
    if b == .null then return (n, some [← ground "source" sourceValueClauses])
    return (n, some (← lowerType ctx b))
  return { name, pos, binders, resolution := ResolutionWire.groups parameters, type := t, bounds, packed }

/-- Everything the source path lowers, in one run: the declarations, every
annotation, the imported values, the generic units' binders, the producer's
rows and the claims. -/
def lowerSource (ast claims : Json) : M (List (String × Union) × List (String × (Nat × Nat) × Union) ×
    List GenericValue × List (String × List (String × Tree × Option Union)) ×
    List (String × Tree × Option Union) × Json) := do
  primitives
  let ds := (← get).doc
  let excluded ← match ds[0]? with
    | some d =>
      if ImplicitDependency.arrayProto.selects d.identity then
        let names ← (← arr d.expression "fields").mapM fun f => do PropKey.decode (← field f "name")
        pure (RequestJson.arrayExcludedKeys names.toList)
      else pure (RequestJson.arrayExcludedKeys [])
    | none => pure (RequestJson.arrayExcludedKeys [])
  modify fun s => { s with excluded }
  -- Every declaration: heads now, aliases where they are used.
  for i in [:ds.size] do
    if ds[i]!.isHead then let _ ← declHead i
  -- The built-in array prototype.
  let proto ← protoLabel
  modify fun s => { s with proto := match proto with | .app h _ => some h | _ => none }
  drain
  -- Every written application's bound obligations.
  for entry in ← arr (ast.getObjValD "declarations") "applications" do
    writtenObligations entry
  let functionTrees := (ast.getObjValAs? (Array Json) "functions").toOption.getD #[]
  let annotations ← walk "/functions" [] [] (.arr (functionTrees.map restView))
  -- Generic module functions: their binders, and their types at them.
  let mut generics : List GenericValue := []
  let mut units : List (String × List (String × Tree × Option Union)) := []
  for (f, i) in functionTrees.toList.zipIdx do
    let tps := (f.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
    if tps.isEmpty then continue
    let path := s!"/functions/{i}"
    let _ ← enterUnit path [] (restView f) tps
    units := units ++ [(path, (((← get).unitBinders.lookup path).getD []))]
    let name ← str f "name"
    let pos ← (fromJson? (← field f "namePos") : Except String (Nat × Nat))
    generics := generics ++ [← genericOf name pos path f tps fun scope => do
      -- Its signature by its parameters' annotations: a rest's element, the
      -- claim of a rest being its element's (`Fragment.callableType`).
      let ctx : Ctx := { binders := scope, site := path }
      -- A rest typed by its own type parameter is that parameter as an
      -- argument pack, which each call instantiates.
      if (packRest f).isSome then
        let params ← arr f "params"
        if params.any (·.getObjValD "type" == .null) || f.getObjValD "retType" == .null then
          throw s!"{path}: a generic module function's type needs every parameter's and its result's annotation"
        return .other (← lowerType ctx (Json.mkObj [("k", .str "function"), ("receiver", .null),
          ("params", .arr (params.pop.map (·.getObjValD "type"))), ("rest", params.back!.getObjValD "type"),
          ("result", f.getObjValD "retType"), ("effect", toJson CallEffects.Effect.ordinary),
          ("span", toJson (← (fromJson? (← field f "namePos") : Except String (Nat × Nat))))]))
      let mut params := []
      let mut rest := none
      for p in ← arr f "params" do
        let ty ← field p "type"
        if ty == .null then
          throw s!"{path}: a generic module function's type needs every parameter's annotation"
        if (p.getObjVal? "rest").isOk then
          if kindOf ty != some "array" || (← bool ty "readonly") then
            throw s!"{path}: a generic module function's rest parameter needs a mutable array contract"
          rest := some (← lowerType ctx (← field ty "element"))
        else params := params ++ [← lowerType ctx ty]
      let result ← field f "retType"
      if result == .null then throw s!"{path}: a generic module function's type needs its result's annotation"
      return .function none params rest (← lowerType ctx result)]
  let init := ast.getObjValD "init"
  let _classes ← classScope init
  let initBinders := ((← get).unitBinders.reverse.filter (·.1.startsWith "/init/")).flatMap (·.2)
    |>.foldl (fun (acc : List (String × Tree × Option Union)) (n, t, B) =>
      if (acc.lookup n).isSome then acc else acc ++ [(n, t, B)]) []
  -- The top-level code reads every generic class's binders by name, each
  -- with its declared bound, as a class's own code does.
  let ctors : List Json := match init with
    | .arr sts => sts.toList.flatMap fun st => match st.getObjVal? "bindings" with
      | .ok (.arr bs) => bs.toList.filterMap fun b =>
        let c := b.getObjValD "init"
        if (c.getObjValAs? String "k").toOption == some "ctor" &&
            ((c.getObjValAs? (Array Json) "typeParams").toOption.getD #[]).size > 0 then some c else none
      | _ => []
    | _ => []
  let (initScope, initBounds) ← ctors.foldlM (fun (acc : List (String × Binding) × List (Tree × Union)) c => do
    let tps := (c.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
    let (scope, bounds) ← bindNames [] [] c tps
    let fresh := scope.filter fun (n, _) => (acc.1.lookup n).isNone
    return (acc.1 ++ fresh, acc.2 ++ bounds.filter fun (q, _) => !acc.2.any (·.1 == q))) ([], [])
  let initAnnotations ← walk "/init" initScope initBounds init
  -- Generic classes: their construct signatures at their binders.
  let .arr sts := init | throw "the module initialization is a list"
  for (st, si) in sts.toList.zipIdx do
    if (st.getObjValAs? String "k").toOption != some "const" then continue
    let .ok (.arr bs) := st.getObjVal? "bindings" | continue
    for (b, bi) in bs.toList.zipIdx do
      let ctor := b.getObjValD "init"
      if (ctor.getObjValAs? String "k").toOption != some "ctor" then continue
      let tps := (ctor.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
      if tps.isEmpty then continue
      let path := s!"/init/{si}/bindings/{bi}"
      let name ← str b "name"
      let pos ← (fromJson? (← field b "namePos") : Except String (Nat × Nat))
      -- A binder typing both a value and a rest's argument lists in the
      -- class's construct signature: its rest reads its packed name, which
      -- each instance gives the argument lists of its array (`instancePack`).
      let packed := tps.toList.filterMap fun p => do
        let n ← (p.getObjValAs? String "name").toOption
        let u := binderUse n (b.getObjValD "annot")
        if u.pack && u.value then some n else none
      generics := generics ++ [← genericOf name pos path ctor tps (packed := packed) fun scope => do
        genericType { binders := scope, site := s!"{path}/annot" } (← field b "annot")]
  -- Imported values: a generic one is instantiated at each call.
  let mut values := []
  let document := ast.getObjValD "declarations"
  for (v, vi) in ((document.getObjValAs? (Array Json) "values").toOption.getD #[]).toList.zipIdx do
    fieldsExactly v ["binding", "declaration", "construct", "typeParams", "type"]
    let binding ← field v "binding"
    fieldsExactly binding ["local", "imported", "specifier", "span"]
    let name ← str binding "local"
    let span ← (fromJson? (← field binding "span") : Except String (Nat × Nat))
    let _ ← bool v "construct"
    let path := s!"/declarations/values/{vi}"
    let tps ← arr v "typeParams"
    if tps.isEmpty then
      values := values ++ [(name, span, ← lowerType { site := path } (← field v "type"))]
    else
      -- A binder typing both a value and a rest's argument lists: its rest
      -- reads its packed name (PROGRAM-TYPING.md, "Judgments and constructor
      -- views").
      let packed := tps.toList.filterMap fun p => do
        let n ← (p.getObjValAs? String "name").toOption
        let u := binderUse n (v.getObjValD "type")
        if u.pack && u.value then some n else none
      let v := renamePacks packed v
      let _ ← enterUnit path [] v tps
      units := units ++ [(path, (((← get).unitBinders.lookup path).getD []))]
      let generic ← genericOf name span path v tps (packed := packed) fun scope => do
        genericType { binders := scope, site := path } (← field v "type")
      generics := generics ++ [generic]
  -- The stable non-thenable family resolution descriptors are relative to:
  -- the intrinsic module's `%Stable%`, by its declaration identity.
  for d in ds do
    if ImplicitDependency.stable.selects d.identity then
      if !d.parameters.isEmpty || !d.bases.isEmpty then
        throw "the stable-value intrinsic takes no parameters"
      let stable ← lowerType { site := "/declarations/definitions/%Stable%" } d.expression
      modify fun s => { s with nativeStable := some stable }
  -- The producer's rows and the claims.
  let types ← arr claims "types"
  let P ← (producerRows types : Except String ProducerRows)
  modify fun s => { s with rows := P }
  -- Rows 0 to 3 are the primitive values: null, true, false, undefined.
  let primitives : List (GraphRow Nat) := [.clauses [.nul], .clauses [.boolLit true],
    .clauses [.boolLit false], .clauses [.undef]]
  if types.toList.take 4 != primitives.map toJson then
    throw "invalid source claims: the type table must start with the primitives"
  let claims ← documentForm (fun A => do return unionJson (← claimUnion [] A)) claims
  drain
  return (annotations ++ initAnnotations, values, generics, units, initBinders, claims)


end Verification.EquationLowering
