import Verification.Source.Claims.Wire
import Verification.Source.Claims.Schemes
import Verification.Source.Claims.Diagnostics
import Verification.Source.FragmentTypes

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)
section
variable {ι : Type} [Labels ι]

/-- A source's claims read into a store, and what the source's declarations
give its units: the source tree with its annotations in claim form, the
claims over the store's labels, the imported values at their declared types
and the generic module values. -/
structure Prepared where
  ast : Json
  document : Document EquationStore.State Tree
  /-- Each imported value: its name, its import's span and its declared type's labels. -/
  imported : List (String × Span × List Tree)
  generics : List Instantiable
  /-- Each generic function's binders, by its name and position: an owned
  parameter each, with its declared bound. -/
  units : List ((String × Span) × List (String × Tree × Option (List Tree)))
  /-- The module initialization's binders: every generic class's. -/
  initBinders : List (String × Tree × Option (List Tree))

/-- The claims are about the source: its file and its fingerprint. -/
def checkIdentity (d : Document EquationStore.State Tree) (ast : Json) (fileKey : String) : Except String Unit := do
  if d.file != fileKey || (← jStr (← jField ast "file")) != fileKey then throw "source claim file identity mismatch"
  if (← jStr (← jField ast "sourceSha256")) != d.sourceSha256 then throw "source claim fingerprint mismatch"

/-! ### The equation front

The source's declarations, annotations and claims are lowered in one run to
recursive equations (`EquationLowering.source`, RECURSIVE-EQUATIONS §8): the
store the units grow. Every annotation becomes its labels as graph atoms, a
binder its name's placeholder, which the unit or closure reading it binds
(`annotationAtScopes`, `Function.atRows`, `Scheme.closureRows`). -/

section
open EquationGraphs EquationLowering EquationStore

/-- A union as a claim: its labels as graph atoms. -/
def graphClaim (U : List Tree) : Json :=
  Json.mkObj [("top", toJson false), ("atoms", Json.arr (U.map fun l =>
    Json.mkObj [("a", toJson "graph"), ("label", Tree.toJson l)]).toArray)]

private def topClaim : Json := Json.mkObj [("top", toJson true), ("atoms", Json.arr #[])]

/-- An array or tuple annotation as the claim of its shape, its parts' labels
graph atoms: a reader of a rest parameter's reads its element there
(`Fragment.arrayElement`, `Fragment.tupleRequired`). -/
def arrayClaim (a : ArrayParts) : Json :=
  Json.mkObj [("top", toJson false), ("atoms", Json.arr #[Json.mkObj [("a", toJson "array"),
    ("required", Json.arr (a.required.map graphClaim).toArray),
    ("optional", Json.arr (a.optional.map graphClaim).toArray),
    ("rest", (a.rest.map graphClaim).getD .null), ("readonly", toJson a.readonly),
    ("presence", a.presence)]])]

/-- A claim's graph atoms' labels. -/
def claimLabels (j : Json) : Except String (List Tree) := do
  fieldsExactly j ["top", "atoms"]
  if ← (← jField j "top").getBool? then throw "a type argument is a ground type"
  (← jArr j "atoms").mapM fun a => do
    fieldsExactly a ["a", "label"]
    if (← jStr (← jField a "a")) != "graph" then throw "a type argument is a graph type"
    Tree.fromJson (← jField a "label")

/-- The source gate: a source states no internal graph label and no claim,
so the annotations lowering writes are the only ones the tree holds. -/
partial def sourceGate : Json → Except String Unit
  | .arr xs => xs.forM sourceGate
  | j@(.obj kvs) => do
    if (j.getObjVal? "a").toOption == some (.str "graph") then
      throw "source cannot state an internal graph label"
    if (j.getObjVal? "atoms").isOk then throw "a source annotation is a type term, not a claim"
    kvs.toList.forM fun (_, v) => sourceGate v
  | _ => pure ()

/-- A property key `{"symbol": i}` naming one of `tags`. -/
def isTagKey (tags : List Nat) (key : Json) : Bool :=
  match (key.getObjValAs? Nat "symbol").toOption with
  | some i => tags.contains i
  | none => false

/-- **The tag gate.** No object the source's code makes holds
`Symbol.toStringTag`: no allocation (a literal, a class's prototype or
instance), no class value's static and no write is keyed by it. The native
`Promise` contract requires it of a promise's prototype, so no such object, nor
an object whose prototype it is, meets that contract. -/
partial def tagGate (tags : List Nat) : Json → Except String Unit
  | .arr xs => xs.forM (tagGate tags)
  | j@(.obj kvs) => do
    let keyed := match (j.getObjValAs? String "k").toOption with
      | some "alloc" => ((j.getObjValAs? (Array Json) "fields").toOption.getD #[]).toList.map (fun (f : Json) => f.getObjValD "name")
      | some "ctor" => ((j.getObjValAs? (Array Json) "statics").toOption.getD #[]).toList.map (fun (f : Json) => f.getObjValD "name")
      | some "write" => [j.getObjValD "field"]
      | _ => []
    if keyed.any (isTagKey tags) then
      throw s!"an object the source makes is keyed by `Symbol.toStringTag` at {(j.getObjValD "pos").compress}: no object the program makes holds the tag the native `Promise` contract requires"
    kvs.toList.forM fun (_, v) => tagGate tags v
  | _ => pure ()

/-- **Computed keys.** A field marked `computed` is `(k satisfies ℓ, v)`, ℓ
a string or number literal type, and its key is the one ℓ converts to
(`ToPropertyKey`, a number's by its `ToString`): the key expression's check
at ℓ is what makes the field's key the key's value. -/
partial def computedGate : Json → Except String Unit
  | .arr xs => xs.forM computedGate
  | j@(.obj kvs) => do
    if (j.getObjValAs? String "k").toOption == some "alloc" then
      for f in (j.getObjValAs? (Array Json) "fields").toOption.getD #[] do
        if (f.getObjVal? "computed").toOption.isSome then
          let e := f.getObjValD "e"
          let left := e.getObjValD "left"
          if (e.getObjValAs? String "k").toOption != some "comma" ||
              (left.getObjValAs? String "k").toOption != some "cast" ||
              (left.getObjValAs? String "cast").toOption != some "satisfies" then
            throw "a computed key's field is its key's check at a literal, then its value"
          let spelled ← Fragment.computedKey (left.getObjValD "annot")
          let name := f.getObjValD "name"
          if name != Json.str spelled then
            throw s!"a computed key's field {name.compress} is not the key {(Json.str spelled).compress} its literal converts to"
    kvs.toList.forM fun (_, v) => computedGate v
  | _ => pure ()

/-- Whether a type term names the standard library's `PromiseLike`. -/
partial def namesPromiseLike : Json → Bool
  | .arr xs => xs.any namesPromiseLike
  | j@(.obj kvs) =>
    (match j.getObjVal? "reference" with
      | .ok r => (r.getObjValAs? String "name").toOption == some "PromiseLike" &&
          (((r.getObjValD "target").getObjValAs? String "module").toOption.getD "").startsWith "typescript/lib/"
      | .error _ => false) || kvs.toList.any fun (_, v) => namesPromiseLike v
  | _ => false

/-- **The native `Promise`'s tag.** The native `Promise` definition states
`Symbol.toStringTag`, listed by its identity, on its prototype as a readonly
`string`, and its `then` and `catch` name no `PromiseLike`, their callbacks'
results being native promises or other values. That no other prototype the
store states holds the tag is checked of the lowered heads
(`EquationStore.tagPrototypes`). -/
def tagDeclarations (document : Json) (tags : List Nat) : Except String Unit := do
  for d in ← jArr document "definitions" do
    let native := EquationLowering.ImplicitDependency.promise.selects (d.getObjValD "declaration")
    let expression := d.getObjValD "expression"
    if native then
      let fields := ((expression.getObjValD "prototype").getObjValAs? (Array Json) "fields").toOption.getD #[]
      if !fields.any (fun f => isTagKey tags (f.getObjValD "name") &&
          (f.getObjValAs? Bool "readonly").toOption == some true &&
          (f.getObjValAs? Bool "optional").toOption == some false &&
          ((f.getObjValD "type").getObjValAs? String "name").toOption == some "string") then
        throw "the native Promise contract states no readonly `Symbol.toStringTag` of type string on its prototype"
      if namesPromiseLike expression then
        throw "the native Promise contract names PromiseLike: its callbacks' results resolve as native promises only"

/-- Apply ordered replacements, rebuilding an array once for its children.
A replacement at the node discards all preceding edits beneath it. -/
private partial def setPaths (j : Json) (changes : List (List String × Json)) : Json := Id.run do
  let mut base := j
  let mut children : Std.HashMap String (List (List String × Json)) := {}
  for (path, value) in changes do
    match path with
    | [] => base := value; children := {}
    | key :: rest =>
      let key := if base matches .arr _ then (key.toNat?.map toString).getD key else key
      children := children.insert key ((rest, value) :: children.getD key [])
  if children.isEmpty then return base
  match base with
  | .arr xs => return .arr (xs.mapIdx fun i child => match children.get? (toString i) with
      | some edits => setPaths child edits.reverse
      | none => child)
  | .obj fields => return .obj (children.fold (fun obj key edits => match fields.get? key with
      | some child => obj.insert key (setPaths child edits.reverse)
      | none => obj) fields)
  | _ => return base

/-- A generic value's type at `θ`: its binders read as `θ` gives them, a
signature by its parts, so that the instances a unit's calls name conjoin
as one callable (`Scheme.moduleInstances`). -/
def genericClaim (T : EquationStore.State) (θ : List (String × List Tree)) : GenericType → Json
  | .function recv ps rest res effect guard =>
    let c (U : List Tree) : Json := graphClaim (normUnion (U.flatMap (rebind T θ)))
    let sig (r : Json) (eff : CallEffects.Effect) : Json :=
      Json.mkObj ([("a", toJson "function"),
        ("this", (recv.map c).getD topClaim), ("params", Json.arr (ps.map c).toArray)] ++
        (match rest with
          | some e => [("rest", c e)]
          | none => []) ++
        [("result", r), ("construct", toJson "unknown"), ("array", toJson "unknown")] ++
        (if eff == .ordinary then [] else [("effect", toJson eff)]))
    let plain := sig (c res) effect
    let atom := match guard with
      | some (promise, guardTy) =>
        let promisedEff : CallEffects.Effect :=
          { effect with
            exits := { effect.exits with normal := { effect.exits.normal with ensures := [] } },
            promise := some promise }
        plain.setObjVal! "and" (Json.arr #[sig (c guardTy) promisedEff])
      | none => plain
    Json.mkObj [("top", toJson false), ("atoms", Json.arr #[atom])]
  | .construct ss fs =>
    let c (U : List Tree) : Json := graphClaim (normUnion (U.flatMap (rebind T θ)))
    let statics := fs.map fun (k, r, U) => Json.mkObj ([("name", toJson k), ("type", c U)] ++
      (if r then [("readonly", toJson true)] else []))
    -- Each construct signature is an atom, the ordinary effect written by
    -- leaving it out, as a function atom's; several are one conjunction.
    let atom := fun ((ps, res, e) : List (List Tree) × List Tree × CallEffects.Effect) =>
      Json.mkObj ([("a", toJson "constructor"), ("params", Json.arr (ps.map c).toArray), ("result", c res)] ++
        (if e == .ordinary then [] else [("effect", toJson e)]) ++
        (if statics.isEmpty then [] else [("statics", Json.arr statics.toArray)]))
    let atoms := ss.map atom
    let first := match atoms with
      | [] => Json.mkObj []
      | [one] => one
      | one :: more => one.setObjVal! "and" (Json.arr more.toArray)
    Json.mkObj [("top", toJson false), ("atoms", Json.arr #[first])]
  | .other U => graphClaim (normUnion (U.flatMap (rebind T θ)))

private def emptyDeclarations : Json := Json.mkObj [("roots", Json.arr #[]),
  ("definitions", Json.arr #[]), ("values", Json.arr #[]), ("symbols", Json.arr #[]),
  ("applications", Json.arr #[])]

/-- **The equation front.** The source's declarations, its annotations and
the claims, lowered to one store; the source tree with its annotations in
claim form; the imported values at their declared types; the generic values
at the instances a unit names; and the generic units' binders. A declaration
the lowering refuses is refused at the unit requiring it, and a claim it
cannot read is an invalid document. A variance declaration that does not
check (§7.5) refuses the source at its heads. -/
def lowerEquationFront (ast claims : Json)
    (budget : PositiveCertificates.SearchBudget) (cache : EquationLowering.DefinitionCache := ∅) : Except String SourceLowering := do
  sourceGate (ast.getObjValD "functions")
  sourceGate (ast.getObjValD "init")
  let document ← jField ast "declarations"
  fieldsExactly document ["roots", "definitions", "values", "symbols", "applications"]
  -- A symbol key `{"symbol": i}` is the i-th listed `unique symbol` constant.
  let symbols ← jArr document "symbols"
  if symbols.eraseDups.length != symbols.length then
    throw "a unique symbol declaration is listed twice"
  let tags := EquationLowering.tagSymbols document
  tagGate tags (ast.getObjValD "functions")
  tagGate tags (ast.getObjValD "init")
  computedGate (ast.getObjValD "functions")
  computedGate (ast.getObjValD "init")
  tagDeclarations document tags
  let roots ← (← jArr document "roots").mapM fun root => do jStr (← jField (← jField root "binding") "local")
  if roots.eraseDups.length != roots.length then throw "duplicate declaration root name"
  -- A declaration failure belongs to the unit requiring the contract, not to
  -- an external library's byte offset misread as a span in this file.
  let firstClaimed := ((claims.getObjValAs? (Array Json) "functions").toOption.bind (·[0]?)).bind
    fun f => (f.getObjValAs? Span "namePos").toOption
  let contractSite := firstClaimed.getD (0, 0)
  let empty : EquationStore.State := { doc := #[] }
  (EquationLowering.source ast claims budget cache).mapError fun failure => match failure with
    | .refusal reason =>
      if reason.startsWith "source claims" || reason.startsWith "invalid source claims" ||
          reason.startsWith "a label" || reason.startsWith "a producer's row" then
        s!"invalid source claims: {reason}"
      else sourceRefusal empty contractSite .bindingAnnotation
        s!"the declarations required by this unit cannot be interpreted: {reason}"
    | .bound T pos site actual expected outcome =>
      let pos := pos.getD contractSite
      directFailure T ⟨pos, .bindingAnnotation, .subtyping pos actual expected⟩ outcome (some site)
/-- Apply one validated equation lowering to a source. The store determines
all annotation labels and all subsequent positive and negative intern lookups. -/
def prepareEquationFront (ast : Json) (fileKey : String) (L : SourceLowering) : Except String Prepared := do
  let d ← decodeDocument L.store L.claims
  checkIdentity d ast fileKey
  let functions := (ast.getObjValAs? (Array Json) "functions").toOption.getD #[]
  let arrays := Std.HashMap.ofList L.arrays.reverse
  let ast := setPaths ast (L.annotations.map fun (path, U) =>
    ((path.splitOn "/").drop 1, match arrays.get? path with
      | some a => arrayClaim a
      | none => graphClaim U))
  let ast := ast.setObjVal! "declarations" emptyDeclarations
  let imported := L.values
  let instantiate (g : GenericValue) (closed : Option (Footprints.Closed × Bool))
      (θ : List (String × Json)) (T : EquationStore.State) :
      Except String ((Json × List (String × Option Json)) × EquationStore.State) := do
    let θ ← θ.mapM fun (n, j) => do return (n, ← claimLabels j)
    let (T, θ) ← g.packed.foldlM (fun (T, θ) n => do
      let some X := θ.lookup n | throw s!"no type argument for '{n}'"
      let (T, P) ← SourceTypes.instancePack T X n
      return (T, θ ++ [(EquationLowering.packedName n, P)])) (T, θ)
    let t ← g.type
    let t := match closed with
      | some (fp, ot) => t.withClosed fp ot
      | none => t
    let bounds := g.bounds.map fun (n, B) =>
      (n, B.map fun B => graphClaim (normUnion (B.flatMap (rebind T θ))))
    return ((genericClaim T θ t, bounds), T)
  let generics := L.generics.map fun g =>
    let initial := if !g.ownFunction then none
      else (d.functions.find? fun c => c.name == g.name && c.namePos == g.pos).map fun c => (c.footprint, c.onThrow)
    ({ name := g.name, pos := g.pos, binders := g.binders,
       widenBinders := g.widenBinders,
       resolution := g.resolution,
       instantiate := instantiate g initial,
       withFootprint := if g.ownFunction then some (fun fp ot => instantiate g (some (fp, ot))) else none } :
      Instantiable)
  let units := L.units.filterMap fun (path, bs) => do
    let i ← (path.dropPrefix? "/functions/").bind (·.toString.toNat?)
    let f ← functions[i]?
    let name ← (f.getObjValAs? String "name").toOption
    let pos ← (f.getObjValAs? Span "namePos").toOption
    return ((name, pos), bs)
  return ⟨ast, d, imported, generics, units, L.initBinders⟩

def equationFront (ast claims : Json) (fileKey : String)
    (budget : PositiveCertificates.SearchBudget := {}) : Except String Prepared := do
  prepareEquationFront ast fileKey (← lowerEquationFront ast claims budget)

end


end

end Verification.SourceClaimJson
