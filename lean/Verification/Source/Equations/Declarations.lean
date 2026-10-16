import Verification.Source.Equations.Trees

/-! Section references follow `RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-! ### The declaration document -/

structure Definition where
  identity : Json
  name : String
  parameters : Array Json
  bases : Array Json
  expression : Json
  deriving Inhabited

def field (j : Json) (name : String) : Except String Json := j.getObjVal? name
def arr (j : Json) (name : String) : Except String (Array Json) := do (← field j name).getArr?
def str (j : Json) (name : String) : Except String String := do (← field j name).getStr?
def bool (j : Json) (name : String) : Except String Bool := do (← field j name).getBool?

def definitions (document : Json) : Except String (Array Definition) := do
  (← arr document "definitions").mapM fun j => do
    fieldsExactly j ["declaration", "parameters", "bases", "expression"]
    let identity ← field j "declaration"
    return ⟨identity, ← str identity "name", ← arr j "parameters", ← arr j "bases", ← field j "expression"⟩

/-- `ArrayProto`'s identity, the synthetic declaration array types name. -/
def arrayProtoIdentity : Json :=
  Json.mkObj [("module", "tscert/array-prototype"), ("name", "ArrayProto"), ("span", toJson [0, 0])]

/-- An object term's index signatures, by the keys each constrains. -/
def indexSignatures (term : Json) : List (String × IndexKeys × Json) :=
  [("stringIndex", IndexKeys.strings, term.getObjVal? "stringIndex"),
   ("numberIndex", .numeric, term.getObjVal? "numberIndex"),
   ("symbolIndex", .symbols, term.getObjVal? "symbolIndex")].filterMap
    fun (name, keys, index) => match index with
      | .ok .null | .error _ => none
      | .ok index => some (name, keys, index)

def objectMembers (term : Json) : List String :=
  ["k", "fields", "stringIndex", "calls", "span"] ++
    ((indexSignatures term).map (·.1)).filter (· != "stringIndex") ++
    if (term.getObjVal? "prototype").toOption.isSome then ["prototype"] else []

def kindOf (term : Json) : Option String := (term.getObjValAs? String "k").toOption

/-- A declaration is a head when its equation is an object type, an
interface's or class's, or it has bases. Any other is an alias, inlined at
each use (§8.3). -/
def Definition.isHead (d : Definition) : Bool :=
  kindOf d.expression == some "object" || !d.bases.isEmpty

/-- Uses of one method binder: as a value, as an argument pack. A nested
scheme binding the same name shadows it. -/
structure BinderUse where
  value : Bool := false
  pack : Bool := false
  deriving Inhabited, BEq

private def BinderUse.merge (a b : BinderUse) : BinderUse := ⟨a.value || b.value, a.pack || b.pack⟩

partial def binderUse (name : String) : Json → BinderUse
  | .obj fields =>
    let fields := fields.toList
    if fields.lookup "k" == some (.str "binder") then
      ⟨fields.lookup "name" == some (.str name), false⟩
    else if fields.lookup "k" == some (.str "pack") then
      match fields.lookup "of" with
      | some (.obj operand) =>
        if operand.toList.lookup "k" == some (.str "binder") then
          ⟨false, operand.toList.lookup "name" == some (.str name)⟩
        else binderUse name (.obj operand)
      | some other => binderUse name other
      | none => {}
    else if fields.lookup "k" == some (.str "scheme") &&
        (match fields.lookup "binders" with
          | some (.arr bs) => bs.any fun b => (b.getObjValAs? String "name").toOption == some name
          | _ => false) then {}
    else fields.foldl (fun acc field => acc.merge (binderUse name field.2)) {}
  | .arr terms => terms.foldl (fun acc term => acc.merge (binderUse name term)) {}
  | _ => {}

/-- The types a method form's host must meet: none for the declaration as
receiver (`self`), the other parts for its intersection with the type a
`this` parameter states. -/
def statedReceivers (f : Json) : Option (Array Json) :=
  let r := (f.getObjVal? "receiver").toOption
  match r.bind kindOf with
  | some "self" => some #[]
  | some "intersection" =>
    let parts := (r.bind fun r => (r.getObjValAs? (Array Json) "parts").toOption).getD #[]
    let stated := parts.filter (kindOf · != some "self")
    if parts.size - stated.size == 1 && !stated.isEmpty then some stated else none
  | _ => none

/-- A field's method forms: one signature or an intersection of several, each
with the declaration as receiver, or its intersection with stated types. -/
def methodForms (t : Json) : Option (Array Json) :=
  let forms := if kindOf t == some "intersection"
    then (t.getObjValAs? (Array Json) "parts").toOption.getD #[] else #[t]
  if !forms.isEmpty && forms.all (fun f => kindOf f == some "function" &&
      (statedReceivers f).isSome)
  then some forms else none

/-- A generic method: a scheme whose signatures take the declaration as
receiver. The forwarding function ignores the receiver it is given, so the
scheme's own receivers admit any value. -/
def schemeMethod (t : Json) : Option Json := do
  guard (kindOf t == some "scheme")
  let sigs ← (t.getObjValAs? (Array Json) "signatures").toOption
  guard (!sigs.isEmpty && sigs.all fun f => ((f.getObjVal? "receiver").toOption.bind kindOf) == some "self")
  let anyReceiver (f : Json) : Json := f.setObjVal! "receiver"
    (Json.mkObj [("k", "atom"), ("name", "unknown"), ("span", f.getObjValD "span")])
  return t.setObjVal! "signatures" (toJson (sigs.map anyReceiver))

/-! ### Scopes -/

/-- What a term may name from its surroundings: a parameter of the
declaration it is written in, a binder, or the declaration's receiver. -/
inductive Item where
  | param (index : Nat)
  | binder (name : String)
  | self
  deriving BEq, Repr

private def Item.push (acc : Array Item) (i : Item) : Array Item :=
  if acc.contains i then acc else acc.push i

/-- The items a term mentions, in first-occurrence order. A nested scheme's
binders shadow; a method form's `self` receiver is dropped by lowering, so it
is no mention. -/
partial def mentionsAux (shadow : List String) (acc : Array Item) : Json → Array Item
  | .arr xs => xs.foldl (mentionsAux shadow) acc
  | j@(.obj kvs) =>
    match kindOf j with
    | some "parameter" => match (j.getObjValAs? Nat "index").toOption with
      | some i => Item.push acc (.param i)
      | none => acc
    | some "binder" => match (j.getObjValAs? String "name").toOption with
      | some n => if shadow.contains n then acc else Item.push acc (.binder n)
      | none => acc
    | some "self" => Item.push acc .self
    | some "scheme" =>
      let bs := (j.getObjValAs? (Array Json) "binders").toOption.getD #[]
      let names := bs.toList.filterMap fun b => (b.getObjValAs? String "name").toOption
      let acc := bs.foldl (fun acc b => mentionsAux shadow acc (b.getObjValD "bound")) acc
      mentionsAux (names ++ shadow) acc (j.getObjValD "signatures")
    | some "object" =>
      kvs.toList.foldl (fun acc (k, v) =>
        if k != "fields" then mentionsAux shadow acc v else
        ((v.getArr?).toOption.getD #[]).foldl (fun acc f =>
          let ty := f.getObjValD "type"
          let optional := (f.getObjValAs? Bool "optional").toOption.getD false
          match (if optional then none else methodForms ty), (if optional then none else schemeMethod ty) with
          | some forms, _ => forms.foldl (fun acc form =>
              let acc := ((statedReceivers form).getD #[]).foldl (mentionsAux shadow) acc
              ["params", "rest", "result"].foldl (fun acc k => mentionsAux shadow acc (form.getObjValD k)) acc) acc
          | none, some t => mentionsAux shadow acc t
          | none, none => mentionsAux shadow acc ty) acc) acc
    | _ => kvs.toList.foldl (fun acc (_, v) => mentionsAux shadow acc v) acc
  | _ => acc

def mentions (shadow : List String) (term : Json) : List Item :=
  (mentionsAux shadow #[] term).toList

/-- A binder in scope: its kind and what it stands for here. A packed binder
(`packed`) is a value binder whose rest uses read its row as argument lists. -/
structure Binding where
  pack : Bool
  value : Union
  packed : Bool := false
  deriving Repr, Inhabited

/-- The name of the argument lists of a binder typing a value and a rest: a
packed binder, whose row holds its values and its argument lists. -/
def packedName (n : String) : String := n ++ "#pack"

/-- The parameters a declaration's expression uses as a rest's argument
 lists inside it, `...args: T` for its own `T`: packed parameters, whose
 arguments are completed with their array's argument lists. -/
partial def packedParameters : Json → List Nat
  | .obj fields =>
    let fields := fields.toList
    let own := if fields.lookup "k" == some (.str "pack") then
        match fields.lookup "of" with
        | some operand =>
          if (operand.getObjValAs? String "k").toOption == some "parameter" then
            ((operand.getObjValAs? Nat "index").toOption).toList
          else []
        | none => []
      else []
    own ++ fields.flatMap fun f => packedParameters f.2
  | .arr terms => terms.toList.flatMap packedParameters
  | _ => []

/-- Where a term is lowered: the declaration its `parameter` and `self`
terms belong to, and their values; the binders in scope; the aliases being
inlined since the last constructor (guardedness, §8.3); the head whose row is
being built; and the site diagnostics name. Values are in the placeholder
space of the row being built, or closed outside one. -/
structure Ctx where
  decl : Option Nat := none
  params : Array Union := #[]
  self : Option Union := none
  binders : List (String × Binding) := []
  aliases : List Nat := []
  owner : Option Nat := none
  site : String := ""
  /-- Whether the terms come from this client's function tree. Declaration
  terms belong to their own module and are located at the requesting unit. -/
  source : Bool := false
  /-- The declared bounds of the placeholders in scope (`arg i`, `local j`),
  read when a bound obligation inside the template is checked (§8.2). -/
  bounds : List (Tree × Union) := []
  /-- Whether an application's declared bounds are checked here: where the
  source writes it. A claim's are not: a claim is a proposal the program is
  checked against, and bounds carry no meaning (§8.2). -/
  checkBounds : Bool := true
  deriving Inhabited


end Verification.EquationLowering
