import Lean.Data.Json
import Verification.Types.EquationGraphs

/-! The tree spelling of RECURSIVE-EQUATIONS §9.2: a nullary application is
its head's number; every other tree is an object with exactly its own fields,
one spelling each. Decoding refuses an unknown field, a missing one, and a
second spelling of the same tree (`{"app": h, "args": []}` for `h`, an owned
parameter's empty `args`). Both directions are linear in the tree. Source
claims carry graph labels in this spelling (`SourceClaimJson.graphClaim`). -/
namespace Verification.EquationGraphs
open Lean PositiveGraphs

private def kindName : ParameterKind → String
  | .value => "value"
  | .arguments => "arguments"
  | .packed => "packed"

private def kindOf : String → Except String ParameterKind
  | "value" => .ok .value
  | "arguments" => .ok .arguments
  | "packed" => .ok .packed
  | k => .error s!"unknown parameter kind '{k}'"

mutual
def Tree.toJson : Tree → Json
  | .app h .nil => toJson h
  | .app h args => Json.mkObj [("app", toJson h), ("args", Json.arr args.toJsons.toArray)]
  | .bound h .nil i => Json.mkObj [("bound", toJson h), ("slot", toJson i)]
  | .bound h args i =>
    Json.mkObj [("bound", toJson h), ("args", Json.arr args.toJsons.toArray), ("slot", toJson i)]
  | .argument i => Json.mkObj [("arg", toJson i)]
  | .local i => Json.mkObj [("local", toJson i)]
  | .var o i k => Json.mkObj [("var", toJson i), ("owner", toJson o), ("kind", kindName k)]
  | .meet ps => Json.mkObj [("meet", Json.arr ps.toJsons.toArray)]
/-- A union's trees. -/
def Types.toJsons : Types → List Json
  | .nil => []
  | .cons t ts => t.toJson :: ts.toJsons
/-- Arguments, each a union spelled as an array of trees. -/
def Args.toJsons : Args → List Json
  | .nil => []
  | .cons ts args => Json.arr ts.toJsons.toArray :: args.toJsons
end

private def exactly (fields : List (String × Json)) (keys : List String) : Except String Unit :=
  if fields.length == keys.length && fields.all (keys.contains ·.1) then .ok ()
  else .error s!"a tree with fields {fields.map (·.1)}: expected exactly {keys}"

private def natField (j : Json) (key : String) : Except String Nat := do
  match j.getObjVal? key with
  | .ok v => match v.getNat? with
    | .ok n => .ok n
    | .error _ => .error s!"field '{key}' is not a natural number"
  | .error _ => .error s!"missing field '{key}'"

mutual
partial def Tree.fromJson (j : Json) : Except String Tree :=
  match j with
  | .num _ => match j.getNat? with
    | .ok h => .ok (.app h .nil)
    | .error _ => .error "a head is a natural number"
  | .obj kvs => do
    let fields := kvs.toList
    let has (k : String) := fields.any (·.1 == k)
    if has "app" then
      exactly fields ["app", "args"]
      let args ← argsFromJson (← j.getObjVal? "args")
      if args matches .nil then throw "a nullary application is spelled as its head's number"
      return .app (← natField j "app") args
    else if has "bound" then
      if has "args" then
        exactly fields ["bound", "args", "slot"]
        let args ← argsFromJson (← j.getObjVal? "args")
        if args matches .nil then throw "an owned parameter with no arguments leaves out 'args'"
        return .bound (← natField j "bound") args (← natField j "slot")
      else
        exactly fields ["bound", "slot"]
        return .bound (← natField j "bound") .nil (← natField j "slot")
    else if has "meet" then
      exactly fields ["meet"]
      return .meet (← typesFromJson (← j.getObjVal? "meet"))
    else if has "arg" then
      exactly fields ["arg"]
      return .argument (← natField j "arg")
    else if has "local" then
      exactly fields ["local"]
      return .local (← natField j "local")
    else if has "var" then
      exactly fields ["var", "owner", "kind"]
      return .var (← natField j "owner") (← natField j "var") (← kindOf (← (← j.getObjVal? "kind").getStr?))
    else throw s!"unknown tree with fields {fields.map (·.1)}"
  | _ => .error "a tree is a head number or an object"
/-- A union: an array of trees. -/
partial def typesFromJson (j : Json) : Except String Types := do
  let items ← j.getArr?
  items.toList.foldr (fun t acc => do return .cons (← Tree.fromJson t) (← acc)) (pure .nil)
/-- Arguments: an array of unions. -/
partial def argsFromJson (j : Json) : Except String Args := do
  let items ← j.getArr?
  items.toList.foldr (fun t acc => do return .cons (← typesFromJson t) (← acc)) (pure .nil)
end

end Verification.EquationGraphs
