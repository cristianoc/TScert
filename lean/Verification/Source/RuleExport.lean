import Lean.Data.Json
import Lean.Elab.Term
import Verification.Semantics.ArithmeticRules

/-! # The arithmetic rules as JSON

`verifier --export rules arithmetic` writes the rules of
`ArithmeticRules.rules` to standard output, each with every semantic field
and the declarations that state and prove it (`ruleEntries`), for the
generated sections (docs/GENERATED-SECTIONS.md). The reader is
`dev/generated-sections.mts`. -/
namespace Verification.RuleExport
open Lean Verification.ArithmeticRules

/-- A rule with the declarations that state and prove it, and the proof:
the proof term is checked to prove the rule's soundness. -/
structure RuleEntry where
  rule : ArithRule
  declaration : Name
  proof : Name
  sound : rule.Sound

open Elab Term in
/-- `ruleEntry% r`: the entry of the rule `r`, its proof the declaration
`r_sound`, both names resolved from `r`, so that a name cannot stand
beside another rule's declaration. -/
elab "ruleEntry% " x:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo x
  let p := n.appendAfter "_sound"
  elabTerm (← `(RuleEntry.mk $(mkIdent n) $(quote n) $(quote p) $(mkIdent p))) (some (mkConst ``RuleEntry))

/-- The rules' entries, in the order of `rules`. -/
def ruleEntries : List RuleEntry :=
  [ruleEntry% shr, ruleEntry% maskRange, ruleEntry% maskBound, ruleEntry% shl, ruleEntry% bitOr]

#guard ruleEntries.map (·.rule) == rules

def jInt (i : Int) : Json := toJson i

def jOptInt : Option Int → Json
  | some i => jInt i
  | none => .null

def domainJson : Domain → Json
  | .safeInteger => "safeInteger"
  | .number => "number"

def normalisationJson : Normalisation → Json
  | .identity => "identity"
  | .shiftCount => "shiftCount"

def coefJson (c : Coef) : Json :=
  Json.mkObj [("lit", jInt c.lit), ("byConstant", jInt c.byConstant), ("byPower", jInt c.byPower)]

def varJson : RuleVar → Json
  | .left => "left"
  | .right => "right"
  | .result => "result"

def factJson (F : RuleFact) : Json :=
  Json.mkObj [("terms", Json.arr (F.terms.map fun (x, a) => Json.mkObj [("var", varJson x), ("coef", coefJson a)]).toArray),
    ("bound", coefJson F.bound)]

def rightJson : Right → Json
  | .operand d => Json.mkObj [("operand", domainJson d)]
  | .constant c => Json.mkObj [("constant", Json.mkObj [("symbol", (c.symbol : Json)), ("lower", jOptInt c.lower),
      ("upper", jOptInt c.upper), ("normalisation", normalisationJson c.normalisation)])]

/-- The operator's name in the calculus (`Arith`). -/
def opJson : Arith → Json
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .pow => "pow" | .xor => "xor"
  | .rem => "rem" | .bitAnd => "bitAnd" | .bitOr => "bitOr" | .shl => "shl" | .shr => "shr" | .ushr => "ushr"
  | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge" | .eq => "eq" | .looseEq => "looseEq"

def ruleJson (r : ArithRule) (decl proof : Name) : Json :=
  Json.mkObj [("name", (r.name : Json)), ("declaration", (decl.toString : Json)), ("proof", (proof.toString : Json)),
    ("op", opJson r.op), ("left", domainJson r.left), ("right", rightJson r.right),
    ("premises", Json.arr (r.premises.map factJson).toArray), ("result", domainJson r.result),
    ("conclusion", Json.arr (r.conclusion.map factJson).toArray)]

/-- The rules' document: the soundness statement, its proof over every rule,
and the rules in the paper's order. -/
def rulesJson : Json :=
  Json.mkObj [("statement", ((``ArithRule.Sound).toString : Json)), ("soundness", ((``rules_sound).toString : Json)),
    ("rules", Json.arr (ruleEntries.map fun e => ruleJson e.rule e.declaration e.proof).toArray)]

#guard opJson .bitAnd == "bitAnd"

end Verification.RuleExport
