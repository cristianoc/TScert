import Lean.Elab.Term
import Verification.Semantics.ArithmeticRules

/-! # The arithmetic rules as Markdown

`verifier --export rules arithmetic` writes the rules of
`ArithmeticRules.rules` to standard output as a Markdown document, each
rule with every semantic field, its variables' roles and sorts, and the
declarations that state and prove it (`ruleEntries`). The document reads
on its own; the generated sections (docs/GENERATED-SECTIONS.md) are
rendered from it by `dev/generated-sections.mts`, which reads exactly the
form `rulesMarkdown` writes. -/
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

/-- A monomial of a coefficient: `n`, `n·k` or `n·2^k`, a factor `1` or `-1`
written as its sign. -/
def monomial (n : Int) (unit : String) : String :=
  if unit = "" then toString n
  else if n = 1 then unit else if n = -1 then "-" ++ unit else s!"{n}·{unit}"

/-- A coefficient `lit + byConstant·k + byPower·2^k`, its nonzero parts in
the order `2^k`, `k`, the literal, joined by `+` and `-`; `0` when none. -/
def coefText (c : Coef) : String :=
  let parts := [(c.byPower, "2^k"), (c.byConstant, "k"), (c.lit, "")].filter (·.1 ≠ 0)
  match parts.map fun (n, u) => monomial n u with
  | [] => "0"
  | m :: ms => ms.foldl (fun acc t => if t.startsWith "-" then acc ++ " - " ++ (t.drop 1).toString else acc ++ " + " ++ t) m

def varText : RuleVar → String
  | .left => "left"
  | .right => "right"
  | .result => "result"

/-- A fact `Σ aᵢ·vᵢ ≤ b`, each coefficient in parentheses. -/
def factText (F : RuleFact) : String :=
  let terms := F.terms.map fun (x, a) => s!"({coefText a})·{varText x}"
  s!"`{" + ".intercalate terms} ≤ {coefText F.bound}`"

/-- The operator's name in the calculus (`Arith`). -/
def opText : Arith → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .pow => "pow" | .xor => "xor"
  | .rem => "rem" | .bitAnd => "bitAnd" | .bitOr => "bitOr" | .shl => "shl" | .shr => "shr" | .ushr => "ushr"
  | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge" | .eq => "eq" | .looseEq => "looseEq"

def sortText : VarSort → String
  | .num => "Num"
  | .safeInt => "SafeInt"

/-- A variable's role; a constant's with the way the rule reads it. -/
def roleText (r : ArithRule) : Role → String
  | .operand => "operand"
  | .result => "result"
  | .constant => match r.right with
    | .constant { normalisation := .shiftCount, .. } => "constant, a shift count"
    | _ => "constant, read as itself"

/-- The constant's side condition and normalisation, as a sentence. -/
def constantText (c : Constant) : String :=
  let lower := match c.lower with | some l => s!"at least {l}" | none => "no lower bound"
  let upper := match c.upper with | some u => s!"at most {u}" | none => "no upper bound"
  let read := match c.normalisation with
    | .identity => "read as itself"
    | .shiftCount => "read as a shift count, modulo 32"
  s!"The constant: {lower}; {upper}; {read}."

def factsText (title : String) (Fs : List RuleFact) : List String :=
  if Fs.isEmpty then [s!"{title}: none."] else [s!"{title}:", ""] ++ Fs.map fun F => s!"- {factText F}"

/-- A rule's section. -/
def ruleMarkdown (r : ArithRule) (decl proof : Name) : List String :=
  [s!"## {r.name}", "",
    s!"Operator `{opText r.op}`. Stated by `{decl}`, proved by `{proof}`.", "",
    "| Variable | Role | Sort |", "| --- | --- | --- |"] ++
  r.variables.map (fun (x, role, sort) => s!"| `{varText x}` | {roleText r role} | `{sortText sort}` |") ++
  [""] ++
  (match r.right with | .constant c => [constantText c, ""] | .operand _ => []) ++
  factsText "Premises" r.premises ++ [""] ++ factsText "Conclusion" r.conclusion

/-- **The rules' document**: the soundness statement, its proof over every
rule, and each rule in the paper's order. -/
def rulesMarkdown : String :=
  let header := ["# Arithmetic rules", "",
    s!"The rules of `{``rules}`, in the paper's order. Each is sound by `{``ArithRule.Sound}`, " ++
      s!"which `{``rules_sound}` proves of every rule.", "",
    "A fact is `Σ (coefficient)·variable ≤ bound`; `k` is the rule's constant as the rule reads it."]
  "\n".intercalate (header ++ (ruleEntries.flatMap fun e => [""] ++ ruleMarkdown e.rule e.declaration e.proof)) ++ "\n"

#guard coefText { lit := -1, byPower := 1 } == "2^k - 1"
#guard coefText { byPower := -1 } == "-2^k"
#guard coefText {} == "0"

end Verification.RuleExport
