import Lean.Elab.Term
import Verification.Semantics.ArithmeticRules
import Verification.Semantics.StringPostconditions

/-! # The step rules as Markdown

`verifier --export rules arithmetic` writes the rules of
`ArithmeticRules.rules` to standard output as a Markdown document, each
rule with every semantic field (its operation, its variables' roles and
sorts, its premises, conclusion, atoms and effect, its display), and the
declaration that states it with its evidence: the proof of a proved rule,
the native contracts an assumed rule rests on (`ruleEntries`). The document reads
on its own; the generated sections (docs/GENERATED-SECTIONS.md) are
rendered from it by `dev/generated-sections.mts`, which reads exactly the
form `rulesMarkdown` writes. -/
namespace Verification.RuleExport
open Lean Verification.ArithmeticRules

/-- How a rule's entry establishes it: a proved rule by the declaration of
its proof, whose term proves the rule's soundness; an assumed rule by the
native contracts its trust names. -/
inductive Evidence (r : ArithRule) where
  | proved (proof : Name) (trust : r.trust = .proved) (sound : r.Sound)
  | assumed (contracts : List String) (trust : r.trust = .assumed contracts)

/-- A rule with the declaration that states it, its evidence, and the
lemmas of the Lean model that prove an assumed contract's arithmetic. -/
structure RuleEntry where
  rule : ArithRule
  declaration : Name
  evidence : Evidence rule
  lemmas : List Name := []

/-- `ruleEntry% r [m, …]`: the entry of the rule `r`, its name resolved from `r`:
a proved rule's proof the declaration `r_sound`, so that a name cannot
stand beside another rule's declaration, and an assumed rule's contracts
those of its trust. Either is checked against the rule's trust. The
lemmas `m` of the Lean model, where given, resolve to declarations. -/
syntax "ruleEntry% " ident (" [" ident,* "]")? : term

open Elab Term in
elab_rules : term
  | `(ruleEntry% $x $[[$ms,*]]?) => do
    let n ← realizeGlobalConstNoOverloadWithInfo x
    let p := n.appendAfter "_sound"
    let evidence ← if (← getEnv).contains p then `(Evidence.proved $(quote p) rfl $(mkIdent p))
      else `(Evidence.assumed _ rfl)
    -- Each lemma the entry names resolves to a declaration.
    let lemmas ← (ms.map (·.getElems.toList)).getD [] |>.mapM fun i => realizeGlobalConstNoOverloadWithInfo i.raw
    elabTerm (← `(RuleEntry.mk $(mkIdent n) $(quote n) $evidence $(quote lemmas))) (some (mkConst ``RuleEntry))

/-- The rules' entries, in the order of `rules`. -/
def ruleEntries : List RuleEntry :=
  [ruleEntry% add, ruleEntry% sub, ruleEntry% scale, ruleEntry% shr, ruleEntry% maskRange, ruleEntry% maskBound,
    ruleEntry% shl, ruleEntry% bitOr, ruleEntry% strLength, ruleEntry% strRead, ruleEntry% concat,
    ruleEntry% charCodeAt [StringPostconditions.unit_bound, StringPostconditions.code_unit_safe],
    ruleEntry% codePointAt, ruleEntry% codePointPair,
    ruleEntry% indexOf [StringPostconditions.search_bounds],
    ruleEntry% indexOfNonempty [StringPostconditions.search_bounds],
    ruleEntry% slice [StringPostconditions.slice_length], ruleEntry% arrayIndexOf, ruleEntry% newView,
    ruleEntry% viewLength, ruleEntry% viewRead, ruleEntry% viewWrite, ruleEntry% viewWriteAny]

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

def baseText : Base → String
  | .left => "left"
  | .right => "right"
  | .third => "third"
  | .result => "result"

/-- A variable, or its length `|x|`. -/
def varText : RuleVar → String
  | .left => "left"
  | .right => "right"
  | .third => "third"
  | .result => "result"
  | .len x => s!"|{baseText x}|"

/-- A fact `Σ aᵢ·vᵢ ≤ b`, each coefficient in parentheses. -/
def factBody (F : RuleFact) : String :=
  let terms := F.terms.map fun (x, a) => s!"({coefText a})·{varText x}"
  s!"{" + ".intercalate terms} ≤ {coefText F.bound}"

def factText (F : RuleFact) : String := s!"`{factBody F}`"

/-- The operator's name in the calculus (`Arith`). -/
def arithText : Arith → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .pow => "pow" | .xor => "xor"
  | .rem => "rem" | .bitAnd => "bitAnd" | .bitOr => "bitOr" | .shl => "shl" | .shr => "shr" | .ushr => "ushr"
  | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge" | .eq => "eq" | .looseEq => "looseEq"

/-- The operation's name: a binary operator's in the calculus, another
step's as the datum names it. -/
def opText : Operation → String
  | .binary o => arithText o
  | .strLength => "strLength"
  | .strRead => "strRead"
  | .viewLength => "viewLength"
  | .viewRead => "viewRead"
  | .viewWrite => "viewWrite"
  | .call ms indexed => s!"call {",".intercalate ms}" ++ (if indexed then " (indexed)" else "")
  | .construct => "construct"

def displayText : Display → String
  | .arithmetic => "arithmetic"
  | .strings => "strings"
  | .views => "views"
  | .library => "library"

def sortText : VarSort → String
  | .num => "Num"
  | .safeInt => "SafeInt"
  | .string => "String"
  | .array => "Array"
  | .typedArray => "TypedArray"
  | .value => "Value"

/-- A variable's role; a constant's with the way the rule reads it. -/
def roleText (r : ArithRule) : ArithmeticRules.Role → String
  | .operand => "operand"
  | .index => "index"
  | .written => "written"
  | .argument => "argument"
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

def listText {α : Type} (title : String) (item : α → String) (xs : List α) : List String :=
  if xs.isEmpty then [s!"{title}: none."] else [s!"{title}:", ""] ++ xs.map fun x => s!"- {item x}"

/-- An atom: `x[i] ≐ y`, the value converted to the format `conv(v)`, or
every other index kept, `kept x ≠ i`. -/
def atomText : RuleAtom → String
  | .elem c i v false => s!"`{varText c}[{varText i}] ≐ {varText v}`"
  | .elem c i v true => s!"`{varText c}[{varText i}] ≐ conv({varText v})`"
  | .othersKept c i => s!"`kept {varText c} ≠ {varText i}`"
  | .implies F G => s!"`{factBody F} ⇒ {factBody G}`"

def regionText : Region → String
  | .st => "st" | .vw => "vw" | .val => "val"
  | .spine x => s!"{varText x}.spine" | .cells x => s!"{varText x}.cells"
  | .field x f => s!"{varText x}.{f}" | .fields x => s!"{varText x}.fields"

def changeText : Change → String
  | .keep => "keep" | .init => "init" | .scalar => "scalar" | .extend => "extend" | .grow => "grow" | .any => "any"

/-- The evidence's sentence. -/
def evidenceText {r : ArithRule} : Evidence r → String
  | .proved p _ _ => s!"proved by `{p}`"
  | .assumed cs _ => "assumed of " ++ ", ".intercalate (cs.map fun c => s!"`{c}`")

/-- The model's lemmas' sentence, where the entry names any. -/
def modelText (ms : List Name) : List String :=
  if ms.isEmpty then [] else ["", "The Lean model proves " ++ ", ".intercalate (ms.map fun m => s!"`{m}`") ++ "."]

/-- A rule's section. -/
def ruleMarkdown (r : ArithRule) (decl : Name) (e : Evidence r) (ms : List Name) : List String :=
  [s!"## {r.name}", "",
    s!"Operation `{opText r.op}`, in the display `{displayText r.display}`. Stated by `{decl}`, {evidenceText e}."] ++
  modelText ms ++ ["",
    "| Variable | Role | Sort |", "| --- | --- | --- |"] ++
  r.variables.map (fun (x, role, sort) => s!"| `{varText x}` | {roleText r role} | `{sortText sort}` |") ++
  [""] ++
  (match r.right with | .constant c => [constantText c, ""] | _ => []) ++
  listText "Premises" factText r.premises ++ [""] ++ listText "Conclusion" factText r.conclusion ++ [""] ++
  listText "Atoms" atomText r.atoms ++ [""] ++
  listText "Effect" (fun (g, d) => s!"`{regionText g}: {changeText d}`") r.effect ++
  (if r.allocates then ["", "The result is allocated."] else [])

/-- **The rules' document**: the soundness statement, its proof over every
rule, and each rule in the paper's order. -/
def rulesMarkdown : String :=
  let header := ["# Step rules", "",
    s!"The rules of `{``rules}`, in the paper's order. A proved rule is sound by `{``ArithRule.Sound}`, " ++
      s!"which `{``rules_sound}` proves of every proved rule; an assumed rule names the native contracts it rests on.", "",
    "A fact is `Σ (coefficient)·term ≤ bound`, a term a variable or its length `|variable|`; " ++
      "`k` is the rule's constant as the rule reads it."]
  "\n".intercalate (header ++ (ruleEntries.flatMap fun e => [""] ++ ruleMarkdown e.rule e.declaration e.evidence e.lemmas)) ++ "\n"

#guard coefText { lit := -1, byPower := 1 } == "2^k - 1"
#guard coefText { byPower := -1 } == "-2^k"
#guard coefText {} == "0"

end Verification.RuleExport
