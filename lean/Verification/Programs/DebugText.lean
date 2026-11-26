import Verification.Programs.ControlFlow
import Verification.Semantics.HeapKnowledge
import Verification.Semantics.HeapFacts
import Verification.Semantics.HeapLinks
import Verification.Semantics.HeapSeparation

/-!
# Debug text

One-line text of a node's term and of the facts a state holds, read by the
pass's dump (`TSCERT_DUMP`, docs/REQUEST-PROTOCOL.md). A slot `#i` is the
`i`-th slot of the node's context; a name `nK` is the name a state gives a
value, which facts are stated over. The text is for reading only: nothing
parses it and no check reads it.
-/

namespace Verification.DebugText

open ControlFlow

/-- A single-line rendering of a value's derived `Repr`. -/
def oneLine {α : Type} [Repr α] (a : α) : String := (repr a).pretty 100000

def tag : Tag → String
  | .numEq bits => s!"=={bits}"
  | .strEq v => s!"=={v.quote}"
  | t => oneLine t |>.replace "Verification.Tag." ""

def arith (op : Arith) : String :=
  match op with
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .pow => "**" | .xor => "^" | .rem => "%"
  | .bitAnd => "&" | .bitOr => "|" | .shl => "<<" | .shr => ">>" | .ushr => ">>>"
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">=" | .eq => "==="
  | o => oneLine o |>.replace "Verification.Arith." ""

def key (k : PropKey) : String :=
  match k with
  | .str s => s
  | k => oneLine k

/-- A term, at most `depth` constructors deep (`…` below). -/
partial def term (depth : Nat := 6) : Tm → String
  | t =>
    if depth = 0 then "…" else
    let go := term (depth - 1)
    let args := fun (ts : List Tm) => String.intercalate ", " (ts.map go)
    match t with
    | .var i => s!"#{i}"
    | .nul => "null" | .undef => "undefined" | .tru => "true" | .fls => "false"
    | .num bits => s!"num({bits})"
    | .str v => v.quote
    | .bigint v => s!"{v}n"
    | .sym id => s!"sym({id})"
    | .invoke f r as => s!"{go f}.call({go r}{if as.isEmpty then "" else ", " ++ args as})"
    | .construct f as => s!"new {go f}({args as})"
    | .letE a b => s!"let {go a} in {go b}"
    | .objAt _ _ id => s!"obj@{id}"
    | .makeAt _ names inits => s!"\{{String.intercalate ", " ((names.zip inits).map fun (k, v) => s!"{key k}: {go v}")}}"
    | .readAt k a => s!"{go a}.{key k}"
    | .indexAt a k => s!"{go a}[{go k}]"
    | .writeAt k a b => s!"{go a}.{key k} := {go b}"
    | .test k a => s!"test({tag k}, {go a})"
    | .ite c a b => s!"({go c} ? {go a} : {go b})"
    | .arith op a b => s!"({go a} {arith op} {go b})"
    | .arrLit as => s!"[{args as}]"
    | .elemAt a i => s!"{go a}[{go i}]"
    | .setElem a i v => s!"{go a}[{go i}] := {go v}"
    | .lenOf a => s!"len({go a})"
    | .spread a => s!"...{go a}"
    | .throw a => s!"throw {go a}"
    | .merge _ a b => s!"merge({go a}, {go b})"
    | .makeKey k v => s!"key({go k}, {go v})"
    | .arr _ => "arr" | .viewSpine _ _ => "view"
    | .goto es .. => s!"goto[{es.length} nodes]"
    | .frame es .. => s!"frame[{es.length} nodes]"

def target (t : Target) : String :=
  match t.mapping with
  | none => s!"n{t.label}"
  | some m => s!"n{t.label}{m}"

def continuation : Continuation → String
  | .ret => "return"
  | .bind t => s!"bind → {target t}"
  | .effect t => s!"→ {target t}"
  | .branch y n => s!"yes → {target y}, no → {target n}"
  | .branchBind y n => s!"bind; yes → {target y}, no → {target n}"
  | .tagBind k y n => s!"bind; test {tag k}: yes → {target y}, no → {target n}"

/-- A node: its term and where it continues. -/
def node (n : ControlFlow.Node) : String :=
  s!"{term 8 n.expression}   [{continuation n.continuation}]" ++
    (match n.handler with | some h => s!" handler → {target h}" | none => "")

def heapTerm (t : HeapKnowledge.Term) : String :=
  let base := s!"n{t.slot}" ++ String.join (t.path.map ("." ++ ·)) ++ (if t.atEntry then "@entry" else "")
  match t.kind with
  | .value => base | .length => s!"len({base})" | .view => s!"view({base})" | .strLength => s!"slen({base})"
  | .bitMask m => s!"mask{m}({base})"

def form (F : Linear.Form HeapKnowledge.Term) : String :=
  if F.isEmpty then "0" else
  String.intercalate " + " (F.map fun (x, c) =>
    if c == 1 then heapTerm x else if c == -1 then s!"-{heapTerm x}" else s!"{c}·{heapTerm x}")

partial def indexFact : HeapKnowledge.IndexFact → String
  | .linear (.le F d) => s!"{form F} ≤ {d}"
  | .linear (.ne F d) => s!"{form F} ≠ {d}"
  | .int n => s!"int(n{n})"
  | .index n => s!"index(n{n})"
  | .pastSafe n => s!"pastSafe(n{n})"
  | .length a l => s!"length(n{a}) = n{l}"
  | .bound a i strict => s!"n{i} {if strict then "<" else "≤"} len(n{a})"
  | .either a b => s!"({indexFact a}) ∨ ({indexFact b})"
  | .apart a p b q => s!"apart(n{a}{String.join (p.map ("." ++ ·))}, n{b}{String.join (q.map ("." ++ ·))})"
  | .same a b => s!"same(n{a}, n{b})"
  | f => oneLine f |>.replace "Verification.HeapKnowledge.IndexFact." ""

/-- An index atom with its condition: `[if nC]` holds where the Boolean `nC`
is true, `[unless nC]` where it is false. -/
def indexAtom (a : HeapKnowledge.IndexAtom) : String :=
  (match a.cond with
   | none => ""
   | some c => if a.negated then s!"[unless n{c}] " else s!"[if n{c}] ") ++ indexFact a.fact

end Verification.DebugText
