import Verification.Types.EquationGraphs

/-! The equation validator (RECURSIVE-EQUATIONS §2, §5): raw heads,
as a decoder or a lowering produces them, become `Equations` only when every
template is scoped, lexical and constructor-headed, every meet is in normal
form, and every parameter declares its kind. A refusal names the
head and the position. The checks decide the very predicates the kernel types
carry (`Tree.scoped`, `Tree.lexical`, `RowTemplate.wellBound`); the located
diagnosis only explains a refusal. -/
namespace Verification.EquationGraphs
open PositiveGraphs PositiveNormalization CallEffects

/-- Whether parts are in canonical order: each at most the next. -/
def canonicalOrder (ts : List Tree) : Bool :=
  (ts.zip ts.tail).all fun (a, b) => compare a b != .gt

/- Meet normal form at every meet: at least one part, in canonical order.
A singleton meet preserves the value-only interpretation of intersections.
Flatness is part of scoping. -/
mutual
def Tree.meetNormal : Tree → Bool
  | .app _ args | .bound _ args _ => args.meetNormal
  | .meet ps => decide (1 ≤ ps.toList.length) && canonicalOrder ps.toList && ps.meetNormal
  | .argument _ | .local _ | .var .. => true
def Types.meetNormal : Types → Bool
  | .nil => true
  | .cons t ts => t.meetNormal && ts.meetNormal
def Args.meetNormal : Args → Bool
  | .nil => true
  | .cons ts args => ts.meetNormal && args.meetNormal
end

/-- Where a tree may occur: a closed label, a template operand, or a template
bound (which cannot name a local). -/
inductive Place where
  | label
  | operand
  | bound
  deriving DecidableEq

/- The first problem in a tree, if any, as a located message. It explains
why `Tree.scoped`, `Tree.lexical` or `Tree.meetNormal` fails. -/
mutual
def Tree.problem (sig : Signature) (parameters locals : Nat) (place : Place) : Tree → Option String
  | .app h args =>
    match sig[h]? with
    | none => some s!"application of unknown head {h}"
    | some hd =>
      if args.toList.length != hd.parameters then
        some s!"head {h} takes {hd.parameters} arguments, given {args.toList.length}"
      else (args.problem sig parameters locals place 0).map (s!"head {h} " ++ ·)
  | .bound h args i =>
    if place != .label then some s!"owned parameter of head {h} in a template" else
    match sig[h]? with
    | none => some s!"owned parameter of unknown head {h}"
    | some hd =>
      if args.toList.length != hd.parameters then
        some s!"head {h} takes {hd.parameters} arguments, given {args.toList.length}"
      else if hd.binders.length ≤ i then
        some s!"head {h} binds {hd.binders.length} locals, slot {i} named"
      else (args.problem sig parameters locals place 0).map (s!"parameter of head {h} " ++ ·)
  | .argument i =>
    if place == .label then some s!"placeholder arg {i} in a closed label"
    else if parameters ≤ i then some s!"arg {i} out of range: {parameters} parameters"
    else none
  | .local i =>
    if place == .label then some s!"placeholder local {i} in a closed label"
    else if place == .bound then some s!"local {i} in a bound, which is read outside the scheme"
    else if locals ≤ i then some s!"local {i} out of range: {locals} locals"
    else none
  | .var .. => if place != .label then some "family variable in a template" else none
  | .meet ps =>
    if ps.toList.isEmpty then some "meet of no parts: at least one"
    else if ps.toList.any Tree.isMeet then some "meet with a meet as a part: parts are flat"
    else if !canonicalOrder ps.toList then some "meet parts not in canonical order"
    else (ps.problem sig parameters locals place 0).map ("meet " ++ ·)
def Types.problem (sig : Signature) (parameters locals : Nat) (place : Place) (index : Nat) :
    Types → Option String
  | .nil => none
  | .cons t ts => (t.problem sig parameters locals place).map (s!"part {index}: " ++ ·) <|>
      (ts.problem sig parameters locals place (index + 1))
def Args.problem (sig : Signature) (parameters locals : Nat) (place : Place) (index : Nat) :
    Args → Option String
  | .nil => none
  | .cons ts args => (ts.problem sig parameters locals place 0).map (s!"argument {index} " ++ ·) <|>
      (args.problem sig parameters locals place (index + 1))
end

/-- A closed tree as a label: scoped with no placeholders, and every meet in
normal form. -/
def Label.ofTree? (t : Tree) : Option (Label sig) :=
  if h : t.scoped sig 0 0 = true ∧ t.meetNormal = true then some ⟨t, h.1⟩ else none

/-- A closed tree as a label, or the located reason it is not one. -/
def Label.ofTree (sig : Signature) (t : Tree) : Except String (Label sig) :=
  match Label.ofTree? t with
  | some l => .ok l
  | none => .error ((t.problem sig 0 0 .label).getD "not a closed label")

/-- A head as a decoder or a lowering states it: its signature entry and its
body, whose operands are unions of trees. `name` is diagnostic only. -/
structure RawHead where
  name : String
  header : Header
  body : GraphRow Tree (List Tree)
  deriving Repr

private def expressionOf? (sig : Signature) (h : Header) (t : Tree) : Option (Expression sig h) :=
  if hv : t.scoped sig h.parameters h.binders.length = true ∧ t.lexical true = true then
    some ⟨t, hv⟩ else none

private def referenceOf? (sig : Signature) (h : Header) (t : Tree) : Option (Reference sig h) :=
  (expressionOf? sig h t).bind fun e => if hs : e.1.single = true then some ⟨e, hs⟩ else none

/-- The first problem among a row's operands, located. -/
private def operandsProblem (sig : Signature) (h : Header) (place : Place) (what : String)
    (ops : List (List Tree)) : Option String :=
  ops.zipIdx.findSome? fun (U, oi) => U.zipIdx.findSome? fun (t, ti) =>
    (t.problem sig h.parameters h.binders.length place <|>
      (if t.meetNormal then none else some "meet not in normal form")).map
      (s!"{what} operand {oi} label {ti}: " ++ ·)

/-- Why a raw body is no template of its header, located. -/
def templateProblem (sig : Signature) (h : Header) : GraphRow Tree (List Tree) → Option String
  | .clauses cs =>
    if !h.binders.isEmpty then some s!"a clause row binds no locals, {h.binders.length} declared"
    else cs.zipIdx.findSome? fun (c, ci) => operandsProblem sig h .operand s!"clause {ci}" c.operands
  | .scheme bs sigs bounds rests _ _ =>
    if bs != (List.range h.binders.length).map Tree.local then
      some s!"a scheme binds exactly its {h.binders.length} locals, in order"
    else
      (sigs.zipIdx.findSome? fun (a, si) =>
        operandsProblem sig h .operand s!"signature {si}" a.operands) <|>
      (bounds.zipIdx.findSome? fun ((b, T), bi) =>
        (if bs.contains b then none else some s!"bound {bi}: not on a binder of the scheme") <|>
        operandsProblem sig h .bound s!"bound {bi}" [T]) <|>
      (rests.zipIdx.findSome? fun (r, ri) =>
        operandsProblem sig h .operand s!"variadic signature {ri}" r.operands)
  | .param .. => some "a parameter row is no template: parameters come from applications"
  | .meet .. => some "a meet row is no template: intersections are meet labels"

private def toTemplateRow (sig : Signature) (head : Fin sig.length) :
    GraphRow Tree (List Tree) → RowTemplate sig head
  | .clauses cs => .clauses (cs.map (Clause.map (·.filterMap (expressionOf? sig sig[head]))))
  | .scheme bs sigs bounds rests resolution construct =>
    .scheme (bs.filterMap (referenceOf? sig sig[head]))
      (sigs.map (Arrow.map (·.filterMap (expressionOf? sig sig[head]))))
      (bounds.filterMap fun (b, T) =>
        (referenceOf? sig sig[head] b).map (·, T.filterMap (expressionOf? sig sig[head])))
      (rests.map (RestArrow.map (·.filterMap (expressionOf? sig sig[head])))) resolution construct
  | .param .. | .meet .. => .clauses []

private def eraseRow (row : RowTemplate sig head) : GraphRow Tree (List Tree) :=
  row.map (fun r => r.1.1) (·.map (·.1))

/-- A raw body as a template of its head: converted, then required to be
exactly the raw body (nothing dropped), in normal form, and well bound. -/
def templateOf? (sig : Signature) (head : Fin sig.length) (raw : GraphRow Tree (List Tree)) :
    Except String (Template sig head) :=
  match templateProblem sig sig[head] raw with
  | some e => .error e
  | none =>
    let row := toTemplateRow sig head raw
    if eraseRow row != raw then .error "a label is not well formed"
    else if !(raw.operands.all (·.all Tree.meetNormal)) then .error "a meet is not in normal form"
    else if hw : row.wellBound head = true then .ok ⟨row, hw⟩
    else .error "the row does not bind exactly its locals"

/-- A head's parameter kinds: one per parameter. -/
def kindProblem (h : Header) : Option String :=
  if h.kinds.length == h.parameters then none
  else some s!"{h.kinds.length} parameter kinds for {h.parameters} parameters"

/-- **The equation validator.** Raw heads become equations only when every
head declares a kind per parameter and every body is a template
of its header (`templateOf?`). A refusal names the head. -/
def Equations.ofRaw (heads : List RawHead) : Except String Equations :=
  let sig : Signature := heads.map (·.header)
  let raw (i : Fin sig.length) : GraphRow Tree (List Tree) :=
    (heads[i.val]'(by simpa [sig] using i.isLt)).body
  let located := (List.finRange sig.length).findSome? fun i =>
    let hd := heads[i.val]'(by simpa [sig] using i.isLt)
    ((kindProblem hd.header) <|>
      (match templateOf? sig i (raw i) with
       | .error e => some e
       | .ok _ => none)).map (s!"head {i.val} ({hd.name}): " ++ ·)
  match located with
  | some e => .error e
  | none =>
    if hall : ∀ i : Fin sig.length, (templateOf? sig i (raw i)).toOption.isSome = true then
      .ok { signature := sig, body := fun i => (templateOf? sig i (raw i)).toOption.get (hall i) }
    else .error "equations: a head is not a template"

end Verification.EquationGraphs
