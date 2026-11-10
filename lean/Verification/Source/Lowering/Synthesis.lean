import Verification.Source.SourceExtraction

/-! # The types of a function's declarations and expressions, computed

One forward walk over a function's fragment body, in evaluation order, that
computes the type of each expression occurrence and of each binding at each
statement entry from the types the source writes (parameters, annotated
declarations, signatures of the module values it reads) and the language's
typing of each construct. What it computes is a proposal: the proved rules
check every type the lowering states, so nothing here adds trust.

The walk has no search, fixed point or retry. A construct whose type the
direct rule does not determine is recorded as undetermined, with the reason.
A loop body is walked once, from the loop head, where each binding the loop
assigns holds its declared type (its annotation, or its initializer's type
widened as a `let` widens it); at a merge a binding holds the union of what
the arms give it.

`compareUnit` sets the computed types beside the claims document's at every
expression occurrence and statement entry the claims name. -/
namespace Verification.SourceExtraction.Synthesis
open Lean ProgramTyping PositiveRules LabelStore Fragment
open EquationGraphs (Tree)

/-- What a binding holds at a point: its current type, its declared type, and
the narrowed types of the member paths read from it. -/
structure Env where
  vars : List (String × Ty Tree) := []
  decl : List (String × Ty Tree) := []
  paths : List ((String × List PropKey) × Ty Tree) := []

/-- A generic module function: its binders' names and its signature at
given binder types, in claim form (`Instantiable.instantiate`). -/
structure Generic where
  binders : List String
  instantiate : List (String × Json) → SourceTypes.Lowering Json

/-- What the walk records: each expression occurrence's construct kind and
computed type or reason, each statement entry's bindings, and the
environments a `break` leaves with, by label; and the generic module
functions it reads. -/
structure Walk where
  generics : List (String × Generic) := []
  /-- The types the `return`s of the body being walked give, and the result
  its signature expects. -/
  returns : List (Option (Ty Tree)) := []
  expected : Option (Ty Tree) := none
  /-- Each `let`'s storage contract, by its initializer's span and name:
  its declared type. -/
  contracts : List ((Span × String) × Ty Tree) := []
  /-- The type expected of a value, by the value's span: a declaration's,
  an assignment's or a return's. -/
  hints : List (Span × Ty Tree) := []
  /-- Whether the function literal being walked may change the heap: a write,
  an assignment of a binding it does not declare, or a call whose instance
  states another footprint than keeping both values and stores; and the
  bindings it declares. -/
  writes : Bool := false
  locals : List String := []
  exprs : Std.HashMap Span (String × Except String (Ty Tree)) := {}
  entries : Std.HashMap Nat (List (String × Ty Tree)) := {}
  breaks : List (Option String × Env) := []

abbrev W := StateT Walk Compiler

def norm (A : Ty Tree) : Ty Tree := (A.mergeSort Labels.le).eraseDups

def graphNow : Compiler (PositiveGraphs.NormalGraph Tree) := return SourceTypes.graph (← table)

def prim (c : PositiveNormalization.Clause (Ty Tree)) : Compiler (Ty Tree) :=
  return [← lower (SourceTypes.use c)]

def boolTy : Ty Tree := norm [Labels.tru, Labels.fls]

def upd (xs : List (α × β)) (k : α) (v : β) [BEq α] : List (α × β) := (k, v) :: xs.filter (·.1 != k)

/-- The construct kind the table counts an expression under. -/
def kindOf : Expr → String
  | .var .. => "identifier"
  | .lit .. => "literal"
  | .equality .. | .singletonTest .. | .shapeTest .. | .tagMember .. | .inKeys .. | .not .. => "comparison"
  | .arith _ op _ _ => match op with
    | .lt | .le | .gt | .ge | .eq | .looseEq => "comparison"
    | _ => "arithmetic"
  | .unary .. | .update .. => "arithmetic"
  | .read .. | .index .. | .elemAt .. => "member read"
  | .call .. | .invoke .. | .construct .. | .callWithReceiver .. | .applyWithReceiver ..
  | .bindWithReceiver .. => "call"
  | .ifBody .. | .logical .. | .coalesce .. => "conditional"
  | _ => "other"

/-- A literal's type: its singleton, numbers and strings interned as the
claims' are (`SourceTypes.numberLabels`). -/
def literal : Claim.Val → Compiler (Ty Tree)
  | .vnull => pure [Labels.nul]
  | .vundef => pure [Labels.undef]
  | .vbool b => pure [if b then Labels.tru else Labels.fls]
  | .vnum b => prim (.numLit b)
  | .vstr s => lower (SourceTypes.numberLabels ⟨false, [.strLit s]⟩)
  | .vbigint i => lower (SourceTypes.numberLabels ⟨false, [.bigintLit i]⟩)

/-- A type shown to a reader of the comparison, two levels deep: records by
their fields, arrays by their elements, functions by their signatures. -/
partial def shown (T : EquationStore.State) (A : Ty Tree) (depth : Nat := 2) : String :=
  let G := SourceTypes.graph T
  let one (l : Tree) : String :=
    if depth == 0 then SourceTypes.render T [l] else
    match PositiveRules.expand G [l] with
    | [.refs fs [] vs os _ _ _] =>
      match (fs ++ vs).lookup SourceTypes.storeField with
      | some S => match PositiveRules.expand G S with
        | [.list t []] =>
          let parts := t.required.map (shown T · (depth - 1)) ++ t.optional.map (fun o => shown T o (depth - 1) ++ "?")
          let rest := (t.rest.map fun r => s!"...{shown T r (depth - 1)}").toList
          s!"[{", ".intercalate (parts ++ rest)}]"
        | _ => "array"
      | none =>
        let named := (fs ++ vs).filter (·.1 != SourceTypes.protoField) |>.map fun (k, B) =>
          s!"{match k with | .str n => n | _ => "#"}: {shown T B (depth - 1)}"
        let opt := os.map fun o => s!"{match o.key with | .str n => n | _ => "#"}?: {shown T o.type (depth - 1)}"
        "{" ++ ", ".intercalate (named ++ opt) ++ "}"
    | [.arrs L _] => " & ".intercalate (L.map fun a =>
        s!"({", ".intercalate (a.arguments.map (shown T · (depth - 1)))}) => {shown T a.result (depth - 1)}")
    | _ => SourceTypes.render T [l]
  if A.isEmpty then "never" else " | ".intercalate (A.map one).eraseDups

/-- A `let`'s declared type from its initializer: each literal type widened
to its primitive (TypeScript's widening of a mutable location). -/
def widen (A : Ty Tree) : Compiler (Ty Tree) := do
  let G ← graphNow
  let mut out := []
  for l in A do
    match PositiveRules.expand G [l] with
    | [.numLit _] | [.numIn _] => out := out ++ (← prim .num)
    | [.strLit _] | [.strIn _] => out := out ++ (← prim .str)
    | [.boolLit _] => out := out ++ boolTy
    | [.bigintLit _] => out := out ++ (← prim .bigint)
    | _ => out := out ++ [l]
  return norm out

def shapeOf (G : PositiveGraphs.NormalGraph Tree) (l : Tree) : Option Tag :=
  match PositiveRules.expand G [l] with
  | [.str] | [.strLit _] | [.strIn _] => some .isStr
  | [.num] | [.numLit _] | [.numIn _] => some .isNum
  | [.bigint] | [.bigintLit _] => some .isBigint
  | [.bool] | [.boolLit _] => some .isBool
  | _ => none

def slice (A : Ty Tree) (tag : Tag) (q : Bool) : Compiler (Ty Tree) := do
  return norm (BranchRefinement.tagSlice (← graphNow) A tag q)

/-- The union of two types, a member of `B` within `A` already stated by
`A`: one label for one meaning where the two state it twice. -/
def joinTy (A B : Ty Tree) : Compiler (Ty Tree) := do
  let T ← table
  return norm (A ++ B.filter fun b => !within T [b] A)

def nonNullish (A : Ty Tree) : Compiler (Ty Tree) := slice A .isNullish false

/-- The type a binding declared at `D` holds after an assignment of a value
of type `A`: `A` where it is within `D`; else the members of `D` some member
of `A` is within, `D` where none is (an assignment's narrowing). -/
def assigned (D A : Ty Tree) : Compiler (Ty Tree) := do
  let T ← table
  if !A.isEmpty && within T A D then return A
  let kept := D.filter fun d => A.any fun a => within T [a] [d]
  return if kept.isEmpty then D else kept

/-- The prototype a primitive's member is read from, by its shape. -/
def protoFor (vars : List (String × Ty Tree)) (tag : Tag) : Compiler (Ty Tree) := do
  let some (_, name) := SourceTypes.primitivePrototypes.find? (·.1 == tag)
    | throw "a member of a primitive of no prototype"
  let some P := vars.lookup name | throw s!"{name} is not in scope"
  return P

/-- `o.f` of an `o` of type `A`: each primitive member by its prototype's
field (a string's `length` a number), an array's `length` a number, and an
object's field as the read rule reads it (`readCell`, `HeapExpressionRules`'
read, view, optional and prototype reads). -/
def readField (vars : List (String × Ty Tree)) (A : Ty Tree) (fld : PropKey) : Compiler (Ty Tree) := do
  if A.isEmpty then throw "a read of a value of no type"
  let G ← graphNow
  let (prims, objs) := A.partition fun l => (shapeOf G l).isSome
  let mut out : Ty Tree := []
  for l in prims do
    let some tag := shapeOf G l | continue
    if tag == .isStr && fld == lengthKey then
      out := out ++ (← prim .num)
    else
      let P ← protoFor vars tag
      let some B := fieldRow G P fld | throw s!"a primitive's prototype names no field '{reprStr fld}'"
      out := out ++ B
  if !objs.isEmpty then
    if fld == lengthKey && arraysOnly G objs then out := out ++ (← prim .num)
    else
      let plan ← readCell G [objs] fld (DirectProof.var [objs] 0 objs)
      out := out ++ plan.type
  return norm out

/-- The positions of an array's store: the type at index `k`, where the key
is that one index, with `undefined` past the required positions; any
position's with `undefined` otherwise (an index read past the end). -/
def elementAt (A : Ty Tree) (index : Option Nat) (missing : Bool := true) : Compiler (Ty Tree) := do
  if A.isEmpty then throw "an element read of a value of no type"
  let G ← graphNow
  let mut out : Ty Tree := []
  for l in A do
    if shapeOf G l == some .isStr then
      out := out ++ (← prim .str) ++ (if missing then [Labels.undef] else [])
      continue
    match storeOf G [l] with
    | some S =>
      match PositiveRules.expand G S with
      | [.list t []] =>
        match index.bind t.position with
        | some B => out := out ++ B ++
            (if missing && t.required.length ≤ index.getD 0 then [Labels.undef] else [])
        | none => out := out ++ t.required.flatten ++ t.optional.flatten ++ t.rest.getD [] ++
            (if missing then [Labels.undef] else [])
      | _ => throw "an array of more than one tuple contract"
    | none =>
      match PositiveRules.expand G [l] with
      | [.dict _ _ _ ix _ _ _ _ _] =>
        out := out ++ ix.flatMap (·.2) ++ (if missing then [Labels.undef] else [])
      | _ => throw "an element read of a value that is no array"
  return norm out

/-- The one index a key's type names, where it names one. -/
def keyIndex (K : Ty Tree) : Compiler (Option Nat) := do
  let G ← graphNow
  match K.flatMap fun l => PositiveRules.expand G [l] with
  | [.numLit b] => return indexOfBits b
  | _ => return none

def keyString (K : Ty Tree) : Compiler (Option String) := do
  let G ← graphNow
  match K.flatMap fun l => PositiveRules.expand G [l] with
  | [.strLit s] => return some s
  | _ => return none

/-- A signature as a call selects it: its parameters, whether further
actuals are admitted (a rest), and its result. -/
structure Sig where
  params : List (Ty Tree)
  rest : Bool
  result : Ty Tree

/-- The signature a call's actuals select: the first whose parameter count
admits them (omitted positions admitting `undefined`) and whose parameters
each actual is within, else the first whose count admits them. -/
def choose (sigs : List Sig) (args : List (Ty Tree)) : Compiler Sig := do
  let T ← table
  let G := SourceTypes.graph T
  let fits (s : Sig) : Bool :=
    if s.rest then s.params.length ≤ args.length
    else args.length ≤ s.params.length && (s.params.drop args.length).all (admitsUndefined G)
  let candidates := sigs.filter fits
  let accepts (s : Sig) : Bool := (args.zip s.params).all fun (A, D) => within T A D
  match candidates.find? accepts <|> candidates.head? with
  | some s => return s
  | none => throw s!"no signature admits {args.length} actuals (of {sigs.map fun s => (s.params.length, s.rest)})"

/-- The signatures a callable type offers, fixed and variadic. -/
def callSigsOf (F : Ty Tree) : Compiler (List Sig) := do
  let G ← graphNow
  let fixed := (ProgramTyping.callSigs G F).map fun a => ⟨a.arguments, false, a.result⟩
  let rests := (ProgramTyping.restSigs G F).map fun a => ⟨a.arguments.1, true, a.result⟩
  return fixed ++ rests

/-- The prototype a record reads an inherited key from: its prototype field
or view. -/
def protoOf (G : PositiveGraphs.NormalGraph Tree) (O : Ty Tree) : Option (Ty Tree) :=
  match PositiveRules.expand G O with
  | [.refs fs [] vs _ _ _ _] => (fs ++ vs).lookup SourceTypes.protoField
  | _ => none

def memberSigs (m : MethodMembers.Sig (Ty Tree)) : Compiler (List Sig) := do
  if m.calls.isEmpty && m.rests.isEmpty then
    throw "a generic member: its signature needs type arguments"
  return m.calls.map (fun a => ⟨a.arguments, false, a.result⟩) ++
    m.rests.map (fun a => ⟨a.arguments.1, true, a.result⟩)

/-- The narrowing a test of `tag` answering `q` makes of the binding or the
member path `target` reads, and, for a test of a member `x.f`, of `x` itself:
the members of `x`'s type whose `f` can answer so (a discriminant). -/
def narrowTarget (env : Env) (target : Expr) (tag : Tag) (q : Bool) : Compiler Env := do
  match memberPath target with
  | some (root, []) =>
    let some A := env.vars.lookup root | return env
    return { env with vars := upd env.vars root (← slice A tag q) }
  | some (root, path) =>
    let some A := env.vars.lookup root | return env
    let mut env := env
    -- The path's type: its narrowed one, or read along it.
    let P ← match env.paths.lookup (root, path) with
      | some P => pure (some P)
      | none => tryCatch (some <$> path.foldlM (fun B f => readField env.vars B f) A) fun _ => pure none
    if let some P := P then
      env := { env with paths := upd env.paths (root, path) (← slice P tag q) }
    if let [f] := path then
      let mut kept : Ty Tree := []
      for l in A do
        let keep ← tryCatch (do
            let B ← readField env.vars [l] f
            return !(← slice B tag q).isEmpty) fun _ => pure true
        if keep then kept := kept ++ [l]
      if !kept.isEmpty then env := { env with vars := upd env.vars root kept }
    return env
  | none => return env

/-- The union of two environments where both are reached: each binding both
hold, at the union of its two types; each path both narrow, likewise. -/
def join : Option Env → Option Env → Option Env
  | none, b => b
  | a, none => a
  | some a, some b => some {
      vars := a.vars.filterMap fun (n, A) => (b.vars.lookup n).map fun B => (n, if A == B then A else norm (A ++ B))
      decl := a.decl ++ b.decl.filter fun (n, _) => (a.decl.lookup n).isNone
      paths := a.paths.filterMap fun (p, A) => (b.paths.lookup p).map fun B => (p, norm (A ++ B)) }

/-- The environment at a loop head: every binding the loop assigns at its
declared type, and no path rooted at one narrowed. -/
def loopHead (env : Env) (ss : List Stmt) : Env :=
  let changed := env.vars.filter fun (n, _) => ss.any (assignsStmt n)
  { env with
    vars := env.vars.map fun (n, A) =>
      if changed.any (·.1 == n) then (n, (env.decl.lookup n).getD A) else (n, A)
    paths := env.paths.filter fun ((r, _), _) => !changed.any (·.1 == r) }

def typeofNames : List String := ["bigint", "boolean", "function", "number", "object", "string", "symbol", "undefined"]

def need (o : Option (Ty Tree)) (what : String) : Compiler (Ty Tree) :=
  match o with
  | some A => pure A
  | none => throw s!"{what} undetermined"

/-- The result of an arithmetic or relational operator (the operator typing
of `OperatorTyping`): a Boolean for a comparison, a string for `+` with a
string operand, a bigint for bigint operands, a number otherwise. -/
def arithType (op : Arith) (L R : Ty Tree) : Compiler (Ty Tree) := do
  let G ← graphNow
  let isStr (A : Ty Tree) := A.any fun l => shapeOf G l == some .isStr
  let isBig (A : Ty Tree) := !A.isEmpty && A.all fun l => shapeOf G l == some .isBigint
  match op with
  | .lt | .le | .gt | .ge | .eq | .looseEq => return boolTy
  | .add =>
    if isStr L || isStr R then prim .str
    else if isBig L && isBig R then prim .bigint else prim .num
  | .shl | .shr | .ushr | .bitAnd | .bitOr => prim .num
  | _ => if isBig L && isBig R then prim .bigint else prim .num

/-- A label's type in claim form, read back by `Fragment.translate`. -/
def graphJson (A : Ty Tree) : Json := Json.mkObj [("top", toJson false),
  ("atoms", toJson (A.map fun l => Json.mkObj [("a", toJson "graph"), ("label", toJson l)]))]

/-- What a parameter of type `P`, which may mention the binder `b`, says `b`
is, given an actual of type `A`: `A` where `P` is `b`, `A`'s elements where
`P` is an array of `b`, `A`'s result where `P` is a function returning `b`
(the simplest matching of an actual against a parameter). -/
def isBinder (b : Tree) (P : Ty Tree) : Bool :=
  P == [b] || match P with
    | [.meet ps] => ps.toList.contains b
    | _ => false

def matchBinder (b : Tree) (P A : Ty Tree) : Compiler (Option (Ty Tree)) := do
  if isBinder b P then return some A
  let G ← graphNow
  let [l] := P | return none
  if let some S := storeOf G [l] then
    if let [.list t []] := PositiveRules.expand G S then
      if (t.rest.map (isBinder b)).getD false || (!t.required.isEmpty && t.required.all (isBinder b)) then
        return some (← elementAt A none (missing := false))
    return none
  let some s := (ProgramTyping.callSigs G [l]).head? | return none
  if !isBinder b s.result then return none
  return (← callSigsOf A).head?.map (·.result)

/-- `A` with each binder `σ` names read as its type; a binder's meet with
its bound read as the type too, which an instance within the bound is. -/
def substitute (σ : List (Tree × Ty Tree)) (A : Ty Tree) : Ty Tree :=
  norm (A.flatMap (EquationLowering.treeReplace fun u => match u with
    | .meet ps => ps.toList.findSome? (σ.lookup ·)
    | u => σ.lookup u))

/-- What a call selects its signature from: a callee's binders (none for a
callee that is no scheme), its signatures, the receiver the call passes, the
binders' types written as explicit type arguments, and, for a callee that is
no instance, its own type. -/
structure Callee where
  binders : List Tree := []
  fixed : List (CallEffects.Arrow (Ty Tree)) := []
  rests : List (CallEffects.RestArrow (Ty Tree)) := []
  receiver : Ty Tree := [Labels.undef]
  seed : List (Tree × Ty Tree) := []
  own : Option (Ty Tree) := none
  /-- A class's construct signatures: its instance is a constructor's. -/
  construct : Bool := false

/-- The callee a value of type `F` is, called with receiver `O`: a scheme
by its binders and signatures, at `typeArgs` where they are written; any
other callable by its signatures. -/
def calleeOf (F O : Ty Tree) (typeArgs : List Json := []) : Compiler Callee := do
  let G ← graphNow
  if let [l] := F then
    if let some s := G.schemes l then
      let θ ← typeArgs.mapM fun t => lower (Fragment.translate t)
      if !θ.isEmpty && θ.length != s.binders.length then
        throw "explicit type arguments of another count than the binders"
      return { binders := s.binders, fixed := s.signatures, rests := s.variadic, receiver := O,
               seed := s.binders.zip θ }
  return { fixed := ProgramTyping.callSigs G F, rests := ProgramTyping.restSigs G F, receiver := O, own := some F }

/-- A generic module function's callee: its signature at fresh binders, or
at its explicit type arguments. -/
def genericCallee (g : Generic) (typeArgs : List Json) : Compiler Callee := do
  if !typeArgs.isEmpty then
    if typeArgs.length != g.binders.length then throw "explicit type arguments of another count than the binders"
    let inst ← lower (do Fragment.translate (← g.instantiate (g.binders.zip typeArgs)))
    let G ← graphNow
    return { fixed := ProgramTyping.callSigs G inst, rests := ProgramTyping.restSigs G inst }
  let ps ← lower (modifyGet fun T => let (T, ps) := EquationStore.binders T g.binders; (ps, T))
  let fresh ← lower (do Fragment.translate (← g.instantiate (g.binders.zip (ps.map fun p => graphJson [p]))))
  let G ← graphNow
  return { binders := ps, fixed := ProgramTyping.callSigs G fresh, rests := ProgramTyping.restSigs G fresh }

/-- The member `o.k` names, `o` of type `O`: its own (a host-relative
member), else its prototype's. -/
def memberFor (vars : List (String × Ty Tree)) (O : Ty Tree) (fld : PropKey) :
    Compiler (Option (MethodMembers.Sig (Ty Tree))) := do
  let G ← graphNow
  let O ← match O.filterMap (shapeOf G) |>.eraseDups with
    | [tag] => if O.all (fun l => shapeOf G l == some tag) then protoFor vars tag else pure O
    | _ => pure O
  if let some m := ProgramTyping.memberOf G O fld then return some m
  if let some P := protoOf G O then
    if let some m := ProgramTyping.memberOf G P fld then return some m
  return none

/-- The callee `o.k(…)` calls, `o` of type `O`: the object's member, its
prototype's, or a field holding a callable. -/
def methodCallee (vars : List (String × Ty Tree)) (O : Ty Tree) (fld : PropKey) : Compiler Callee := do
  if let some m ← memberFor vars O fld then
    if m.calls.isEmpty && m.rests.isEmpty then
      let some S := m.schemes.head? | throw "a member of no signature"
      return ← calleeOf S O
    let fixed := m.calls.map (·.withReceiver O)
    let rests := m.rests.map (·.withReceiver O)
    return { fixed, rests, receiver := O, own := some [← lower (SourceTypes.use (.arrs fixed rests))] }
  calleeOf (← readField vars O fld) O

/-- The callee `new C(…)` calls: its construct signatures. -/
def constructCallee (F : Ty Tree) (typeArgs : List Json) : Compiler Callee := do
  let G ← graphNow
  if let [l] := F then
    if (G.schemes l).isSome then return { ← calleeOf F [Labels.undef] typeArgs with construct := true }
  match PositiveRules.expand G F with
  | [.ctors L S ..] =>
    return { fixed := L.map (·.withReceiver [Labels.undef]), rests := S.map (·.withReceiver [Labels.undef]) }
  | _ => throw "a construction of a value of no construct signature"

/-- Whether an actual is a callback: a function literal some parameter of
which is not written, typed by the parameter it is passed at. -/
def callback : Expr → Bool
  | .lambda _ _ _ params .. => params.any (·.2 == Json.null)
  | _ => false

mutual
/-- The bindings statements declare, nested ones included. -/
partial def declaredIn (ss : List Stmt) : List String :=
  ss.flatMap fun s => s.bound ++ match s with
    | .ite _ _ t e => declaredIn t ++ declaredIn (e.getD [])
    | .loop _ _ b u _ => declaredIn b ++ declaredIn u
    | .block _ _ b => declaredIn b
    | .forOf _ n _ _ _ b => n :: declaredIn b
    | .tryStmt _ b h f => declaredIn b ++ (match h with
        | some (p, hs) => (p.map (·.1)).toList ++ declaredIn hs
        | none => []) ++ declaredIn (f.getD [])
    | .closing _ c b => declaredIn c ++ declaredIn b
    | _ => []
end

/-- The walk records a change of the heap. -/
def wrote : W Unit := modify fun w => { w with writes := true }

/-- An assignment of `n`: a change of the heap where the function literal
being walked does not declare `n`. -/
def assigns (n : String) : W Unit := do
  if !(← get).locals.contains n then wrote

mutual
/-- Record an expression's computed type or the reason it has none. -/
partial def record (e : Expr) (r : Except String (Ty Tree)) : W (Option (Ty Tree)) := do
  modify fun w => { w with exprs := w.exprs.insert e.span (kindOf e, r) }
  return r.toOption

partial def recordAt (span : Span) (kind : String) (r : Except String (Ty Tree)) : W Unit :=
  modify fun w => { w with exprs := w.exprs.insert span (kind, r) }

partial def attempt (e : Expr) (x : Compiler (Ty Tree)) : W (Option (Ty Tree)) := do
  let r ← StateT.lift (tryCatch (Except.ok <$> x) fun msg => pure (.error msg))
  record e r

/-- The narrowing a condition answering `q` makes. -/
partial def refine (env : Env) (c : Expr) (q : Bool) : W Env := do
  match c with
  | .var .. | .read .. => StateT.lift (narrowTarget env c .truthy q)
  | .not _ e => refine env e !q
  | .cast _ _ e => refine env e q
  | .logical _ andOp l r =>
    if andOp == q then refine (← refine env l q) r q
    else
      let a ← refine env l q
      let b ← refine (← refine env l !q) r q
      return (join (some a) (some b)).getD a
  | .shapeTest _ tag equal e => StateT.lift (narrowTarget env e tag (equal == q))
  | .singletonTest _ tag equal testLeft l r =>
    StateT.lift (narrowTarget env (if testLeft then l else r) tag (equal == q))
  -- Strict equality with an operand of one value: the test of that value on
  -- the other operand (`comparisonsExpr`'s choice, `singletonTag`).
  | .equality _ equal l r =>
    let w ← get
    let typeOf (x : Expr) : Option (Ty Tree) := (w.exprs.get? x.span).bind (·.2.toOption)
    let G ← StateT.lift graphNow
    match (typeOf r).bind (singletonTag G), (typeOf l).bind (singletonTag G) with
    | some tag, _ => StateT.lift (narrowTarget env l tag (equal == q))
    | _, some tag => StateT.lift (narrowTarget env r tag (equal == q))
    | _, _ => return env
  | .tagMember _ _ none tags _ e =>
    match memberPath e with
    | some (root, []) =>
      let some A := env.vars.lookup root | return env
      let B ← if q then do
          let parts ← tags.mapM fun t => StateT.lift (slice A t true)
          pure (norm parts.flatten)
        else tags.foldlM (fun B t => StateT.lift (slice B t false)) A
      return { env with vars := upd env.vars root B }
    | _ => return env
  | _ => return env

/-- An expression's type, recorded at its occurrence, and the environment
after it. -/
partial def expr (env : Env) (e : Expr) : W (Option (Ty Tree) × Env) := do
  match e with
  | .var _ n =>
    let r := match env.vars.lookup n with
      | some A => .ok A
      | none => .error s!"'{n}' is bound outside what the walk sees"
    return (← record e r, env)
  | .lit _ v => return (← attempt e (literal v), env)
  | .logical _ andOp l r =>
    let (L, e1) ← expr env l
    let (R, e2) ← expr (← refine e1 l andOp) r
    let A ← attempt e do
      let L ← need L "the left operand"
      let R ← need R "the right operand"
      -- `a && b`: `a`'s falsy part or `b`; `a || b`: `a`'s truthy part or `b`.
      joinTy (← slice L .truthy !andOp) R
    return (A, (join (some (← refine e1 l !andOp)) (some e2)).getD e2)
  | .coalesce _ l r =>
    let (L, e1) ← expr env l
    let (R, e2) ← expr e1 r
    -- `a ?? b`: `a` less null and undefined, or `b`.
    let A ← attempt e do joinTy (← nonNullish (← need L "the left operand")) (← need R "the right operand")
    return (A, (join (some e1) (some e2)).getD e2)
  | .optional _ _ recv body =>
    let (O, e1) ← expr env recv
    let some O := O | do
      let _ ← expr e1 body
      return (← record e (.error "the chain's receiver undetermined"), e1)
    let inner := { e1 with vars := upd e1.vars chainName (← StateT.lift (nonNullish O)) }
    let (B, e2) ← expr inner body
    let A ← attempt e do
      let B ← need B "the chain's body"
      let nullish := !(← slice O .isNullish true).isEmpty
      return norm (B ++ (if nullish then [Labels.undef] else []))
    return (A, { e2 with vars := e2.vars.filter (·.1 != chainName) })
  | .withObject _ _ obj body =>
    let (O, e1) ← expr env obj
    let inner := match O with
      | some O => { e1 with vars := upd e1.vars objectName O }
      | none => e1
    let (B, e2) ← expr inner body
    return (← record e (match B with | some B => .ok B | none => .error "the body undetermined"),
      { e2 with vars := e2.vars.filter (·.1 != objectName) })
  | .shapeTest _ _ _ x | .tagMember _ _ _ _ _ x | .not _ x =>
    let (_, e1) ← expr env x
    return (← record e (.ok boolTy), e1)
  | .equality _ _ l r | .singletonTest _ _ _ _ l r | .inKeys _ l r =>
    let (_, e1) ← expr env l
    let (_, e2) ← expr e1 r
    return (← record e (.ok boolTy), e2)
  | .cast _ annot x =>
    let (A, e1) ← expr env x
    let r ← attempt e do
      match annot with
      | some ty => lower (Fragment.translate ty)
      -- `e!` (or `as const`): the operand less null and undefined.
      | none => nonNullish (← need A "the operand")
    -- `f(…)!` and `xs[i]!`: the call or the read proposed at the operand
    -- less null and undefined, which its own step proves where the facts
    -- select a signature giving it (`SinglePass.directCall`'s order).
    if annot.isNone then
      match x, r with
      | .call .., some B | .invoke .., some B | .elemAt .., some B => let _ ← record x (.ok B)
      | _, _ => pure ()
    -- `[…] as const`: the readonly tuple of its elements' own types.
    let r ← match annot, x with
      | none, .arrayLit _ es [] => do
        let w ← get
        match es.mapM (fun y => (w.exprs.get? y.span).bind (·.2.toOption)) with
        | some Es => attempt e (lower do
            let s ← SourceTypes.use (.list ⟨Es, [], none, true, .dense⟩ [])
            let T ← get
            return [← SourceTypes.use (SourceTypes.arrayOf T s true)])
        | none => pure r
      | _, _ => pure r
    return (r, e1)
  | .alloc _ names es =>
    let (As, e1) ← exprs env es
    let r ← attempt e do
      let fields ← (names.zip As).mapM fun (n, A) => do return (n, ← widen (← need A "a field"))
      prim (.refs fields [] [] [] [] [])
    return (r, e1)
  | .build _ names es =>
    -- An object literal with spreads: each spread's record fields, then each
    -- named field, a later key replacing an earlier one.
    let (As, e1) ← exprs env es
    let r ← attempt e do
      let G ← graphNow
      let mut fields : List (PropKey × Ty Tree) := []
      let mut optional : List (OptionalField (Ty Tree)) := []
      for (k, A) in names.zip As do
        let A ← need A "a part"
        match k with
        | some k =>
          fields := upd fields (.str k) (← widen A)
          optional := optional.filter (·.key != PropKey.str k)
        | none =>
          match PositiveRules.expand G A with
          | [.refs fs [] vs os ms _ _] =>
            -- A key the type also states as a method may sit on the
            -- prototype, which a spread does not copy: no field of the copy.
            for (f, B) in fs ++ vs do
              if f != SourceTypes.protoField && f != SourceTypes.storeField && !ms.any (·.key == f) then
                fields := upd fields f B
                optional := optional.filter (·.key != f)
            -- An optional field the spread may lack keeps an earlier value.
            for o in os do
              if (fields.lookup o.key).isNone then optional := o :: optional.filter (·.key != o.key)
          | _ => throw "a spread of a value of no one record contract"
      prim (.refs fields.reverse [] [] optional.reverse [] [])
    return (r, e1)
  | .read _ fld x =>
    let (O, e1) ← expr env x
    let narrowed := (memberPath e).bind fun p => e1.paths.lookup p
    let r ← attempt e do
      if let some P := narrowed then return P
      readField e1.vars (← need O "the receiver") fld
    return (r, e1)
  | .write _ fld recv rhs =>
    wrote
    let (O, e1) ← expr env recv
    -- The reference `recv.fld`, as the read gives it.
    if let .str f := fld then
      let r ← StateT.lift (tryCatch (do
          return Except.ok (← readField e1.vars (← need O "the receiver") fld)) fun m => pure (.error m))
      recordAt (recv.span.1, recv.span.2 + 1 + f.length) "member read" r
    let (R, e2) ← expr e1 rhs
    -- A write ends the narrowing of every path through the field.
    let e2 := { e2 with paths := e2.paths.filter fun ((_, p), _) => !p.contains fld }
    return (← record e (match R with | some R => .ok R | none => .error "the value undetermined"), e2)
  | .index _ field x key =>
    let (O, e1) ← expr env x
    let (K, e2) ← expr e1 key
    let r ← attempt e do
      let O ← need O "the receiver"
      let K ← need K "the key"
      match field with
      | some f => readField e2.vars O (.str f)
      | none => match ← keyString K with
        | some s => readField e2.vars O (.str s)
        | none => elementAt O (← keyIndex K)
    return (r, e2)
  | .elemWrite p recv key rhs => expr env (.indexWrite p none recv key rhs)
  | .indexWrite _ field recv key rhs =>
    wrote
    let (O, e1) ← expr env recv
    let (K, e2) ← expr e1 key
    -- The reference `recv[key]`, read where the write's target is read: the
    -- contents there, as the read gives them.
    let r ← StateT.lift (tryCatch (do
        let O ← need O "the receiver"
        let K ← need K "the key"
        let B ← match field with
          | some f => readField e2.vars O (.str f)
          | none => match ← keyString K with
            | some s => readField e2.vars O (.str s)
            | none => elementAt O (← keyIndex K)
        return Except.ok B) fun m => pure (.error m))
    recordAt (recv.span.1, key.span.2 + 1) "member read" r
    let (R, e3) ← expr e2 rhs
    return (← record e (match R with | some R => .ok R | none => .error "the value undetermined"), e3)
  | .elemAt _ x key =>
    let (O, e1) ← expr env x
    let (K, e2) ← expr e1 key
    let r ← attempt e do elementAt (← need O "the receiver") (← keyIndex (← need K "the key"))
    return (r, e2)
  | .arrayLit _ es spreads =>
    let (As, e1) ← exprs env es
    let r ← attempt e do
      let mut elems : Ty Tree := []
      for (A, i) in As.zipIdx do
        let A ← need A "an element"
        let B ← if spreads.contains i then elementAt A none (missing := false) else widen A
        elems := elems ++ B
      let elems' := norm elems
      lower do
        let s ← SourceTypes.use (.list ⟨[], [], some elems', false, .dense⟩ [])
        let T ← get
        return [← SourceTypes.use (SourceTypes.arrayOf T s false)]
    return (r, e1)
  | .arrayAssign _ targets rest rhs =>
    wrote
    let (R, e1) ← expr env rhs
    let mut env := e1
    for t in targets do
      let (_, e') ← expr env t.target
      env := e'
      if let some d := t.default_ then env := (← expr env d).2
    let names := targets.filterMap (·.target.targetLocal) ++ (rest.bind fun r => r.2.2.target.targetLocal).toList
    env := { env with vars := env.vars.map fun (n, A) =>
      if names.contains n then (n, (env.decl.lookup n).getD A) else (n, A) }
    return (← record e (match R with | some R => .ok R | none => .error "the value undetermined"), env)
  | .arith _ op l r =>
    let (L, e1) ← expr env l
    let (R, e2) ← expr e1 r
    let A ← attempt e do arithType op (← need L "the left operand") (← need R "the right operand")
    return (A, e2)
  | .comma _ l r =>
    let (_, e1) ← expr env l
    let (R, e2) ← expr e1 r
    return (← record e (match R with | some R => .ok R | none => .error "the right operand undetermined"), e2)
  | .unary _ op x =>
    let (A, e1) ← expr env x
    let r ← attempt e do
      match op with
      | .typeof => prim (.strIn typeofNames)
      | .plus => prim .num
      | .neg | .bitNot =>
        let A ← need A "the operand"
        let G ← graphNow
        if !A.isEmpty && A.all (shapeOf G · == some .isBigint) then prim .bigint else prim .num
    return (r, e1)
  | .update _ op target rhs _ =>
    match target with
    | .var _ n => assigns n
    | _ => wrote
    let (L, e1) ← expr env target
    let (R, e2) ← match rhs with
      | some r => do let (R, e2) ← expr e1 r; pure (R, e2)
      | none => pure (some [], e1)
    let r ← attempt e do
      let L ← need L "the target"
      let R ← need R "the right operand"
      arithType op L (if rhs.isSome then R else L)
    let e3 ← match target, r with
      | .var _ n, some A => do
        let D := (e2.decl.lookup n).getD A
        pure { e2 with vars := upd e2.vars n (← StateT.lift (assigned D A)), paths := e2.paths.filter (·.1.1 != n) }
      | _, _ => pure e2
    return (r, e3)
  | .logicalAssign _ op target rhs =>
    match target with
    | .var _ n => assigns n
    | _ => wrote
    let (L, e1) ← expr env target
    let (R, e2) ← expr e1 rhs
    let r ← attempt e do
      let L ← need L "the target"
      let R ← need R "the right operand"
      let kept ← match op with
        | .nullish => nonNullish L
        | .orElse => slice L .truthy true
        | .andAlso => slice L .truthy false
      joinTy kept R
    let e3 ← match target, r with
      | .var _ n, some A => pure { e2 with vars := upd e2.vars n A, paths := e2.paths.filter (·.1.1 != n) }
      | _, _ => pure e2
    return (r, e3)
  | .nullishAssign _ n namePos rhs =>
    assigns n
    recordAt namePos "identifier" (match env.vars.lookup n with
      | some A => .ok A
      | none => .error s!"'{n}' is bound outside what the walk sees")
    if let some D := env.decl.lookup n then
      let D ← StateT.lift (nonNullish D)
      modify fun w => { w with hints := (rhs.span, D) :: w.hints }
    let (R, e1) ← expr env rhs
    let R ← match env.decl.lookup n with
      | some D => fit D rhs R
      | none => pure R
    let r ← attempt e do
      let some L := env.vars.lookup n | throw s!"'{n}' is bound outside what the walk sees"
      joinTy (← nonNullish L) (← need R "the right operand")
    let e2 := match r with
      | some A => { e1 with vars := upd e1.vars n A, paths := e1.paths.filter (·.1.1 != n) }
      | none => e1
    return (r, e2)
  | .assign _ n _ rhs =>
    assigns n
    if let some D := env.decl.lookup n then modify fun w => { w with hints := (rhs.span, D) :: w.hints }
    let (R, e1) ← expr env rhs
    let R ← match env.decl.lookup n with
      | some D => fit D rhs R
      | none => pure R
    let r ← record e (match R with | some R => .ok R | none => .error "the value undetermined")
    let e2 ← match R with
      | some A => do
        let D := (e1.decl.lookup n).getD A
        pure { e1 with vars := upd e1.vars n (← StateT.lift (assigned D A)), paths := e1.paths.filter (·.1.1 != n) }
      | none => pure (match e1.decl.lookup n with
        | some D => { e1 with vars := upd e1.vars n D, paths := e1.paths.filter (·.1.1 != n) }
        | none => { e1 with vars := e1.vars.filter (·.1 != n) })
    return (r, e2)
  | .withValue _ fn initial _ _ =>
    let (_, e1) ← expr env fn
    let (_, e2) ← expr e1 initial
    return (← record e (.error "a function's value bag"), e2)
  | .objectAssign _ target sources =>
    wrote
    let (A, e1) ← expr env target
    let (_, e2) ← exprs e1 sources
    return (← record e (match A with | some A => .ok A | none => .error "the target undetermined"), e2)
  | .lambda .. => return (← walkLambda env e none, env)
  | .ctor _ lam statics =>
    -- A class value: its constructor's written parameters, its instance its
    -- receiver's annotation, its static fields at their initializers'
    -- widened types (the construct rule's `ctors` clause).
    let _ ← walkLambda env lam none
    let (Ss, e1) ← exprs env (statics.map (·.2))
    let r ← attempt e do
      let .lambda _ (some (inst, _)) _ params _ _ _ _ _ _ _ _ := lam | throw "a class of no instance annotation"
      let I ← lower (Fragment.translate inst)
      let ps ← params.mapM fun (_, ty) => lower (Fragment.translate ty)
      let fields ← (statics.zip Ss).mapM fun ((k, _), S) => do return (k, ← widen (← need S "a static field"))
      prim (.ctors [⟨(), ps, I, .ordinary⟩] [] fields)
    return (r, e1)
  | .block _ ss =>
    let _ ← stmts (some env) ss
    return (← record e (.error "a function body"), env)
  | .construct _ callee args spreads typeArgs =>
    let (F, e1) ← expr env callee
    let (As, e2) ← actuals e1 args
    let c ← StateT.lift (tryCatch (do
        if !spreads.isEmpty then throw "a construction with spreads"
        return Except.ok (← constructCallee (← need F "the class") typeArgs)) fun m => pure (.error m))
    let r ← called e2 c args As e.span
    -- A generic class's occurrence is read at its instance.
    if let (.ok c, .ok (inst, _)) := (c, r) then
      if !c.binders.isEmpty then let _ ← record callee (.ok inst)
    return (← record e ((·.2) <$> r), e2)
  | .call _ callee args spreads typeArgs =>
    let gs := (← get).generics
    let generic := match callee with
      | .var _ n => gs.lookup n
      | _ => none
    let (F, e1) ← expr env callee
    let (As, e2) ← actuals e1 args
    let c ← StateT.lift (tryCatch (do
        if !spreads.isEmpty then throw "a call with spreads"
        match generic with
        | some g => return Except.ok (← genericCallee g typeArgs)
        | none => return Except.ok (← calleeOf (← need F "the callee") [Labels.undef] typeArgs))
      fun m => pure (.error m))
    let r ← called e2 c args As e.span
    -- A generic module function's occurrence is read at its instance.
    if generic.isSome then if let .ok (inst, _) := r then let _ ← record callee (.ok inst)
    return (← record e ((·.2) <$> r), e2)
  | .callWithReceiver _ callee recv args =>
    let (F, e1) ← expr env callee
    let (R, e2) ← expr e1 recv
    let (As, e3) ← actuals e2 args
    let c ← StateT.lift (tryCatch (do
        return Except.ok (← calleeOf (← need F "the callee") (R.getD [Labels.undef]))) fun m => pure (.error m))
    let r ← called e3 c args As e.span
    return (← record e ((·.2) <$> r), e3)
  | .applyWithReceiver _ callee recv list _ =>
    let (_, e1) ← expr env callee
    let (_, e2) ← expr e1 recv
    let e3 ← match list with
      | some l => do pure (← expr e2 l).2
      | none => pure e2
    return (← record e (.error "a call through apply"), e3)
  | .bindWithReceiver _ callee recv args =>
    -- `o.m.bind(o)`: the method's signatures, its receiver the object
    -- (`bindMember`); with no further actual bound.
    match callee with
    | .read _ fld o =>
      let (O, e1) ← expr env o
      let (_, e2) ← expr e1 recv
      let (_, e3) ← exprs e2 args
      let r ← StateT.lift (tryCatch (do
          if !args.isEmpty then throw "a bound function with bound actuals"
          let c ← methodCallee e1.vars (← need O "the receiver") fld
          match c.own with
          | some M => return Except.ok M
          | none => throw "a bound generic method") fun m => pure (.error m))
      let _ ← record callee r
      return (← record e r, e3)
    | _ =>
      let (_, e1) ← expr env callee
      let (_, e2) ← expr e1 recv
      let (_, e3) ← exprs e2 args
      return (← record e (.error "a bound function of a computed member"), e3)
  | .invoke _ callee args spreads _ =>
    -- The method's object, then its read (the member, recorded apart), then
    -- the actuals.
    let (obj, fld, keyE) := match callee with
      | .read _ f o => (some o, some f, none)
      | .index _ (some f) o k => (some o, some (PropKey.str f), some k)
      | .index _ none o k => (some o, none, some k)
      | _ => (none, none, none)
    let some o := obj | do
      let (_, e1) ← expr env callee
      let (_, e2) ← exprs e1 args
      return (← record e (.error "a method call of an unknown form"), e2)
    let (O, e1) ← expr env o
    let e1 ← match keyE with
      | some k => do pure (← expr e1 k).2
      | none => pure e1
    let (As, e2) ← actuals e1 args
    let c ← StateT.lift (tryCatch (do
        if !spreads.isEmpty then throw "a call with spreads"
        let some fld := fld | throw "a method of a computed key"
        return Except.ok (← methodCallee e1.vars (← need O "the receiver") fld)) fun m => pure (.error m))
    let r ← called e2 c args As e.span
    let _ ← record callee ((·.1) <$> r)
    let r ← record e ((·.2) <$> r)
    return (r, e2)
  | .ifBody _ c t f =>
    let (_, e1) ← expr env c
    let (A, e2) ← expr (← refine e1 c true) t
    let (B, e3) ← expr (← refine e1 c false) f
    let r ← attempt e do joinTy (← need A "the true arm") (← need B "the false arm")
    return (r, (join (some e2) (some e3)).getD e2)

partial def exprs (env : Env) (es : List Expr) : W (List (Option (Ty Tree)) × Env) := do
  let mut env := env
  let mut out := []
  for x in es do
    let (A, e') ← expr env x
    out := out ++ [A]
    env := e'
  return (out, env)

/-- A call's actuals in order, a callback left for the signature's pass
(`applyCall`), none in its place. -/
partial def actuals (env : Env) (args : List Expr) : W (List (Option (Ty Tree)) × Env) := do
  let mut env := env
  let mut out := []
  for x in args do
    if callback x then out := out ++ [none]
    else
      let (A, e') ← expr env x
      out := out ++ [A]
      env := e'
  return (out, env)

/-- `applyCall` where the callee is known; the callbacks walked unexpected
where it is not. -/
partial def called (env : Env) (c : Except String Callee) (args : List Expr) (As : List (Option (Ty Tree)))
    (at_ : Span) : W (Except String (Ty Tree × Ty Tree)) := do
  match c with
  | .ok c => applyCall env c args As ((← get).hints.lookup at_)
  | .error m =>
    for x in args do if callback x then let _ ← walkLambda env x none
    return .error m

/-- A call's instance, in a fixed order (TypeScript's contextual typing of
arguments, one pass): the signature the actuals' count and the walked
actuals' types select; each binder from the receiver and the walked
actuals (`matchBinder`); then each callback walked with its parameters at
the selected signature's, under those binders, its result binding what
remains; each literal actual at the parameter's shape (`fit`). The callee's
type at the call and the call's result. -/
partial def applyCall (env : Env) (c : Callee) (args : List Expr) (As : List (Option (Ty Tree)))
    (hint : Option (Ty Tree) := none) : W (Except String (Ty Tree × Ty Tree)) := do
  let T ← StateT.lift table
  let G := SourceTypes.graph T
  let n := args.length
  let fits (a : CallEffects.Arrow (Ty Tree)) : Bool :=
    n ≤ a.arguments.length && (a.arguments.drop n).all (admitsUndefined G)
  -- A variadic signature: its fixed parameters, then each further actual at
  -- the element its rest's argument list states.
  let variadic := c.rests.filterMap fun r =>
    if r.arguments.1.length ≤ n then
      match PositiveRules.expand G r.arguments.2 with
      | [.pack t []] => t.rest.map fun E =>
        ((⟨r.receiver, r.arguments.1 ++ (List.replicate (n - r.arguments.1.length) E), r.result, r.effect⟩ :
          CallEffects.Arrow (Ty Tree)), some r)
      | _ => none
    else none
  let candidates := (c.fixed.filter fits).map (·, none) ++ variadic
  let accepts (a : CallEffects.Arrow (Ty Tree)) : Bool :=
    !c.binders.isEmpty || (As.zip a.arguments).all fun (A, D) => A.all fun A => within T A D
  let some (a, rest) := candidates.find? (accepts ·.1) <|> candidates.head?
    | do
      for x in args do if callback x then let _ ← walkLambda env x none
      return .error s!"no signature admits {n} actuals"
  let mut σ : List (Tree × Ty Tree) := c.seed
  let bindFrom (σ : List (Tree × Ty Tree)) (pairs : List (Ty Tree × Ty Tree)) : W (List (Tree × Ty Tree)) := do
    let mut σ := σ
    for b in c.binders do
      if (σ.lookup b).isSome then continue
      for (P, A) in pairs do
        if (σ.lookup b).isNone then
          if let some B ← StateT.lift (tryCatch (matchBinder b P A) fun _ => pure none) then σ := σ ++ [(b, B)]
    return σ
  -- The type expected of the call's value first, where the instance it
  -- gives admits every walked actual (the inference from the result's
  -- context); else from the receiver and the actuals.
  if let some H := hint then
    let σh ← bindFrom σ [(a.result, H)]
    if c.binders.all (fun b => (σh.lookup b).isSome) then
      let subh (A : Ty Tree) : Ty Tree := substitute σh A
      if (As.zip a.arguments).all (fun (A, P) => A.all fun A => within T A (subh P)) then σ := σh
  σ ← bindFrom σ ((a.receiver, c.receiver) :: (a.arguments.zip As).filterMap fun (P, A) => A.map (P, ·))
  let mut As := As
  for ((x, P), i) in (args.zip a.arguments).zipIdx do
    let sub (A : Ty Tree) : Ty Tree := substitute σ A
    if callback x then
      let expect := (ProgramTyping.callSigs G (sub P)).head?
      let L ← walkLambda env x expect
      As := As.set i L
      if let some L := L then σ ← bindFrom σ [(P, L)]
    else if let some A := As[i]? then
      As := As.set i (← fit (sub P) x A)
  let sub (A : Ty Tree) : Ty Tree := substitute σ A
  if let some b := c.binders.find? (fun b => (σ.lookup b).isNone) then
    let _ := b
    return .error "a type argument is not an actual's type"
  let inst := a.map sub
  -- A call changing the heap, by its instance's footprint.
  if inst.effect.footprint != ⟨.keep, .keep⟩ then wrote
  let own ← StateT.lift (match c.own, rest with
    | some F, _ => pure F
    | none, some r => do return [← lower (SourceTypes.use (.arrs [] [r.map sub]))]
    | none, none =>
      if c.construct then do return [← lower (SourceTypes.use (.ctors [⟨(), inst.arguments, inst.result, inst.effect⟩]))]
      -- Every signature of the scheme the actuals' count admits, at the
      -- binders: the step chooses among them (`SinglePass.directCall`), a
      -- precondition's where the facts establish it.
      else do return [← lower (SourceTypes.use (.arrs (if c.binders.isEmpty then [inst]
        else (c.fixed.filter fits).map (·.map sub)) []))])
  return .ok (own, inst.result)

/-- A function literal's walk: its parameters at their written types, or
else at `expected` (a callback's, from the parameter it is passed at),
every binding it captures at its declared type; its result its written one,
or else what its body gives (its returns' union, `undefined` where it
completes). Recorded at the literal as a signature where every part is
determined. -/
partial def walkLambda (env : Env) (e : Expr) (sig : Option (CallEffects.Arrow (Ty Tree))) : W (Option (Ty Tree)) := do
  let expected := sig.map (·.arguments)
  let expectedResult := sig.map (·.result)
  let .lambda _ receiver _ params defaults _ result _ _ async _ body := e
    | return none
  let captured := env.vars.map fun (n, A) => (n, (env.decl.lookup n).getD A)
  let mut vars := captured
  let mut ps : List (Option (Ty Tree)) := []
  for ((n, ty), i) in params.zipIdx do
    let A ← if ty == Json.null then pure ((expected.bind (·[i]?)))
      else StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
    ps := ps ++ [A]
    match A with
    | some A => vars := upd vars n A
    | none => vars := vars.filter (·.1 != n)
  if let some (ty, _) := receiver then
    match ← StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none) with
    | some A => vars := upd vars "this" A
    | none => pure ()
  let written ← match result with
    | some ty => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
    | none => pure none
  let inner : Env := { vars, decl := vars, paths := [] }
  for (_, d) in defaults do let _ ← expr inner d
  let saved ← get
  let declared := params.map (·.1) ++ (match body with
    | .block _ ss => declaredIn ss
    | _ => [])
  modify fun w => { w with writes := false, locals := declared }
  modify fun w => { w with returns := [], expected := written <|> (if async then none else expectedResult) }
  -- An expression body's entry is its prologue's, at the body's start.
  modify fun w => { w with entries := w.entries.insert body.span.1 inner.vars }
  let R ← match body with
    | .block _ ss => do
      let done ← stmts (some inner) ss
      let _ ← record body (.error "a function body")
      let rs := (← get).returns ++ (if done.isSome then [some [Labels.undef]] else [])
      pure (if rs.all (·.isSome) then some (norm (rs.filterMap id).flatten) else none)
    | x => do
      let (A, _) ← expr inner x
      match (← get).expected, A with
      | some P, some A => fit P x A
      | _, _ => pure A
  -- A body that changes nothing keeps both values and stores: the
  -- footprint its calls are checked at (the producer's inferred effect).
  let pure_ := !(← get).writes
  modify fun w => { w with breaks := saved.breaks, returns := saved.returns, expected := saved.expected }
  modify fun w => { w with writes := saved.writes, locals := saved.locals }
  let R := if written.isSome then written else if async then none else R
  match ps.mapM id, R with
  | some qs, some R =>
    -- A callback is checked at the signature it is passed at, its result its
    -- body's; any other literal at its own parameters.
    let a : CallEffects.Arrow (Ty Tree) ← match sig with
      | some a => pure { a with result := R, effect := if pure_ then .ofFootprint ⟨.keep, .keep⟩ else a.effect }
      | none => do pure ⟨← StateT.lift (prim .top), qs, R,
          if pure_ then .ofFootprint ⟨.keep, .keep⟩ else .ordinary⟩
    record e (.ok [← StateT.lift (lower (SourceTypes.use (.arrs [a] [])))])
  | _, _ => record e (.error "a function value: a parameter or its result undetermined")

/-- A literal where a type `P` is expected: `[]` at the arrays of `P`
(whose own type would be an array of no element); an array or object
literal at the members of `P` its type, or its elements' tuple, is within
(TypeScript's contextual typing of a literal). Any other value keeps its
type `A`. -/
partial def fit (P : Ty Tree) (x : Expr) (A : Option (Ty Tree)) : W (Option (Ty Tree)) := do
  let T ← StateT.lift table
  let G := SourceTypes.graph T
  match x with
  | .ifBody _ _ t f =>
    -- Each arm where the conditional's value is expected.
    let w ← get
    let typeOf (y : Expr) : Option (Ty Tree) := (w.exprs.get? y.span).bind (·.2.toOption)
    let A' ← fit P t (typeOf t)
    let B' ← fit P f (typeOf f)
    match A', B' with
    | some A', some B' => record x (← StateT.lift (tryCatch (.ok <$> joinTy A' B') fun m => pure (.error m)))
    | _, _ => return A
  | .arrayLit _ [] _ =>
    let arrays := P.filter fun l => (storeOf G [l]).isSome
    if arrays.isEmpty then return A
    record x (.ok arrays)
  | .alloc _ names es =>
    -- The literal's own record, each field at the expected record's field
    -- where the value, itself fitted there, is within it: the record the
    -- allocation makes, which the expected type then admits.
    let some A := A | return none
    for l in P do
      let w ← get
      let Ds ← StateT.lift (tryCatch (some <$> names.mapM fun k => readField [] [l] k) fun _ => pure none)
      let some Ds := Ds | continue
      let mut fields : List (PropKey × Ty Tree) := []
      let mut ok := true
      for ((k, y), D) in (names.zip es).zip Ds do
        let some B ← fit D y ((w.exprs.get? y.span).bind (·.2.toOption)) | ok := false; break
        fields := fields ++ [(k, if within T B D then D else B)]
      if !ok then continue
      let R? ← StateT.lift (tryCatch (do
          -- The literal's record as written, else stating its own keys
          -- exactly (`HasTyUsing.alloc`'s bound), which meets optional fields.
          -- Each key in the expected record's form: a field where it states
          -- one, a view where it states one, its stable keys kept.
          let (fs, vs, st) := match PositiveRules.expand G [l] with
            | [.refs _ [] evs _ _ _ est] =>
              (fields.filter (fun (k, _) => (evs.lookup k).isNone), fields.filter (fun (k, _) => (evs.lookup k).isSome),
                est.filter names.contains)
            | _ => (fields, [], [])
          let R ← prim (.refs fs [] vs [] [] [] st)
          if within (← table) R [l] then return some (R, false)
          let R ← prim (.refs fs [] vs [] [] [⟨true, names⟩] st)
          return if within (← table) R [l] then some (R, true) else none) fun _ => pure none)
      if let some (R, _) := R? then return ← record x (.ok R)
    return some A
  | .arrayLit _ es [] | .build _ _ es =>
    let w ← get
    let tuple ← match x, es.mapM (fun y => (w.exprs.get? y.span).bind (·.2.toOption)) with
      | .arrayLit .., some Es => StateT.lift (tryCatch (do
          let t ← lower do
            let s ← SourceTypes.use (.list ⟨Es, [], none, false, .dense⟩ [])
            let T ← get
            return [← SourceTypes.use (SourceTypes.arrayOf T s false)]
          pure (some t)) fun _ => pure none)
      | _, _ => pure none
    let some A := A | return none
    let kept := P.filter fun l => within T A [l] || (tuple.any fun t => within T t [l])
    if kept.isEmpty then return some A
    record x (.ok kept)
  | _ => return A

/-- Bind a pattern's names to the parts of a value of type `A` (none where
`A` is undetermined). -/
partial def bindPattern (env : Env) (p : Pattern Expr) (A : Option (Ty Tree)) : W Env := do
  match p with
  | .name n namePos =>
    recordAt namePos "identifier" (match A with
      | some A => .ok A
      | none => .error "the bound value undetermined")
    match A with
    | some A => return { env with vars := upd env.vars n A, decl := upd env.decl n A }
    | none => return { env with vars := env.vars.filter (·.1 != n) }
  | .object _ props rest =>
    let mut env := env
    for (key, q, d) in props do
      let B ← match A with
        | some A => StateT.lift (tryCatch (some <$> readField env.vars A (.str key)) fun _ => pure none)
        | none => pure none
      let (B, e') ← withDefault env B d
      env ← bindPattern e' q B
    if let some (_, q) := rest then env ← bindPattern env q none
    return env
  | .array _ elems rest =>
    let mut env := env
    for (i, q, d) in elems do
      let B ← match A with
        | some A => StateT.lift (tryCatch (some <$> elementAt A (some i)) fun _ => pure none)
        | none => pure none
      let (B, e') ← withDefault env B d
      env ← bindPattern e' q B
    if let some (_, _, _, q) := rest then env ← bindPattern env q none
    return env

/-- A part with a default: the part less `undefined`, or the default's. -/
partial def withDefault (env : Env) (B : Option (Ty Tree)) (d : Option Expr) : W (Option (Ty Tree) × Env) := do
  match d with
  | none => return (B, env)
  | some d =>
    let (D, e1) ← expr env d
    match B, D with
    | some B, some D => return (some (norm ((← StateT.lift (slice B .isUndef false)) ++ D)), e1)
    | _, _ => return (none, e1)

/-- Walk statements from `env` (none: unreached), recording each statement
entry; the environment where the list completes, none where it does not. -/
partial def stmts (env : Option Env) (ss : List Stmt) : W (Option Env) := do
  let mut env := env
  let mut prev : Option Stmt := none
  for s in ss do
    let some e := env | return none
    -- A `for`'s loop, right after its declarations, has its head's entry at
    -- the `for`'s start, the declarations' position: there the bindings
    -- the loop's entry holds, then the declarations' entry's.
    let at_ := match prev, s with
      | some (.mutables p _), .loop q .. | some (.constants p _), .loop q .. => if p.2 == q.1 then p.1 else s.pos.1
      | _, _ => s.pos.1
    -- A loop's entry is its head's: each binding the loop assigns at its
    -- declared type (`loopHead`).
    let vars := match s with
      | .loop _ c body update _ => (loopHead e (.effect c.span c :: body ++ update)).vars
      | _ => e.vars
    modify fun w =>
      let earlier := if at_ == s.pos.1 then [] else
        ((w.entries.get? at_).getD []).filter fun (n, _) => (vars.lookup n).isNone
      { w with entries := (w.entries.insert s.pos.1 vars).insert at_ (vars ++ earlier) }
    env ← stmt e s
    prev := some s
  return env

partial def collectBreaks (label : Option String) (saved : List (Option String × Env)) : W (Option Env) := do
  let w ← get
  let (mine, others) := w.breaks.partition (·.1 == label)
  set { w with breaks := others ++ saved }
  return mine.foldl (fun acc (_, b) => join acc (some b)) none

partial def stmt (env : Env) (s : Stmt) : W (Option Env) := do
  match s with
  | .ret _ x =>
    if let some P := (← get).expected then modify fun w => { w with hints := (x.span, P) :: w.hints }
    let (A, _) ← expr env x
    let A ← match (← get).expected with
      | some P => fit P x A
      | none => pure A
    modify fun w => { w with returns := w.returns ++ [A] }
    return none
  | .throw _ x =>
    let _ ← expr env x
    return none
  | .effect _ x => return some (← expr env x).2
  | .constants _ bs =>
    let mut env := env
    for b in bs do
      if let some ty := b.annot then
        if let some D ← StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none) then
          modify fun w => { w with hints := (b.init.span, D) :: w.hints }
      let (A, e1) ← expr env b.init
      env := e1
      let D ← match b.annot with
        | some ty => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
        | none => pure A
      let A ← match b.annot, D, A with
        | some _, some D, A => fit D b.init A
        | _, _, A => pure A
      match D, A with
      | some D, some A =>
        env := { env with vars := upd env.vars b.name (← StateT.lift (assigned D A)), decl := upd env.decl b.name D }
      | some D, none => env := { env with vars := upd env.vars b.name D, decl := upd env.decl b.name D }
      | none, _ => env := { env with vars := env.vars.filter (·.1 != b.name) }
    return some env
  | .mutables _ bs =>
    let mut env := env
    for b in bs do
      if let some ty := b.annot then
        if let some D ← StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none) then
          modify fun w => { w with hints := (b.init.span, D) :: w.hints }
      let (A, e1) ← expr env b.init
      env := e1
      let D ← match b.annot, A with
        | some ty, _ => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
        | none, some A => some <$> StateT.lift (widen A)
        | none, none => pure none
      let A ← match b.annot, D, A with
        | some _, some D, A => fit D b.init A
        | _, _, A => pure A
      if let some D := D then
        modify fun w => { w with contracts := ((b.init.span, b.name), D) :: w.contracts }
      match D, A with
      | some D, some A =>
        env := { env with vars := upd env.vars b.name (← StateT.lift (assigned D A)), decl := upd env.decl b.name D }
      | some D, none => env := { env with vars := upd env.vars b.name D, decl := upd env.decl b.name D }
      | none, _ => env := { env with vars := env.vars.filter (·.1 != b.name) }
    return some env
  | .destructure _ target d init =>
    let (A, e1) ← expr env init
    let (A, e2) ← withDefault e1 A d
    return some (← bindPattern e2 target A)
  | .ite _ c thn els =>
    let (_, e1) ← expr env c
    let t ← stmts (some (← refine e1 c true)) thn
    let f ← stmts (some (← refine e1 c false)) (els.getD [])
    return join t f
  | .brk _ label =>
    modify fun w => { w with breaks := (label, env) :: w.breaks }
    return none
  | .cont _ => return none
  | .loop _ c body update _ =>
    let head := loopHead env (.effect c.span c :: body ++ update)
    let (_, e1) ← expr head c
    let saved := (← get).breaks
    modify fun w => { w with breaks := [] }
    let b ← stmts (some (← refine e1 c true)) body
    let _ ← stmts (some (b.getD head)) update
    let out ← collectBreaks none saved
    return join (some (← refine e1 c false)) out
  | .block _ label body =>
    match label with
    | none => stmts (some env) body
    | some l =>
      let saved := (← get).breaks
      modify fun w => { w with breaks := [] }
      let r ← stmts (some env) body
      -- Unlabeled breaks inside go to an enclosing loop.
      let out ← collectBreaks (some l) saved
      return join r out
  | .forOf _ name _ _ iterable body =>
    let (I, e1) ← expr env iterable
    let head := loopHead e1 body
    let elem ← match I with
      | some I => StateT.lift (tryCatch (some <$> elementAt I none (missing := false)) fun _ => pure none)
      | none => pure none
    let inner := match elem with
      | some A => { head with vars := upd head.vars name A, decl := upd head.decl name A }
      | none => { head with vars := head.vars.filter (·.1 != name) }
    let saved := (← get).breaks
    modify fun w => { w with breaks := [] }
    let _ ← stmts (some inner) body
    let out ← collectBreaks none saved
    return join (some head) out
  | .tryStmt _ body handler finalizer =>
    let b ← stmts (some env) body
    let reset := loopHead env body
    let h ← match handler with
      | some (param, hs) =>
        let unknown ← StateT.lift (prim .source)
        let hEnv := match param with
          | some (n, _) => { reset with vars := upd reset.vars n unknown, decl := upd reset.decl n unknown }
          | none => reset
        stmts (some hEnv) hs
      | none => pure none
    let joined := if handler.isSome then join b h else b
    match finalizer with
    | some fs =>
      let f ← stmts (some (joined.getD reset)) fs
      return if f.isNone then none else joined
    | none => return joined
  | .closing _ close body =>
    let b ← stmts (some env) body
    let _ ← stmts (some (b.getD env)) close
    return b
end

/-- How a computed type stands to the claimed one. -/
def classify (T : EquationStore.State) (A C : Ty Tree) : String :=
  if within T A C && within T C A then "identical"
  else if within T C A then "wider"
  else if within T A C then "narrower"
  else "unrelated"

/-- The comparison of a walk with a function's claims: per construct kind
and class, the count; and each occurrence that is not identical, with its
span, kind, class and both types rendered, or the reason. -/
def compareWalk (T : EquationStore.State) (fc : SourceClaims.Function Tree) (w : Walk) :
    Std.HashMap (String × String) Nat × Array Json := Id.run do
  let mut counts : Std.HashMap (String × String) Nat := {}
  let mut samples : Array Json := #[]
  let mut seen : Std.HashSet Span := {}
  let bump (m : Std.HashMap (String × String) Nat) (k : String × String) := m.insert k ((m.getD k 0) + 1)
  for (span, cand) in fc.exprs do
    if seen.contains span then continue
    seen := seen.insert span
    let some C := (SourceClaims.resolve T cand).toOption | continue
    let (kind, r) := (w.exprs.get? span).getD ("unvisited", .error "not reached by the walk")
    let cls := match r with
      | .ok A => classify T A C
      | .error _ => "undetermined"
    counts := bump counts (kind, cls)
    -- Same meaning under other labels: what a syntactic reading of the type
    -- (a clause's form) may still tell apart.
    let other := match r with
      | .ok A => cls == "identical" && norm A != norm C
      | .error _ => false
    if other then
      samples := samples.push (Json.mkObj [("span", toJson span), ("kind", toJson kind), ("class", toJson "same meaning, other labels"),
        ("computed", toJson (match r with | .ok A => reprStr (A.map fun l => PositiveRules.expand (SourceTypes.graph T) [l]) | .error m => m)),
        ("claimed", toJson (reprStr (C.map fun l => PositiveRules.expand (SourceTypes.graph T) [l])))])
    if cls != "identical" then
      samples := samples.push (Json.mkObj [("span", toJson span), ("kind", toJson kind), ("class", toJson cls),
        ("computed", toJson (match r with | .ok A => shown T A | .error m => s!"({m})")),
        ("claimed", toJson (shown T C))])
  for (pos, vars) in fc.envs do
    let computed := w.entries.get? pos
    for (n, cand) in vars do
      let some C := (SourceClaims.resolve T cand).toOption | continue
      let r : Except String (Ty Tree) := match computed with
        | none => .error "statement not reached by the walk"
        | some vs => match vs.lookup n with
          | some A => .ok A
          | none => .error s!"binding not held by the walk (held: {vs.map (·.1)})"
      let cls := match r with
        | .ok A => classify T A C
        | .error _ => "undetermined"
      counts := bump counts ("entry", cls)
      if cls != "identical" then
        samples := samples.push (Json.mkObj [("pos", toJson pos), ("name", toJson n), ("kind", toJson "entry"),
          ("class", toJson cls),
          ("computed", toJson (match r with | .ok A => shown T A | .error m => s!"({m})")),
          ("claimed", toJson (shown T C))])
  return (counts, samples)

/-- A unit's walk over the store `T`, from its parameters' written types
and the module values `module` it reads: what it records, and the grown
store. -/
def walkUnit (T : EquationStore.State) (f : Fragment.Fn)
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := []) :
    Except String (Walk × EquationStore.State) := do
  let action : Compiler (Walk × EquationStore.State) := do
    let mut vars : List (String × Ty Tree) := []
    for (n, ty) in module do
      match ← tryCatch (some <$> ty) fun _ => pure none with
      | some A => vars := upd vars n A
      | none => pure ()
    for p in f.params do
      match ← tryCatch (some <$> lower (Fragment.translate p.ty)) fun _ => pure none with
      | some A => vars := upd vars p.name A
      | none => pure ()
    let env : Env := { vars, decl := vars }
    let expected ← tryCatch (some <$> lower (Fragment.translate f.ret)) fun _ => pure none
    let (_, w) ← (stmts (some env) f.body).run { generics, expected, entries := (({} : Std.HashMap Nat _).insert 0 vars).insert f.namePos.1 vars }
    return (w, ← table)
  let ((w, T'), _) ← runCompiler T [] action
  return (w, T')

/-- A unit's walk compared with its claims. -/
def compareUnit (T : EquationStore.State) (f : Fragment.Fn) (fc : SourceClaims.Function Tree)
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := []) :
    Except String Json := do
  let (w, T') ← walkUnit T f module generics
  let (counts, samples) := compareWalk T' fc w
  return Json.mkObj [
    ("counts", Json.arr (counts.toArray.map fun ((k, c), n) =>
      Json.mkObj [("kind", toJson k), ("class", toJson c), ("n", toJson n)])),
    ("samples", Json.arr samples)]

/-- A unit's claims with what the walk computes in place of what a producer
infers: every expression's type, every statement entry's bindings and every
`let`'s storage contract, at each execution point alike; no asserted field
contents, entry facts or per-closure overlays. The signature, footprints and
the execution points' names are the unit's own (`fc`). The first undetermined
type the lowering would read is the unit's refusal there. -/
def retypeUnit (T : EquationStore.State) (f : Fragment.Fn) (fc : SourceClaims.Function Tree)
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := [])
    (parts : String := "xec") :
    Except String (EquationStore.State × SourceClaims.Function Tree) := do
  let (w, T') ← walkUnit T f module generics
  let exprs : List (Span × SourceClaims.Candidate Tree) := w.exprs.toList.map fun (span, (_, r)) =>
    (span, r.mapError fun m => s!"not handled: {m} (type undetermined)")
  let envs : List (Nat × List (String × SourceClaims.Candidate Tree)) :=
    w.entries.toList.map fun (pos, vars) => (pos, vars.map fun (n, A) => (n, .ok A))
  let contracts : SourceClaims.Contracts Tree := w.contracts.map fun (k, D) => (k, .ok D)
  -- Debugging: which parts are replaced (`x` expressions, `e` entries, `c`
  -- contracts), the claims' kept for the others.
  let claimed := fc.exprs.foldl (fun (acc : List (Span × SourceClaims.Candidate Tree)) (sp, c) =>
    if (acc.lookup sp).isSome then acc else (sp, c) :: acc) []
  let lo := ((parts.splitOn ":")[1]?.bind String.toNat?).getD 0
  let hi := ((parts.splitOn ":")[2]?.bind String.toNat?).getD 0
  let exprs := if parts.contains 'x' then
      (if hi > 0 then claimed.filter (fun (sp, _) => lo ≤ sp.1 && sp.1 < hi) ++
        exprs.filter (fun (sp, _) => !(lo ≤ sp.1 && sp.1 < hi)) else exprs)
    else claimed
  let envs := if parts.contains 'e' then envs else fc.envs
  let contracts := if parts.contains 'c' then contracts else fc.contracts
  -- The entry facts are the given ones (class (d) of the single pass's
  -- draft, section 8): the unit's own, kept per point.
  -- Debugging: `k` keeps the claims' asserted field contents (`current`).
  let keep := parts.contains 'k'
  return (T', { fc with
    exprs, envs, contracts
    entryCurrent := if keep then fc.entryCurrent else []
    exprCurrent := if keep then fc.exprCurrent else []
    arrowClaims := []
    points := fc.points.map fun (id, row) =>
      (id, { row with exprs := exprs, envs := envs,
                      entryCurrent := if keep then row.entryCurrent else [],
                      exprCurrent := if keep then row.exprCurrent else [] }) })

end Verification.SourceExtraction.Synthesis
