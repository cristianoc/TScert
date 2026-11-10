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

/-- A call of a generic module function: its signature at fresh binders,
each binder matched against the actuals (`matchBinder`), then its signature
at what they say, and the result of the signature the actuals select. -/
def genericResult (g : Generic) (As : List (Ty Tree)) (typeArgs : List Json := []) :
    Compiler (Ty Tree × Ty Tree) := do
  if !typeArgs.isEmpty then
    -- Explicit type arguments are the binders' types, in order.
    if typeArgs.length != g.binders.length then throw "explicit type arguments of another count than the binders"
    let inst ← lower (do Fragment.translate (← g.instantiate (g.binders.zip typeArgs)))
    return (inst, (← choose (← callSigsOf inst) As).result)
  let ps ← lower (modifyGet fun T => let (T, ps) := EquationStore.binders T g.binders; (ps, T))
  let fresh ← lower (do Fragment.translate (← g.instantiate (g.binders.zip (ps.map fun p => graphJson [p]))))
  let sigs ← callSigsOf fresh
  let some s := sigs.head? | throw "a generic function of no call signature"
  let mut θ : List (String × Json) := []
  for (n, b) in g.binders.zip ps do
    let mut found : Option (Ty Tree) := none
    for (P, A) in s.params.zip As do
      if found.isNone then found ← matchBinder b P A
    let some B := found | throw s!"the type argument for '{n}' is not an actual's type"
    θ := θ ++ [(n, graphJson B)]
  let inst ← lower (do Fragment.translate (← g.instantiate θ))
  return (inst, (← choose (← callSigsOf inst) As).result)

/-- The member `o.k` names, `o` of type `O`: its own (a host-relative
member), else its prototype's; with the type it is read from. -/
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

/-- Each binder of a scheme matched against the parameters it occurs in
(`matchBinder`), the receiver first: the instance the actuals say, as one
signature, and its result. -/
def schemeCall (s : PositiveGraphs.SchemeRow Tree) (O : Ty Tree) (As : List (Ty Tree)) :
    Compiler (Ty Tree × Ty Tree) := do
  let T ← table
  let G := SourceTypes.graph T
  let fits (a : CallEffects.Arrow (Ty Tree)) : Bool :=
    As.length ≤ a.arguments.length && (a.arguments.drop As.length).all (admitsUndefined G)
  -- A variadic signature (`push(...items: T[])`): its fixed parameters, then
  -- each further actual at the element its rest's argument list states.
  let variadic : Option (CallEffects.RestArrow (Ty Tree) × CallEffects.Arrow (Ty Tree)) :=
    s.variadic.findSome? fun r =>
      if r.arguments.1.length ≤ As.length then
        match PositiveRules.expand G r.arguments.2 with
        | [.pack t []] => t.rest.map fun E =>
          (r, ⟨r.receiver, r.arguments.1 ++ (As.drop r.arguments.1.length).map (fun _ => E), r.result, r.effect⟩)
        | _ => none
      else none
  let some a := s.signatures.find? fits <|> variadic.map (·.2)
    | throw "no signature of the generic member admits the actuals' count"
  let mut σ : List (Tree × Ty Tree) := []
  for b in s.binders do
    let mut found : Option (Ty Tree) := none
    for (P, A) in (a.receiver, O) :: a.arguments.zip As do
      if found.isNone then found ← tryCatch (matchBinder b P A) fun _ => pure none
    let some B := found | throw "a type argument of the generic member is not an actual's type"
    σ := σ ++ [(b, B)]
  let sub (A : Ty Tree) : Ty Tree := norm (A.flatMap (EquationLowering.treeReplace (fun u => σ.lookup u)))
  let inst := a.map sub
  -- The instance as the member states it: a variadic one keeps its rest.
  match s.signatures.find? fits, variadic with
  | none, some (r, _) =>
    let r' := r.map sub
    return ([← lower (SourceTypes.use (.arrs [] [r']))], inst.result)
  | _, _ => return ([← lower (SourceTypes.use (.arrs [inst] []))], inst.result)

/-- A generic callee at explicit type arguments: its binders, in order, at
the types written, and the result of its first signature admitting the
actuals' count. -/
def explicitCall (s : PositiveGraphs.SchemeRow Tree) (θ : List (Ty Tree)) (As : List (Ty Tree)) :
    Compiler (Ty Tree) := do
  let G ← graphNow
  if θ.length != s.binders.length then throw "explicit type arguments of another count than the binders"
  let σ := s.binders.zip θ
  let sub (A : Ty Tree) : Ty Tree := norm (A.flatMap (EquationLowering.treeReplace (fun u => σ.lookup u)))
  let some a := s.signatures.find? fun a =>
      As.length ≤ a.arguments.length && (a.arguments.drop As.length).all (admitsUndefined G)
    | throw "no signature of the generic callee admits the actuals' count"
  return sub a.result

/-- `o.k(…)` with `o` of type `O` and actuals of types `As`: the method's
type and the call's result. The member is the object's own, its
prototype's (`memberFor`), or a field holding a callable; a generic one is
instantiated at the call (`schemeCall`). -/
def methodCall (vars : List (String × Ty Tree)) (O : Ty Tree) (fld : PropKey) (As : List (Ty Tree)) :
    Compiler (Ty Tree × Ty Tree) := do
  let G ← graphNow
  if let some m ← memberFor vars O fld then
    if m.calls.isEmpty && m.rests.isEmpty then
      let some s := m.schemes.head?.bind fun S => S.head?.bind G.schemes | throw "a member of no signature"
      return ← schemeCall s O As
    let M ← prim (.arrs (m.calls.map (·.withReceiver O)) (m.rests.map (·.withReceiver O)))
    return (M, (← choose (← memberSigs m) As).result)
  let F ← readField vars O fld
  if let [l] := F then
    if let some s := G.schemes l then return ← schemeCall s O As
  return (F, (← choose (← callSigsOf F) As).result)

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

/-- An empty array literal where a declared type is expected: the arrays
of that type (TypeScript's contextual typing of `[]`, whose own type would
be an array of no element). Any other value keeps its type `A`. -/
partial def contextual (D : Option (Ty Tree)) (x : Expr) (A : Option (Ty Tree)) : W (Option (Ty Tree)) := do
  let .arrayLit _ [] _ := x | return A
  let some D := D | return A
  let G ← StateT.lift graphNow
  let arrays := D.filter fun l => (storeOf G [l]).isSome
  if arrays.isEmpty then return A
  record x (.ok arrays)

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
      return norm ((← slice L .truthy !andOp) ++ R)
    return (A, (join (some (← refine e1 l !andOp)) (some e2)).getD e2)
  | .coalesce _ l r =>
    let (L, e1) ← expr env l
    let (R, e2) ← expr e1 r
    -- `a ?? b`: `a` less null and undefined, or `b`.
    let A ← attempt e do return norm ((← nonNullish (← need L "the left operand")) ++ (← need R "the right operand"))
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
  | .build _ _ es =>
    let (_, e1) ← exprs env es
    return (← record e (.error "an object literal with spreads"), e1)
  | .read _ fld x =>
    let (O, e1) ← expr env x
    let narrowed := (memberPath e).bind fun p => e1.paths.lookup p
    let r ← attempt e do
      if let some P := narrowed then return P
      readField e1.vars (← need O "the receiver") fld
    return (r, e1)
  | .write _ fld recv rhs =>
    let (_, e1) ← expr env recv
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
  | .indexWrite _ _ recv key rhs | .elemWrite _ recv key rhs =>
    let (_, e1) ← expr env recv
    let (_, e2) ← expr e1 key
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
    let (L, e1) ← expr env target
    let (R, e2) ← expr e1 rhs
    let r ← attempt e do
      let L ← need L "the target"
      let R ← need R "the right operand"
      let kept ← match op with
        | .nullish => nonNullish L
        | .orElse => slice L .truthy true
        | .andAlso => slice L .truthy false
      return norm (kept ++ R)
    let e3 ← match target, r with
      | .var _ n, some A => pure { e2 with vars := upd e2.vars n A, paths := e2.paths.filter (·.1.1 != n) }
      | _, _ => pure e2
    return (r, e3)
  | .nullishAssign _ n namePos rhs =>
    recordAt namePos "identifier" (match env.vars.lookup n with
      | some A => .ok A
      | none => .error s!"'{n}' is bound outside what the walk sees")
    let (R, e1) ← expr env rhs
    let R ← contextual (env.decl.lookup n) rhs R
    let r ← attempt e do
      let some L := env.vars.lookup n | throw s!"'{n}' is bound outside what the walk sees"
      return norm ((← nonNullish L) ++ (← need R "the right operand"))
    let e2 := match r with
      | some A => { e1 with vars := upd e1.vars n A, paths := e1.paths.filter (·.1.1 != n) }
      | none => e1
    return (r, e2)
  | .assign _ n _ rhs =>
    let (R, e1) ← expr env rhs
    let R ← contextual (env.decl.lookup n) rhs R
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
    let (A, e1) ← expr env target
    let (_, e2) ← exprs e1 sources
    return (← record e (match A with | some A => .ok A | none => .error "the target undetermined"), e2)
  | .lambda _ receiver _ params defaults _ _ _ _ _ _ body =>
    -- The closure's own walk: its parameters at their written types, and
    -- every binding it captures at its declared type.
    let captured := env.vars.map fun (n, A) => (n, (env.decl.lookup n).getD A)
    let mut vars := captured
    for (n, ty) in params do
      match ← StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none) with
      | some A => vars := upd vars n A
      | none => vars := vars.filter (·.1 != n)
    if let some (ty, _) := receiver then
      match ← StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none) with
      | some A => vars := upd vars "this" A
      | none => pure ()
    let inner : Env := { vars, decl := vars, paths := [] }
    for (_, d) in defaults do let _ ← expr inner d
    let saved := (← get).breaks
    -- An expression body's entry is its prologue's, at the body's start.
    modify fun w => { w with entries := w.entries.insert body.span.1 inner.vars }
    let _ ← expr inner body
    modify fun w => { w with breaks := saved }
    return (← record e (.error "a function value"), env)
  | .ctor _ lam statics =>
    let _ ← expr env lam
    let (_, e1) ← exprs env (statics.map (·.2))
    return (← record e (.error "a class value"), e1)
  | .block _ ss =>
    let _ ← stmts (some env) ss
    return (← record e (.error "a function body"), env)
  | .construct _ callee args spreads typeArgs =>
    let (F, e1) ← expr env callee
    let (As, e2) ← exprs e1 args
    let r ← attempt e do
      if !spreads.isEmpty then throw "a construction with spreads"
      let F ← need F "the class"
      let As ← As.mapM (need · "an actual")
      let G ← graphNow
      if let [l] := F then
        if let some s := G.schemes l then
          if typeArgs.isEmpty then return (← schemeCall s [Labels.undef] As).2
          return ← explicitCall s (← typeArgs.mapM fun t => lower (Fragment.translate t)) As
      match PositiveRules.expand G F with
      | [.ctors L S ..] =>
        let sigs := L.map (fun a => (⟨a.arguments, false, a.result⟩ : Sig)) ++
          S.map (fun a => ⟨a.arguments.1, true, a.result⟩)
        return (← choose sigs As).result
      | _ => throw "a construction of a value of no construct signature"
    return (r, e2)
  | .call _ callee args spreads typeArgs =>
    let (F, e1) ← expr env callee
    let (As, e2) ← exprs e1 args
    let gs := (← get).generics
    let generic := match callee with
      | .var _ n => gs.lookup n
      | _ => none
    if let some g := generic then
      let r ← StateT.lift (tryCatch (do
          if !spreads.isEmpty then throw "a call with spreads"
          let As ← As.mapM (need · "an actual")
          return Except.ok (← genericResult g As typeArgs)) fun m => pure (.error m))
      match r with
      | .ok (inst, R) =>
        let _ ← record callee (.ok inst)
        return (← record e (.ok R), e2)
      | .error m => return (← record e (.error m), e2)
    let r ← attempt e do
      if !spreads.isEmpty then throw "a call with spreads"
      let As ← As.mapM (need · "an actual")
      callResult (← need F "the callee") As
    return (r, e2)
  | .callWithReceiver _ callee recv args =>
    let (F, e1) ← expr env callee
    let (_, e2) ← expr e1 recv
    let (As, e3) ← exprs e2 args
    let r ← attempt e do callResult (← need F "the callee") (← As.mapM (need · "an actual"))
    return (r, e3)
  | .applyWithReceiver _ callee recv list _ =>
    let (_, e1) ← expr env callee
    let (_, e2) ← expr e1 recv
    let e3 ← match list with
      | some l => do pure (← expr e2 l).2
      | none => pure e2
    return (← record e (.error "a call through apply"), e3)
  | .bindWithReceiver _ callee recv args =>
    let (_, e1) ← expr env callee
    let (_, e2) ← expr e1 recv
    let (_, e3) ← exprs e2 args
    return (← record e (.error "a bound function"), e3)
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
    let (As, e2) ← exprs e1 args
    let r ← StateT.lift (tryCatch (do
        if !spreads.isEmpty then throw "a call with spreads"
        let some fld := fld | throw "a method of a computed key"
        let O ← need O "the receiver"
        let As ← As.mapM (need · "an actual")
        return Except.ok (← methodCall e1.vars O fld As)) fun m => pure (.error m))
    let r ← match r with
      | .ok (M, R) => do
        let _ ← record callee (.ok M)
        record e (.ok R)
      | .error m => do
        let _ ← record callee (.error m)
        record e (.error m)
    return (r, e2)
  | .ifBody _ c t f =>
    let (_, e1) ← expr env c
    let (A, e2) ← expr (← refine e1 c true) t
    let (B, e3) ← expr (← refine e1 c false) f
    let r ← attempt e do return norm ((← need A "the true arm") ++ (← need B "the false arm"))
    return (r, (join (some e2) (some e3)).getD e2)

partial def exprs (env : Env) (es : List Expr) : W (List (Option (Ty Tree)) × Env) := do
  let mut env := env
  let mut out := []
  for x in es do
    let (A, e') ← expr env x
    out := out ++ [A]
    env := e'
  return (out, env)

/-- A call's result: the result of the callee's signature the actuals select
(`selectSignature`'s choice, `choose`). -/
partial def callResult (F : Ty Tree) (As : List (Ty Tree)) : Compiler (Ty Tree) := do
  let G ← graphNow
  if let [l] := F then
    if let some s := G.schemes l then return (← schemeCall s [Labels.undef] As).2
  let sigs ← callSigsOf F
  if sigs.isEmpty then throw "a call of a value of no call signature"
  return (← choose sigs As).result

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
  for s in ss do
    let some e := env | return none
    modify fun w => { w with entries := w.entries.insert s.pos.1 e.vars }
    env ← stmt e s
  return env

partial def collectBreaks (label : Option String) (saved : List (Option String × Env)) : W (Option Env) := do
  let w ← get
  let (mine, others) := w.breaks.partition (·.1 == label)
  set { w with breaks := others ++ saved }
  return mine.foldl (fun acc (_, b) => join acc (some b)) none

partial def stmt (env : Env) (s : Stmt) : W (Option Env) := do
  match s with
  | .ret _ x | .throw _ x =>
    let _ ← expr env x
    return none
  | .effect _ x => return some (← expr env x).2
  | .constants _ bs =>
    let mut env := env
    for b in bs do
      let (A, e1) ← expr env b.init
      env := e1
      let D ← match b.annot with
        | some ty => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
        | none => pure A
      let A ← if b.annot.isSome then contextual D b.init A else pure A
      match D, A with
      | some D, some A =>
        env := { env with vars := upd env.vars b.name (← StateT.lift (assigned D A)), decl := upd env.decl b.name D }
      | some D, none => env := { env with vars := upd env.vars b.name D, decl := upd env.decl b.name D }
      | none, _ => env := { env with vars := env.vars.filter (·.1 != b.name) }
    return some env
  | .mutables _ bs =>
    let mut env := env
    for b in bs do
      let (A, e1) ← expr env b.init
      env := e1
      let D ← match b.annot, A with
        | some ty, _ => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
        | none, some A => some <$> StateT.lift (widen A)
        | none, none => pure none
      let A ← if b.annot.isSome then contextual D b.init A else pure A
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
          | none => .error "binding not held by the walk"
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

/-- Walk a unit's body over the store `T` from its parameters' written types
and the module values `module` it reads, and compare the result with its
claims. -/
def compareUnit (T : EquationStore.State) (f : Fragment.Fn) (fc : SourceClaims.Function Tree)
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := []) :
    Except String Json := do
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
    let (_, w) ← (stmts (some env) f.body).run { generics }
    return (w, ← table)
  let ((w, T'), _) ← runCompiler T [] action
  let (counts, samples) := compareWalk T' fc w
  return Json.mkObj [
    ("counts", Json.arr (counts.toArray.map fun ((k, c), n) =>
      Json.mkObj [("kind", toJson k), ("class", toJson c), ("n", toJson n)])),
    ("samples", Json.arr samples)]

end Verification.SourceExtraction.Synthesis
