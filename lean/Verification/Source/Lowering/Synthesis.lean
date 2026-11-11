import Verification.Source.SourceExtraction
import Verification.Source.Claims.Schemes

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
  /-- Reached only through an arm a test leaves no value of a binding it
  held (an exhaustive test's remaining arm): walked for its entries, where
  it completes or returns unreached. -/
  ghost : Bool := false

/-- A generic module function: its binders' names and its signature at
given binder types, in claim form (`Instantiable.instantiate`). -/
structure Generic where
  binders : List String
  instantiate : List (String × Json) → SourceTypes.Lowering Json
  /-- Its binders a resolution qualifies, by position: each one's input,
  observation and result. -/
  resolution : List PositiveGraphs.ResolutionSlots := []

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
  /-- Whether a call in it may leave a changed heap on its throw: one whose
  instance states no bound on a throw (`onThrow`). -/
  throwWrites : Bool := false
  /-- The changes it may make, by class of contents: to the old locations
  holding a value, and to those holding an array store. -/
  valueChange : Footprints.Change := .keep
  storeChange : Footprints.Change := .keep
  locals : List String := []
  exprs : Std.HashMap Span (String × Except String (Ty Tree)) := {}
  /-- Each call of a generic module function, by its span: the type each
  binder takes at it, by the binder's name; and the last call's, until its
  call records it. -/
  instances : List (Span × List (String × Ty Tree)) := []
  /-- Each such call's certificate for each binder a resolution qualifies,
  by its span; and the last call's. -/
  resolutions : List (Span × List (String × ResolutionWire.Certificate)) := []
  lastResolution : List (String × ResolutionWire.Certificate) := []
  /-- The unit's own scheme row where a resolution qualifies its binders,
  with their names: what a certificate's binder names. -/
  scope : Option (PositiveGraphs.SchemeRow Tree × List String) := none
  /-- Adversarial proposals forced, for the referee's measurement
  (`TSCERT_FORCE`): `literals` states every function literal at keep/keep,
  `elements` every element read without `undefined`, `objects` every
  object literal at its expected type, `spreads` every spread with every
  key its operand's type states. -/
  force : List String := []
  /-- Where the unit's body completes: its bindings there, or none where it
  never completes. -/
  completion : Option (List (String × Ty Tree)) := none
  lastInstance : Option (List (String × Ty Tree)) := none
  entries : Std.HashMap Nat (List (String × Ty Tree)) := {}
  /-- The bindings before each declaration of a statement declaring several,
  by the statement's start and the declared name: the entry of that
  declaration's own node. -/
  declarations : Std.HashMap (Nat × String) (List (String × Ty Tree)) := {}
  /-- Each statement entry's narrowed member paths, by root: what a test or
  a write found a field to hold (the entry's `current` contents). -/
  currents : Std.HashMap Nat (List (String × List (List PropKey × Ty Tree))) := {}
  breaks : List (Option String × Env) := []
  /-- The bindings a function literal walked so far assigns that it does not
  declare (captured ones, held in cells). -/
  closureAssigned : List String := []
  /-- Whether a function literal is being walked. -/
  inLiteral : Bool := false
  /-- The constants in scope: a write of a key one's record may lack grows
  its type. -/
  consts : List String := []
  /-- Whether the last call may have changed a value of the heap (its
  instance's footprint): the narrowed paths end there. -/
  changedValues : Bool := false
  /-- The environments a `continue` of the innermost loop leaves with. -/
  continues : List Env := []

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

def slice (A : Ty Tree) (tag : Tag) (q : Bool) (literalOperand : Bool := false) : Compiler (Ty Tree) := do
  let G ← graphNow
  -- `unknown` (a `source` label) as the kinds of value the test does not
  -- contradict, where it contradicts some (`BranchRefinement.sourceSlice`).
  let kinds : List (PositiveNormalization.Clause (Ty Tree)) := BranchRefinement.sourceKinds
  -- Equality with a literal holding: a label of its family is that
  -- singleton (the value the test compares with).
  let one : Option (Compiler (Ty Tree)) := if !q || !literalOperand then none else match tag with
    -- (`0` equals `-0` too: no one number)
    | .numEq b => if b == (0 : Float).toBits || b == (-0 : Float).toBits then none else some (prim (.numLit b))
    | .strEq v => some (literal (.vstr v))
    | .boolEq v => some (pure [if v then Labels.tru else Labels.fls])
    | .bigintEq i => some (literal (.vbigint i))
    | _ => none
  -- `Array.isArray` holding: the labels the edge's observation keeps, the
  -- built-ins' `readonly unknown[]` for the records and `unknown` it does
  -- not (`arrayRefine`, `BranchRefinement.arraySlice`).
  if tag == .isArray && q && G.builtins.isSome then
    return norm (arrayRefine G A (← builtinArrayTy))
  let mut out : Ty Tree := []
  for a in BranchRefinement.tagSlice G A tag q do
    -- `k in x` holding: a record's optional `k` present (a field where the
    -- record states one, else a view); a dictionary not naming `k` states
    -- it as a view of its index.
    if let (.hasKey k, true) := (tag, q) then
      match PositiveRules.expand G [a] with
      | [.refs fs [] vs os ms bs st] =>
        if let some o := os.find? (·.key == k) then
          let os := os.filter (·.key != k)
          let c : PositiveNormalization.Clause (Ty Tree) :=
            if fs.isEmpty then .refs fs [] (vs ++ [(k, o.type)]) os ms bs st
            else .refs (fs ++ [(k, o.type)]) [] vs os ms bs st
          out := out ++ (← prim c)
          continue
      | [.dict fs [] vs ix os ms bs cells st] =>
        if (fs.lookup k).isNone && (vs.lookup k).isNone && !os.any (·.key == k) then
          if let .str _ := k then
            if !ix.isEmpty then
              out := out ++ (← prim (.dict fs [] (vs ++ [(k, norm (ix.flatMap (·.2)))]) ix os ms bs cells st))
              continue
      | _ => pure ()
    if let some S := one then
      match PositiveRules.expand G [a], tag with
      | [.num], .numEq _ | [.str], .strEq _ | [.bool], .boolEq _ | [.bigint], .bigintEq _ =>
        out := out ++ (← S)
        continue
      | _, _ => pure ()
    if G.plain a && PositiveRules.expand G [a] == [.source] then
      let kept := kinds.filter fun k => tagClause tag k != some (!q)
      if kept.length < kinds.length then
        for k in kept do out := out ++ (← prim k)
        continue
    out := out ++ [a]
  return norm out

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
def narrowTarget (env : Env) (target : Expr) (tag : Tag) (q : Bool) (literalOperand : Bool := false) : Compiler Env := do
  let slice (A : Ty Tree) (tag : Tag) (q : Bool) := slice A tag q literalOperand
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
    -- A member of an object only (a primitive's member is no location).
    let G ← graphNow
    let receiver ← tryCatch (some <$> path.dropLast.foldlM (fun B f => readField env.vars B f) A) fun _ => pure none
    let ofObject := path.getLast? != some lengthKey && receiver.any fun R => R.all fun l => (shapeOf G l).isNone
    if let some P := P then
      if ofObject then env := { env with paths := upd env.paths (root, path) (← slice P tag q) }
    if let [f] := path then
      let mut kept : Ty Tree := []
      for l in A do
        let keep ← tryCatch (do
            let B ← readField env.vars [l] f
            return !(← slice B tag q).isEmpty) fun _ => pure true
        if keep then kept := kept ++ [l]
      -- (none of them: the binding holds no value there)
      env := { env with vars := upd env.vars root kept }
    return env
  | none => return env

/-- A binding narrowed to a promised type `R`: its members within
`R`, else `R` (a type guard's true arm, an assertion's normal return). -/
def narrowTo (env : Env) (target : Expr) (R : Ty Tree) : Compiler Env := do
  let T ← table
  let at_ (A : Ty Tree) : Ty Tree :=
    let kept := A.filter fun a => within T [a] R
    if kept.isEmpty then R else kept
  match memberPath target with
  | some (root, []) =>
    let some A := env.vars.lookup root | return env
    return { env with vars := upd env.vars root (at_ A) }
  | _ => return env

/-- A write of key `k` at a value of type `R` on a constant of type `O` whose
records may lack it: the contract the key is added at (the optional field's
where a record states one, else the value's type, a literal's widened), and
`O` with every record owning it there (TypeScript's growth of a fresh
literal's keys, the write step's output). None where `O` is not records or
states `k` of each. -/
def growth (O : Ty Tree) (k : PropKey) (R : Ty Tree) (literal_ : Bool) : Compiler (Option (Ty Tree × Ty Tree)) := do
  let G ← graphNow
  let mut arms : List (List (PropKey × Ty Tree) × List (PropKey × Ty Tree) × List (OptionalField (Ty Tree)) ×
      List (MethodMembers.Sig (Ty Tree)) × List KeyBound × List PropKey) := []
  for l in O do
    let [.refs fs [] vs os ms bs st] := PositiveRules.expand G [l] | return none
    if fs.any (·.1 == SourceTypes.storeField) || fs.any (·.1 == SourceTypes.protoField) then return none
    arms := arms ++ [(fs, vs, os, ms, bs, st)]
  if arms.isEmpty then return none
  let lacks := arms.any fun (fs, vs, _, ms, _, _) => (fs.lookup k).isNone && (vs.lookup k).isNone && !ms.any (·.key == k)
  if !lacks then return none
  let declared := arms.findSome? fun (_, _, os, _, _, _) => (os.find? fun o => o.key == k && !o.readonly).map (·.type)
  let c ← match declared with
    | some D => pure D
    | none => if literal_ then widen R else pure R
  let mut grown : Ty Tree := []
  for (fs, vs, os, ms, bs, st) in arms do
    let bs := bs.map fun b => if b.among && !b.keys.contains k then { b with keys := b.keys ++ [k] } else b
    grown := grown ++ (← prim (.refs (fs.filter (·.1 != k) ++ [(k, c)]) [] (vs.filter (·.1 != k)) (os.filter (·.key != k)) ms bs st))
  return some (c, norm grown)

/-- Whether evaluating an expression may call: conservatively, any form
other than a name, a literal, a read and the tests and operators over them. -/
partial def mayCall : Expr → Bool
  | .var .. | .lit .. => false
  | .read _ _ x | .not _ x | .unary _ _ x | .shapeTest _ _ _ x | .tagMember _ _ _ _ _ x | .cast _ _ x => mayCall x
  | .equality _ _ l r | .singletonTest _ _ _ _ l r | .logical _ _ l r | .coalesce _ l r | .arith _ _ l r
  | .inKeys _ l r | .elemAt _ l r | .index _ _ l r => mayCall l || mayCall r
  | _ => true

/-- An environment's narrowed paths by root. -/
def currentOf (env : Env) : List (String × List (List PropKey × Ty Tree)) :=
  let roots := ((env.paths.filter (!·.2.isEmpty)).map (·.1.1)).eraseDups
  roots.map fun r => (r, (env.paths.filter (fun ((q, _), A) => q == r && !A.isEmpty)).map fun ((_, p), A) => (p, A))

/-- Whether a test leaves an arm unreached: a binding or a path it leaves no
value it held (an exhaustive test's remaining arm). The arm is still walked,
a ghost, for its entries, each binding so emptied at the empty type. -/
def emptiedBy (before after : Env) : Option Env :=
  let emptied (old : Option (Ty Tree)) (A : Ty Tree) : Bool := A.isEmpty && !(old.getD []).isEmpty
  let pathOld (p : String × List PropKey) : Option (Ty Tree) :=
    (before.paths.lookup p) <|> some [Labels.undef]
  if after.vars.any (fun (n, A) => emptied (before.vars.lookup n) A) ||
     after.paths.any (fun (p, A) => emptied (pathOld p) A) then
    some { after with ghost := true }
  else none

/-- The union of two environments where both are reached: each binding both
hold, at the union of its two types; each path both narrow, likewise. -/
def join : Option Env → Option Env → Option Env
  | none, b => b
  | a, none => a
  | some a, some b =>
    if a.ghost && !b.ghost then some b else if b.ghost && !a.ghost then some a else some {
      ghost := a.ghost
      vars := a.vars.filterMap fun (n, A) => (b.vars.lookup n).map fun B => (n, if A == B then A else norm (A ++ B))
      decl := a.decl ++ b.decl.filter fun (n, _) => (a.decl.lookup n).isNone
      paths := a.paths.filterMap fun (p, A) => (b.paths.lookup p).map fun B => (p, norm (A ++ B)) }

/-- The environment at a loop head: every binding the loop assigns at its
declared type, and no path narrowed (a loop head holds its given facts,
which state no field's contents). -/
def loopHead (env : Env) (ss : List Stmt) : Env :=
  let changed := env.vars.filter fun (n, _) => ss.any (assignsStmt n)
  { env with
    vars := env.vars.map fun (n, A) =>
      if changed.any (·.1 == n) then (n, (env.decl.lookup n).getD A) else (n, A)
    paths := [] }

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
  /-- A generic module function's binders' names, each of `binders`; or
  its explicit type arguments, by its binders' names. -/
  names : List String := []
  explicit : List (String × Ty Tree) := []
  /-- The binders a resolution qualifies, by position in `binders`. -/
  resolution : List PositiveGraphs.ResolutionSlots := []

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
  let hidden := g.resolution.flatMap (·.associated)
  if !typeArgs.isEmpty && hidden.isEmpty then
    if typeArgs.length != g.binders.length then throw "explicit type arguments of another count than the binders"
    let inst ← lower (do Fragment.translate (← g.instantiate (g.binders.zip typeArgs)))
    let θ ← typeArgs.mapM fun t => lower (Fragment.translate t)
    let G ← graphNow
    return { fixed := ProgramTyping.callSigs G inst, rests := ProgramTyping.restSigs G inst,
             explicit := g.binders.zip θ }
  -- Written type arguments of a scheme a resolution qualifies are its
  -- binders' but the resolutions' observations and results, which the
  -- call's resolution gives.
  let shown := (List.range g.binders.length).filter (!hidden.contains ·)
  if !typeArgs.isEmpty && typeArgs.length != shown.length then
    throw "explicit type arguments of another count than the binders"
  let θ ← typeArgs.mapM fun t => lower (Fragment.translate t)
  let ps ← lower (modifyGet fun T => let (T, ps) := EquationStore.binders T g.binders; (ps, T))
  let fresh ← lower (do Fragment.translate (← g.instantiate (g.binders.zip (ps.map fun p => graphJson [p]))))
  let G ← graphNow
  return { binders := ps, fixed := ProgramTyping.callSigs G fresh, rests := ProgramTyping.restSigs G fresh,
           names := g.binders, resolution := g.resolution, seed := (shown.filterMap (ps[·]?)).zip θ }

/-- Whether an actual is a callback: a function literal, typed by the
parameter it is passed at where it writes no parameter's type, and stated
at that parameter's signature (`walkLambda`). -/
def callback : Expr → Bool
  | .lambda .. => true
  | _ => false

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

/-- Whether the binder `b` occurs in a label. -/
partial def occurs (b : Tree) (t : Tree) : Bool :=
  t == b || match t with
    | .app _ args | .bound _ args _ => args.toList.any fun ts => ts.toList.any (occurs b)
    | .meet ps => ps.toList.any (occurs b)
    | _ => false

/-- What a parameter of type `P` says the binder `b` is, given an actual of
type `A`, matched structurally one level at a time (no search; the first
part mentioning `b` decides): `A` where `P` is `b`; in a union, the one
member mentioning `b` at `A` less what the others admit; in an application
of one head, its arguments at `A`'s of that head; in an array, its elements
at `A`'s; in a record, each field at `A`'s; in a callable, its result at
`A`'s. -/
partial def matchBinder (b : Tree) (P A : Ty Tree) (fuel : Nat := 6) : Compiler (Option (Ty Tree)) := do
  if isBinder b P then return some A
  if fuel == 0 || A.isEmpty then return none
  let T ← table
  let G := SourceTypes.graph T
  let (withB, others) := P.partition (occurs b)
  -- A union: the actual less what the members not mentioning `b` admit;
  -- each of its labels at the first member mentioning `b` it matches.
  let perLabel (A : Ty Tree) : Compiler (Option (Ty Tree)) := do
    if A.length < 2 then return none
    let mut out : Ty Tree := []
    for a in A do
      let mut got : Option (Ty Tree) := none
      for m in withB do
        if got.isNone then got ← matchBinder b [m] [a] (fuel - 1)
      let some B := got | return none
      out := out ++ B
    return some (norm out)
  let [l] := withB | do
    if withB.isEmpty then return none
    perLabel (A.filter fun a => !within T [a] others)
  if !others.isEmpty then
    let A' := A.filter fun a => !within T [a] others
    if let some B ← matchBinder b [l] A' (fuel - 1) then return some B
    return ← perLabel A'
  -- One head applied: its arguments, each at `A`'s of the same head.
  if let .app h ps := l then
    let same := A.filterMap fun a => match a with
      | .app h' as => if h' == h then some as else none
      | _ => none
    if same.length == A.length then
      for (Pi, i) in ps.toList.zipIdx do
        if Pi.toList.any (occurs b) then
          let Ai := norm (same.flatMap fun as => ((as.toList[i]?).map (·.toList)).getD [])
          if let some B ← matchBinder b Pi.toList Ai (fuel - 1) then return some B
  let first (xs : List (Ty Tree × Compiler (Ty Tree))) : Compiler (Option (Ty Tree)) := do
    for (Q, read) in xs do
      if Q.any (occurs b) then
        if let some B ← tryCatch (some <$> read) (fun _ => pure none) then
          if let some C ← matchBinder b Q B (fuel - 1) then return some C
    return none
  if let some S := storeOf G [l] then
    if let [.list t []] := PositiveRules.expand G S then
      let E := norm (t.required.flatten ++ t.optional.flatten ++ t.rest.getD [])
      if let some B ← first [(E, elementAt A none (missing := false))] then return some B
    return ← perLabel A
  let r ← match PositiveRules.expand G [l] with
  | [.dict _ _ _ ix _ _ _ _ _] => first [(norm (ix.flatMap (·.2)), elementAt A none (missing := false))]
  | [.refs fs [] vs os ms _ _] =>
    first (((fs ++ vs).filter (fun (k, _) => k != SourceTypes.protoField)).map (fun (k, F) => (F, readField [] A k)) ++
      os.map (fun o => (o.type, do slice (← readField [] A o.key) .isUndef false)) ++
      -- A method: its result at `A`'s member's.
      ms.map fun m => (norm (m.calls.flatMap (·.result)), do
        let some m' ← memberFor [] A m.key | throw "no member"
        let some a := m'.calls.head? | throw "no signature"
        pure a.result))
  | _ =>
    let some s := (ProgramTyping.callSigs G [l]).head? | return none
    first [(s.result, do
      let some r := (← callSigsOf A).head? | throw "no signature"
      pure r.result)]
  if r.isSome then return r
  perLabel A

/-- The callee `o.k(…)` calls, `o` of type `O`: the object's member, its
prototype's, or a field holding a callable. -/
def methodCallee (vars : List (String × Ty Tree)) (O : Ty Tree) (fld : PropKey) (callbacks : List Bool := []) :
    Compiler Callee := do
  if let some m ← memberFor vars O fld then
    if m.calls.isEmpty && m.rests.isEmpty then
      let some S := m.schemes.head? | throw "a member of no signature"
      let first ← calleeOf S O
      if !callbacks.any id then return first
      -- A member with several schemes (one per receiver label) called with
      -- callbacks: the scheme whose callback parameters take the most
      -- parameters, at which a walked callback admits every scheme's call.
      let G ← graphNow
      let width (c : Callee) : Nat := match c.fixed.find? (callbacks.length ≤ ·.arguments.length) with
        | some a => ((a.arguments.zip callbacks).filter (·.2)).foldl (fun (n : Nat) (P, _) =>
            n + (((ProgramTyping.callSigs G P).head?.map (·.arguments.length)).getD 0)) 0
        | none => 0
      let others ← m.schemes.tail.mapM fun S => calleeOf S O
      return others.foldl (fun (best c : Callee) => if Nat.blt (width best) (width c) then c else best) first
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

/-- The signature of a callable type taking the most parameters. -/
def widestOf (G : PositiveGraphs.NormalGraph Tree) (P : Ty Tree) : Option (CallEffects.Arrow (Ty Tree)) :=
  (ProgramTyping.callSigs G P).foldl (fun (best : Option (CallEffects.Arrow (Ty Tree))) a =>
    match best with
    | some b => if Nat.blt b.arguments.length a.arguments.length then some a else some b
    | none => some a) none

/-- The type expected of a key `k` of a literal where `P` is expected: the
union of the field each member of `P` states at `k`, a dictionary's index
included; none where no member states one. -/
def fieldExpected (P : Ty Tree) (k : PropKey) : Compiler (Option (Ty Tree)) := do
  let mut out : Ty Tree := []
  for l in P do
    if let some D ← tryCatch (some <$> readField [] [l] k) (fun _ => pure none) then
      out := out ++ D
  return if out.isEmpty then none else some (norm out)

/-- The array members of an expected type. -/
def arrayArms (G : PositiveGraphs.NormalGraph Tree) (P : Ty Tree) : List Tree :=
  P.filter fun l => (storeOf G [l]).isSome

/-- What an iterable other than an array yields, where `P` is expected:
for each member of `P` stating a method of a symbol key (its
`[Symbol.iterator]`), the `value` of each result of its iterator's `next`
that is not done. -/
def iteratedElement (P : Ty Tree) : Compiler (Option (Ty Tree)) := do
  let G ← graphNow
  let mut out : Ty Tree := []
  for l in P do
    if (storeOf G [l]).isSome then continue
    let [.refs _ [] _ _ ms _ _] := PositiveRules.expand G [l] | continue
    let some m := ms.find? (fun m => match m.key with | .sym _ => true | _ => false) | continue
    let some a := m.calls.head? | continue
    let some n ← memberFor [] a.result (.str "next") | continue
    let some r := n.calls.head? | continue
    for u in r.result do
      let done ← tryCatch (some <$> readField [] [u] (.str "done")) (fun _ => pure none)
      if done == some [Labels.tru] then continue
      if let some V ← tryCatch (some <$> readField [] [u] (.str "value")) (fun _ => pure none) then
        out := out ++ V
  return if out.isEmpty then none else some (norm out)

/-- The type expected of position `i` of an array literal where `P` is
expected: the union of the positions its array members state there, else
what its iterable members yield. -/
def positionExpected (P : Ty Tree) (i : Nat) : Compiler (Option (Ty Tree)) := do
  let G ← graphNow
  let mut out : Ty Tree := []
  for l in arrayArms G P do
    if let some B ← tryCatch (some <$> elementAt [l] (some i) (missing := false)) (fun _ => pure none) then
      out := out ++ B
  if out.isEmpty then return ← iteratedElement P
  return some (norm out)

/-- A call's fresh result (its signature stating `fresh`) where `H` is
expected: the first array member of `H` whose elements the result's are
within, the store the call allocates taking any contract
(`HasTyUsing.alloc`'s bound at a fresh result). -/
def freshAt (H R : Ty Tree) : Compiler (Option (Ty Tree)) := do
  let T ← table
  let G := SourceTypes.graph T
  if (storeOf G R).isNone then return none
  let E ← elementAt R none (missing := false)
  for l in arrayArms G H do
    if within T R [l] then return none
    let D ← elementAt [l] none (missing := false)
    if within T E D then return some [l]
  return none


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
def wrote (value store : Footprints.Change := .any) : W Unit :=
  modify fun w => { w with writes := true, valueChange := w.valueChange.max value, storeChange := w.storeChange.max store }

/-- An assignment of `n`: a change of the heap where the function literal
being walked does not declare `n`. -/
def assigns (n : String) : W Unit := do
  let w ← get
  if !w.locals.contains n then
    wrote .any .keep
    -- Inside a function literal, a captured binding.
    if w.inLiteral && !w.closureAssigned.contains n then
      modify fun w => { w with closureAssigned := n :: w.closureAssigned }

/-- An early binding's written contract (the flow graph's `.early` rule):
its annotation, else a function literal's written receiver, parameters (a
defaulted one admitting `undefined`) and result at its written effect, else
the ordinary one; none where the source states neither. -/
def earlyContract (b : Fragment.Binding) (effect : CallEffects.Effect := .ordinary) : W (Option (Ty Tree)) :=
  StateT.lift (tryCatch (some <$> match b.annot, b.init with
    | some ty, _ => lower (Fragment.translate ty)
    | none, .lambda _ receiver [] params defaults false (some result) _ stated _ _ _ => do
      let Ds ← params.zipIdx.mapM fun ((_, j), i) => do
        let D ← lower (Fragment.translate j)
        pure (if defaults.any (·.1 == i) then (D ++ [Labels.undef]).eraseDups else D)
      let R ← lower (Fragment.translate result)
      let Rt ← match receiver with
        | some (t, _) => lower (Fragment.translate t)
        | none => prim .top
      return [← lower (SourceTypes.use (.arrs [⟨Rt, Ds, R, stated.getD effect⟩] []))]
    | _, _ => throw "no written contract") fun _ => pure none)

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

/-- The environment after a call: its narrowed paths end where the call may
change a value of the heap, or where its callee is unknown. -/
partial def afterCall (env : Env) (r : Except String (Ty Tree × Ty Tree)) : W Env := do
  let w ← get
  if w.changedValues || r.toOption.isNone then
    -- A binding a function literal assigns is held in a cell the call may
    -- change: at its declared type again (`TSCERT_FORCE=stale` keeps it).
    let reset := if w.force.contains "stale" then [] else w.closureAssigned
    return { env with
      paths := []
      vars := env.vars.map fun (n, A) => if reset.contains n then (n, (env.decl.lookup n).getD A) else (n, A) }
  return env

/-- The narrowing a condition answering `q` makes. -/
partial def refine (env : Env) (c : Expr) (q : Bool) : W Env := do
  match c with
  | .var .. | .read .. => StateT.lift (narrowTarget env c .truthy q)
  | .not _ e => refine env e !q
  | .cast _ _ e => refine env e q
  | .logical _ andOp l r =>
    -- The right operand runs after the left's narrowing: a call in it ends
    -- the narrowed paths.
    let after (e : Env) : Env := if mayCall r then { e with paths := [] } else e
    if andOp == q then refine (after (← refine env l q)) r q
    else
      let a ← refine env l q
      let b ← refine (after (← refine env l !q)) r q
      return (join (some a) (some b)).getD a
  | .shapeTest _ tag equal e => StateT.lift (narrowTarget env e tag (equal == q))
  | .singletonTest _ tag equal testLeft l r =>
    let other := if testLeft then r else l
    StateT.lift (narrowTarget env (if testLeft then l else r) tag (equal == q) (match other with | .lit .. => true | _ => false))
  -- Strict equality with an operand of one value: the test of that value on
  -- the other operand (`comparisonsExpr`'s choice, `singletonTag`).
  | .equality _ equal l r =>
    let w ← get
    let typeOf (x : Expr) : Option (Ty Tree) := (w.exprs.get? x.span).bind (·.2.toOption)
    let G ← StateT.lift graphNow
    let isLit (x : Expr) : Bool := match x with | .lit .. => true | _ => false
    match (typeOf r).bind (singletonTag G), (typeOf l).bind (singletonTag G) with
    | some tag, _ => StateT.lift (narrowTarget env l tag (equal == q) (isLit r))
    | _, some tag => StateT.lift (narrowTarget env r tag (equal == q) (isLit l))
    | _, _ =>
      -- Equal to an operand holding one of several singletons: each
      -- operand the union of its slices at each singleton the other may
      -- hold (the lowering's split, one singleton at a time).
      if equal != q then return env
      let singletons (y : Expr) : Option (List Tag) :=
        (typeOf y).bind fun B => if B.isEmpty then none else B.mapM fun b => singletonTag G [b]
      let mut env := env
      for (x, y) in [(l, r), (r, l)] do
        if let some ts := singletons y then
          let mut out : Option Env := none
          for t in ts do out := join out (some (← StateT.lift (narrowTarget env x t true)))
          env := out.getD env
      return env
  -- A call of a type guard (`promise := guards p`): on its true arm its
  -- actual `p` at the guarded type (`PromiseCalls`' implication).
  | .call _ callee args _ _ | .callWithReceiver _ callee _ args =>
    if !q then return env
    promised env callee args false
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

/-- The environment where a call of a guard (or, `asserts`, an assertion
function) of the callee's recorded type holds: the actual its promise names
at the signature's guarded type, the first signature stating one whose
parameters admit the actuals' recorded types. -/
partial def promised (env : Env) (callee : Expr) (args : List Expr) (asserts : Bool) : W Env := do
  let w ← get
  let typeOf (x : Expr) : Option (Ty Tree) := (w.exprs.get? x.span).bind (·.2.toOption)
  let some F := typeOf callee | return env
  let T ← StateT.lift table
  let G := SourceTypes.graph T
  for s in ProgramTyping.callSigs G F do
    let p? := match s.effect.promise with
      | some (.guards p) => if asserts then none else some p
      | some (.asserts p) => if asserts then some p else none
      | none => none
    let some p := p? | continue
    let admits := (args.zip s.arguments).all fun (x, D) => match typeOf x with
      | some A => within T A D
      | none => true
    if !admits || args.length < p + 1 then continue
    let some x := args[p]? | continue
    return ← StateT.lift (narrowTo env x s.result)
  return env

/-- An expression's type, recorded at its occurrence, and the environment
after it; where a type `exp` is expected of its value (a return's, an
annotated declaration's, an assignment's, a field's, a parameter's), a
literal, a function literal or a fresh store made at it (`fit`), and each
part of it walked at the part's expected type. -/
partial def expr (env : Env) (e : Expr) (exp : Option (Ty Tree) := none) : W (Option (Ty Tree) × Env) := do
  let forceElements := (← get).force.contains "elements"
  let forceSpreads := (← get).force.contains "spreads"
  match e with
  | .var _ n =>
    let r := match env.vars.lookup n with
      | some A => .ok A
      | none => .error s!"'{n}' is bound outside what the walk sees"
    return (← record e r, env)
  | .lit _ v => return (← attempt e (literal v), env)
  | .logical _ andOp l r =>
    let (L, e1) ← expr env l
    let (R, e2) ← expr (← refine e1 l andOp) r exp
    let A ← attempt e do
      let L ← need L "the left operand"
      let R ← need R "the right operand"
      -- `a && b`: `a`'s falsy part or `b`; `a || b`: `a`'s truthy part or `b`.
      joinTy (← slice L .truthy !andOp) R
    return (A, (join (some (← refine e1 l !andOp)) (some e2)).getD e2)
  | .coalesce _ l r =>
    let (L, e1) ← expr env l
    let (R, e2) ← expr e1 r exp
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
    -- `x as T`: the operand made at `T`.
    let target ← match annot with
      | some ty => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
      | none => pure none
    let (A, e1) ← expr env x target
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
        | some Es => do
          let r ← attempt e (lower do
            let s ← SourceTypes.use (.list ⟨Es, [], none, true, .dense⟩ [])
            let T ← get
            return [← SourceTypes.use (SourceTypes.arrayOf T s true)])
          -- The operand is made at its const type.
          if let some C := r then let _ ← record x (.ok C)
          pure r
        | none => pure r
      -- `{…} as const`: the record of its fields' own types, made so.
      | none, .alloc _ names es => do
        let w ← get
        match es.mapM (fun y => (w.exprs.get? y.span).bind (·.2.toOption)) with
        | some Es => do
          let r ← attempt e (prim (.refs (names.zip Es) [] [] [] [] [⟨true, names⟩] []))
          if let some C := r then let _ ← record x (.ok C)
          pure r
        | none => pure r
      | _, _ => pure r
    return (r, e1)
  | .alloc _ names es =>
    -- Each field walked at the field the expected type states at its key.
    let mut e1 := env
    let mut As : List (Option (Ty Tree)) := []
    for (k, y) in names.zip es do
      let D ← match exp with
        | some P => StateT.lift (fieldExpected P k)
        | none => pure none
      let (A, e') ← expr e1 y D
      As := As ++ [A]
      e1 := e'
    let r ← attempt e do
      let fields ← (names.zip As).mapM fun (n, A) => do return (n, ← widen (← need A "a field"))
      -- Its own keys exactly (`HasTyUsing.alloc`'s bound).
      prim (.refs fields [] [] [] [] [⟨true, names⟩] [])
    let r ← match exp with
      | some P => fit P e r
      | none => pure r
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
              if f != SourceTypes.protoField && f != SourceTypes.storeField && (forceSpreads || !ms.any (·.key == f)) then
                fields := upd fields f B
                optional := optional.filter (·.key != f)
            -- An optional field the spread may lack keeps an earlier value.
            for o in os do
              if forceSpreads then
                fields := upd fields o.key o.type
                optional := optional.filter (·.key != o.key)
              else if (fields.lookup o.key).isNone then optional := o :: optional.filter (·.key != o.key)
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
    wrote .any (if fld == lengthKey then .any else .keep)
    let (O, e1) ← expr env recv
    -- The reference `recv.fld`, as the read gives it.
    let mut D : Option (Ty Tree) := none
    if let .str f := fld then
      let r ← StateT.lift (tryCatch (do
          return Except.ok (← readField e1.vars (← need O "the receiver") fld)) fun m => pure (.error m))
      recordAt (recv.span.1, recv.span.2 + 1 + f.length) "member read" r
      D := r.toOption
    -- The value made at the field's type.
    let (R, e2) ← expr e1 rhs D
    -- A write ends the narrowing of every path through the field.
    let e2 := { e2 with paths := e2.paths.filter fun ((_, p), _) => !p.contains fld }
    -- A key a constant's records may lack: the write at the contract it adds
    -- the key at, and the constant's records owning it after.
    if let (.var _ n, some O, some R) := (recv, O, R) then
      if (← get).consts.contains n then
        let literal_ := match rhs with | .var .. | .read .. => false | _ => true
        if let some (c, grown) ← StateT.lift (tryCatch (growth O fld R literal_) fun _ => pure none) then
          return (← record e (.ok c), { e2 with vars := upd e2.vars n grown })
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
        | none => elementAt O (← keyIndex K) (missing := !forceElements)
    return (r, e2)
  | .elemWrite p recv key rhs => expr env (.indexWrite p none recv key rhs)
  | .indexWrite _ field recv key rhs =>
    -- An element write changes values and grows stores (`writeWithinAt`).
    wrote .any .grow
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
    -- The value made at the contents' type.
    let D ← match r with
      | .ok B => some <$> StateT.lift (slice B .isUndef false)
      | .error _ => pure none
    let (R, e3) ← expr e2 rhs D
    return (← record e (match R with | some R => .ok R | none => .error "the value undetermined"), e3)
  | .elemAt _ x key =>
    let (O, e1) ← expr env x
    let (K, e2) ← expr e1 key
    let r ← attempt e do elementAt (← need O "the receiver") (← keyIndex (← need K "the key")) (missing := !forceElements)
    return (r, e2)
  | .arrayLit _ es spreads =>
    -- Each element walked at the position the expected type states.
    let mut e1 := env
    let mut As : List (Option (Ty Tree)) := []
    for (y, i) in es.zipIdx do
      let D ← match exp with
        | some P => if spreads.contains i then pure none else StateT.lift (positionExpected P i)
        | none => pure none
      let (A, e') ← expr e1 y D
      As := As ++ [A]
      e1 := e'
    let r ← attempt e do
      let mut elems : Ty Tree := []
      for (A, i) in As.zipIdx do
        let A ← need A "an element"
        let B ← if spreads.contains i then elementAt A none (missing := false) else widen A
        elems := elems ++ B
      let elems' := norm elems
      -- Made where no type is expected: holes read as `undefined` where its
      -- elements admit it (the presence a mutable array's contract states).
      lower do
        let s ← SourceTypes.use (.list ⟨[], [], some elems', false, .readable⟩ [])
        let T ← get
        return [← SourceTypes.use (SourceTypes.arrayOf T s false)]
    let r ← match exp with
      | some P => fit P e r
      | none => pure r
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
    let (R, e2) ← expr e1 r exp
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
    let D := match target with
      | .var _ n => env.decl.lookup n
      | _ => none
    let (R, e2) ← expr e1 rhs D
    let r ← attempt e do
      let L ← need L "the target"
      let R ← need R "the right operand"
      let kept ← match op with
        | .nullish => nonNullish L
        | .orElse => slice L .truthy true
        | .andAlso => slice L .truthy false
      joinTy kept R
    -- The right operand runs on one path only: the bindings after it joined
    -- with those before it.
    let e2 := (join (some e1) (some e2)).getD e2
    let e3 ← match target, r with
      | .var _ n, some A => pure { e2 with vars := upd e2.vars n A, paths := e2.paths.filter (·.1.1 != n) }
      | _, _ => pure e2
    return (r, e3)
  | .nullishAssign _ n namePos rhs =>
    assigns n
    recordAt namePos "identifier" (match env.vars.lookup n with
      | some A => .ok A
      | none => .error s!"'{n}' is bound outside what the walk sees")
    let D ← match env.decl.lookup n with
      | some D => some <$> StateT.lift (nonNullish D)
      | none => pure none
    if let some D := D then modify fun w => { w with hints := (rhs.span, D) :: w.hints }
    let (R, e1) ← expr env rhs D
    let r ← attempt e do
      let some L := env.vars.lookup n | throw s!"'{n}' is bound outside what the walk sees"
      joinTy (← nonNullish L) (← need R "the right operand")
    -- The right operand runs on one path only.
    let e1 := (join (some env) (some e1)).getD e1
    let e2 := match r with
      | some A => { e1 with vars := upd e1.vars n A, paths := e1.paths.filter (·.1.1 != n) }
      | none => e1
    return (r, e2)
  | .assign _ n _ rhs =>
    assigns n
    if let some D := env.decl.lookup n then modify fun w => { w with hints := (rhs.span, D) :: w.hints }
    let (R, e1) ← expr env rhs (env.decl.lookup n)
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
    wrote .any .keep
    let (A, e1) ← expr env target
    let (Ss, e2) ← exprs e1 sources
    -- The target's fields, then each source's, a later key replacing an
    -- earlier one: the object the call returns, the target grown.
    let r ← attempt e do
      let G ← graphNow
      let mut fields : List (PropKey × Ty Tree) := []
      for P in (A :: Ss) do
        let P ← need P "a part"
        match PositiveRules.expand G P with
        | [.refs fs [] vs [] ms _ _] =>
          for (f, B) in fs ++ vs do
            if f != SourceTypes.protoField && f != SourceTypes.storeField && !ms.any (·.key == f) then
              fields := upd fields f B
        | _ => throw "an assignment of a value of no one record contract"
      prim (.refs fields.reverse [] [] [] [] [])
    return (r, e2)
  -- A function literal where a callable is expected, writing no parameter's
  -- type: at the expected signature taking the most parameters.
  | .lambda _ _ _ params .. =>
    let G ← StateT.lift graphNow
    let sig := if params.all (·.2 == Json.null) then exp.bind (widestOf G) else none
    return (← walkLambda env e sig, env)
  | .ctor _ lam statics =>
    -- A class value: its constructor's written parameters, its instance its
    -- written result, its static fields at their initializers' widened
    -- types (the construct rule's `ctors` clause). A class whose code is
    -- its fresh constructor bound earlier (`.var`) takes that one's
    -- signatures.
    match lam with
    | .lambda .. => let _ ← walkLambda env lam none
    | _ => let _ ← expr env lam
    let (Ss, e1) ← exprs env (statics.map (·.2))
    -- A static the class binding's annotation states is at its type there
    -- (a data property agrees both ways), any other at its initializer's.
    let G ← StateT.lift graphNow
    let written := match (← get).hints.lookup e.span with
      | some D => match PositiveRules.expand G D with
        | [.ctors _ _ fs] => fs
        | _ => []
      | none => []
    let r ← attempt e do
      let fields ← (statics.zip Ss).mapM fun ((k, _), S) => do
        match written.lookup k with
        | some D => return (k, D)
        | none => return (k, ← widen (← need S "a static field"))
      match lam with
      | .lambda _ _ _ params _ _ (some inst) _ _ _ _ _ =>
        let I ← lower (Fragment.translate inst)
        let ps ← params.mapM fun (_, ty) => lower (Fragment.translate ty)
        prim (.ctors [⟨(), ps, I, .ordinary⟩] [] fields)
      | .var _ n =>
        let some F := env.vars.lookup n | throw s!"'{n}' is bound outside what the walk sees"
        match PositiveRules.expand (← graphNow) F with
        | [.ctors L S ..] => prim (.ctors L S fields)
        | _ => throw "a class whose constructor is no class value"
      | _ => throw "a class of no written instance"
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
    -- A generic module class's binders, by its scheme's order.
    let gs := (← get).generics
    let generic := match callee with
      | .var _ n => gs.lookup n
      | _ => none
    let c := c.map fun c => match generic with
      | some g => if g.binders.length == c.binders.length then { c with names := g.binders } else c
      | none => c
    modify fun w => { w with lastInstance := none, lastResolution := [] }
    let r ← called e2 c args As e.span exp
    -- A generic class's occurrence is read at its instance, and the call's
    -- type arguments recorded.
    if let (.ok c, .ok (inst, _)) := (c, r) then
      if !c.binders.isEmpty then let _ ← record callee (.ok inst)
    if let some θ := (← get).lastInstance then
      modify fun w => { w with instances := (e.span, θ) :: w.instances, resolutions := (e.span, w.lastResolution) :: w.resolutions, lastInstance := none, lastResolution := [] }
    return (← record e ((·.2) <$> r), ← afterCall e2 r)
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
    modify fun w => { w with lastInstance := none, lastResolution := [] }
    let r ← called e2 c args As e.span exp
    -- A generic module function's occurrence is read at its instance, and
    -- the call's type arguments recorded.
    if generic.isSome then
      if let .ok (inst, _) := r then let _ ← record callee (.ok inst)
      if let some θ := (← get).lastInstance then
        modify fun w => { w with instances := (e.span, θ) :: w.instances, resolutions := (e.span, w.lastResolution) :: w.resolutions, lastInstance := none, lastResolution := [] }
    return (← record e ((·.2) <$> r), ← afterCall e2 r)
  | .callWithReceiver _ callee recv args =>
    let (F, e1) ← expr env callee
    let (R, e2) ← expr e1 recv
    let (As, e3) ← actuals e2 args
    let c ← StateT.lift (tryCatch (do
        return Except.ok (← calleeOf (← need F "the callee") (R.getD [Labels.undef]))) fun m => pure (.error m))
    let r ← called e3 c args As e.span exp
    return (← record e ((·.2) <$> r), ← afterCall e3 r)
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
        return Except.ok (← methodCallee e1.vars (← need O "the receiver") fld (args.map callback))) fun m => pure (.error m))
    let r ← called e2 c args As e.span exp
    let e2 ← afterCall e2 r
    let _ ← record callee ((·.1) <$> r)
    let r ← record e ((·.2) <$> r)
    return (r, e2)
  | .ifBody _ c t f =>
    let (_, e1) ← expr env c
    let (A, e2) ← expr (← refine e1 c true) t exp
    let (B, e3) ← expr (← refine e1 c false) f exp
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
    (at_ : Span) (exp : Option (Ty Tree) := none) : W (Except String (Ty Tree × Ty Tree)) := do
  modify fun w => { w with changedValues := false }
  match c with
  | .ok c => applyCall env c args As (exp <|> (← get).hints.lookup at_)
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
  -- A resolution's observation and result are the resolution's, never an
  -- actual's.
  let hidden := (c.resolution.flatMap (·.associated)).filterMap (c.binders[·]?)
  let bindFrom (σ : List (Tree × Ty Tree)) (pairs : List (Ty Tree × Ty Tree)) : W (List (Tree × Ty Tree)) := do
    let mut σ := σ
    for b in c.binders do
      if (σ.lookup b).isSome || hidden.contains b then continue
      for (P, A) in pairs do
        if (σ.lookup b).isNone then
          if let some B ← StateT.lift (tryCatch (matchBinder b P A) fun _ => pure none) then σ := σ ++ [(b, B)]
    return σ
  -- The first signature, in order, each walked actual is within (a
  -- scheme's at the binders its walked actuals give); else the first the
  -- count admits.
  -- The signature taking the most parameters of a callback parameter.
  let widest (P : Ty Tree) : Option (CallEffects.Arrow (Ty Tree)) :=
    (ProgramTyping.callSigs G P).foldl (fun (best : Option (CallEffects.Arrow (Ty Tree))) a =>
      match best with
      | some b => if Nat.blt b.arguments.length a.arguments.length then some a else some b
      | none => some a) none
  -- Of several signatures, each callback walked first at the first one's
  -- parameter, at its own effect: the signature chosen is one whose
  -- parameter admits it (the producer's claim at the literal).
  let mut walked : List (Nat × Ty Tree) := []
  if candidates.length > 1 then
    if let some (a0, _) := candidates.head? then
      for ((x, P), i) in (args.zip a0.arguments).zipIdx do
        if callback x then
          let w0 ← get
          let L ← walkLambda env x (widest (substitute c.seed P)) (own := true)
          set w0
          if let some L := L then walked := walked ++ [(i, L)]
  let mut chosen : Option (CallEffects.Arrow (Ty Tree) × Option (CallEffects.RestArrow (Ty Tree))) := none
  let mut fallback : Option (CallEffects.Arrow (Ty Tree) × Option (CallEffects.RestArrow (Ty Tree))) := none
  for (a, r) in candidates do
    if chosen.isSome then break
    let σa ← if c.binders.isEmpty then pure c.seed else
      bindFrom c.seed ((a.receiver, c.receiver) :: (a.arguments.zip As).filterMap fun (P, A) => A.map (P, ·))
    if (As.zip a.arguments).all fun (A, D) => A.all fun A => within T A (substitute σa D) then
      if fallback.isNone then fallback := some (a, r)
      let σa ← if c.binders.isEmpty then pure σa else
        bindFrom σa (walked.filterMap fun (i, L) => (a.arguments[i]?).map (·, L))
      -- With every binder the actuals and callbacks give bound.
      let bound := walked.isEmpty || c.binders.all fun b => hidden.contains b || (σa.lookup b).isSome
      -- (each of the parameter's signatures covering the callback's effect,
      -- which subtyping of the arrows alone does not decide here).
      let covers (L D : Ty Tree) : Bool :=
        let mine := (ProgramTyping.callSigs G L).map (·.effect)
        (ProgramTyping.callSigs G D).all fun (s : CallEffects.Arrow (Ty Tree)) =>
          mine.all fun m => s.effect.covers m || s.effect.covers { m with onThrow := false }
      if bound && walked.all fun (i, L) => match a.arguments[i]? with
          | some D => within T L (substitute σa D) && covers L (substitute σa D)
          | none => false then chosen := some (a, r)
  chosen := chosen <|> fallback
  let some (a, rest) := chosen <|> candidates.head?
    | do
      for x in args do if callback x then let _ ← walkLambda env x none
      return .error s!"no signature admits {n} actuals"
  let mut σ : List (Tree × Ty Tree) := c.seed
  -- Each binder from the receiver and the walked actuals first; then those
  -- still unbound from the type expected of the call's value, where the
  -- instance admits every walked actual (a callback is then walked at it).
  let admitsAt (σ : List (Tree × Ty Tree)) : Bool :=
    (As.zip a.arguments).all (fun (A, P) => A.all fun A => within T A (substitute σ P))
  σ ← bindFrom σ ((a.receiver, c.receiver) :: (a.arguments.zip As).filterMap fun (P, A) => A.map (P, ·))
  if let some H := hint then
    let σh ← bindFrom σ [(a.result, H)]
    if admitsAt σh then σ := σh
    -- Where the two conflict (the instance the actuals give has a result
    -- the expected type does not admit), the expected type's instance, where
    -- it binds every binder and admits the actuals (TypeScript's widening of
    -- an inferred literal at its context).
    if c.binders.all (fun b => hidden.contains b || (σ.lookup b).isSome) &&
        !within T (substitute σ a.result) H then
      let σe ← bindFrom c.seed [(a.result, H)]
      if c.binders.all (fun b => hidden.contains b || (σe.lookup b).isSome) && admitsAt σe then σ := σe
  let mut As := As
  for ((x, P), i) in (args.zip a.arguments).zipIdx do
    let sub (A : Ty Tree) : Ty Tree := substitute σ A
    if callback x then
      -- The callback's parameter's signature taking the most parameters:
      -- the callback walked there is within each of them.
      let L ← walkLambda env x (widest (sub P))
      As := As.set i L
      if let some L := L then σ ← bindFrom σ [(P, L)]
    else if let some A := As[i]? then
      As := As.set i (← fit (sub P) x A)
  -- A binder a resolution qualifies: its observation and result the
  -- resolution of its input's type by the certificate its form gives
  -- (`resolutionCertificate`), checked (`resolutionInstance`).
  let mut certificates : List (String × ResolutionWire.Certificate) := []
  for group in c.resolution do
    let (some b, some o) := (c.binders[group.input]?, c.binders[group.observation]?) | continue
    let some A := σ.lookup b | continue
    let T ← StateT.lift table
    let scope := (← get).scope
    let r : Except String (ResolutionWire.Certificate × Option (Ty Tree) × Option (Ty Tree)) := do
      let row := scope.map (·.1)
      let names := (scope.map (·.2)).getD []
      let cert ← SourceClaimJson.Scheme.resolutionCertificate T row names A group.result.isSome
      let (O, R) ← SourceClaimJson.Scheme.resolutionInstance T row names A cert
      return (cert, O, R)
    match r with
    | .error m =>
      return .error s!"the resolution of a binder's type: {m}"
    | .ok (cert, O, R) =>
      if let some n := c.names[group.input]? then certificates := certificates ++ [(n, cert)]
      -- An observation no source type names is placed at the empty type:
      -- the instance's check admits it only where the signature does not
      -- read it (`moduleInstances`).
      σ := σ.filter (·.1 != o) ++ [(o, O.getD [])]
      if let (some slot, some R) := (group.result, R) then
        if let some rb := c.binders[slot]? then σ := σ.filter (·.1 != rb) ++ [(rb, R)]
  let sub (A : Ty Tree) : Ty Tree := substitute σ A
  if let some b := c.binders.find? (fun b => (σ.lookup b).isNone) then
    let _ := b
    return .error "a type argument is not an actual's type"
  let inst := a.map sub
  -- A generic module function's instance: each binder's type, by name.
  if !c.names.isEmpty || !c.explicit.isEmpty then
    modify fun w => { w with lastInstance := some (c.explicit ++
      c.names.zip (c.binders.map fun b => (σ.lookup b).getD [])), lastResolution := certificates }
  -- A call changing the heap, by its instance's footprint.
  if inst.effect.footprint != ⟨.keep, .keep⟩ then wrote inst.effect.footprint.value inst.effect.footprint.store
  if inst.effect.footprint.value != .keep || inst.effect.receiverOwn || inst.effect.receiverStore ||
      inst.effect.elementWrite.isSome then
    modify fun w => { w with changedValues := true }
  -- A change its receiver's store or elements state beside the footprint.
  -- (a growing receiver within its footprint; one changing its own
  -- locations at the values and its store's change; a receiver's store or
  -- elements both).
  if inst.effect.receiverOwn then wrote .any inst.effect.footprint.store
  if inst.effect.receiverStore || inst.effect.elementWrite.isSome then wrote .any .any
  if !inst.effect.onThrow then modify fun w => { w with throwWrites := true }
  -- A fresh result where a type is expected: made at the expected array.
  let mut result := inst.result
  if let some H := hint then
    if inst.effect.fresh then
      if let some R ← StateT.lift (tryCatch (freshAt H inst.result) fun _ => pure none) then result := R
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
  return .ok (own, result)

/-- A function literal's walk: its parameters at their written types, or
else at `expected` (a callback's, from the parameter it is passed at),
every binding it captures at its declared type; its result its written one,
or else what its body gives (its returns' union, `undefined` where it
completes). Recorded at the literal as a signature where every part is
determined. -/
partial def walkLambda (env : Env) (e : Expr) (sig : Option (CallEffects.Arrow (Ty Tree))) (own : Bool := false) :
    W (Option (Ty Tree)) := do
  let expected := sig.map (·.arguments)
  let expectedResult := sig.map (·.result)
  let .lambda _ receiver _ params defaults _ result guard stated async _ body := e
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
  let mut thisTy : Option (Ty Tree) := none
  if let some (ty, _) := receiver then
    match ← StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none) with
    | some A => vars := upd vars "this" A; thisTy := some A
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
  modify fun w => { w with writes := false, throwWrites := false, valueChange := .keep, storeChange := .keep, locals := declared, inLiteral := true }
  modify fun w => { w with returns := [], expected := written <|> (if async then none else expectedResult) }
  -- An expression body's entry is its prologue's, at the body's start.
  modify fun w => { w with entries := w.entries.insert body.span.1 inner.vars }
  let R ← match body with
    | .block _ ss => do
      let done ← stmts (some inner) ss
      let _ ← record body (.error "a function body")
      let rs := (← get).returns ++ (if done.any (!·.ghost) then [some [Labels.undef]] else [])
      pure (if rs.all (·.isSome) then some (norm (rs.filterMap id).flatten) else none)
    | x => do
      let (A, _) ← expr inner x (← get).expected
      pure A
  -- A body that changes nothing keeps both values and stores: the
  -- footprint its calls are checked at (the producer's inferred effect).
  let pure_ := !(← get).writes
  -- One that also calls nothing leaving a changed heap on its throw keeps
  -- them on a throw too (`onThrow`).
  let kept : CallEffects.Effect := { CallEffects.Effect.ofFootprint ⟨.keep, .keep⟩ with onThrow := !(← get).throwWrites }
  -- One that changes the heap at the classes of contents its writes and
  -- calls change.
  let changed : CallEffects.Effect :=
    { CallEffects.Effect.ofFootprint ⟨(← get).valueChange, (← get).storeChange⟩ with onThrow := !(← get).throwWrites }
  modify fun w => { w with breaks := saved.breaks, returns := saved.returns, expected := saved.expected }
  modify fun w => { w with writes := saved.writes, throwWrites := saved.throwWrites, locals := saved.locals, inLiteral := saved.inLiteral }
  modify fun w => { w with valueChange := saved.valueChange, storeChange := saved.storeChange }
  let R := if written.isSome then written else if async then none else R
  let forced := (← get).force.contains "literals"
  -- A written effect (`Modifies<…>`) is the one it states.
  let kept := stated.getD kept
  let changed := stated.getD changed
  match ps.mapM id, R with
  | some qs, some R =>
    -- A callback is checked at the signature it is passed at, its result its
    -- body's; any other literal at its own parameters.
    let a : CallEffects.Arrow (Ty Tree) ← match sig with
      | some a =>
        if pure_ then pure { a with result := R, effect := kept }
        else if forced then pure { a with result := R, effect := .ofFootprint ⟨.keep, .keep⟩ }
        else
          -- A callback that changes the heap at its own effect where the
          -- parameter admits it (or `own`, for choosing the call's
          -- signature), else at the parameter's.
          -- (without its bound on a throw where the parameter states none)
          let changed := if a.effect.covers changed then changed else { changed with onThrow := false }
          let mine := { a with result := R, effect := changed }
          let admitted := a.effect.covers changed
          pure (if own || admitted then mine else { a with result := R })
      -- Any other literal at its own parameters and written receiver (a
      -- method's `this`), else a receiver admitting every value.
      | none => do pure ⟨← match thisTy with
            | some A => pure A
            | none => StateT.lift (prim .top), qs, R,
          if pure_ then kept else if forced then .ofFootprint ⟨.keep, .keep⟩ else changed⟩
    -- A written type guard or assertion: its promise, the result its
    -- promised type (`ClosureSetup`'s written promise).
    let a ← match guard with
      | some g => do
        let promised ← StateT.lift (lower (Fragment.translate g.type))
        let promise : CallEffects.TypePromise := if g.asserts then .asserts g.param else .guards g.param
        pure { a with result := promised, effect := { a.effect with promise := some promise } }
      | none => pure a
    -- A guard is also offered at its own parameters, where its promise is
    -- checked (`ClosureSetup`'s written promise).
    let offered := if guard.isSome && a.arguments.length != qs.length then
      [a, { a with arguments := a.arguments.take qs.length }] else [a]
    record e (.ok [← StateT.lift (lower (SourceTypes.use (.arrs offered [])))])
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
    if (← get).force.contains "objects" && !P.isEmpty then return ← record x (.ok P)
    for l in P do
      let w ← get
      -- A dictionary with a writable index: the literal allocated at the
      -- dictionary itself, each of its keys a field at the dictionary's
      -- field there or else at the index, the contract's optional fields it
      -- leaves out absent.
      if let [.dict first [] vs ix os [] bs cells st] := PositiveRules.expand G [l] then
        if !cells.isEmpty && first.all (fun (k, _) => names.contains k) then
          let index := norm (cells.flatMap (·.2))
          let mut ok := true
          let mut fields : List (PropKey × Ty Tree) := []
          for (k, y) in names.zip es do
            let D := (first.lookup k).getD index
            let some B ← fit D y ((w.exprs.get? y.span).bind (·.2.toOption)) | ok := false; break
            if !within T B D then ok := false; break
            fields := fields ++ [(k, D)]
          if ok then
            let R ← StateT.lift (prim (.dict fields [] vs ix (os.filter fun o => !names.contains o.key) [] bs cells st))
            if within (← StateT.lift table) R [l] then return ← record x (.ok R)
          continue
      -- An instance's prototype key (`[[proto]]`), which the declared
      -- instance type does not name, at its walked type.
      let Ds ← StateT.lift (tryCatch (some <$> (names.zip es).mapM fun (k, _) =>
          readField [] [l] k) fun _ => pure none)
      let some Ds := Ds | continue
      let mut fields : List (PropKey × Ty Tree) := []
      let mut own : List (PropKey × Ty Tree) := []
      let mut ok := true
      for ((k, y), D) in (names.zip es).zip Ds do
        let some B ← fit D y ((w.exprs.get? y.span).bind (·.2.toOption)) | ok := false; break
        fields := fields ++ [(k, if within T B D then D else B)]
        own := own ++ [(k, B)]
      if !ok then continue
      -- Each field at the expected one, else at the value's own type (a
      -- literal kept where the expected member states it).
      for byField in [fields, own] do
        let R? ← StateT.lift (tryCatch (do
            -- The literal's record as written, else stating its own keys
            -- exactly (`HasTyUsing.alloc`'s bound), which meets optional
            -- fields.
            -- Each key a field the allocation writes once (a field is within
            -- a view of its read type), but a stable key the expected record
            -- states as a view: a view of its value; its stable keys kept.
            let (fs, vs, st) := match PositiveRules.expand G [l] with
              | [.refs _ [] evs _ _ _ est] =>
                let isView (k : PropKey) : Bool := (evs.lookup k).isSome && est.contains k
                (byField.filter (fun (k, _) => !isView k), byField.filter (fun (k, _) => isView k),
                  est.filter names.contains)
              | _ => (byField, [], [])
            let R ← prim (.refs fs [] vs [] [] [] st)
            if within (← table) R [l] then return some (R, false)
            let R ← prim (.refs fs [] vs [] [] [⟨true, names⟩] st)
            return if within (← table) R [l] then some (R, true) else none) fun _ => pure none)
        if let some (R, _) := R? then return ← record x (.ok R)
    return some A
  | .arrayLit _ es [] =>
    -- The one array member of `P` whose positions admit the elements, each
    -- element made at its position: the store's contract (positions, rest,
    -- `readonly`, presence) is that member's.
    let some A := A | return none
    for l in arrayArms G P do
      let some S := storeOf G [l] | continue
      let [.list t []] := PositiveRules.expand G S | continue
      let n := es.length
      if !(t.required.length ≤ n && (n ≤ t.required.length + t.optional.length || t.rest.isSome)) then continue
      let w ← get
      let mut ok := true
      for (y, i) in es.zipIdx do
        let some D := t.position i | ok := false; break
        let some B ← fit D y ((w.exprs.get? y.span).bind (·.2.toOption)) | ok := false; break
        if !within T B D then ok := false; break
      if ok then return ← record x (.ok [l])
    -- At an iterable other than an array: the readonly array of what it
    -- yields, holes read as `undefined` where that admits it.
    if let some E ← StateT.lift (iteratedElement P) then
      let w ← get
      let mut ok := true
      for y in es do
        let some B ← fit E y ((w.exprs.get? y.span).bind (·.2.toOption)) | ok := false; break
        if !within T B E then ok := false; break
      if ok then
        let R ← StateT.lift (lower do
          let s ← SourceTypes.use (.list ⟨[], [], some E, true, .readable⟩ [])
          let T ← get
          return [← SourceTypes.use (SourceTypes.arrayOf T s true)])
        if within (← StateT.lift table) R P then return ← record x (.ok R)
    return some A
  | .build _ _ es =>
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
    -- A name at its value's own span (a defaulted parameter's binding)
    -- keeps the value's record there.
    if !(← get).exprs.contains namePos then
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
    if let some (k, rp, slice, q) := rest then
      let R ← restOf env A k rp slice
      env ← bindPattern env q R
    return env

/-- An array pattern's rest after `k` positions of a value of type `A`,
recorded at its span `rp`: a slice rest the call of `%RestFrom:k%` at `A`
(its intrinsic read at the `...`); any other the fresh array of the
positions of `A`'s tuple from `k` on. -/
partial def restOf (env : Env) (A : Option (Ty Tree)) (k : Nat) (rp : Span) (slice : Bool) : W (Option (Ty Tree)) := do
  let some A := A | return none
  if slice then
    let some g := (← get).generics.lookup (restFromName k) | return none
    let .ok c ← StateT.lift (tryCatch (Except.ok <$> genericCallee g []) fun m => pure (Except.error m)) | return none
    modify fun w => { w with lastInstance := none, lastResolution := [] }
    let r ← applyCall env c [.var rp "%rest%"] [some A]
    recordAt (rp.1, rp.1 + "...".length) "identifier" ((·.1) <$> r)
    recordAt rp "call" ((·.2) <$> r)
    if let some θ := (← get).lastInstance then
      modify fun w => { w with instances := (rp, θ) :: w.instances, resolutions := (rp, w.lastResolution) :: w.resolutions, lastInstance := none, lastResolution := [] }
    return ((·.2) <$> r).toOption
  let r ← StateT.lift (tryCatch (do
      let G ← graphNow
      let some S := storeOf G A | throw "a rest of a value that is no array"
      let [.list t []] := PositiveRules.expand G S | throw "an array of more than one tuple contract"
      let Es := t.required.drop k
      let Os := t.optional.drop (k - t.required.length)
      Except.ok <$> lower do
        let s ← SourceTypes.use (.list ⟨Es, Os, t.rest, false, .dense⟩ [])
        let T ← get
        return [← SourceTypes.use (SourceTypes.arrayOf T s false)]) fun m => pure (.error m))
  recordAt rp "other" r
  return r.toOption

/-- A part with a default: the part less `undefined`, or the default's. -/
partial def withDefault (env : Env) (B : Option (Ty Tree)) (d : Option Expr) : W (Option (Ty Tree) × Env) := do
  match d with
  | none => return (B, env)
  | some d =>
    let (D, e1) ← expr env d
    match B, D with
    -- The default only where the part may be `undefined`.
    | some B, some D =>
      if (← StateT.lift (slice B .isUndef true)).isEmpty then return (some B, (join (some env) (some e1)).getD e1)
      return (some (norm ((← StateT.lift (slice B .isUndef false)) ++ D)), (join (some env) (some e1)).getD e1)
    | _, _ => return (none, e1)

/-- Walk statements from `env` (none: unreached), recording each statement
entry; the environment where the list completes, none where it does not. -/
partial def stmts (env : Option Env) (ss : List Stmt) : W (Option Env) := do
  let mut env := env
  -- The list's early bindings, each allocated at the list's entry (the flow
  -- graph's `.early` node): from there on at its written contract, which
  -- is its storage contract.
  if let some e0 := env then
    let mut e := e0
    for s in ss do
      let bs := match s with
        | .constants _ bs | .mutables _ bs => bs
        | _ => []
      for b in bs.filter (·.early) do
        if let some D ← earlyContract b then
          modify fun w => { w with contracts := w.contracts ++ [((b.init.span, b.name), D)] }
          e := { e with vars := upd e.vars b.name D, decl := upd e.decl b.name D }
    env := some e
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
    -- The narrowed paths of an entry no loop's head is (a `for`'s head
    -- shares its declarations' entry).
    match s with
    | .loop .. | .forOf .. => modify fun w => { w with currents := w.currents.erase at_ }
    | _ => if !e.paths.isEmpty then modify fun w => { w with currents := w.currents.insert s.pos.1 (currentOf e) }
    env ← stmt e s
    prev := some s
  return env

/-- A function literal a constant holds that reads the constant (its self
entry, SOURCE-ELABORATION.md, "Recursive constants"): walked with the
constant at its written type, else at its written signature changing
nothing and bounding its throws, raised to the type the walk gives it until
the two agree (the producer's `raise_selves`), at most four rounds: the
footprint of each class of contents only rises and `onThrow` only falls. -/
partial def recursiveConstant (env : Env) (b : Fragment.Binding) (written : Bool) :
    W (Option (Ty Tree) × Env) := do
  let some S0 ← earlyContract b { CallEffects.Effect.ofFootprint ⟨.keep, .keep⟩ with onThrow := true }
    | expr env b.init
  let w0 ← get
  let mut S := S0
  for _ in [0:4] do
    set w0
    let (A, e1) ← expr { env with vars := upd env.vars b.name S, decl := upd env.decl b.name S } b.init
    let some L := A | return (A, e1)
    if written || sameMeaning (← StateT.lift table) L S then return (A, e1)
    S := L
  set w0
  return (← record b.init (.error "not handled: a recursive closure's effect undetermined"), env)

partial def collectBreaks (label : Option String) (saved : List (Option String × Env)) : W (Option Env) := do
  let w ← get
  let (mine, others) := w.breaks.partition (·.1 == label)
  set { w with breaks := others ++ saved }
  return mine.foldl (fun acc (_, b) => join acc (some b)) none

partial def stmt (env : Env) (s : Stmt) : W (Option Env) := do
  match s with
  | .ret _ x =>
    -- The value's entry, where a finalizer holds the return (the flow
    -- graph's `.returnHeld`): the statement's bindings.
    modify fun w => { w with entries := w.entries.insert x.span.1 env.vars }
    if let some P := (← get).expected then modify fun w => { w with hints := (x.span, P) :: w.hints }
    let (A, _) ← expr env x (← get).expected
    if !env.ghost then modify fun w => { w with returns := w.returns ++ [A] }
    return none
  | .throw _ x =>
    let _ ← expr env x
    return none
  | .effect _ x =>
    let e1 := (← expr env x).2
    -- An assertion function's normal return: its promise holds.
    match x with
    | .call _ callee args _ _ | .callWithReceiver _ callee _ args => return some (← promised e1 callee args true)
    | _ => return some e1
  | .constants p bs =>
    let mut env := env
    modify fun w => { w with consts := bs.map (·.name) ++ w.consts }
    for b in bs do
      modify fun w => { w with declarations := w.declarations.insert (p.1, b.name) env.vars }
      let written ← match b.annot with
        | some ty => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
        | none => pure none
      if let some D := written then modify fun w => { w with hints := (b.init.span, D) :: w.hints }
      -- The initializer made at the annotation's type.
      let (A, e1) ← match b.init with
        | .lambda _ _ _ _ _ _ _ _ stated _ _ _ =>
          if b.init.freeNames.contains b.name then recursiveConstant env b (b.annot.isSome || stated.isSome)
          else expr env b.init written
        | _ => expr env b.init written
      env := e1
      let D := if b.annot.isSome then written else A
      match D, A with
      | some D, some A =>
        env := { env with vars := upd env.vars b.name (← StateT.lift (assigned D A)), decl := upd env.decl b.name D }
      | some D, none => env := { env with vars := upd env.vars b.name D, decl := upd env.decl b.name D }
      | none, _ => env := { env with vars := env.vars.filter (·.1 != b.name) }
    return some env
  | .mutables p bs =>
    let mut env := env
    modify fun w => { w with consts := w.consts.filter fun n => !bs.any (·.name == n) }
    for b in bs do
      modify fun w => { w with declarations := w.declarations.insert (p.1, b.name) env.vars }
      let written ← match b.annot with
        | some ty => StateT.lift (tryCatch (some <$> lower (Fragment.translate ty)) fun _ => pure none)
        | none => pure none
      if let some D := written then modify fun w => { w with hints := (b.init.span, D) :: w.hints }
      -- The initializer made at the annotation's type.
      let (A, e1) ← expr env b.init written
      env := e1
      let D ← match b.annot, A with
        | some _, _ => pure written
        | none, some A => some <$> StateT.lift (widen A)
        | none, none => pure none
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
    let arm (q : Bool) (ss : List Stmt) : W (Option Env) := do
      let r ← refine e1 c q
      match emptiedBy e1 r with
      | some walked => stmts (some walked) ss
      | none => stmts (some r) ss
    let t ← arm true thn
    let f ← arm false (els.getD [])
    return join t f
  | .brk _ label =>
    modify fun w => { w with breaks := (label, env) :: w.breaks }
    return none
  | .cont _ =>
    modify fun w => { w with continues := env :: w.continues }
    return none
  | .loop _ c body update _ =>
    let head := loopHead env (.effect c.span c :: body ++ update)
    let (_, e1) ← expr head c
    let saved := (← get).breaks
    let savedContinues := (← get).continues
    modify fun w => { w with breaks := [], continues := [] }
    let b ← stmts (some (← refine e1 c true)) body
    -- The update runs after the body's end and after each `continue`.
    let continued := (← get).continues.foldl (fun acc c => join acc (some c)) b
    modify fun w => { w with continues := savedContinues }
    let _ ← stmts (some (continued.getD head)) update
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
  | .forOf p name namePos it iterable body =>
    let (I, e1) ← expr env iterable
    -- A generic iteration intrinsic's instance: its call at the iterable,
    -- the stepper it gives held at the loop's head (`%next@…%`) and its
    -- one binder the element.
    let mut stepper : Option (Ty Tree) := none
    let mut bound : Option (Ty Tree) := none
    if let some g := (← get).generics.lookup it then
      let c? : Except String Callee ← StateT.lift (tryCatch (Except.ok <$> genericCallee g []) fun m => pure (Except.error m))
      if let .ok c := c? then
        modify fun w => { w with lastInstance := none, lastResolution := [] }
        let r ← applyCall e1 c [iterable] [I]
        -- The call at the loop's span, its intrinsic read at the `for`
        -- keyword (`Stmt.callees`).
        recordAt (p.1, p.1 + "for".length) "identifier" ((·.1) <$> r)
        recordAt p "call" ((·.2) <$> r)
        stepper := ((·.2) <$> r).toOption
        if let some θ := (← get).lastInstance then
          if let [(_, A)] := θ then bound := some A
          modify fun w => { w with instances := (p, θ) :: w.instances, resolutions := (p, w.lastResolution) :: w.resolutions, lastInstance := none, lastResolution := [] }
    let exit := loopHead e1 body
    let head := match stepper with
      | some N => { exit with vars := upd exit.vars s!"%next@{p.1}%" N, decl := upd exit.decl s!"%next@{p.1}%" N }
      | none => exit
    modify fun w => { w with entries := w.entries.insert p.1 head.vars }
    let elem ← match bound, I with
      | some A, _ => pure (some A)
      | none, some I => StateT.lift (tryCatch (some <$> elementAt I none (missing := false)) fun _ => pure none)
      | none, none => pure none
    recordAt namePos "identifier" (match elem with | some A => .ok A | none => .error "the element undetermined")
    let inner := match elem with
      | some A => { head with vars := upd head.vars name A, decl := upd head.decl name A }
      | none => { head with vars := head.vars.filter (·.1 != name) }
    let saved := (← get).breaks
    modify fun w => { w with breaks := [] }
    let _ ← stmts (some inner) body
    let out ← collectBreaks none saved
    return join (some exit) (out.map fun o => { o with vars := o.vars.filter (·.1 != s!"%next@{p.1}%") })
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
      -- After the finalizer, its bindings where the statement completes.
      let f ← stmts (some (joined.getD reset)) fs
      return if joined.isNone then none else f
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
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := [])
    (force : List String := []) (scope : Option (PositiveGraphs.SchemeRow Tree × List String) := none) :
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
    let (done, w) ← (stmts (some env) f.body).run { generics, expected, force, scope, entries := (({} : Std.HashMap Nat _).insert 0 vars).insert f.namePos.1 vars }
    let w := { w with completion := done.bind fun d => if d.ghost then none else some d.vars }
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
type the lowering would read is the unit's refusal there. Beside them, where
the unit's body completes (`Walk.completion`). -/
def retypeUnitWith (T : EquationStore.State) (f : Fragment.Fn) (fc : SourceClaims.Function Tree)
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := [])
    (parts : String := "xec") (force : List String := [])
    (scope : Option (PositiveGraphs.SchemeRow Tree × List String) := none) :
    Except String (EquationStore.State × SourceClaims.Function Tree × Option (List (String × Ty Tree)) ×
      Std.HashMap (Nat × String) (List (String × Ty Tree))) := do
  let (w, T') ← walkUnit T f module generics force scope
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
  return (T', ({ fc with
    exprs, envs, contracts
    entryCurrent := if keep then fc.entryCurrent else w.currents.toList
    exprCurrent := if keep then fc.exprCurrent else []
    arrowClaims := []
    points := fc.points.map fun (id, row) =>
      (id, { row with exprs := exprs, envs := envs,
                      entryCurrent := if keep then row.entryCurrent else w.currents.toList,
                      exprCurrent := if keep then row.exprCurrent else [] }) } : SourceClaims.Function Tree), w.completion,
    w.declarations)

/-- `retypeUnitWith`'s grown store and claims. -/
def retypeUnit (T : EquationStore.State) (f : Fragment.Fn) (fc : SourceClaims.Function Tree)
    (module : List (String × Compiler (Ty Tree))) (generics : List (String × Generic) := [])
    (parts : String := "xec") (force : List String := [])
    (scope : Option (PositiveGraphs.SchemeRow Tree × List String) := none) :
    Except String (EquationStore.State × SourceClaims.Function Tree) := do
  let (T, fc, _, _) ← retypeUnitWith T f fc module generics parts force scope
  return (T, fc)

end Verification.SourceExtraction.Synthesis
