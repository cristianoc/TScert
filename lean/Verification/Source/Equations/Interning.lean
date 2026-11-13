import Verification.Source.Equations.State
import Verification.Source.ResolutionWire

/-! Section references follow `RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-- The owner of name placeholders: a binder the source spells by its name,
`T`, is lowered as the placeholder of that name until a unit or closure
decides what the name stands for (`EquationStore.rebind`). Placeholders are
family-variable trees of a reserved owner, parameter rows of their kind; no
checked request holds one (`EquationStore.freeze` refuses it). -/
def nameOwner : Nat := 4000000000

/-- The owner of fresh placeholders: a scheme's binders before its head
binds them (`EquationStore.binders`, `EquationStore.scheme`). -/
def freshOwner : Nat := 4000000001

/-- Whether a tree is a placeholder. -/
def isPlaceholder : Tree → Bool
  | .var o _ _ => o == nameOwner || o == freshOwner
  | _ => false

/-- The name placeholder of a binder name and kind. -/
def placeholder (name : String) (kind : ParameterKind) : M Tree := do
  let s ← get
  match s.names.toList.idxOf? (name, kind) with
  | some i => return .var nameOwner i kind
  | none =>
    set { s with names := s.names.push (name, kind) }
    return .var nameOwner s.names.size kind

/-- The head with key `key`, allocated with `draft` and its row's job when
new. -/
def alloc (key : String) (draft : Draft) (job : Nat → Option Job) : M Nat := do
  if let some h := (← get).keys.get? key then return h
  let h := (← get).heads.size
  modify fun s =>
    { s with heads := s.heads.push draft, keys := s.keys.insert key h, jobs := s.jobs ++ (job h).toList
             nullary := s.nullary.push (Thunk.mk fun _ => nullaryRow (s.heads.push draft) s.heads.size)
             nullary_eq := by rw [s.nullary_eq, nullaryOf_push] }
  return h

def setBody (h : Nat) (row : GraphRow Tree (List Tree)) : M Unit :=
  modify fun s =>
    let heads := s.heads.modify h fun d => { d with body := some row }
    { s with heads, nullary := s.nullary.set! h (Thunk.mk fun _ => nullaryRow heads h)
             nullary_eq := by rw [s.nullary_eq, nullaryOf_modify] }

/-- A scheme head's declared binder defaults (`Draft.defaults`). -/
def setDefaults (h : Nat) (defaults : List (Nat × List Tree)) : M Unit :=
  modify fun s =>
    let heads := s.heads.modify h fun d => { d with defaults }
    { s with heads, nullary := s.nullary.set! h (Thunk.mk fun _ => nullaryRow heads h)
             nullary_eq := by rw [s.nullary_eq, nullaryOf_modify] }

def draft (h : Nat) : M Draft := do
  match (← get).heads[h]? with
  | some d => return d
  | none => throw s!"no head {h}"

/-- How a hash-consing key spells a value: its compressed JSON, which
determines the value. -/
def spelling {α : Type} [ToJson α] (x : α) : String := (toJson x).compress

/-- How a key spells binders: each one's name and kind. -/
def bindersSpelling (bs : List Binder) : String := spelling (bs.map fun b => (b.name, b.kind))

/-- A nullary head whose row is the given clauses, hash-consed by them. -/
def ground (name : String) (cs : List (Clause (List Tree))) : M Tree := do
  let key := s!"ground|{spelling cs}"
  let h ← alloc key { name, kind := .primitive, kinds := [], body := some (.clauses cs) } fun _ => none
  return mkApp h []

def prim (name : String) (c : Clause (List Tree)) : M Tree := ground name [c]

/-- The literals a label stands for, where its row is one literal or one tag
set; none otherwise. -/
def literalsOf (t : Tree) : M (Option (List LitKey)) := do
  let .app h _ := t | return none
  if t != mkApp h [] then return none
  match (← draft h).body with
  | some (.clauses [.numLit b]) => return some [.num b]
  | some (.clauses [.numIn bs]) => return some (bs.map .num)
  | some (.clauses [.strLit s]) => return some [.str s]
  | some (.clauses [.strIn ss]) => return some (ss.map .str)
  | _ => return none

/-- The label of a finite set of numbers, its elements' labels interned too, so
that a reader can split it (HOST-FAMILIES.md, "Tag sets"). -/
def numSetLabel (bits : List UInt64) : M Tree := do
  let bits := (bits.mergeSort (· ≤ ·)).eraseDups
  match bits with
  | [b] => prim s!"number {b}" (.numLit b)
  | _ =>
    for b in bits do let _ ← prim s!"number {b}" (.numLit b)
    prim "number set" (.numIn bits)

def strSetLabel (values : List String) : M Tree := do
  let values := (values.mergeSort fun a b => decide (a ≤ b)).eraseDups
  match values with
  | [v] => prim (Json.str v).compress (.strLit v)
  | _ =>
    for v in values do let _ ← prim (Json.str v).compress (.strLit v)
    prim "string set" (.strIn values)

/-- A union with its literals and tag sets of one primitive as one tag set
(HOST-FAMILIES.md, "Tag sets"); every other label as it is. -/
def mergeLiterals (u : Union) : M Union := do
  let mut nums : List UInt64 := []
  let mut strs : List String := []
  let mut numLabels := 0
  let mut strLabels := 0
  let mut rest : Union := []
  for t in u do
    match ← literalsOf t with
    | some ks =>
      if ks.all (fun k => match k with | .num _ => true | .str _ => false) then
        nums := nums ++ ks.filterMap (fun k => match k with | .num b => some b | .str _ => none)
        numLabels := numLabels + 1
      else
        strs := strs ++ ks.filterMap (fun k => match k with | .str v => some v | .num _ => none)
        strLabels := strLabels + 1
    | none => rest := rest ++ [t]
  if numLabels ≤ 1 && strLabels ≤ 1 then return u
  let mut out := rest
  if !nums.isEmpty then out := out ++ [← numSetLabel nums]
  if !strs.isEmpty then out := out ++ [← strSetLabel strs]
  return normUnion out

/-- The key of the built-ins' `unknown`: the nullary head of the `source` clause. -/
def unknownKey : String := s!"ground|{spelling ([.source] : List (Clause (List Tree)))}"

/-- The four primitive values' heads come first, as `LabelStore.Labels`
requires: `null`, `true`, `false`, `undefined`. -/
def primitives : M Unit := do
  let _ ← prim "null" .nul
  let _ ← prim "true" (.boolLit true)
  let _ ← prim "false" (.boolLit false)
  let _ ← prim "undefined" .undef

def top : M Tree := prim "unknown" .source

/-- The empty intersection's refusal. -/
def emptyMeet : String :=
  "the intersection is empty: its operands have no value in common (no value has two shapes, and an array owns no key its prototype provides), and an empty intersection is refused rather than verified vacuously"

/-- A union read arm by arm: an intersection arm with no value is the union's
bottom and adds nothing. A union with an intersection arm (`meets`) is refused
when it has no value as a whole: empty here, or each of its meets empty once
the rows are known (`meetChecks`). -/
def unionOfArms (site : String) (U : Union) (meets : Bool) : M Union := do
  if meets then
    if U.isEmpty then throw s!"{site}: {emptyMeet}"
    modify fun s => { s with meetChecks := s.meetChecks ++ [(U, site)] }
  return U

/-- An object clause whose methods are its only statement of their keys: a
key one operand states as a method and another as a field, a view or an
optional field is a method of the object, which may hold it on its
prototype, as a class instance holds its methods. The fields at a method's
key are left out, so no reader takes the key for an own property; a call of
the key is checked at the method's signatures. -/
def methodKeysOnly (c : Clause α) : Clause α :=
  let fields (ms : List (MethodMembers.Sig α)) (fs : List (Stored α)) : List (Stored α) :=
    fs.filter fun f => !ms.any (·.key == f.1)
  let views (ms : List (MethodMembers.Sig α)) (fs : List (PropKey × α)) : List (PropKey × α) :=
    fs.filter fun f => !ms.any (·.key == f.1)
  let operands (ms : List (MethodMembers.Sig α)) (bs : List (List (Stored α))) :
      List (List (Stored α)) :=
    (bs.map (fields ms)).filter (!·.isEmpty)
  let optional (ms : List (MethodMembers.Sig α)) (os : List (OptionalField α)) : List (OptionalField α) :=
    os.filter fun o => !ms.any (·.key == o.key)
  match c with
  | .refs a bs vs os ms ks st => .refs (fields ms a) (operands ms bs) (views ms vs) (optional ms os) ms ks st
  | .dict a bs vs ix os ms ks cs st =>
    .dict (fields ms a) (operands ms bs) (views ms vs) ix (optional ms os) ms ks cs st
  | .callable a bs L S ms => .callable (fields ms a) (operands ms bs) L S ms
  | c => c

/-- The refusal of an intersection mentioning a type parameter whose operands
state one key as a method and as a field. -/
def methodFieldMeet : String :=
  "an intersection mentioning a type parameter whose operands state a key both as a method and as a field is outside the fragment: the key is a method of the meet, which may sit on the prototype, and the meet is read at each instance as the model's, which owns the field"

/-- Two operands' clauses as TypeScript meets them: the model's meet, except
that a record of invariant fields met with a function type is the function
carrying those fields, a `callable`, and that a key one operand states as a
method is a method of the meet (`methodKeysOnly`). -/
def sourceMeetLists [BEq α] (A B : List (Clause α)) : Except String (List (Clause α)) := do
  let plainRecord (c : Clause α) : Bool := match c with
    | .refs .. => !c.presentKeys.contains CallArguments.arrayStoreField
    | .dict .. => true
    | _ => false
  let calls (c : Clause α) : Bool := match c with
    | .arrs .. | .callable .. => true
    | _ => false
  let pair (a b : Clause α) : List (Clause α) :=
    match a, b with
    | .refs f fs [] [] [] [], .arrs L S | .arrs L S, .refs f fs [] [] [] [] => [.callable f fs L S]
    | .refs f fs [] [] [] [], .callable c cs L S | .callable c cs L S, .refs f fs [] [] [] [] =>
      [.callable (f ++ c) (fs ++ cs) L S]
    | a, b => ((PositiveNormalization.meet a b).map methodKeysOnly).filter Clause.consistent
  let pairs := A.flatMap fun a => B.map fun b => (a, b)
  let met := pairs.flatMap fun (a, b) => pair a b
  if met.isEmpty && pairs.any (fun (a, b) => (plainRecord a && calls b) || (calls a && plainRecord b)) then
    throw "the intersection of a function type and a record with readonly or optional fields, methods or an index is a callable with them, which no clause states"
  return met

/-- A clause row's template at arguments. -/
def instantiateClauses (cs : List (Clause (List Tree))) (args : List Union) : List (Clause (List Tree)) :=
  cs.map (Clause.map (·.flatMap (treeSubst (fun i => args.getD i []) (fun j => [.local j]))))

def ctxValue (ctx : Ctx) : Item → Except String Union
  | .param i => match ctx.params[i]? with
    | some v => .ok v
    | none => .error s!"{ctx.site}: declaration parameter index {i} outside the application"
  | .binder n => match ctx.binders.lookup n with
    | some b => .ok b.value
    | none => .error s!"{ctx.site}: the type parameter {n} is not in scope"
  | .self => match ctx.self with
    | some v => .ok v
    | none => .error s!"{ctx.site}: a receiver outside a declaration's methods"

def ctxKind (ctx : Ctx) : Item → ParameterKind
  | .binder n => if (ctx.binders.lookup n).any (·.packed) then .packed
    else if (ctx.binders.lookup n).any (·.pack) then .arguments else .value
  | _ => .value

/-- What a head is lifted over: a packed binder's argument lists, under its
packed name, go with it; once when they are its row (a unit's or a closure's
binder), and as an item of their own otherwise (a generic value's binder,
whose instance gives its argument lists apart). -/
def liftedItems (ctx : Ctx) (named : List Item) : List Item :=
  let sameRow (n : String) : Bool :=
    match ctx.binders.lookup n, ctx.binders.lookup (packedName n) with
    | some b, some p => b.packed && b.value == p.value
    | _, _ => false
  let canonical := (named.map fun it => match it with
    | .binder x => match x.dropSuffix? "#pack" with
      | some b => if sameRow b.toString then .binder b.toString else it
      | none => it
    | _ => it).eraseDups
  canonical ++ canonical.filterMap fun it => match it with
    | .binder n => if (ctx.binders.lookup (packedName n)).isSome && !sameRow n &&
        !canonical.contains (.binder (packedName n)) then some (.binder (packedName n)) else none
    | _ => none

/-- The scope inside a head lifted over `items`: each item is its argument. -/
def liftedCtx (ctx : Ctx) (items : List Item) (h : Nat) : Ctx :=
  let indexed := items.zipIdx
  let size := indexed.foldl (fun n (it, _) => match it with | .param i => max n (i + 1) | _ => n) 0
  { decl := ctx.decl
    params := (Array.range size).map fun i =>
      match indexed.find? (fun (it, _) => it == .param i) with
      | some (_, j) => [.argument j]
      | none => []
    self := (indexed.find? (·.1 == .self)).map fun (_, j) => [.argument j]
    -- A packed binder's argument lists, under its packed name, are its row:
    -- the same argument.
    binders := indexed.flatMap fun (it, j) => match it with
      | .binder n =>
        let packed := (ctx.binders.lookup n).any (·.packed)
        (n, Binding.mk ((ctx.binders.lookup n).any (·.pack)) [.argument j] packed) ::
          (if packed && !items.contains (.binder (packedName n)) then
            [(packedName n, Binding.mk true [.argument j] false)] else [])
      | _ => []
    owner := some h
    site := ctx.site
    source := ctx.source
    bounds := ctx.bounds.filterMap fun (p, U) => do
      let (_, j) ← indexed.find? fun (it, _) => (ctxValue ctx it).toOption == some [p]
      let moved (q : Tree) : Option Union :=
        (indexed.find? fun (it, _) => (ctxValue ctx it).toOption == some [q]).map fun (_, k) => [.argument k]
      -- A bound naming what the head is lifted over names its argument.
      let U' ← U.mapM fun t => match moved t with
        | some m => some m
        | none => if treeOpen t then none else some [t]
      return (.argument j, U'.flatten) }

def literalName (term : Json) : String :=
  s!"literal {(kindOf term).getD "?"} at {(term.getObjValD "span").compress}"

/-- The head of a source occurrence, lifted over the items it mentions and
applied to their values here (§8.1). The key is the occurrence's text and the
kinds of what it mentions: equal keys lower to equal templates. -/
def occurrence (ctx : Ctx) (tag : String) (term : Json) (shadow : List String := [])
    (binders : List Binder := []) (job : Nat → Ctx → Job) : M Tree := do
  let items := liftedItems ctx (mentions shadow term)
  let args ← items.mapM fun it => (ctxValue ctx it : Except String Union)
  let kinds := items.map (ctxKind ctx)
  let key := s!"{tag}|{spelling kinds}|{term.compress}"
  let kind := if tag == "scheme" then HeadKind.scheme else .literal
  let h ← alloc key { name := literalName term, kind, kinds, binders } fun h =>
    some (job h (liftedCtx ctx items h))
  return mkApp h args

/-- The array heads and the built-in prototype. Without an `ArrayProto`
declaration in the document (a library bound naming an array, in a source
with none), the prototype is an object of which nothing is known. -/
def arrayHead (readonly : Bool) (proto : Tree) : M Nat := do
  let excluded := (← get).excluded
  modify fun s => { s with arrays := true }
  -- The built-ins' `unknown`, the type of an array's elements.
  let _ ← ground "unknown" [.source]
  alloc s!"array|{readonly}"
    { name := if readonly then "ReadonlyArray" else "Array", kind := .array readonly, kinds := [.value],
      body := some (.clauses [arrayClauseOf [.argument 0] [proto] excluded readonly]) } fun _ => none

/-! ### Heads added after the declarations

What the store adds while a unit is extracted (`EquationStore`): a union of
clauses, a scheme over fresh binders, a bounded binder's meet. A template
holds no owned parameter or variable (§3.1: it names parameters only through
its arguments), so each such closed subtree is lifted to an argument, as a
literal is lifted over the binders it mentions (§8.1). The head is keyed by
the lifted template, so equal templates share a head. -/

/-- A tree with its rigid subtrees lifted to arguments, in first-occurrence
order: the arguments so far and the template. -/
partial def liftTree (acc : Array Tree) : Tree → Array Tree × Tree
  | t@(.bound ..) | t@(.var ..) =>
    match acc.toList.idxOf? t with
    | some i => (acc, .argument i)
    | none => (acc.push t, .argument acc.size)
  | .app h args =>
    let (acc, ts) := args.toList.foldl (fun (acc, out) ts =>
      let (acc, us) := ts.toList.foldl (fun (acc, us) u =>
        let (acc, u) := liftTree acc u
        (acc, us ++ [u])) (acc, [])
      (acc, out ++ [Types.ofList us])) (acc, [])
    (acc, .app h (Args.ofList ts))
  | .meet ps =>
    let (acc, us) := ps.toList.foldl (fun (acc, us) u =>
      let (acc, u) := liftTree acc u
      (acc, us ++ [u])) (acc, [])
    (acc, canonMeet us)
  | t => (acc, t)

def liftUnion (acc : Array Tree) (U : Union) : Array Tree × Union :=
  U.foldl (fun (acc, out) t => let (acc, t) := liftTree acc t; (acc, out ++ [t])) (acc, [])

/-- A rigid subtree's kind: an owned parameter's is its binder's, a
variable's its own. -/
def rigidKindIn (heads : Array Draft) : Tree → ParameterKind
  | .bound h _ j => ((heads[h]?.bind (·.binders[j]?)).map (·.kind)).getD .value
  | .var _ _ k => k
  | _ => .value

/-- Clauses with their rigid subtrees lifted: the arguments and the
template. -/
def liftClauses (cs : List (Clause (List Tree))) : Array Tree × List (Clause (List Tree)) :=
  cs.foldl (fun (acc, out) c =>
    let ops := c.operands
    let (acc, lifted) := ops.foldl (fun (acc, out) U =>
      let (acc, U) := liftUnion acc U
      (acc, out ++ [U])) (acc, [])
    let table := ops.zip lifted
    (acc, out ++ [c.map fun U => (table.lookup U).getD U])) ((#[] : Array Tree), [])

/-- The key of a union of clauses' head, and what it is applied to: the key
`ground` gives when nothing is lifted. -/
def internKey (heads : Array Draft) (cs : List (Clause (List Tree))) : String × List Union :=
  let (acc, cs') := liftClauses cs
  if acc.isEmpty then (s!"ground|{spelling cs}", [])
  else (s!"lifted|{spelling (acc.toList.map (rigidKindIn heads))}|{spelling cs'}", acc.toList.map ([·]))

/-- The label of a union of clauses: its head, lifted over its rigid
subtrees, applied to them. Nullary when there are none, and then the head
`ground` would give. -/
def internLifted (name : String) (cs : List (Clause (List Tree))) : M Tree := do
  let (acc, cs') := liftClauses cs
  if acc.isEmpty then return ← ground name cs
  let heads := (← get).heads
  let (key, args) := internKey heads cs
  let h ← alloc key
    { name, kind := .literal, kinds := acc.toList.map (rigidKindIn heads), body := some (.clauses cs') }
    fun _ => none
  return mkApp h args

/-- A fresh placeholder for a scheme's binder, until the scheme's head binds
it (`schemeOver`). -/
def freshBinder (name : String) (kind : ParameterKind := .value) : M Tree := do
  let s ← get
  set { s with fresh := s.fresh.push name }
  return .var freshOwner s.fresh.size kind

/-- A scheme over binders from `freshBinder`: its head's template has the
binders as its locals, and every other rigid subtree lifted. The label is the
head applied to what was lifted; its binders are the head's owned
parameters, which the caller reads from the label's row. -/
def schemeOver (binders : List Tree) (sigs : List (Arrow (List Tree))) (bounds : List (Tree × List Tree))
    (rests : List (RestArrow (List Tree))) (construct : Bool := false) : M Tree := do
  let loc (t : Tree) : Option Union := (binders.idxOf? t).map fun j => [.local j]
  let local_ (U : Union) : Union := U.flatMap (treeReplace loc)
  let sigs := sigs.map (Arrow.map local_)
  let rests := rests.map (RestArrow.map local_)
  let bounds := bounds.filterMap fun (b, U) => (binders.idxOf? b).map fun j => (Tree.local j, local_ U)
  let liftA (acc : Array Tree) (a : Arrow (List Tree)) : Array Tree × Arrow (List Tree) :=
    let ops := a.operands
    let (acc, lifted) := ops.foldl (fun (acc, out) U =>
      let (acc, U) := liftUnion acc U; (acc, out ++ [U])) (acc, [])
    (acc, a.map fun U => ((ops.zip lifted).lookup U).getD U)
  let liftR (acc : Array Tree) (a : RestArrow (List Tree)) : Array Tree × RestArrow (List Tree) :=
    let ops := a.operands
    let (acc, lifted) := ops.foldl (fun (acc, out) U =>
      let (acc, U) := liftUnion acc U; (acc, out ++ [U])) (acc, [])
    (acc, a.map fun U => ((ops.zip lifted).lookup U).getD U)
  let (acc, sigs) := sigs.foldl (fun (acc, out) a => let (acc, a) := liftA acc a; (acc, out ++ [a]))
    ((#[] : Array Tree), [])
  let (acc, bounds) := bounds.foldl (fun (acc, out) (b, U) =>
    let (acc, U) := liftUnion acc U; (acc, out ++ [(b, U)])) (acc, [])
  let (acc, rests) := rests.foldl (fun (acc, out) a => let (acc, a) := liftR acc a; (acc, out ++ [a]))
    (acc, [])
  let kinds := acc.toList.map (rigidKindIn (← get).heads)
  let s ← get
  let names := binders.map fun b => match b with
    | .var o i _ => if o == freshOwner then (s.fresh[i]?).getD "_" else "_"
    | _ => "_"
  let bs : List Binder := (names.zip binders).map fun (n, b) => ⟨n, match b with
    | .var _ _ k => k
    | _ => .value⟩
  let row : GraphRow Tree (List Tree) :=
    .scheme ((List.range binders.length).map Tree.local) sigs bounds rests [] construct
  let key := s!"schemeOver|{spelling kinds}|{bindersSpelling bs}|{spelling row}"
  let h ← alloc key { name := "scheme", kind := .scheme, kinds, binders := bs, body := some row }
    fun _ => none
  return mkApp h (acc.toList.map ([·]))

/-! ### Lowering source types -/

def unitBinders (names : List String) (packs : List String) : List Binder :=
  names.map fun n => ⟨n, if packs.contains n then .arguments else .value⟩

/-- A scheme's binders, their kinds, and the refusals of forms a scheme
cannot state. -/
def schemeBinders (site : String) (term : Json) : Except String (List String × List String × List ResolutionSlots) := do
  fieldsExactly term ["k", "binders", "signatures", "span"]
  let bs ← arr term "binders"
  let sigTerms ← arr term "signatures"
  let refuse (reason : String) : Except String Unit :=
    throw s!"{site}: generic contract at {(term.getObjValD "span").compress}: {reason}; the contract cannot be erased"
  let parameters ← bs.toList.mapM fun b => do
    fieldsExactly b ["name", "bound", "default", "span", "resolution"]
    let name ← str b "name"
    let resolution ← (fromJson? (← field b "resolution") : Except String (Option ResolutionWire.Slots))
    return (name, resolution)
  ResolutionWire.validateOwnership parameters
  let names := parameters.flatMap fun (n, s) => ResolutionWire.ownedNames n s
  let own (j : Json) : Bool := names.any fun n => let u := binderUse n j; u.value || u.pack
  if bs.any (fun b => own (b.getObjValD "bound")) then refuse "dependent method bounds are not represented"
  let uses : List (String × BinderUse) := names.map fun n => (n, binderUse n (.arr sigTerms))
  if uses.any (fun (p : String × BinderUse) => p.2.pack && p.2.value) then
    refuse "a binder used as both a value and an argument pack is not represented"
  return (names, (uses.filter fun (p : String × BinderUse) => p.2.pack).map Prod.fst,
    ResolutionWire.groups parameters)

def referenceIndex (term : Json) : M Nat := do
  fieldsExactly term ["k", "reference", "args", "span"]
  let target ← field (← field term "reference") "target"
  let s ← get
  let ds := s.doc
  match ((s.identities.get? target).getD []).filter fun i => ds[i]!.identity == target with
  | [i] => return i
  | [] => throw "reference has no declaration equation"
  | _ => throw "duplicate declaration identity"

/-- A literal type's labels. A numeric zero is both zeros, as TypeScript's
literal type `0` is. -/
def literalLabels (term : Json) : M Union := do
  fieldsExactly term ["k", "name", "text", "span"]
  match ← str term "name" with
  | "true" => return [← prim "true" (.boolLit true)]
  | "false" => return [← prim "false" (.boolLit false)]
  | "number" =>
    let text ← str term "text"
    let bits ← (Verification.numBits text : Except String UInt64)
    let one ← prim s!"{text}" (.numLit bits)
    if Float.ofBits bits == 0.0 then
      return [one, ← prim "-0" (.numLit (9223372036854775808 : UInt64))]
    return [one]
  | "string" => let text ← str term "text"; return [← prim (Json.str text).compress (.strLit text)]
  | "bigint" =>
    let text ← str term "text"
    return [← prim s!"{text}n" (.bigintLit (← (Verification.decodeBigint text : Except String Int)))]
  | _ => throw "unsupported source literal"

/-- A `unique symbol` type's label: the one symbol whose identity is the
`symbol`-th listed `unique symbol` declaration, as a symbol key `{"symbol": i}`
names it. -/
def uniqueLabels (term : Json) : M Union := do
  fieldsExactly term ["k", "symbol", "span"]
  let id ← (← field term "symbol").getNat?
  return [← prim s!"unique symbol {id}" (.symbolLit id)]

/-- The source-value universe, independent of record builtins invariants. -/
def sourceValueClauses : List (Clause (List Tree)) :=
  [.source]

def atomLabels (term : Json) : M Union := do
  match ← str term "name" with
  | "null" => return [← prim "null" .nul]
  | "undefined" => return [← prim "undefined" .undef]
  | "boolean" => return [← prim "true" (.boolLit true), ← prim "false" (.boolLit false)]
  | "number" => return [← prim "number" .num]
  | "string" => return [← prim "string" .str]
  | "bigint" => return [← prim "bigint" .bigint]
  | "symbol" => return [← prim "symbol" .symbol]
  | "unknown" => return [← ground "source" sourceValueClauses]
  | "void" => return [← ground "void" sourceValueClauses]
  | "never" => return []
  | "object" =>
    return normUnion [← prim "object" (.refs [] [] []), ← prim "function" (.arrs [] []),
      ← prim "constructor" (.ctors [])]
  -- Every value but a host object (COMPILER-API.md, "Restricted values"):
  -- the primitives, the callables and the objects owning no `[[host]]`. No
  -- source spells it; the library overlay states it at the parameters of the
  -- obligated `Object` members.
  | "nonHost" =>
    return normUnion [← prim "null" .nul, ← prim "undefined" .undef, ← prim "true" (.boolLit true),
      ← prim "false" (.boolLit false), ← prim "number" .num, ← prim "string" .str, ← prim "bigint" .bigint,
      ← prim "symbol" .symbol, ← prim "non-host object" (.refs [] [] [] [] [] [⟨false, [hostKey]⟩]),
      ← prim "function" (.arrs [] []), ← prim "constructor" (.ctors [])]
  | "nonHostObject" =>
    return [← prim "non-host object" (.refs [] [] [] [] [] [⟨false, [hostKey]⟩])]
  -- Every value with call code, of which no signature is known: a function
  -- type whose rest admits no argument list, `(...args: never) => R`. No
  -- class value meets it, its code having `[[Construct]]` only.
  | "function" => return [← prim "function" (.arrs [] [])]
  -- Every class value, of which no construct signature is known: a
  -- constructor type whose rest admits no argument list,
  -- `abstract new (...args: never) => R`.
  | "class" => return [← prim "constructor" (.ctors [])]
  | _ => throw "unsupported declaration primitive"


end Verification.EquationLowering
