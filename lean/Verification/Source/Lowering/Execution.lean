import Verification.Source.Lowering.Atoms
import Verification.Source.Lowering.Control
import Verification.Source.Lowering.Operands

namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

namespace LoweringExecution

set_option maxHeartbeats 1000000

/-- The labels of `A` a tag test answering `q` keeps (`tagSlice`), each meet
row narrowed to the meets of its parts with each clause the test does not
contradict, one meet row per clause as a claimed intersection distributes over
a union, and dropped where it contradicts every one: `T ⊓ (null | number)` is
`T ⊓ number` where a nullish test fails (`BranchRefinement.meetSlice`). -/
@[nospecialize] def observedSlice (A : Ty Tree) (tag : Tag) (q : Bool) : Compiler (Ty Tree) := do
  let base ← tagRefine A tag q
  let T ← table
  let mut kept : Ty Tree := []
  for a in base do
    match StoreView.row T a with
    | .meet p cs also =>
      let left := cs.filter fun c => tagClause tag c != some (!q)
      if left.length == cs.length then kept := kept ++ [a]
      else
        for c in left do
          kept := kept ++ [← lower (SourceTypes.bounded p [c] also)]
    | _ => kept := kept ++ [a]
  return kept

@[nospecialize] partial def executionSaved (scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (value : SourceExecution.Saved) : Compiler (Nat × Ty Tree) := do
  let some (i, .value) := resolve scope value.name
    | throw s!"internal execution plan: missing saved value '{value.name}'"
  let some A := Γ[i]? | throw "internal execution plan: saved value has no type"
  return (i, A)

/-- A location a reference names: a cell's or a field's, or an element of an
array's store, each read and written where the receiver is. -/
private inductive Location where
  | field (object : Tm) (fld : PropKey) (contract : Ty Tree)
  | element (object : Tm) (index : Tm) (contract : Ty Tree)

private def Location.read : Location → Tm
  | .field object fld _ => .readAt fld object
  | .element object index _ => .elemAt (.readAt SourceTypes.storeField object) index

private def Location.contract : Location → Ty Tree
  | .field _ _ T | .element _ _ T => T

/-- The write of `value` at the location, its object shifted by `shift` slots. -/
private def Location.write (shift : Nat) (value : Tm) : Location → Except String Tm
  | .field (.var i) fld _ => pure (.writeAt fld (.var (i+shift)) value)
  | .element (.var i) index _ =>
    let object := Tm.var (i+shift)
    pure (.writeAt SourceTypes.storeField object (.setElem (.readAt SourceTypes.storeField object) index value))
  | _ => throw "internal execution plan: reference is not a saved location"

/-- The saved receiver slot of a field or element reference, and its nullish
split (`nullishSplit`): a reference to a nullish receiver's member throws
before the member is read. -/
@[nospecialize] private def referenceReceiver (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree)) :
    SourceExecution.Reference → Compiler (Option (Nat × Option (Ty Tree × Ty Tree)))
  | .field _ receiver _ => do
    match resolve scope receiver.name with
    | some (i, _) => pure (some (i, (Γ[i]?).bind (nullishSplit (SourceTypes.graph (← table)))))
    | none => pure none
  | .local .. => pure none

/-- `Γ` with a reference's receiver refined past its nullish guard. -/
@[nospecialize] private def refinedReceiver (Γ : List (Ty Tree)) :
    Option (Nat × Option (Ty Tree × Ty Tree)) → List (Ty Tree)
  | some (i, some (_, F)) => Γ.set i F
  | _ => Γ

@[nospecialize] private partial def executionReference (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (reference : SourceExecution.Reference) : Compiler Location := do
  match reference with
  | .local name source =>
    match resolve scope name with
    | some (i, .cell contract _) => return .field (.var i) valueField contract
    -- A slot is read at what it holds now; `localSlot` keeps it from being
    -- read or written as a cell.
    | some (i, .slot _) => return .field (.var i) valueField (Γ[i]?.getD [])
    -- An early binding's cell holds the marker until its declaration
    -- writes it; the reference names its contents at the contract.
    | some (i, .early stored _ true) => return .field (.var i) valueField (← initializedContract stored)
    | some (_, .early _ _ false) => throw (← constantWriteRefusal source name)
    | _ => throw s!"assignment to '{name}', which is not a mutable local"
  | .field original receiver key =>
    let (i, B) ← executionSaved scope Γ receiver
    let object := Fragment.Expr.var receiver.source receiver.name
    let prepared ← match original with
      | .read pos fld _ => pure (Fragment.Expr.read pos fld object)
      | .index pos fld _ _ =>
        let some key := key | throw "internal execution plan: missing reference key"
        pure (.index pos fld object (.var key.source key.name))
      | .elemAt pos _ _ =>
        let some key := key | throw "internal execution plan: missing reference key"
        pure (.elemAt pos object (.var key.source key.name))
      | _ => throw "only field and local assignments are supported"
    let prepared ← comparisonsExpr fc prepared
    -- An element of an array's store, at the position the key names.
    if let .elemAt _ _ keyExpr := prepared then
      let index ← arrayKeyTerm keyExpr.span (← exprType fc keyExpr)
      return .element (.var i) index (← exprType fc original)
    let fld ← match prepared with
      | .read _ fld _ => pure fld
      | .index _ (some fld) _ _ => pure (.str fld)
      | _ => throw "only field and local assignments are supported"
    match PositiveRules.expand (SourceTypes.graph (← table)) B with
    | [.refs fs [] _ _ _ _] =>
      let some T := fs.lookup fld
        | throw (locatedRefusal (← table) original.span .storageWrite
          s!"update of a field '{fld}' the contract does not name as a writable location")
      pure (.field (.var i) fld T)
    | _ => throw (locatedRefusal (← table) original.span .storageWrite
        "an assignment needs one cell contract")

/-- The slot a local reference names, with its contract, when the local is
held in a slot. -/
@[nospecialize] private def localSlot (scope : List (ScopeBinding Tree)) :
    SourceExecution.Reference → Option (Nat × Ty Tree)
  | .local name _ => match resolve scope name with
    | some (i, .slot contract) => some (i, contract)
    | _ => none
  | .field .. => none

/-- The name of a local reference held in an early binding's cell. -/
@[nospecialize] private def earlyLocal (scope : List (ScopeBinding Tree)) :
    SourceExecution.Reference → Option String
  | .local name _ => match resolve scope name with
    | some (_, .early ..) => some name
    | _ => none
  | .field .. => none

/-- The slot an operation rebinds: a write of a local held in a slot. -/
@[nospecialize] private def rebound (scope : List (ScopeBinding Tree)) :
    SourceExecution.Operation → Option Nat
  | .evaluate _ _ (.cellWrite name _) => match resolve scope name with
    | some (i, .slot _) => some i
    | _ => none
  | .referenceWrite _ reference _ | .updateSaved _ reference _ _ => (localSlot scope reference).map (·.1)
  | _ => none

/-- Locals a plan may rebind on any of its paths. -/
@[nospecialize] private partial def executionRebound (scope : List (ScopeBinding Tree)) :
    SourceExecution.Plan → List String
  | .atom _ operation => ((rebound scope operation).bind (scope[·]?)).toList.map (·.source.name)
  | .observe _ evaluate => executionRebound scope evaluate
  | .sequence _ _ evaluate next => executionRebound scope evaluate ++ executionRebound scope next
  | .choose _ _ _ _ evaluate yes no =>
    executionRebound scope evaluate ++ executionRebound scope yes ++ executionRebound scope no

@[nospecialize] private partial def executionClaim (fc : SourceClaims.Function Tree)
    (source : Span) (fallback : Compiler (Ty Tree)) : Compiler (Ty Tree) :=
  match fc.exprs.lookup source with
  | some candidate => do SourceClaims.resolve (← table) candidate
  | none => fallback

/-- Synthetic operation results are derived from their operand contracts.
    Original operations retain their exact producer result obligation. -/
@[nospecialize] private partial def executionOperationType (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (operation : SourceExecution.Operation) : Compiler (Ty Tree) := do
  match operation with
  | .evaluate original prepared _ => do
    if let .var _ name := prepared then
      if let some A := (← executionType name) then return A
    let A ← executionClaim fc original.span (exprType fc prepared)
    if let .not _ operand := prepared then
      if let some D := LoweringAtoms.decidedNegation (SourceTypes.graph (← table)) A (← exprType fc operand) then
        return D
    return A
  | .methodRead .. | .invokeSaved .. => LoweringAtoms.methodPlanType fc scope Γ operation
  | .snapshotSpread .. | .snapshotObject .. => snapshotPlanType fc scope Γ operation
  | .referenceRead source reference =>
    let location ← executionReference fc scope
      (refinedReceiver Γ (← referenceReceiver scope Γ reference)) reference
    executionClaim fc source (pure location.contract)
  | .referenceWrite source _ value =>
    executionClaim fc source (do return (← executionSaved scope Γ value).2)
  | .updateSaved original _ previous _ =>
    executionClaim fc original.span (do return (← executionSaved scope Γ previous).2)
  | .positionRead source array index =>
    tryCatch (positionRead (SourceTypes.graph (← table)) (← executionSaved scope Γ array).2 index) fun reason => do
      throw (locatedRefusal (← table) source .bindingAnnotation reason)
  | .arrayRest source _ _ _ => claimAt fc source
  | .emptyObject _ => groupType [] []
  | .outcome _ truth => pure [if truth then Labels.tru else Labels.fls]
  | .addField original base key value final =>
    let .str key := key | throw "internal execution plan: object literal field is not a string"
    let A ← claimAt fc original.span
    let fields ← claimedFields A
    let V := (← executionSaved scope Γ value).2
    let V := (fields.lookup key).getD V
    let L := (← executionSaved scope Γ base).2
    let F ← groupType [key] [V]
    if key == Fragment.protoKeyName then return F
    if final && ObjectMerge.MergeOk (SourceTypes.graph (← table)) [] L F A then pure A
    else mergeType L F
  | .mergeObjects source left right final assign =>
    let L := (← executionSaved scope Γ left).2
    -- A bounded binder's value is copied at its bound.
    let R ← boundOf (← executionSaved scope Γ right).2
    -- `Object.assign` writes each key the source owns onto the target: a
    -- source that may own a reserved key is a reserved write.
    if assign then
      reservedWriteCheck right.source L (!excludesErrorOwnedKeys (SourceTypes.graph (← table)) R)
    if assign && !ownsNoProto (SourceTypes.graph (← table)) R then
      throw (locatedRefusal (← table) right.source .expressionClaim
        "Object.assign from a source that may own `__proto__`: it sets that key through the prototype's setter, which replaces the target's prototype rather than adds a key")
    if final then
      let A ← claimAt fc source
      if ObjectMerge.MergeOk (SourceTypes.graph (← table)) [] L R A then return A
    mergeType L R

@[nospecialize] partial def executionPlanType (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (plan : SourceExecution.Plan) : Compiler (Ty Tree) := do
  match plan with
  | .observe source evaluate => executionClaim fc source (executionPlanType fc scope Γ evaluate)
  | .atom _ operation => executionOperationType fc scope Γ operation
  | .sequence _ binding evaluate next =>
    let A ← executionPlanType fc scope Γ evaluate
    let scope := { source := ⟨binding.name, some binding.source⟩, fixed := some A : ScopeBinding Tree } :: scope
    withExecutionType binding.name A (executionPlanType fc scope (A::Γ) next)
  | .choose source _ _ binding evaluate yes no =>
    executionClaim fc source (do
      let A ← executionPlanType fc scope Γ evaluate
      let scope := { source := ⟨binding.name, some binding.source⟩, fixed := some A : ScopeBinding Tree } :: scope
      withExecutionType binding.name A do
        let Y ← executionPlanType fc scope (A::Γ) yes
        let N ← executionPlanType fc scope (A::Γ) no
        pure (Y ++ N).eraseDups)

/-- A key-adding write on an owned object, as its copy: the slot and storage
of each binding holding the object, the saved receiver's and right side's slots, the one-key allocation in the
statement's context, whether the object is copied onto the allocation
(`swapped`) rather than the allocation onto it, the key's slot where the key
may be `__proto__`, and the claims of the write, the allocation and the copy. -/
private structure Growth where
  holders : List (Nat × Storage Tree)
  receiver : Nat
  value : Nat
  alloc : Tm
  swapped : Bool
  proto : Option Nat
  W : Ty Tree
  F : Ty Tree
  M : Ty Tree

/-- Whether every clause of an object's type lists its own keys, each a key a
copy takes: the copy of such an object holds all of it. -/
@[nospecialize] private def listsCopiedKeys (G : PositiveGraphs.NormalGraph Tree) (X : Ty Tree) : Bool :=
  let cs := PositiveRules.expand G X
  !cs.isEmpty && cs.all fun c => match c with
    | .refs _ _ _ _ _ ks _ | .dict _ _ _ _ _ _ ks _ _ => ks.any fun K => K.among && K.keys.all copiedKey
    | _ => false

/-- Whether no value of a type is an object or `null`, which the prototype's
`__proto__` setter would make the object's prototype. -/
@[nospecialize] private def noPrototypeValue (G : PositiveGraphs.NormalGraph Tree) (V : Ty Tree) : Bool :=
  let cs := PositiveRules.expand G V
  G.plainTy V && cs.all fun c => match c with
    | .undef | .bool | .boolLit _ | .num | .numLit _ | .numIn _ | .str | .strLit _ | .strIn _
    | .bigint | .bigintLit _ | .symbol | .symbolLit _ => true
    | _ => false

/-- A checked owned write replaces every reference to its object, each
    holder's slot or cell, with a fresh copy. Operand slots are supplied by the shared execution plan. A string key the
    source spells is allocated by `makeAt` and copied over the object; a key
    known only at run time by `makeKey` at the key's value. A symbol key, which
    the copy of an object does not take, is the allocation the object is copied
    onto, where the object's type lists its keys, none a symbol, so that copy
    holds all of it. A string key known only at run time may be `__proto__`,
    which JavaScript's write gives to the prototype's setter where the object
    does not own it: with a value no object nor `null` the setter changes
    nothing, which the lowering dispatches on (`executionEvaluate`); another
    value is refused. -/
@[nospecialize] private partial def executionGrowth (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (original prepared : Fragment.Expr) : Compiler (Option Growth) := do
  -- A write on a module cell the module owns is a site wherever it is, its
  -- value the right side's; any other only as its own statement.
  let module ← match original with
    | .write _ _ (.var _ n) _ | .indexWrite _ _ (.var _ n) _ _ => moduleOwnedCell scope n
    | _ => pure none
  if module.isNone && (← ownedWrite) != some original.span then return none
  let (holders, static) ← match ← computedGrowth fc scope original with
    | some (holders, _, _, _) => pure (holders, none)
    | none => match ← growingWrite fc scope original with
      | some (holders, _, field, _, _) => pure (holders, some field)
      | none => return none
  let prepared ← comparisonsExpr fc prepared
  let (receiver, key, rhs) ← match prepared with
    | .write _ _ receiver rhs => pure (receiver, none, rhs)
    | .indexWrite _ _ receiver key rhs => pure (receiver, some key, rhs)
    | _ => throw "internal execution plan: a prepared owned write has no operands"
  let .var _ receiverName := receiver | throw "internal execution plan: owned receiver was not saved"
  let .var _ rhsName := rhs | throw "internal execution plan: owned right side was not saved"
  let some r := valueSlot scope receiverName | throw "internal execution plan: missing owned receiver"
  let some v := valueSlot scope rhsName | throw "internal execution plan: missing owned right side"
  let G := SourceTypes.graph (← table)
  let T ← table
  let refuse := fun {α : Type} (reason : String) =>
    (throw (locatedRefusal T original.span .expressionClaim reason) : Compiler α)
  let W ← exprType fc original
  -- The object of a module cell is read again after the operands, at the
  -- cell's contract: the right side may have replaced it.
  let X ← match module with
    | some (_, .early stored _ _) => initializedContract stored
    | _ => pure (Γ[r]?.getD [])
  -- A key-adding write is a write: at a reserved key, onto a proto-free
  -- object only (`reservedWriteCheck`).
  reservedWriteCheck original.span X (match static with
    | some fld => errorOwnedKey fld
    | none => match key with
      | some (.var _ keyName) => (valueSlot scope keyName).all fun k => errorOwnedKeyClaim G (Γ[k]?.getD [])
      | _ => true)
  let symbolCopy := fun (F : Ty Tree) => do
    if !listsCopiedKeys G X then
      refuse "a key-adding write of a symbol key on an object whose type does not list its keys: the copy of an object takes its string keys, and the symbol keys it may own are not known"
    mergeType F X
  -- No object the source makes holds `Symbol.toStringTag`
  -- (SOURCE-CONTRACTS.md, "Objects owning `then`"): a key-adding write
  -- of a key that may be it is refused.
  let tagged := fun (i : Nat) => T.tags.contains i
  let tagRefusal := "a key-adding write at a key that may be `Symbol.toStringTag`: no object the program makes holds the tag the native `Promise` contract requires of a prototype"
  match static with
  | some (.sym i) => if tagged i then refuse tagRefusal
  | _ => pure ()
  -- A module cell's object is copied at string keys alone, onto which no
  -- symbol key and no `__proto__` is ever written: the copy then holds all
  -- of it.
  if module.isSome then
    -- The object's type states its finite key set: object clauses stating
    -- fields, no index.
    if !(PositiveRules.expand G X).all (fun c => match c with | .refs .. => true | _ => false) then
      refuse "a key-adding write on a module's own object whose type states no finite key set: the module's own objects are records of named keys"
    let symbolKey := match static, key with
      | some (.sym _), _ => true
      | none, some (.var _ keyName) => (valueSlot scope keyName).any fun k =>
        (PositiveRules.expand G (Γ[k]?.getD [])).any fun c => match c with
          | .str | .symbol | .symbolLit _ => true
          | .strLit s => s == "__proto__"
          | .strIn ss => ss.contains "__proto__"
          | _ => false
      | _, _ => false
    if symbolKey || static == some (.str "__proto__") then
      refuse "a key-adding write on a module's own object at a key that may be a symbol or `__proto__`: the object is copied at its string keys, which a symbol key or the prototype's setter would not be"
  -- A key every clause of the object's type states as one writable optional
  -- field, of one type: the allocation is at that type, the location the
  -- copy then holds, as the field's.
  let optionalType := fun (keys : List PropKey) =>
    let types := (PositiveRules.expand G X).flatMap fun c => match c with
      | .refs _ _ _ os _ _ _ => keys.map fun k => (os.find? fun q => q.key == k && !q.readonly).map (·.type)
      | _ => [none]
    match (types.filterMap id).eraseDups with
    | [V] => if !types.isEmpty && types.all Option.isSome then some V else none
    | _ => none
  match static with
  | some (.str name) =>
    let F ← groupType [name] [(optionalType [.str name]).getD W]
    let M ← mergeType X F
    pure (some ⟨holders, r, v, .makeAt .absent [.str name] [.var v], false, none, W, F, M⟩)
  | some (.sym i) =>
    let label ← lower (SourceTypes.use (ComputedKey.oneField (.sym i) W))
    recordHints [label]
    let F := [label]
    let M ← symbolCopy F
    pure (some ⟨holders, r, v, .makeAt .absent [.sym i] [.var v], true, none, W, F, M⟩)
  | none =>
    let some (.var _ keyName) := key | throw "internal execution plan: owned key was not saved"
    let some k := valueSlot scope keyName | throw "internal execution plan: missing owned key"
    let K := Γ[k]?.getD []
    let cs := PositiveRules.expand G K
    let symbolic := cs.any fun c => match c with | .symbol | .symbolLit _ => true | _ => false
    let stringy := cs.any fun c => match c with | .symbol | .symbolLit _ => false | _ => true
    if symbolic && stringy then
      refuse "a key-adding write at a key that may be a string or a symbol: the copy holds a string key of the allocation over the object, and the object over a symbol key's allocation"
    -- A key at `symbol` may be the tag at run time, listed or not.
    if cs.any (fun c => match c with | .symbol => true | .symbolLit i => tagged i | _ => false) then
      refuse tagRefusal
    -- A value written where a writable index of the object admits the key
    -- is allocated at that index's type, as a literal meant for a dictionary
    -- is (`allocDict`): the copy then keeps the index.
    let keyClass := fun (c : PositiveNormalization.Clause (Ty Tree)) => match c with
      | .str | .strLit _ | .strIn _ => some IndexKeys.strings
      | .num | .numLit _ | .numIn _ => some IndexKeys.numeric
      | .symbol | .symbolLit _ => some IndexKeys.symbols
      | _ => none
    let classes := (cs.filterMap keyClass).eraseDups
    let cellType : Option (Ty Tree) := match PositiveRules.expand G X with
      | [.dict _ _ _ _ _ _ _ cells _] =>
        let ts := classes.map fun K => (cells.find? fun y => IndexKeys.within K y.1).map (·.2)
        match (ts.filterMap id).eraseDups with
        | [V] => if ts.all Option.isSome then some V else none
        | _ => none
      | _ => none
    let named := (PositiveNormalization.splitSets cs).map fun c => match ComputedKey.keyedClause c W with
      | some (.refs [(f, _)] _ _ _ _ _ _) => some f
      | _ => none
    let fieldType := if named.all Option.isSome then optionalType (named.filterMap id) else none
    let F ← keyedType K ((cellType <|> fieldType).getD W)
    let proto := cs.any fun c => match c with | .str => true | .strLit s => s == "__proto__" | .strIn ss => ss.contains "__proto__" | _ => false
    if proto && !noPrototypeValue G (Γ[v]?.getD []) then
      refuse "a write at a string key known only at run time may name `__proto__`, whose setter, where the object does not own the key, makes an object or `null` value the object's prototype rather than a property"
    -- Where the copy is of the object's own type, the local keeps it: the
    -- path on which the key is `__proto__` leaves the object as it is.
    let M ← if symbolic then symbolCopy F
      else if ObjectMerge.MergeOk G [] X F X then pure X else mergeType X F
    pure (some ⟨holders, r, v, .makeKey (.var k) (.var v), symbolic, if proto then some k else none, W, F, M⟩)

/-- An update's operation: its result type, its right operand (the family's
one for an increment), and the slot of the old value. -/
@[nospecialize] private partial def updateType (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (original : Fragment.Expr) (_reference : SourceExecution.Reference)
    (previous : SourceExecution.Saved) (rhs : Option SourceExecution.Saved) :
    Compiler (Ty Tree × Tm × Nat) := do
  let .update source op _ _ _ := original | throw "internal execution plan: expected an update"
  let (old, T) ← executionSaved scope Γ previous
  let clauses := PositiveRules.expand (SourceTypes.graph (← table)) T
  if rhs.isNone && (clauses.isEmpty ||
      !(clauses.all ProgramTyping.numberClause || clauses.all ProgramTyping.bigintClause)) then
    throw s!"unsupported source expression at [{source.1},{source.2}): an increment needs a target of one numeric family, number or bigint"
  let (delta, C) ← match rhs with
    | some rhs => do
      let (i, C) ← executionSaved scope Γ rhs
      pure (Tm.var i, C)
    | none => do
      if !clauses.isEmpty && clauses.all ProgramTyping.bigintClause then
        pure (Tm.bigint 1, [← lower (SourceTypes.use (.bigintLit 1))])
      else pure (Tm.num (1.0 : Float).toBits, [← lower (SourceTypes.use (.numLit (1.0 : Float).toBits))])
  return (← operatorResult op T C, delta, old)

/-- Typed atomic copies can replace one owned local while every source
    operand remains scheduled by the execution plan. -/
@[nospecialize] private partial def executionAfterContext (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (operation : SourceExecution.Operation) : Compiler (List (Ty Tree)) := do
  -- A write of a slot rebinds it to the operation's value; an update's
  -- value is the operation's result, its new value.
  if let some i := rebound scope operation then
    if let .updateSaved original reference previous rhs := operation then
      return Γ.set i (← updateType scope Γ original reference previous rhs).1
    return Γ.set i (← executionOperationType fc scope Γ operation)
  match operation with
  | .evaluate original prepared _ =>
    if let some g ← executionGrowth fc scope Γ original prepared then
      return g.holders.foldl (fun Γ (i, storage) => match storage with
        | .value | .slot _ => Γ.set i g.M
        | .cell .. | .early .. => Γ) Γ
    if (← ownedWrite) == some original.span then
      if let .objectAssign _ (.var _ name) _ := original then
        let some i := valueSlot scope name | throw "internal execution plan: missing owned Object.assign target"
        return Γ.set i (← executionOperationType fc scope Γ operation)
    -- A completed member read narrows its receiver (`readNarrowing`).
    return LoweringAtoms.narrowed Γ (← LoweringAtoms.readNarrowing scope Γ prepared)
  | _ => pure Γ

/-- A key-adding write on a module cell `i` the module owns, its operands
saved: the allocation at the key, then the checked access of the cell again
(the right side may have replaced its object, and in JavaScript the binding
still names the one object), the copy of what it holds with the allocation,
written to the cell at its contract, and the right side's value. -/
@[nospecialize] private partial def moduleGrowth (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (original : Fragment.Expr) (g : Growth) (i : Nat) (stored : Ty Tree) (next : Target) : Compiler Target := do
  let G := SourceTypes.graph (← table)
  let some (t, _) := resolve scope throwUninitializedName
    | throw s!"internal extraction error: an early binding's access without {throwUninitializedName}"
  let X ← initializedContract stored
  let S := (X ++ (← uninitializedTy)).eraseDups
  let found := BranchRefinement.tagSlice G S (.hasKey uninitializedKey) true
  let tested := held ⟨"",some original.span⟩
  -- Environments, innermost first: Γ; F::Γ the allocation; S::F::Γ the
  -- cell's contents; X::F::Γ past the marker's test; M::X::F::Γ the copy.
  let copyScope := tested :: tested :: tested :: scope
  let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
    (fun j => if j == 0 then 0 else j+3)
  let result ← emitAt original.span (.var (g.value+3)) (.bind ⟨next.label,some mapping⟩)
    (g.M::X::g.F::Γ) g.W "expression-claim" (scope := copyScope)
  let write ← emitAt original.span (.writeAt valueField (.var (i+3)) (.var 0)) (.effect result)
    (g.M::X::g.F::Γ) [Labels.nul] "storage-contract" (scope := copyScope)
  let merge ← emitAt original.span (.merge [] (.var 0) (.var 1)) (.bind write)
    (X::g.F::Γ) g.M "owned-copy" (scope := copyScope.tail)
  let raise ← emitAt original.span (Tm.call (.var (t+3)) []) .ret (found :: S :: g.F :: Γ) []
    "uninitialized-binding" (scope := copyScope)
  let toMerge : Target := ⟨merge.label, some ((List.range (Γ.length+2)).map
    (fun j => if j == 0 then 0 else j+1))⟩
  let dispatch ← emitAt original.span (.var 0) (.tagBind (.hasKey uninitializedKey) raise toMerge)
    (S::g.F::Γ) S "tag-dispatch" (scope := copyScope.tail)
  let read ← emitAt original.span (.readAt valueField (.var (i+1))) (.bind dispatch)
    (g.F::Γ) S (scope := tested :: scope)
  emitAt original.span g.alloc (.bind read) Γ g.F "owned-field" (scope := scope)

/-- Every prepared primitive is checked at the original expression's claim,
    including a result represented internally by a saved-value read. -/
@[nospecialize] private partial def executionEvaluate (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (original prepared : Fragment.Expr) (next : Target) : Compiler Target := do
  if let some g ← executionGrowth fc scope Γ original prepared then
    if let [(i, .early stored _ true)] := g.holders then
      return ← moduleGrowth scope Γ original g i stored next
    let values := g.holders.filterMap fun (i, storage) => match storage with
      | .value | .slot _ => some i
      | .cell .. | .early .. => none
    let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else if values.contains (j-1) then 1 else j+2)
    let merged := held ⟨"",some original.span⟩ :: held ⟨"",some original.span⟩ :: scope
    let result ← emitAt original.span (.var (g.value+2)) (.bind ⟨next.label,some mapping⟩)
      (g.M::g.F::Γ) g.W "expression-claim" (scope := merged)
    -- A holder that is a `let` holds the copy from then on: in its cell, or,
    -- held in a slot, rebound to it, the copy checked at its contract.
    let stored ← g.holders.foldlM (init := result) fun next (i, storage) => match storage with
      | .value => pure next
      | .slot contract => emitAt original.span (.var 0) (.effect next)
          (g.M::g.F::Γ) contract "storage-contract" (scope := merged)
      | .cell .. => emitAt original.span (.writeAt valueField (.var (i+2)) (.var 0)) (.effect next)
          (g.M::g.F::Γ) [Labels.nul] "storage-contract" (scope := merged)
      | .early .. => throw (s!"unsupported source expression at [{original.span.1},{original.span.2}): " ++
          "a key-adding write of an object an early binding holds is outside the fragment")
    let copy := if g.swapped then Tm.merge [] (.var 0) (.var (g.receiver+1))
      else .merge [] (.var (g.receiver+1)) (.var 0)
    let merge ← emitAt original.span copy (.bind stored)
      (g.F::Γ) g.M "owned-copy" (scope := merged.tail)
    let copied ← emitAt original.span g.alloc (.bind merge)
      Γ g.F "owned-field" (scope := scope)
    let some k := g.proto | return copied
    -- The key is `__proto__` and the object does not own it: the write runs
    -- the prototype's setter, which with this value changes nothing. Where
    -- the object owns the key, the write is its copy, as at any other key.
    let width := Γ.length
    let kept ← emitAt original.span (.var g.value) (.bind next) Γ g.W "expression-claim" (scope := scope)
    let owns ← emitAt original.span (.var g.receiver)
      (.tagBind (.hasKey (.str "__proto__")) (branchMapping width none copied) (branchMapping width none kept))
      Γ (Γ[g.receiver]?.getD []) "tag-dispatch" (scope := scope)
    return ← emitAt original.span (.var k)
      (.tagBind (.strEq "__proto__") (branchMapping width none owns) (branchMapping width none copied))
      Γ (Γ[k]?.getD []) "tag-dispatch" (scope := scope)
  if let .objectAssign _ target _ := original then
    match target with
    | .alloc .. | .build .. => pure ()
    | .construct _ callee _ _ _ =>
      let G := SourceTypes.graph (← table)
      let fresh := match PositiveRules.expand G (← exprType fc callee) with
        | [.ctors signatures _ _ _ _] => !signatures.isEmpty &&
          signatures.all (fun s => PromiseCalls.keepsHeap s.effect && s.effect.freshObject)
        | _ => false
      unless fresh && (← freshNativeConstructor scope callee) do
        throw (locatedRefusal (← table) original.span .expressionClaim
          "Object.assign onto a constructed target needs a constructor contract stating a fresh object")
    | .var .. =>
      if (← ownedWrite) != some original.span then
        throw (locatedRefusal (← table) original.span .expressionClaim
          "Object.assign onto an object that is not a fresh literal is lowered only as a statement on a local's own object: the call's value would be one more reference to it")
    | _ => throw (locatedRefusal (← table) original.span .expressionClaim
        "Object.assign onto an object that is not a fresh literal is lowered only as a statement on a local's own object: the call's value would be one more reference to it")
  let A ← executionClaim fc original.span (exprType fc prepared)
  let B ← exprType fc prepared
  let copied ← if (← ownedWrite) == some original.span then
      match original with
      | .objectAssign _ (.var _ name) _ => pure (valueSlot scope name)
      | _ => pure none
    else match original with
      -- An assignment of a slot rebinds it to the value it yields.
      | .assign _ name _ rhs => pure (rebound scope (.evaluate original prepared (.cellWrite name rhs.span)))
      | _ => pure none
  if let .var _ name := prepared then
    if (← executionType name).isSome then
      -- A source claim checks the saved value without forgetting the more
      -- precise type carried by its selected branch.
      let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
        (fun i => if i > 0 && copied == some (i-1) then 0 else i)
      let checked ← emitAt original.span (.var 0) (.effect ⟨next.label,some mapping⟩)
        (B::Γ) A "expression-claim" (scope := held ⟨"",some original.span⟩ :: scope)
      return ← LoweringAtoms.compileAtom recursive fc scope Γ prepared checked
  if let .not _ operand := prepared then
    -- A negation its operand decides keeps that answer past its claim's
    -- check, as a saved value does (`decidedNegation`).
    if let some D := LoweringAtoms.decidedNegation (SourceTypes.graph (← table)) A (← exprType fc operand) then
      let checked ← emitAt original.span (.var 0) (.effect next)
        (D::Γ) A "expression-claim" (scope := held ⟨"",some original.span⟩ :: scope)
      return ← withPreparedAtom original (LoweringAtoms.compileAtom recursive fc scope Γ prepared checked)
  let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
    (fun i => if i == 0 || copied == some (i-1) then 0 else i+1)
  -- An assertion function's call leaves its actual at the promise's type
  -- from its return on.
  -- An actual read from a member path is the path's witness where that
  -- read is the witness's newest: a later read of the path rebinds it.
  let witnesses ← executionWitnesses
  let newest := fun (n : String) => (newestWitness witnesses n).getD n
  let G := SourceTypes.graph (← table)
  let returned := match promiseNarrowing G scope Γ true original with
    | some (j, T) => Γ.set j T
    | none => match promiseNarrowing G scope Γ true prepared newest with
      | some (j, T) => Γ.set j T
      | none => Γ
  withPreparedAtom original do
    let prepared ← comparisonsExpr fc prepared
    -- A completed member read narrows its receiver (`readNarrowing`).
    let returned := LoweringAtoms.narrowed returned (← LoweringAtoms.readNarrowing scope Γ prepared)
    let cast ← emitAt original.span (.var 0) (.bind ⟨next.label, some mapping⟩)
      (B::returned) A "expression-claim" (scope := held ⟨"",some original.span⟩ :: scope)
    LoweringAtoms.compileAtom recursive fc scope Γ prepared cast

@[nospecialize] private partial def compileExecutionOperation (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (source : Span) (operation : SourceExecution.Operation) (next : Target) : Compiler Target := do
  let A ← executionOperationType fc scope Γ operation
  match operation with
  | .evaluate original prepared _ => executionEvaluate recursive fc scope Γ original prepared next
  | .methodRead .. | .invokeSaved .. => LoweringAtoms.compileMethodOperation recursive fc scope Γ operation next
  | .snapshotSpread .. | .snapshotObject .. => compileSnapshotOperation fc scope Γ operation next
  | .referenceRead _ reference =>
    if let some (i, _) := localSlot scope reference then
      return ← emitAt source (.var i) (.bind next) Γ A (scope := scope)
    -- An early binding's read is its checked access: a throw where the
    -- cell holds the marker. A write through the reference follows the
    -- read, so it meets an initialized cell.
    if let some name := earlyLocal scope reference then
      return ← LoweringAtoms.compileAtom recursive fc scope Γ (.var source name) next
    -- A nullish receiver throws before its member is read.
    let receiver ← referenceReceiver scope Γ reference
    let Δ := refinedReceiver Γ receiver
    let location ← executionReference fc scope Δ reference
    let read ← emitAt source location.read (.bind next) Δ A (scope := scope)
    match receiver with
    | some (i, split) => LoweringAtoms.guarded source Γ i split scope read
    | none => pure read
  | .referenceWrite _ reference value =>
    if let some (j, contract) := localSlot scope reference then
      -- The value, checked at the contract, rebinds the slot.
      let (i, _) ← executionSaved scope Γ value
      let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
        (fun k => if k == j+1 then 0 else k)
      let result ← emitAt source (.var i) (.bind ⟨next.label, some mapping⟩) Γ A "expression-claim" (scope := scope)
      return ← emitAt source (.var i) (.effect result) Γ contract "storage-contract" (scope := scope)
    let location ← executionReference fc scope Γ reference
    let .field object fld contract := location
      | throw "only field and local assignments are supported"
    let (i, _) ← executionSaved scope Γ value
    let result ← emitAt source (.var i) (.bind next) Γ A "expression-claim" (scope := scope)
    let write ← emitAt source (.writeAt fld object (.var i)) (.effect result) Γ [Labels.nul]
      "storage-contract" (scope := scope)
    -- An early binding's cell also holds the marker: the value is checked
    -- at the binding's contract before it is written.
    if (earlyLocal scope reference).isSome then
      return ← emitAt source (.var i) (.effect write) Γ contract "storage-contract" (scope := scope)
    return write
  | .updateSaved original reference previous rhs =>
    let .update _ op _ _ post := original | throw "internal execution plan: expected an update"
    let (N, delta, old) ← updateType scope Γ original reference previous rhs
    let scope' := held ⟨"",some source⟩ :: scope
    if let some (i, contract) := localSlot scope reference then
      -- The new value, checked at the contract, rebinds the slot; the
      -- expression's value is the old or the new one.
      let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
        (fun j => if j == 0 then 0 else if j == i+1 then 1 else j+1)
      let result ← emitAt source (.var (if post then old+1 else 0)) (.bind ⟨next.label, some mapping⟩)
        (N::Γ) A "expression-claim" (scope := scope')
      let check ← emitAt source (.var 0) (.effect result) (N::Γ) contract "storage-contract" (scope := scope')
      return ← emitAt source (.arith op (.var old) delta) (.bind check) Γ N (scope := scope)
    -- The old value was read past the receiver's nullish guard; the write
    -- tests the receiver again, which then never throws, so that it is
    -- typed at the refined receiver.
    let receiver ← referenceReceiver scope Γ reference
    let Δ := refinedReceiver Γ receiver
    let location ← executionReference fc scope Δ reference
    let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1)
    let result ← emitAt source (.var (if post then old+1 else 0)) (.bind ⟨next.label, some mapping⟩)
      (N::Γ) A "expression-claim" (scope := scope')
    let write ← emitAt source (← location.write 1 (.var 0)) (.effect result)
      (N::Δ) [Labels.nul] "storage-contract" (scope := scope')
    let write ← if (earlyLocal scope reference).isSome then
        emitAt source (.var 0) (.effect write) (N::Δ) location.contract "storage-contract" (scope := scope')
      else pure write
    let write ← match receiver with
      | some (i, split) => LoweringAtoms.guarded source (N::Γ) (i+1) split scope' write
      | none => pure write
    emitAt source (.arith op (.var old) delta) (.bind write) Γ N (scope := scope)
  | .positionRead _ array index =>
    let (i, _) ← executionSaved scope Γ array
    emitAt source (.elemAt (.readAt SourceTypes.storeField (.var i)) (← indexTerm index))
      (.bind next) Γ A "pattern-read" (scope := scope)
  | .arrayRest _ array start slice =>
    let (i, B) ← executionSaved scope Γ array
    if slice then
      emitAt source (← sliceCall scope i start) (.bind next) Γ A "pattern-rest" (scope := scope)
    else
      let (store, S, _) ← restArray fc B i start source
      let temporary := held ⟨"",some source⟩ :: scope
      let proto ← prototypeSlot temporary
      let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
        (fun j => if j == 0 then 0 else j+1)
      let object ← emitAt source (arrayTerm proto) (.bind ⟨next.label, some mapping⟩)
        (S::Γ) A "pattern-rest" (scope := temporary)
      emitAt source store (.bind object) Γ S "pattern-rest" (scope := scope)
  | .emptyObject _ => emitAt source (.makeAt .absent [] []) (.bind next) Γ A (scope := scope)
  | .outcome _ truth => emitAt source (if truth then .tru else .fls) (.bind next) Γ A (scope := scope)
  | .addField original base key value _ =>
    let .str key := key | throw "internal execution plan: object literal field is not a string"
    let (baseIndex, _) ← executionSaved scope Γ base
    let (valueIndex, V) ← executionSaved scope Γ value
    let fields ← claimedFields (← claimAt fc original.span)
    let V := (fields.lookup key).getD V
    let F ← groupType [key] [V]
    if key == Fragment.protoKeyName then
      return ← emitAt source (.makeAt .absent [.str key] [.var valueIndex]) (.bind next) Γ A (scope := scope)
    let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else j+1)
    let merge ← emitAt source (.merge [] (.var (baseIndex+1)) (.var 0))
      (.bind ⟨next.label, some mapping⟩) (F::Γ) A (scope := held ⟨"",some source⟩ :: scope)
    emitAt source (.makeAt .absent [.str key] [.var valueIndex]) (.bind merge) Γ F (scope := scope)
  | .mergeObjects _ left right _ _ =>
    let (leftIndex, _) ← executionSaved scope Γ left
    let (rightIndex, _) ← executionSaved scope Γ right
    emitAt source (.merge [] (.var leftIndex) (.var rightIndex)) (.bind next) Γ A (scope := scope)

/-- The newest origin recorded for `name`, with the origins older than it,
the bindings its own names were read in when it was recorded, and the names
the newer entries and this one bind. -/
private def originEntry (name : String) (newer : List String := []) :
    List (String × Fragment.Expr) → Option (Fragment.Expr × List (String × Fragment.Expr) × List String)
  | [] => none
  | (n, origin) :: older =>
    if n == name then some (origin, older, n :: newer) else originEntry name (n :: newer) older

/-- Predicate metadata recovers immutable aliases and reads whose cells have
not been invalidated by an intervening effect. A binding's origin names the
bindings older than it, so it is expanded in those alone, a shorter list at
each step. The expansion replaces the binding only where each name it
mentions still denotes the binding it was recorded with: bound once in the
scope, and by no entry from the binding's own to the newest. One name binds
every optional chain's saved receiver (`Fragment.chainName`), and a mention of
it recorded for an inner chain does not denote an outer chain's binding. -/
@[nospecialize] private partial def executionPredicate (G : PositiveGraphs.NormalGraph Tree) (Γ : List (Ty Tree)) (scope : List (ScopeBinding Tree))
    (origins : List (String × Fragment.Expr)) (e : Fragment.Expr) : Fragment.Expr :=
  let witness := fun e => do
    let i ← pathWitness scope e
    -- A primitive field of the root is tested through its receiver, retaining
    -- the root's discriminant refinement. A nested path's entry instead
    -- requires its saved witness and the chain of links to that value.
    let nested := ((scope[i]?).bind fun b => b.witness).any
      (fun (p : String × List PropKey) => p.2.length > 1)
    if !nested && (HeapKnowledge.atoms G (Γ[i]?.getD [])).isSome then none else some i
  let operand : Fragment.Expr → Fragment.Expr := fun (e : Fragment.Expr) =>
    let read := match e with
      | .var _ name => (originEntry name [] origins).map (fun (x : Fragment.Expr × List (String × Fragment.Expr) × List String) => x.1)
      | _ => some e
    match read with
    | some (.read p f receiver) =>
      match witness receiver with
      | some i => .read p f (.var receiver.span ((scope[i]?).map
          (fun (b : ScopeBinding Tree) => b.source.name) |>.getD ""))
      | none => executionPredicate G Γ scope origins e
    | _ => executionPredicate G Γ scope origins e
  match e with
  | .var p name =>
    let expanded := match originEntry name [] origins with
      | some (.var _ original, _, newer) =>
        if original != name && (valueSlot scope original).isSome then some (Fragment.Expr.var p original, newer)
        else none
      | some (read@(.read ..), older, newer) =>
        match witness read with
        | some i => some (.var p ((scope[i]?).map (fun (b : ScopeBinding Tree) => b.source.name) |>.getD ""), newer)
        | none => some (executionPredicate G Γ scope older read, newer)
      | some (predicate@(.not ..), older, newer) | some (predicate@(.shapeTest ..), older, newer)
        | some (predicate@(.tagMember ..), older, newer)
        | some (predicate@(.singletonTest ..), older, newer) | some (predicate@(.arith ..), older, newer)
        | some (predicate@(.inKeys ..), older, newer) =>
          some (executionPredicate G Γ scope older predicate, newer)
      | _ => none
    match expanded with
    | some (x, newer) =>
      if x.freeNames.all fun n => !newer.contains n && ((names scope).filter (· == n)).length ≤ 1 then x else e
    | none => e
  | .not p e => .not p (executionPredicate G Γ scope origins e)
  | .shapeTest p tag eq e => .shapeTest p tag eq (executionPredicate G Γ scope origins e)
  | .tagMember p d f ts u e => .tagMember p d f ts u (executionPredicate G Γ scope origins e)
  | .singletonTest p tag eq side l r => .singletonTest p tag eq side (operand l) (operand r)
  | .arith p op l r => .arith p op (operand l) (operand r)
  | read@(.read p fld e) =>
    match witness read with
    | some i => .var p ((scope[i]?).map (fun (b : ScopeBinding Tree) => b.source.name) |>.getD "")
    | none => .read p fld (executionPredicate G Γ scope origins e)
  | .inKeys p k e => .inKeys p (executionPredicate G Γ scope origins k) (executionPredicate G Γ scope origins e)
  | _ => e

/-- The answer a test of `origin` has where `origin` reads an immutable
binding whose slot type in `Δ` answers it one way: `true` where every label
of it answers `answer`, `false` where none does, with that slot. The slot
type is the context the graph checker establishes on every incoming edge. -/
private def knownAnswer (G : PositiveGraphs.NormalGraph Tree) (scope : List (ScopeBinding Tree))
    (Δ : List (Ty Tree)) (origin : Fragment.Expr) (tag : Tag) (answer : Bool) : Option (Nat × Bool) := do
  let .var _ name := origin | none
  let (i, .value) ← resolve scope name | none
  let T ← Δ[i]?
  if decide (Answers G T tag answer) then some (i, true)
  else if decide (Answers G T tag (!answer)) then some (i, false)
  else none

private partial def executionBranches : SourceExecution.Plan → Bool
  | .atom .. => false
  | .observe _ evaluate => executionBranches evaluate
  | .sequence _ _ evaluate next => executionBranches evaluate || executionBranches next
  | .choose .. => true

/-- A source read in the unconditional, effect-free prefix of a shared plan.
Its claim is an entry candidate checked by the incoming branch edge. A value
binding (`immutable`) holds one value throughout, so a read of it past other
reads (of members, references and positions, and effect-free evaluations)
serves as well, checked by the same edge; a call, which may narrow it as an
assertion does, ends the prefix, but a call of a native intrinsic (a `%`
name no source declares), whose contract states no promise. -/
private partial def executionEntryRead (name : String) (immutable : Bool := false) :
    SourceExecution.Plan → Option Span × Bool
  | .observe _ evaluate => executionEntryRead name immutable evaluate
  | .atom _ (.evaluate original _ .none) =>
    match original with
    | .var p n => (if n == name then some p else none, true)
    | .lit .. => (none, true)
    | _ => (none, immutable)
  | .atom _ (.methodRead ..) | .atom _ (.referenceRead ..) | .atom _ (.positionRead ..) => (none, immutable)
  | .atom _ (.evaluate (.call _ (.var _ callee) ..) _ _) => (none, immutable && callee.startsWith "%")
  | .sequence _ _ evaluate next =>
    let (found, more) := executionEntryRead name immutable evaluate
    if found.isSome || !more then (found, false) else executionEntryRead name immutable next
  | .choose _ _ _ _ evaluate _ _ => ((executionEntryRead name immutable evaluate).1, false)
  | _ => (none, false)

@[nospecialize] private partial def executionArmContext (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree)) (plan : SourceExecution.Plan) :
    Compiler (List (Ty Tree)) := do
  let G := SourceTypes.graph (← table)
  scope.zipIdx.foldlM (fun Δ (b,i) => do
    if b.source.name == "" || isSnapshot b.source.name then return Δ
    -- A slot of fixed type keeps it, as at a statement entry (`envCore`): a
    -- read's claim is derived from it, so it says no more.
    if b.fixed.isSome then return Δ
    -- A cell's slot, an early binding's included, holds the cell: a read's
    -- claim is its contents' type.
    match b.storage with
    | .cell .. | .early .. => return Δ
    | .value | .slot _ => pure ()
    if (Γ[i]?.bind (ProgramCertificates.schemeOf G ·)).isSome then return Δ
    let immutable := match b.storage with | .value => true | _ => false
    let some p := (executionEntryRead b.source.name immutable plan).1 | return Δ
    match fc.exprs.lookup p with
    | some _ =>
      let claimed ← claimAt fc p
      let refined ← if immutable then do
          let some current := Γ[i]? | throw "internal execution arm: missing value slot"
          -- A value keeps its checked type as the arm establishes its read
          -- claim. Their intersection retains both facts at the join.
          if current.all claimed.contains then pure current
          else if claimed.all current.contains then pure claimed
          else
            let (T, generation) ← tableAt
            if ← withinAt T generation current claimed then pure current
            else if ← withinAt T generation claimed current then pure claimed
            else lower (EquationStore.meet [current, claimed])
        else pure claimed
      return Δ.set i refined
    | none => return Δ) Γ

/-- A pure predicate can name a path witness in place of a source read.
Its type is the witness slot's current checked context type. Such internal
slots have no source expression claim; their uses remain ordinary typed
variable reads in the generated graph. The types are scoped to predicate
compilation, so later effects cannot retain a stale witness type. -/
@[nospecialize] private def withPredicateWitnessTypes
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (action : Compiler Target) : Compiler Target := do
  let previous ← executionBindings
  let witnesses := (scope.zip Γ).filterMap fun (b, A) =>
    if b.witness.isSome then some (b.source.name, A) else none
  withExecutionBindings { previous with types := witnesses ++ previous.types } action

/-- A terminal continuation sees the result first and all evaluated operands.
Only the plan traverses source execution; the continuation can inspect the
prepared predicate without replaying an effectful source operand. A
condition's plan (`SourceExecution.buildCondition`) may name its outcomes'
destinations (`exit`): a dispatch whose arm is an outcome then goes to that
destination itself, in the dispatch's own scope, so the edge's refinement is
the one the graph checker computes for the dispatch. -/
@[nospecialize] partial def executePlanTail (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree)) (plan : SourceExecution.Plan)
    (k : List (ScopeBinding Tree) → List (Ty Tree) → Fragment.Expr → Compiler Target)
    (exit : Option (List (ScopeBinding Tree) → List (Ty Tree) → Bool → Compiler Target) := none) :
    Compiler Target := do
  -- Defaults and expression bodies also enter here, without a statement
  -- graph's ambient witnesses. Reserve the missing paths before their tests.
  let missing := (testedPaths plan).eraseDups.filter fun p => !scope.any (·.witness == some p)
  if !missing.isEmpty then
    let source := match plan with
      | .observe p _ | .atom p _ | .sequence p _ _ _ | .choose p _ _ _ _ _ _ => p
    let top ← lower (SourceTypes.use .source)
    let witnesses : List (ScopeBinding Tree) := missing.zipIdx.map fun (p,i) =>
      { source := ⟨s!".path:{source.1}:{source.2}:{scope.length}:{i}", some source⟩,
        fixed := some [top], witness := some p }
    let mut target ← executePlanTail recursive fc (witnesses ++ scope)
      (List.replicate witnesses.length [top] ++ Γ) plan k exit
    for i in List.range witnesses.length do
      target ← emitAt source .undef (.bind target)
        (List.replicate (witnesses.length-i-1) [top] ++ Γ) [top]
        "path-witness" (scope := witnesses.drop (i+1) ++ scope)
    return target
  match plan with
  | .observe source evaluate =>
    executePlanTail recursive fc scope Γ evaluate fun scope' Δ origin => do
      let some A := Δ.head? | throw "internal execution plan: no observed result"
      let C ← executionClaim fc source (pure A)
      let next ← k scope' Δ origin
      let next ← LoweringAtoms.observeExprCurrent fc scope'.tail Δ.tail source A next
      emitAt source (.var 0) (.effect next) Δ C "expression-claim" (scope := scope')
  | .atom source operation =>
    -- A path's read whose receiver was read just before, into the prefix's
    -- witness as well, reads its field from the witness: the two slots hold
    -- one value, and the read's link is then the one a statement entry
    -- states from the prefix's witness (HOST-FAMILIES.md, "Entries").
    let operation := match operation with
      | .evaluate original@(.read _ _ receiver) (.read p f (.var q name)) .none =>
        match pathWitness scope original, pathWitness scope receiver, scope.head? with
        | some _, some j, some newest =>
          if newest.source.name == name then
            match scope[j]? with
            | some w => .evaluate original (.read p f (.var q w.source.name)) .none
            | none => operation
          else operation
        | _, _, _ => operation
      | _ => operation
    let A ← executionOperationType fc scope Γ operation
    let previous ← executionOrigins
    let preservesReads := match operation with
      | .evaluate _ _ .none | .methodRead .. | .referenceRead .. | .positionRead .. => true
      | _ => false
    let retained := if preservesReads then previous else
      previous.filter fun (_, origin) => match origin with | .var .. => true | _ => false
    let next ← withExecutionOrigins retained do
      let origin ← match operation with
        | .evaluate original@(.read ..) prepared .none =>
          if (pathWitness scope original).isSome then pure original else comparisonsExpr fc prepared
        | .evaluate _ prepared _ => comparisonsExpr fc prepared
        | _ => pure (Fragment.Expr.var source "")
      let after ← executionAfterContext fc scope Γ operation
      -- An assertion function's call leaves its actual, the name its saved
      -- operand was read from, at the promise's type from its return on.
      let saved := (← executionBindings).origins
      let witnesses ← executionWitnesses
      let original := fun (n : String) => match saved.lookup n with
        | some (.var _ o) => o
        | _ => (newestWitness witnesses n).getD n
      let called := match operation with
        | .invokeSaved source _ _ _ => source
        | _ => origin
      let after := match promiseNarrowing (SourceTypes.graph (← table)) scope after true called original with
        | some (j, T) => after.set j T
        | none => after
      let changed := Γ != after
      let witness := match operation with
        | .evaluate original _ .none => pathWitness scope original
        | _ => none
      let after := match witness with | some i => after.set i A | none => after
      -- A rebound slot no longer holds what an alias saved of it.
      withExecutionOrigins (if changed || (rebound scope operation).isSome then [] else retained)
        (k (held ⟨"",some source⟩ :: scope) (A::after) origin)
    let witness := match operation with
      | .evaluate original _ .none => pathWitness scope original
      | _ => none
    let next := match witness with
      | some i => ⟨next.label, some ((next.mapping.getD (List.range (scope.length+1))).map
          fun j => if j == i+1 then 0 else j)⟩
      | none => next
    compileExecutionOperation recursive fc scope Γ source operation next
  | .sequence _ binding evaluate next =>
    if executionBranches evaluate && executionBranches next then
      -- A sequence joins its evaluated value before compiling its continuation.
      -- Retaining branch-local frames across another choice would duplicate
      -- later conditional arguments and grow the graph exponentially.
      let A ← executionPlanType fc scope Γ evaluate
      let previous ← executionBindings
      let bound : ScopeBinding Tree := { source := ⟨binding.name,some binding.source⟩, fixed := some A }
      -- The shared continuation must not recover a saved value through a
      -- local that either evaluated arm may have rebound.
      let rebound := executionRebound scope evaluate
      let origins := previous.origins.filter fun (_, origin) =>
        !origin.freeNames.any rebound.contains
      let after ← withExecutionBindings { types := (binding.name,A)::previous.types, origins }
        (executePlanTail recursive fc (bound::scope) (A::Γ) next k exit)
      return ← executePlanTail recursive fc scope Γ evaluate fun _ Δ _ => do
        let offset := Δ.length - Γ.length
        return ⟨after.label,some ((after.mapping.getD (List.range (Γ.length+1))).map
          (fun i => if i == 0 then 0 else offset+i-1))⟩
    executePlanTail recursive fc scope Γ evaluate fun scope' Δ origin => do
      let some A := Δ.head? | throw "internal execution plan: no sequence result"
      let previous ← executionBindings
      let G := SourceTypes.graph (← table)
      let origin := match origin with
        | .read .. => if (pathWitness scope' origin).isSome then origin
            else executionPredicate G Δ scope' previous.origins origin
        | _ => executionPredicate G Δ scope' previous.origins origin
      let bound : ScopeBinding Tree := { source := ⟨binding.name,some binding.source⟩, fixed := some A }
      -- A value read from a member path is the path's witness's value.
      let witness := match origin with
        | .read .. => (pathWitness scope' origin).bind fun i =>
            (scope'[i]?).map fun (b : ScopeBinding Tree) => b.source.name
        | _ => none
      let rest := withExecutionBindings ⟨(binding.name,A)::previous.types,(binding.name,origin)::previous.origins⟩
        (executePlanTail recursive fc (bound :: scope'.tail) Δ next k exit)
      match witness with
      | some w => withExecutionWitness binding.name w rest
      | none => rest
  | .choose source _ test binding evaluate yes no =>
    executePlanTail recursive fc scope Γ evaluate fun scope' Δ origin => do
      let some result := Δ.head? | throw "internal execution plan: no condition result"
      -- A tag dispatch splits clauses, including those inside a named union.
      -- Its value expression must prove this equivalent expanded type.
      let A ← byClause result
      let previous ← executionBindings
      let witnesses ← executionWitnesses
      let origin := executionPredicate (SourceTypes.graph (← table)) Δ scope' previous.origins origin
      let G := SourceTypes.graph (← table)
      let tag := match test with
        | .truthy => Tag.truthy | .nullish => .isNullish | .defined => .isUndef
      let answer := test != .defined
      let Y ← observedSlice A tag answer
      let N ← observedSlice A tag (!answer)
      let alias := match origin with
        | .var _ name => valueSlot scope' name
        | _ => none
      -- A tested Boolean is correlated: each arm is reached by the tested
      -- expression's own dispatch and rebinds the outcome. So is a left
      -- operand read for its truthiness alone (role `truth`,
      -- `SourceExecution.buildCondition`), whatever its type: its arms
      -- rebind the outcome, a Boolean, which is all a reader sees.
      let truthOnly := binding.role == "truth"
      let correlated := test == .truthy && !Y.isEmpty && !N.isEmpty &&
        (BranchRefinement.onlyBoolean G A || truthOnly) && readOnly origin && !origin.freeNames.contains ""
      let arrays ← if correlated && arrayTested origin then some <$> builtinArrayTy else pure none
      let singles ← if correlated then conditionSingletons G scope' Δ origin else pure []
      let kinds ← if correlated then sourceKindLabels Δ else pure []
      let G := SourceTypes.graph (← table)
      let arm := fun (truth : Bool) (T : Ty Tree) (body : SourceExecution.Plan) => do
        let T := if correlated && truthOnly then (if truth then [Labels.tru] else [Labels.fls]) else T
        -- A promise's actual is the name its saved operand was read from,
        -- or the witness of the member path it was read from, which holds
        -- the same value (HOST-FAMILIES.md, "Entries").
        let original := fun (n : String) => match previous.origins.lookup n with
          | some (.var _ o) => o
          | _ => (newestWitness witnesses n).getD n
        let constants ← conditionConstants
        let implied := constantImplications G scope' Δ constants arrays (singletonOf singles) kinds
        let base := if correlated then conditionContext G scope' Δ origin truth arrays (singletonOf singles) original kinds implied else
          match alias with
          | some i => Δ.set i T
          | none => Δ
        -- Where a guard's call answered `true`, its actual is at the promise's
        -- type, which the edge's yields establish (`promiseCall_sound`).
        let base := if correlated || !truth then base else
          match promiseNarrowing G scope' Δ false origin original with
          | some (j, P) => base.set j P
          | none => base
        let base ← executionArmContext fc scope' base body
        let types := base.set 0 T
        let bound : ScopeBinding Tree := { source := ⟨binding.name,some binding.source⟩, fixed := some T }
        let sc := bound :: scope'.tail
        let savedTypes := previous.types.map fun (name,B) =>
          (name, ((resolve sc name).bind fun (i,_) => types[i]?).getD B)
        -- A rebound truthiness is that Boolean, no longer the tested value.
        let bindingOrigin := if correlated && truthOnly then Fragment.Expr.lit binding.source (.vbool truth)
          else origin
        withExecutionBindings ⟨(binding.name,T)::savedTypes,(binding.name,bindingOrigin)::previous.origins⟩ do
          let target ← executePlanTail recursive fc sc types body k exit
          if correlated then
            let mapping := (target.mapping.getD (List.range types.length)).map
              (fun i => if i == 0 then 0 else i+1)
            emitAt source (if truth then .tru else .fls) (.bind ⟨target.label,some mapping⟩)
              base T "condition-result" (scope := scope')
          else pure target
      -- An arm that is a condition's outcome goes to that outcome's
      -- destination (`exit`).
      let arm := fun (truth : Bool) (T : Ty Tree) (body : SourceExecution.Plan) =>
        match exit, body with
        | some destination, .atom _ (.outcome _ outcome) => destination scope' Δ outcome
        | _, _ => arm truth T body
      -- A proved answer admits only its selected execution. Keeping A retains
      -- the evaluated value and avoids elaborating observations in a dead arm.
      if decide (Answers G A tag answer) then
        let selected ← arm true A yes
        return ← emitAt source (.var 0) (.effect selected) Δ A "expression-dispatch" (scope := scope')
      if decide (Answers G A tag (!answer)) then
        let selected ← arm false A no
        return ← emitAt source (.var 0) (.effect selected) Δ A "expression-dispatch" (scope := scope')
      -- So does a read of an immutable binding whose slot type, the
      -- context every incoming edge establishes, answers the test. The
      -- tested value is that binding's: the selected arm holds it from the
      -- slot, at the slot's type, so it reads it as narrowly as the slot
      -- states, as `xs ?? f()` does where an earlier `xs ?? f()` on the same
      -- path narrowed `xs`.
      if let some (i, truth) := knownAnswer G scope' Δ origin tag answer then
        let body := if truth then yes else no
        if let (some destination, .atom _ (.outcome _ outcome)) := (exit, body) then
          let selected ← destination scope' Δ outcome
          return ← emitAt source (.var 0) (.effect selected) Δ A "expression-dispatch" (scope := scope')
        let some S := Δ[i]? | throw "internal execution plan: missing tested slot"
        let selected ← arm truth S body
        let fromSlot := (selected.mapping.getD (List.range Δ.length)).map fun j => if j == 0 then i else j
        return ← emitAt source (.var 0) (.effect ⟨selected.label,some fromSlot⟩) Δ A "expression-dispatch" (scope := scope')
      let yes ← arm true Y yes
      let no ← arm false N no
      if correlated then
        return ← withPredicateWitnessTypes scope' Δ
          (LoweringAtoms.compileConditionAtom recursive fc scope' Δ origin yes no)
      let adapt := fun (target : Target) =>
        ⟨target.label,some ((target.mapping.getD (List.range Δ.length)).map
          (fun i => if i == 0 || alias == some i then 0 else i+1))⟩
      let continuation := if answer then Continuation.tagBind tag (adapt yes) (adapt no)
        else .tagBind tag (adapt no) (adapt yes)
      emitAt source (.var 0) continuation Δ A "expression-dispatch" (scope := scope')

/-- A statement condition is its short-circuit plan
(`SourceExecution.buildCondition`): each dispatch whose arm is an outcome
goes to that outcome's destination, the dispatch's edge refining what the
operand's answer establishes. A destination no path answers is not
elaborated (`for (;;)`, `while (true)`: no edge to the statement after the
loop, which is then no point of the graph). -/
@[nospecialize] partial def compileCondition (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree)) (cond : Fragment.Expr)
    (yes no : Compiler Target) : Compiler Target :=
  let destination := fun (Δ : List (Ty Tree)) (truth : Bool) => do
    let offset := Δ.length - Γ.length
    let target ← if truth then yes else no
    return (⟨target.label,some ((target.mapping.getD (List.range Γ.length)).map (·+offset))⟩ : Target)
  -- Every outcome of the plan is a dispatch's arm, which `exit` consumes.
  executePlanTail recursive fc scope Γ (SourceExecution.buildCondition cond)
    (fun _ _ _ => throw "internal execution plan: a condition's outcome outside a dispatch")
    (exit := some fun _ Δ truth => destination Δ truth)

/-- Source operand scheduling is owned by ExpressionPlan. Atomic elaboration
    receives only saved operands and source annotation metadata. -/
@[nospecialize] partial def compileExpr (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (e : Fragment.Expr) (next : Target) : Compiler Target :=
  executePlanTail recursive fc scope Γ (SourceExecution.build e) fun _ Δ _ => do
    let offset := Δ.length - Γ.length
    return ⟨next.label,some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else offset+i-1))⟩

/-- `compileExprThen` whose `tail` also receives the type of the value on
    that path, which a branching expression's arm may state more precisely
    than the expression's claim (a `false` arm of `a && b`). -/
@[nospecialize] partial def compileExprThenAt (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (e : Fragment.Expr) (tail : List (Ty Tree) → Option (Ty Tree) → Compiler Target) : Compiler Target :=
  executePlanTail recursive fc scope Γ (SourceExecution.build e) fun _ Δ _ => do
    let offset := Δ.length - Γ.length
    let next ← tail (Δ.drop offset) Δ.head?
    return ⟨next.label,some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else offset+i-1))⟩

/-- `compileExpr` with the nodes after the value built for the frame the
    expression leaves: `tail` receives each path's frame, a slot narrowed
    where the expression narrowed it (`readNarrowing`), and builds what
    follows the value for that frame and the value. -/
@[nospecialize] partial def compileExprThen (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (e : Fragment.Expr) (tail : List (Ty Tree) → Compiler Target) : Compiler Target :=
  compileExprThenAt recursive fc scope Γ e fun Δ _ => tail Δ


end LoweringExecution
end Verification.SourceExtraction
