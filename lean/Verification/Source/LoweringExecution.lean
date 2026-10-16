import Verification.Source.LoweringAtoms
import Verification.Source.LoweringControl
import Verification.Source.LoweringOperands

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

@[nospecialize] private partial def executionReference (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (reference : SourceExecution.Reference) : Compiler (Tm × PropKey × Ty Tree) := do
  match reference with
  | .local name _ =>
    match resolve scope name with
    | some (i, .cell contract _) => return (.var i, valueField, contract)
    -- A slot is read at what it holds now; `localSlot` keeps it from being
    -- read or written as a cell.
    | some (i, .slot _) => return (.var i, valueField, Γ[i]?.getD [])
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
    let fld ← match prepared with
      | .read _ fld _ => pure fld
      | .index _ (some fld) _ _ => pure (.str fld)
      | _ => throw "only field and local assignments are supported"
    match PositiveRules.expand (SourceTypes.graph (← table)) B with
    | [.refs fs [] _ _ _ _] =>
      let some T := fs.lookup fld
        | throw (locatedRefusal (← table) original.span .storageWrite
          s!"update of a field '{fld}' the contract does not name as a writable location")
      pure (.var i, fld, T)
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

/-- The slot an operation rebinds: a write of a local held in a slot. -/
@[nospecialize] private def rebound (scope : List (ScopeBinding Tree)) :
    SourceExecution.Operation → Option Nat
  | .evaluate _ _ (.cellWrite name _) => match resolve scope name with
    | some (i, .slot _) => some i
    | _ => none
  | .referenceWrite _ reference _ | .updateSaved _ reference _ _ => (localSlot scope reference).map (·.1)
  | _ => none

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
    executionClaim fc original.span (exprType fc prepared)
  | .methodRead .. | .invokeSaved .. => LoweringAtoms.methodPlanType fc scope Γ operation
  | .snapshotSpread .. | .snapshotObject .. => snapshotPlanType fc scope Γ operation
  | .referenceRead source reference =>
    let (_, _, T) ← executionReference fc scope Γ reference
    executionClaim fc source (pure T)
  | .referenceWrite source _ value =>
    executionClaim fc source (do return (← executionSaved scope Γ value).2)
  | .updateSaved original _ previous _ =>
    executionClaim fc original.span (do return (← executionSaved scope Γ previous).2)
  | .positionRead source array index =>
    tryCatch (positionRead (SourceTypes.graph (← table)) (← executionSaved scope Γ array).2 index) fun reason => do
      throw (locatedRefusal (← table) source .bindingAnnotation reason)
  | .arrayRest source _ _ _ => claimAt fc source
  | .emptyObject _ => groupType [] []
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
    let R := (← executionSaved scope Γ right).2
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
    | .refs _ _ _ _ _ ks | .dict _ _ _ _ _ _ ks _ => ks.any fun K => K.among && K.keys.all copiedKey
    | _ => false

/-- Whether no value of a type is an object or `null`, which the prototype's
`__proto__` setter would make the object's prototype. -/
@[nospecialize] private def noPrototypeValue (G : PositiveGraphs.NormalGraph Tree) (V : Ty Tree) : Bool :=
  let cs := PositiveRules.expand G V
  G.plainTy V && cs.all fun c => match c with
    | .undef | .bool | .boolLit _ | .num | .numLit _ | .str | .strLit _ | .bigint | .bigintLit _
    | .symbol | .symbolLit _ => true
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
  if (← ownedWrite) != some original.span then return none
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
  let X := Γ[r]?.getD []
  let symbolCopy := fun (F : Ty Tree) => do
    if !listsCopiedKeys G X then
      refuse "a key-adding write of a symbol key on an object whose type does not list its keys: the copy of an object takes its string keys, and the symbol keys it may own are not known"
    mergeType F X
  match static with
  | some (.str name) =>
    let F ← groupType [name] [W]
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
    -- A value written where a writable index of the object admits the key
    -- is allocated at that index's type, as a literal meant for a dictionary
    -- is (`allocDict`): the copy then keeps the index.
    let keyClass := fun (c : PositiveNormalization.Clause (Ty Tree)) => match c with
      | .str | .strLit _ => some IndexKeys.strings
      | .num | .numLit _ => some IndexKeys.numeric
      | .symbol | .symbolLit _ => some IndexKeys.symbols
      | _ => none
    let classes := (cs.filterMap keyClass).eraseDups
    let cellType : Option (Ty Tree) := match PositiveRules.expand G X with
      | [.dict _ _ _ _ _ _ _ cells] =>
        let ts := classes.map fun K => (cells.find? fun y => IndexKeys.within K y.1).map (·.2)
        match (ts.filterMap id).eraseDups with
        | [V] => if ts.all Option.isSome then some V else none
        | _ => none
      | _ => none
    let F ← keyedType K (cellType.getD W)
    let proto := cs.any fun c => match c with | .str => true | .strLit s => s == "__proto__" | _ => false
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
        | .cell .. => Γ) Γ
    if (← ownedWrite) == some original.span then
      if let .objectAssign _ (.var _ name) _ := original then
        let some i := valueSlot scope name | throw "internal execution plan: missing owned Object.assign target"
        return Γ.set i (← executionOperationType fc scope Γ operation)
    pure Γ
  | _ => pure Γ

/-- Every prepared primitive is checked at the original expression's claim,
    including a result represented internally by a saved-value read. -/
@[nospecialize] private partial def executionEvaluate (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (original prepared : Fragment.Expr) (next : Target) : Compiler Target := do
  if let some g ← executionGrowth fc scope Γ original prepared then
    let values := g.holders.filterMap fun (i, storage) => match storage with
      | .value | .slot _ => some i
      | .cell .. => none
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
  let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
    (fun i => if i == 0 || copied == some (i-1) then 0 else i+1)
  let cast ← emitAt original.span (.var 0) (.bind ⟨next.label, some mapping⟩)
    (B::Γ) A "expression-claim" (scope := held ⟨"",some original.span⟩ :: scope)
  withPreparedAtom original do
    let prepared ← comparisonsExpr fc prepared
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
    let (object, fld, _) ← executionReference fc scope Γ reference
    emitAt source (.readAt fld object) (.bind next) Γ A (scope := scope)
  | .referenceWrite _ reference value =>
    if let some (j, contract) := localSlot scope reference then
      -- The value, checked at the contract, rebinds the slot.
      let (i, _) ← executionSaved scope Γ value
      let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
        (fun k => if k == j+1 then 0 else k)
      let result ← emitAt source (.var i) (.bind ⟨next.label, some mapping⟩) Γ A "expression-claim" (scope := scope)
      return ← emitAt source (.var i) (.effect result) Γ contract "storage-contract" (scope := scope)
    let (object, fld, _) ← executionReference fc scope Γ reference
    let (i, _) ← executionSaved scope Γ value
    let result ← emitAt source (.var i) (.bind next) Γ A "expression-claim" (scope := scope)
    emitAt source (.writeAt fld object (.var i)) (.effect result) Γ [Labels.nul]
      "storage-contract" (scope := scope)
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
    let (object, fld, _) ← executionReference fc scope Γ reference
    let mapping := (next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1)
    let result ← emitAt source (.var (if post then old+1 else 0)) (.bind ⟨next.label, some mapping⟩)
      (N::Γ) A "expression-claim" (scope := scope')
    let object ← match object with
      | .var i => pure (Tm.var (i+1))
      | _ => throw "internal execution plan: reference is not a saved location"
    let write ← emitAt source (.writeAt fld object (.var 0)) (.effect result)
      (N::Γ) [Labels.nul] "storage-contract" (scope := scope')
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

/-- Predicate metadata recovers immutable aliases and reads whose cells have
not been invalidated by an intervening effect. -/
@[nospecialize] private partial def executionPredicate (scope : List (ScopeBinding Tree))
    (origins : List (String × Fragment.Expr)) (e : Fragment.Expr) : Fragment.Expr :=
  match e with
  | .var p name =>
    match origins.lookup name with
    | some (.var _ original) =>
      if original != name && (valueSlot scope original).isSome then
        .var p original
      else e
    | some predicate@(.not ..) | some predicate@(.shapeTest ..)
      | some predicate@(.singletonTest ..) | some predicate@(.arith ..)
      | some predicate@(.inKeys ..) | some predicate@(.read ..) =>
        executionPredicate scope origins predicate
    | _ => e
  | .not p e => .not p (executionPredicate scope origins e)
  | .shapeTest p tag eq e => .shapeTest p tag eq (executionPredicate scope origins e)
  | .singletonTest p tag eq side l r => .singletonTest p tag eq side
      (executionPredicate scope origins l) (executionPredicate scope origins r)
  | .arith p op l r => .arith p op (executionPredicate scope origins l) (executionPredicate scope origins r)
  | .read p fld e => .read p fld (executionPredicate scope origins e)
  | .inKeys p k e => .inKeys p (executionPredicate scope origins k) (executionPredicate scope origins e)
  | _ => e

private partial def executionBranches : SourceExecution.Plan → Bool
  | .atom .. => false
  | .observe _ evaluate => executionBranches evaluate
  | .sequence _ _ evaluate next => executionBranches evaluate || executionBranches next
  | .choose .. => true

/-- A source read in the unconditional, effect-free prefix of a shared plan.
Its claim is an entry candidate checked by the incoming branch edge. -/
private partial def executionEntryRead (name : String) : SourceExecution.Plan → Option Span × Bool
  | .observe _ evaluate => executionEntryRead name evaluate
  | .atom _ (.evaluate original _ .none) =>
    match original with
    | .var p n => (if n == name then some p else none, true)
    | .lit .. => (none, true)
    | _ => (none, false)
  | .sequence _ _ evaluate next =>
    let (found, more) := executionEntryRead name evaluate
    if found.isSome || !more then (found, false) else executionEntryRead name next
  | .choose _ _ _ _ evaluate _ _ => ((executionEntryRead name evaluate).1, false)
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
    if let .cell .. := b.storage then return Δ
    if (Γ[i]?.bind (ProgramCertificates.schemeOf G ·)).isSome then return Δ
    let some p := (executionEntryRead b.source.name plan).1 | return Δ
    match fc.exprs.lookup p with
    | some _ => return Δ.set i (← claimAt fc p)
    | none => return Δ) Γ

/-- A terminal continuation sees the result first and all evaluated operands.
Only the plan traverses source execution; the continuation can inspect the
prepared predicate without replaying an effectful source operand. -/
@[nospecialize] partial def executePlanTail (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree)) (plan : SourceExecution.Plan)
    (k : List (ScopeBinding Tree) → List (Ty Tree) → Fragment.Expr → Compiler Target) : Compiler Target := do
  match plan with
  | .observe source evaluate =>
    executePlanTail recursive fc scope Γ evaluate fun scope' Δ origin => do
      let some A := Δ.head? | throw "internal execution plan: no observed result"
      let C ← executionClaim fc source (pure A)
      let next ← k scope' Δ origin
      let next ← LoweringAtoms.observeExprCurrent fc scope'.tail Δ.tail source A next
      emitAt source (.var 0) (.effect next) Δ C "expression-claim" (scope := scope')
  | .atom source operation =>
    let A ← executionOperationType fc scope Γ operation
    let previous ← executionOrigins
    let preservesReads := match operation with
      | .evaluate _ _ .none | .methodRead .. | .referenceRead .. | .positionRead .. => true
      | _ => false
    let retained := if preservesReads then previous else
      previous.filter fun (_, origin) => match origin with | .var .. => true | _ => false
    let next ← withExecutionOrigins retained do
      let origin ← match operation with
        | .evaluate _ prepared _ => comparisonsExpr fc prepared
        | _ => pure (Fragment.Expr.var source "")
      let after ← executionAfterContext fc scope Γ operation
      -- A rebound slot no longer holds what an alias saved of it.
      withExecutionOrigins (if Γ != after || (rebound scope operation).isSome then [] else retained)
        (k (held ⟨"",some source⟩ :: scope) (A::after) origin)
    compileExecutionOperation recursive fc scope Γ source operation next
  | .sequence _ binding evaluate next =>
    if executionBranches evaluate && executionBranches next then
      -- A sequence joins its evaluated value before compiling its continuation.
      -- Retaining branch-local frames across another choice would duplicate
      -- later conditional arguments and grow the graph exponentially.
      let A ← executionPlanType fc scope Γ evaluate
      let previous ← executionBindings
      let bound : ScopeBinding Tree := { source := ⟨binding.name,some binding.source⟩, fixed := some A }
      let after ← withExecutionBindings { previous with types := (binding.name,A)::previous.types }
        (executePlanTail recursive fc (bound::scope) (A::Γ) next k)
      return ← executePlanTail recursive fc scope Γ evaluate fun _ Δ _ => do
        let offset := Δ.length - Γ.length
        return ⟨after.label,some ((after.mapping.getD (List.range (Γ.length+1))).map
          (fun i => if i == 0 then 0 else offset+i-1))⟩
    executePlanTail recursive fc scope Γ evaluate fun scope' Δ origin => do
      let some A := Δ.head? | throw "internal execution plan: no sequence result"
      let previous ← executionBindings
      let origin := executionPredicate scope' previous.origins origin
      let bound : ScopeBinding Tree := { source := ⟨binding.name,some binding.source⟩, fixed := some A }
      withExecutionBindings ⟨(binding.name,A)::previous.types,(binding.name,origin)::previous.origins⟩
        (executePlanTail recursive fc (bound :: scope'.tail) Δ next k)
  | .choose source _ test binding evaluate yes no =>
    executePlanTail recursive fc scope Γ evaluate fun scope' Δ origin => do
      let some result := Δ.head? | throw "internal execution plan: no condition result"
      -- A tag dispatch splits clauses, including those inside a named union.
      -- Its value expression must prove this equivalent expanded type.
      let A ← byClause result
      let previous ← executionBindings
      let origin := executionPredicate scope' previous.origins origin
      let G := SourceTypes.graph (← table)
      let tag := match test with
        | .truthy => Tag.truthy | .nullish => .isNullish | .defined => .isUndef
      let answer := test != .defined
      let Y ← observedSlice A tag answer
      let N ← observedSlice A tag (!answer)
      let alias := match origin with
        | .var _ name => valueSlot scope' name
        | _ => none
      let correlated := test == .truthy && !Y.isEmpty && !N.isEmpty &&
        BranchRefinement.onlyBoolean G A && readOnly origin && !origin.freeNames.contains ""
      let arrays ← if correlated && arrayTested origin then some <$> builtinArrayTy else pure none
      let arm := fun (truth : Bool) (T : Ty Tree) (body : SourceExecution.Plan) => do
        let base := if correlated then conditionContext G scope' Δ origin truth arrays else
          match alias with
          | some i => Δ.set i T
          | none => Δ
        let base ← executionArmContext fc scope' base body
        let types := base.set 0 T
        let bound : ScopeBinding Tree := { source := ⟨binding.name,some binding.source⟩, fixed := some T }
        let sc := bound :: scope'.tail
        let savedTypes := previous.types.map fun (name,B) =>
          (name, ((resolve sc name).bind fun (i,_) => types[i]?).getD B)
        withExecutionBindings ⟨(binding.name,T)::savedTypes,(binding.name,origin)::previous.origins⟩ do
          let target ← executePlanTail recursive fc sc types body k
          if correlated then
            let mapping := (target.mapping.getD (List.range types.length)).map
              (fun i => if i == 0 then 0 else i+1)
            emitAt source (if truth then .tru else .fls) (.bind ⟨target.label,some mapping⟩)
              base T "condition-result" (scope := scope')
          else pure target
      -- A proved answer admits only its selected execution. Keeping A retains
      -- the evaluated value and avoids elaborating observations in a dead arm.
      if decide (Answers G A tag answer) then
        let selected ← arm true A yes
        return ← emitAt source (.var 0) (.effect selected) Δ A "expression-dispatch" (scope := scope')
      if decide (Answers G A tag (!answer)) then
        let selected ← arm false A no
        return ← emitAt source (.var 0) (.effect selected) Δ A "expression-dispatch" (scope := scope')
      let yes ← arm true Y yes
      let no ← arm false N no
      if correlated then
        return ← LoweringAtoms.compileConditionAtom recursive fc scope' Δ origin yes no
      let adapt := fun (target : Target) =>
        ⟨target.label,some ((target.mapping.getD (List.range Δ.length)).map
          (fun i => if i == 0 || alias == some i then 0 else i+1))⟩
      let continuation := if answer then Continuation.tagBind tag (adapt yes) (adapt no)
        else .tagBind tag (adapt no) (adapt yes)
      emitAt source (.var 0) continuation Δ A "expression-dispatch" (scope := scope')

/-- A statement condition follows the same operand plan as a value expression.
The final pure predicate uses the retained operands to justify refinements. -/
@[nospecialize] partial def compileCondition (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree)) (cond : Fragment.Expr)
    (yes no : Target) : Compiler Target :=
  executePlanTail recursive fc scope Γ (SourceExecution.build cond) fun inner Δ origin => do
    let offset := Δ.length - Γ.length
    let adapt := fun (target : Target) =>
      ⟨target.label,some ((target.mapping.getD (List.range Γ.length)).map (·+offset))⟩
    let predicate := executionPredicate inner (← executionOrigins) origin
    let A := Δ.headD []
    let G := SourceTypes.graph (← table)
    if decide (Answers G A .truthy true) then
      return ← emitAt cond.span (.var 0) (.effect (adapt yes)) Δ A (scope := inner)
    if decide (Answers G A .truthy false) then
      return ← emitAt cond.span (.var 0) (.effect (adapt no)) Δ A (scope := inner)
    let unsettled := !(BranchRefinement.tagSlice G A .truthy true).isEmpty &&
      !(BranchRefinement.tagSlice G A .truthy false).isEmpty
    if unsettled && readOnly predicate && !predicate.freeNames.contains "" then
      LoweringAtoms.compileConditionAtom recursive fc inner Δ predicate (adapt yes) (adapt no)
    else
      let drop := fun (target : Target) =>
        ⟨target.label,some ((target.mapping.getD (List.range Γ.length)).map (·+(offset+1)))⟩
      let transfer := Continuation.tagBind .truthy (drop yes) (drop no)
      emitAt cond.span (.var 0) transfer Δ A (scope := inner)

/-- Source operand scheduling is owned by ExpressionPlan. Atomic elaboration
    receives only saved operands and source annotation metadata. -/
@[nospecialize] partial def compileExpr (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (e : Fragment.Expr) (next : Target) : Compiler Target :=
  executePlanTail recursive fc scope Γ (SourceExecution.build e) fun _ Δ _ => do
    let offset := Δ.length - Γ.length
    return ⟨next.label,some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else offset+i-1))⟩


end LoweringExecution
end Verification.SourceExtraction
