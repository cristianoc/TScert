import Verification.Source.LoweringState
import Verification.Source.LoweringTypes
import Verification.Source.LoweringObservations

/-! Builds direct proof plans for values, predicates and members. -/
namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

section
variable {ι : Type} [Labels ι]

/-- The record a group of an object literal's fields allocates: exactly their
keys, each at its initializer's type, which its own obligation establishes. -/
@[nospecialize] def groupType (ns : List String) (As : List (Ty Tree)) : Compiler (Ty Tree) := do
  let keys := ns.map PropKey.str
  let label ← lower (SourceTypes.use (.refs (keys.zip As) [] [] [] [] [⟨true, keys⟩]))
  -- A type the search may need at a node it types on its own.
  recordHints [label]
  return [label]

/-- The type an object literal's claim states for each key it names, where
its records agree on it: a field initializer is built at it, as a literal's
fields are at its claim's. -/
@[nospecialize] def claimedFields (A : Ty Tree) : Compiler (List (String × Ty Tree)) := do
  let G := SourceTypes.graph (← table)
  let keyed := fun (ps : List (PropKey × Ty Tree)) => ps.filterMap fun (k, T) => match k with
    | .str s => some (s, T) | .sym _ => none
  let each := (PositiveRules.expand G A).map fun c => match c with
    | .refs fs [] vs os _ _ | .dict fs [] vs _ os _ _ _ => keyed (fs ++ vs ++ os.map fun o => (o.key, o.type))
    | _ => []
  -- Over a union, a key every record naming it states at one type.
  let all := each.flatten
  return all.filter fun (k, T) => all.all fun (k', T') => k' != k || T' == T

/-- The type a merge of a source of type `B` onto an accumulator of type `A`
is given, less the dropped keys: one record per pair of their clauses
(`ObjectMerge.mergeResult`), which the merge rule checks. -/
@[nospecialize] def mergeType (A B : Ty Tree) (drop : List PropKey := []) : Compiler (Ty Tree) := do
  let G := SourceTypes.graph (← table)
  let ca := PositiveRules.expand G A
  let cb := PositiveRules.expand G B
  if ca.isEmpty then throw "internal: an object literal's accumulator has no clause"
  if cb.isEmpty then
    throw "a spread's operand must have a type of plain objects, null, undefined, Booleans, numbers, bigints or symbols"
  let mut labels : List Tree := []
  for c in ca do
    for d in cb do
      let some r := ObjectMerge.mergeResult G drop c d
        | throw "a spread copies the own enumerable properties of a plain object; one of a string, an array, a function or a class value is outside the fragment"
      labels := labels ++ [← lower (SourceTypes.use r)]
  recordHints (labels)
  return labels.eraseDups

/-- A saved read is usable only in a subtree with no possible heap effects or
escaping closure. Reads are plain modeled cells, never JavaScript accessors. -/
partial def readOnly : Fragment.Expr → Bool
  | .var .. | .lit .. => true
  | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e => readOnly e
  | .equality _ _ a b | .singletonTest _ _ _ _ a b | .logical _ _ a b | .coalesce _ a b
  | .optional _ _ a b | .index _ _ a b | .arith _ _ a b | .elemAt _ a b
  | .comma _ a b | .inKeys _ a b => readOnly a && readOnly b
  | .ifBody _ c t e => readOnly c && readOnly t && readOnly e
  | .alloc .. | .build .. | .write .. | .indexWrite .. | .update .. | .logicalAssign .. | .assign .. | .arrayLit .. | .elemWrite .. | .arrayAssign .. | .nullishAssign .. | .lambda .. | .withValue .. | .bindWithReceiver ..
  | .callWithReceiver .. | .applyWithReceiver .. | .call .. | .invoke .. | .ctor .. | .construct .. | .block ..
  | .objectAssign .. => false

/-- The other operand of a singleton comparison, when saving the tested read
before it changes nothing: a literal, a name, or one field read. Each is
effect-free, so the two operands' values are the same in either order. The
singleton itself comes from the operand's claimed type, which its expression
obligation must establish; a call or a write could change the tested cell. -/
private def pureOperand : Fragment.Expr → Bool
  | .lit .. | .var .. | .read _ _ (.var ..) => true
  | _ => false

/-- A source read saved once for a guard on its result. -/
@[nospecialize] private def guardSnapshot (scope : List (ScopeBinding ι)) : Fragment.Expr → Option String
  | .read _ fld (.var _ name) => do
    let _ ← resolve scope name
    readSnapshot name fld
  | .var _ name => match resolve scope name with
    | some (_, .cell ..) => some (localSnapshotName name)
    | _ => none
  | _ => none

/-- Save the plain read in a shape or singleton comparison. The singleton's
other operand is effect-free; moving it across the read has no effect. -/
@[nospecialize] def readGuard (scope : List (ScopeBinding ι)) :
    Fragment.Expr → Option (String × Fragment.Expr × Fragment.Expr)
  | .not pos e => (readGuard scope e).map fun (snapshot,r,c) => (snapshot,r,.not pos c)
  | .shapeTest pos tag equal r => do
    let snapshot ← guardSnapshot scope r
    some (snapshot,r,.shapeTest pos tag equal (.var r.span snapshot))
  | .singletonTest pos tag equal testLeft left right => do
    let (r,lit) := if testLeft then (left,right) else (right,left)
    guard (pureOperand lit)
    let snapshot ← guardSnapshot scope r
    let saved := Fragment.Expr.var r.span snapshot
    some (snapshot,r,.singletonTest pos tag equal testLeft
      (if testLeft then saved else lit) (if testLeft then lit else saved))
  | _ => none

/-- Negations of an immutable variable retain its identity and reverse the
branch polarity. Arbitrary expressions deliberately carry no alias refinement. -/
@[nospecialize] def conditionVariable (scope : List (ScopeBinding ι)) : Fragment.Expr → Option (Nat × Bool)
  | .var _ name => (valueSlot scope name).map (·, false)
  | .not _ e => (conditionVariable scope e).map fun (i, reversed) => (i, !reversed)
  | _ => none

/-- Only a syntactic immutable variable retains an alias to the observed value.
Reads and calls deliberately do not qualify, even if their types look stable. -/
@[nospecialize] private def tagConditionVariable (scope : List (ScopeBinding ι)) : Fragment.Expr → Option (Nat × Tag × Bool)
  | .not _ e => (tagConditionVariable scope e).map fun (i, tag, equal) => (i, tag, !equal)
  | .shapeTest _ tag equal (.var _ name) =>
    (valueSlot scope name).map (·, tag, equal)
  | .singletonTest _ tag equal testLeft left right =>
    match (if testLeft then left else right) with
    | .var _ name => (valueSlot scope name).map (·, tag, equal)
    | _ => none
  | _ => none

/-- The tag a condition tests on an immutable variable: its own shape or
singleton test, or, for a variable that is not a Boolean, its truthiness
(`ToBoolean`), which is how JavaScript reads any other value as a condition. -/
@[nospecialize] def conditionTag (G : PositiveGraphs.NormalGraph ι) (scope : List (ScopeBinding ι))
    (Γ : List (Ty ι)) : Fragment.Expr → Option (Nat × Tag × Bool)
  | .not _ e => (conditionTag G scope Γ e).map fun (i, tag, equal) => (i, tag, !equal)
  | .var _ name => do
    let i ← valueSlot scope name
    let A ← Γ[i]?
    if BranchRefinement.onlyBoolean G A then none else some (i, .truthy, true)
  | e => tagConditionVariable scope e

def tagTestTerm (tag : Tag) (equal : Bool) (slot : Nat) : Tm :=
  .ite (.test tag (.var slot)) (if equal then .tru else .fls) (if equal then .fls else .tru)

/-- Split an explicit union and require a known test outcome for each arm.
A broad numeric arm is not silently treated as unequal to the singleton. -/
@[nospecialize] def tagTestPlan (G : PositiveGraphs.NormalGraph ι) (tag : Tag) (Γ : List (Ty ι)) (slot : Nat)
    (equal : Bool) (A : Ty ι) : Except String (DirectProof.Plan ι) := do
  let some C := Γ[slot]? | throw "internal tag-test slot mismatch"
  let term := tagTestTerm tag equal slot
  let children ← C.mapM fun a => do
    let H := Γ.set slot [a]
    let q := decide (Answers G [a] tag true)
    let value := if q == equal then Tm.tru else .fls
    let B := if q == equal then [Labels.tru] else [Labels.fls]
    let rule := if q == equal then ProgramCertificates.Rule.truLit else .flsLit
    if !q && !(decide (Answers G [a] tag false)) then
      -- An arm whose answer its type leaves open (a number against a numeric
      -- singleton, an open record for a key, an unknown shape) is a real
      -- Boolean: the test's own value.
      let test := DirectProof.node H (.test tag (.var slot)) [Labels.tru,Labels.fls] .test [DirectProof.var H slot [a]]
      let yes := DirectProof.cast H A (DirectProof.node H (if equal then .tru else .fls) (if equal then [Labels.tru] else [Labels.fls])
        (if equal then .truLit else .flsLit))
      let no := DirectProof.cast H A (DirectProof.node H (if equal then .fls else .tru) (if equal then [Labels.fls] else [Labels.tru])
        (if equal then .flsLit else .truLit))
      return DirectProof.node H term A .ifBool [test, yes, no]
    pure (DirectProof.node H term A (if q then .ifTrue else .ifFalse)
      [DirectProof.cast H A (DirectProof.node H value B rule)])
  pure (DirectProof.node Γ term A (.unionVar slot) children)

/-- `ite (test tag x) yes no` on the value in `slot`, split by its labels: a
label the tag answers selects its arm, and a mixed label (a number's
truthiness, or an unknown one) needs a real Boolean branch, where both arms
must establish `B`. `??`, a default parameter and `&&`/`||` are this shape, on
the nullish, `undefined` and truthiness tags. -/
@[nospecialize] def selectPlan (G : PositiveGraphs.NormalGraph ι) (Γ : List (Ty ι))
    (slot : Nat) (B : Ty ι) (tag : Tag) (yes no : DirectProof.Plan ι) :
    Except String (DirectProof.Plan ι) := do
  let some C := Γ[slot]? | throw "internal selection slot mismatch"
  let term := Tm.ite (.test tag (.var slot)) yes.term no.term
  let children := C.map fun label =>
    let L := Γ.set slot [label]
    let q := decide (Answers G [label] tag true)
    if q || decide (Answers G [label] tag false) then
      DirectProof.node L term B (if q then .ifTrue else .ifFalse)
        [DirectProof.cast L B (if q then yes else no)]
    else
      let test := DirectProof.node L (.test tag (.var slot)) [Labels.tru,Labels.fls] .test
        [DirectProof.var L slot [label]]
      DirectProof.node L term B .ifBool [test, DirectProof.cast L B yes, DirectProof.cast L B no]
  pure (DirectProof.node Γ term B (.unionVar slot) children)

/-- Where `Array.isArray` holds, the labels `arraySlice` keeps of `A`, and the
builtins's `readonly unknown[]`, `R`, for the records and `unknown` it does not:
the refinement the edge's observation establishes. -/
@[nospecialize] def arrayRefine (G : PositiveGraphs.NormalGraph ι) (A R : Ty ι) : Ty ι :=
  let sliced := BranchRefinement.tagSlice G A .isArray true
  let kept := sliced.filter fun a => !(G.plain a && (G a).all fun c =>
    ProgramTyping.tagClause .isArray c == some false || c.carriesInvariant)
  if kept.length == sliced.length then sliced else kept ++ R

/-- The built-in `readonly unknown[]`: the array shape over a possibly sparse
store of `unknown`. -/
@[nospecialize] def builtinArrayTy : Compiler (Ty Tree) := do
  let u ← lower (SourceTypes.use .source)
  let store ← lower (SourceTypes.use (.list ⟨[], [], some [u], true, .sparse⟩ []))
  return [← lower (SourceTypes.use (SourceTypes.arrayOf (← table) store true))]

/-- What a tag test answering `q` keeps of `A`: `tagSlice`, and where
`Array.isArray` holds, `arrayRefine`. -/
@[nospecialize] def tagRefine (A : Ty Tree) (tag : Tag) (q : Bool) : Compiler (Ty Tree) := do
  let G := SourceTypes.graph (← table)
  if tag == .isArray && q then return arrayRefine G A (← builtinArrayTy)
  else return BranchRefinement.tagSlice G A tag q

/-- Shared conditional proof construction for statement branches, ternaries and
short-circuit operators. Branch builders retain their own source claims; a
logical operator's constant arm is administrative and needs no invented claim. -/
@[nospecialize] def conditionalPlan (scope : List (ScopeBinding Tree)) (H : List (Ty Tree)) (A : Ty Tree)
    (cond : Fragment.Expr) (c : DirectProof.Plan Tree)
    (yesBranch noBranch : List (ScopeBinding Tree) → List (Ty Tree) → Compiler (DirectProof.Plan Tree)) :
    Compiler (DirectProof.Plan Tree) := do
  let G := SourceTypes.graph (← table)
  -- A tested variable's slot, past the saved condition; or, for a condition
  -- that is not a Boolean, the saved value itself, tested for truthiness.
  let tagged : Option (Nat × Tag × Bool) := match conditionTag G scope H cond with
    | some (i, tag, equal) => some (i+1, tag, equal)
    | none => if BranchRefinement.onlyBoolean G c.type then none else some (0, .truthy, true)
  if let some (tested, tag, equal) := tagged then
    -- Preserve the evaluated predicate and its claims in an anonymous slot.
    let K := c.type :: H
    let some C := K[tested]? | throw "internal closure tag-guard slot mismatch"
    let T := K.set tested (← tagRefine C tag true)
    let F := K.set tested (← tagRefine C tag false)
    let t ← yesBranch (held ⟨"",some cond.span⟩ :: scope) (if equal then T else F)
    let e ← noBranch (held ⟨"",some cond.span⟩ :: scope) (if equal then F else T)
    let yes := if equal then t else e
    let no := if equal then e else t
    pure (DirectProof.letE H c (← selectPlan G K tested A tag yes no))
  else
    -- A variable already known `true` or `false` keeps its singleton: the
    -- condition's type selects the reachable arm (`ifKnown`).
    match (conditionVariable scope cond).filter fun (i, _) => H[i]? != some [Labels.tru] && H[i]? != some [Labels.fls] with
    | some (i, reversed) =>
      let T := H.set i [Labels.tru]
      let F := H.set i [Labels.fls]
      let t ← yesBranch scope (if reversed then F else T)
      let e ← noBranch scope (if reversed then T else F)
      let yes := if reversed then e else t
      let no := if reversed then t else e
      pure (DirectProof.node H (.ite (.var i) yes.term no.term) A (.ifBoolVar [Labels.tru] [Labels.fls])
        [DirectProof.cast T A yes,DirectProof.cast F A no])
    | none =>
      let t ← yesBranch scope H
      let e ← noBranch scope H
      pure (DirectProof.ifE G H A c t e)

/-- The scope an operand saved in a fresh slot 0 extends. A named immutable
operand is identical to the saved value: its name moves to that slot, so what
follows sees the refinement a test of the saved value establishes. No mutable
read is given an alias. -/
@[nospecialize] def savedOperandScope (scope : List (ScopeBinding ι)) (operand : Fragment.Expr) :
    List (ScopeBinding ι) :=
  match operand with
  | .var _ name =>
    if (valueSlot scope name).isSome then held ⟨name,some operand.span⟩ ::
      scope.map (fun b => if b.source.name == name then held ⟨"",some operand.span⟩ else b)
    else held ⟨"",some operand.span⟩ :: scope
  | _ => held ⟨"",some operand.span⟩ :: scope

/-- Label 3 is `undefined`: see `SourceTypes.initial`. A position a call may
omit is one whose declared contract admits that value, because `undefined` is
what the machine binds there. -/
@[nospecialize] def admitsUndefined (G : PositiveGraphs.NormalGraph ι) (A : Ty ι) : Bool :=
  (PositiveRules.expand G A).any fun
    | .undef | .top => true
    | _ => false

/-- Select a signature these actuals can call: one declaring exactly the
arguments written, or a longer one whose remaining positions admit `undefined`.
An exact signature is preferred, then one covering every actual type. No actual
is invented for an omitted position; the call term keeps the arguments the
source writes. -/
@[nospecialize] def selectSignature (G : PositiveGraphs.NormalGraph ι) (L : PositiveRules.Ops ι) (As : List (Ty ι))
    (Rr : Ty ι := [Labels.undef]) :
    Except String (Arrow (Ty ι)) := do
  let covers (p : Arrow (Ty ι)) :=
    (As.zip p.arguments).all fun (A,D) => A.all D.contains
  -- Instances of one scheme may differ only in their receiver: prefer the
  -- signature naming the receiver passed.
  let receives (p : Arrow (Ty ι)) := Rr.all p.receiver.contains
  let pick (choices : List (Arrow (Ty ι))) :=
    (choices.find? fun p => covers p && receives p) <|> (choices.find? covers) <|> choices.head?
  let exact := L.filter fun p => p.arguments.length == As.length
  let short := L.filter fun p =>
    As.length < p.arguments.length && (p.arguments.drop As.length).all (admitsUndefined G)
  let some p := pick exact <|> pick short
    | throw "callee has no signature with the actual argument count"
  return p

/-- A list `.apply` reads no element of: every member null or undefined. -/
@[nospecialize] def nullishList (G : PositiveGraphs.NormalGraph ι) (T : Ty ι) : Bool :=
  !T.isEmpty && (PositiveRules.expand G T).all fun
    | .nul | .undef => true
    | _ => false

/-- A plain call passes `undefined` as its receiver: the premise proves it at
the selected signature's receiver contract. -/
@[nospecialize] def plainReceiver (Γ : List (Ty ι)) (Rt : Ty ι) : DirectProof.Plan ι :=
  DirectProof.cast Γ Rt (DirectProof.node Γ .undef [Labels.undef] .undef)

/-- One premise per position the selected signature declares and the call
omits, each proving `undefined` at that position's contract. -/
@[nospecialize] def omittedPremises (Γ : List (Ty ι)) (Ds : List (Ty ι)) (supplied : Nat) :
    List (DirectProof.Plan ι) :=
  (Ds.drop supplied).map fun D =>
    DirectProof.cast Γ D (DirectProof.node Γ .undef [Labels.undef] .undef)

/-- Nest saved operand plans in their original evaluation order. -/
@[nospecialize] def saveOperands (ps : List (DirectProof.Plan ι)) (body : DirectProof.Plan ι) : DirectProof.Plan ι :=
  ps.foldr (fun p b => DirectProof.letE p.goal.context p b) body

@[nospecialize] def allocationChildren : DirectProof.Plan ι → Option (List (DirectProof.Plan ι))
  | .cast _ p => allocationChildren p
  | .rule _ .alloc ps => some ps
  | _ => none

/-- A method call's head: a host-relative member is read from the object in a
slot and bound to that same object (`bindMember`), before any actual runs; any
other member is read as a field. -/
@[nospecialize] def memberHead (G : PositiveGraphs.NormalGraph ι) (O : Ty ι) (fld : PropKey) (obj : Tm) : Tm :=
  match obj, (ProgramTyping.memberOf G O fld).isSome with
  | .var i, true => .letE (.readAt fld (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])
  | _, _ => .readAt fld obj

/-- The row a field read gives before any claim replaces it: the object's own
field or view, or, for a key an own-key bound does not admit, its prototype's, as
`readCell` and the top level's search read it. -/
@[nospecialize] private def fieldRow (G : PositiveGraphs.NormalGraph ι) (O : Ty ι) (fld : PropKey) :
    Option (Ty ι) :=
  match PositiveRules.expand G O with
  | [.refs fs [] vs _ _ ks] => fs.lookup fld <|> vs.lookup fld <|> do
      if !ks.any (fun K => !K.admits fld) then none
      let P ← (fs ++ vs).lookup SourceTypes.protoField
      let [.refs gs [] ws _ _ _] := PositiveRules.expand G P | none
      (gs ++ ws.filter (·.1 != lengthKey)).lookup fld
  | [.callable fs _ _ _] => fs.lookup fld
  | _ => none

/-- A method call's explicit type arguments, `o.m<A₁,…,Aₖ>(…)`, are a
requirement on the instance the call uses: the member read from `O` is a scheme
row, the claimed method type `M` is an instance of it by a checked instance map
(`compareInstancesState`), and that map sends the scheme's first `k` binders to types
of the same meaning as `A₁,…,Aₖ`. The binders past them are the ones the
call's receiver and actuals fix, as for a call without type arguments. The
check only refuses: acceptance still rests on the read's own `inst` proof and
the call's typing. -/
@[nospecialize] def explicitInstance (pos : Span) (O M : Ty Tree) (fld : PropKey) (typeArgs : List Json) :
    Compiler Unit := do
  if typeArgs.isEmpty then return
  let args ← typeArgs.mapM fun t => lower (Fragment.translate t)
  let T ← table
  let G := SourceTypes.graph T
  let refuse (reason : String) := locatedRefusal T pos .schemeElimination reason
  let some S := (ProgramTyping.memberSchemes G O fld).head? <|> fieldRow G O fld
    | throw (refuse s!"explicit type arguments name no member '{fld}' of the receiver")
  let [i] := S | throw (refuse "explicit type arguments need a generic member")
  let some s := G.schemes i | throw (refuse "explicit type arguments need a generic member")
  if args.length > s.binders.length then
    throw (refuse "more explicit type arguments than the member has binders")
  -- Source checks use the same validated equations and image equality as
  -- the final request, including intersections in generic signatures.
  let F ← EquationStore.freeze T
  let S ← EquationLowering.closedUnion F.equations "explicit method receiver" S
  let M ← EquationLowering.closedUnion F.equations "explicit method instance" M
  let args ← (args.mapM (EquationLowering.closedUnion F.equations "explicit type argument") : Except String _)
  let G := StoreView.graph F.store
  let [i] := S | throw (refuse "explicit type arguments need a generic member")
  let some s := G.schemes i | throw (refuse "explicit type arguments need a generic member")
  let [.arrs L Ms] := PositiveRules.expand G M
    | throw (refuse "the call's claimed method is not an instance of its member")
  let images := StoreView.images F.store
  let candidates := CertificateProducer.instanceCandidates G images.sub 64 s L Ms
  let c ← match PositiveCertificates.selectInstancesUsing G images S M candidates
      (CertificateProducer.instantiationUsing G images CertificateProducer.instanceFuel)
      (CertificateProducer.rowInstances G images CertificateProducer.instanceFuel) with
    | .established (c, _) => pure c
    | .notEstablished => throw (refuse "the call's claimed method is not an instance of its member")
    | .exhausted rounds visited => throw (subtypeFailure T pos .schemeElimination
        (S.map Subtype.val) (M.map Subtype.val)
        (.exhausted T.subtypeBudget.rounds rounds visited) "subtype search exhausted while checking the method instance")
  for (A, θ) in args.zip c.instances do
    for (X, Y) in [(A, θ), (θ, A)] do
      match CertificateProducer.comparisonUsing G images X Y with
      | .established _ => pure ()
      | .notEstablished => throw (subtypeFailure T pos .schemeElimination
          (X.map Subtype.val) (Y.map Subtype.val) .notEstablished
          "the call's instance is not the one its explicit type arguments state")
      | .exhausted rounds visited => throw (subtypeFailure T pos .schemeElimination
          (X.map Subtype.val) (Y.map Subtype.val)
          (.exhausted T.subtypeBudget.rounds rounds visited) "subtype search exhausted while checking the explicit type argument")

/-- A plan at a meet row, a bounded binder read as its row met with its bound,
cast to the bound: the row holding exactly the meet's clauses, which the meet
is below (`PositiveRules.meetSources`). A member read through the binder reads
the bound's member. Any other plan is itself. -/
@[nospecialize] def throughBound (Γ : List (Ty Tree)) (a : DirectProof.Plan Tree) : Compiler (DirectProof.Plan Tree) := do
  let T ← table
  let [l] := a.type | return a
  let .meet _ cs _ := StoreView.row T l | return a
  let m ← lower (SourceTypes.useRow cs)
  recordHints [m]
  return DirectProof.cast Γ [m] a

/-- `length` through a view (`lenView`): the view admits an array, whose
`length` is its store's, so the read tests the receiver, held in a slot. -/
@[nospecialize] def lengthView (G : PositiveGraphs.NormalGraph Tree) (Γ : List (Ty Tree))
    (a : DirectProof.Plan Tree) (B : Ty Tree) : Compiler (DirectProof.Plan Tree) := do
  if !PositiveRules.numIn G B then
    throw "a read of `length` through a view whose type neither holds every number nor excludes one: the view may admit an array, whose `length` is its store's"
  match a.term with
  | .var i => pure (DirectProof.node Γ (lengthRead i) B (.lenView i) [])
  | _ => pure (DirectProof.letE Γ a (DirectProof.node (a.type :: Γ) (lengthRead 0) B (.lenView 0) []))

/-- Read a field from a cell plan under context `Γ`: one contract, a callable
bag, or an explicit union of cell contracts each naming the field. -/
@[nospecialize] partial def readCell (G : PositiveGraphs.NormalGraph Tree) (Γ : List (Ty Tree)) (fld : PropKey)
    (a : DirectProof.Plan Tree) : Compiler (DirectProof.Plan Tree) := do
  match PositiveRules.expand G a.type with
  | [.refs fs [] vs os _ ks] =>
    -- An invariant field reads at its contract; a readonly view at its bound;
    -- an optional field at its type or `undefined` (`readOptional`); a key a
    -- bound of the object does not admit at its prototype's field or view
    -- (`readProto`), as at the top level.
    match fs.lookup fld, vs.lookup fld, (os.find? (·.key == fld)).map (·.type) with
    | some B, _, _ => pure (DirectProof.node Γ (.readAt fld a.term) B .read [a])
    | none, some B, _ =>
      if fld == lengthKey && !lengthExcluded G B then lengthView G Γ a B
      else pure (DirectProof.node Γ (.readAt fld a.term) B .readView [a])
    | none, none, some E => pure (DirectProof.node Γ (.readAt fld a.term) (E ++ [Labels.undef]) (.readOptional E [Labels.undef]) [a])
    | none, none, none =>
      let inherited : Option (Ty Tree × Ty Tree) := do
        if !ks.any (fun K => !K.admits fld) then none
        let P ← (fs ++ vs).lookup SourceTypes.protoField
        let [.refs gs [] ws _ _ _] := PositiveRules.expand G P | none
        let B ← (gs ++ ws.filter (·.1 != lengthKey)).lookup fld
        pure (P, B)
      let some (P, B) := inherited | throw s!"read of a field '{fld}' the contract does not name"
      pure (DirectProof.node Γ (.readAt fld a.term) B (.readProto P) [a])
  | [.dict fs [] vs ix [] [] [] _] =>
    -- A named field or view, else an index whose class surely admits the
    -- key, which may miss.
    match fs.lookup fld, vs.lookup fld with
    | some B, _ => pure (DirectProof.node Γ (.readAt fld a.term) B .read [a])
    | none, some B =>
      if fld == lengthKey && !lengthExcluded G B then lengthView G Γ a B
      else pure (DirectProof.node Γ (.readAt fld a.term) B .readView [a])
    | none, none =>
      let some (K, B) := (PositiveNormalization.numericFirst ix).find? (fun (K, _) => K.surely fld)
        | throw s!"read of a key '{fld}' no index of the object constrains"
      pure (DirectProof.node Γ (.readAt fld a.term) (B ++ [Labels.undef]) (.readDict K B [Labels.undef]) [a])
  | [.callable fs _ _ _] =>
    let some B := fs.lookup fld | throw s!"read of a field '{fld}' the contract does not name"
    pure (DirectProof.node Γ (.readAt fld a.term) B .readCallable [a])
  -- A class value's static field, or its readonly view.
  | [.ctors _ _ fs _ vs] =>
    match fs.lookup fld, vs.lookup fld with
    | some B, _ => pure (DirectProof.node Γ (.readAt fld a.term) B .readCallable [a])
    | none, some B => pure (DirectProof.node Γ (.readAt fld a.term) B .readBagView [a])
    | none, none => throw s!"read of a field '{fld}' the contract does not name"
  | _ =>
    -- A union reads each alternative as that alternative reads, at the
    -- union of what they read.
    if a.type.length ≤ 1 then throw "read receiver must name a cell contract"
    let alternatives ← a.type.mapM fun label => do
      let H := [label] :: Γ
      pure (label, ← readCell G H fld (DirectProof.var H 0 [label]))
    let R := (alternatives.flatMap (·.2.type)).eraseDups
    let children := alternatives.map fun (label,plan) =>
      DirectProof.cast ([label] :: Γ) R plan
    pure (DirectProof.letE Γ a (DirectProof.node (a.type::Γ)
      (.readAt fld (.var 0)) R (.unionVar 0) children))

/-- How a member read reaches a primitive of one shape: a string's own
`length`, or the member of its wrapper's prototype, held in slot `proto` at
`P`, through a fresh wrapper of type `R` owning only its `[[proto]]` key. -/
inductive PrimitiveArm (ι : Type) where
  | length
  | proto (proto : Nat) (P R : Ty ι)

/-- The shapes a member read of `O` dispatches on: each primitive shape among
`O`'s clauses, with the arm that reads it (`ToObject`'s wrapper, whose
prototype is the built-ins'). An object shape needs none. -/
@[nospecialize] def primitiveArms (scope : List (ScopeBinding Tree)) (K : List (Ty Tree)) (O : Ty Tree)
    (fld : PropKey) : Compiler (List (Tag × (PrimitiveArm Tree))) := do
  let G := SourceTypes.graph (← table)
  let shapeOf (c : PositiveNormalization.Clause (Ty Tree)) : Option Tag := match c with
    | .str | .strLit _ => some .isStr
    | .num | .numLit _ => some .isNum
    | .bigint | .bigintLit _ => some .isBigint
    | .bool | .boolLit _ => some .isBool
    | _ => none
  let shapes := SourceTypes.primitivePrototypes.filter fun (tag, _) =>
    (PositiveRules.expand G O).any (shapeOf · == some tag)
  shapes.mapM fun (tag, name) => do
    if tag == .isStr && fld == "length" then return (tag, .length)
    let some (p, .value) := resolve scope name
      | throw s!"a member of a primitive is read from {name}, which this unit does not see"
    let some P := K[p]? | throw "internal prototype slot mismatch"
    let R ← lower (SourceTypes.use (.refs [(SourceTypes.protoField, P)] [] [] [] []
      [⟨true, [SourceTypes.protoField]⟩]))
    recordHints [R]
    return (tag, .proto p P [R])

/-- One arm's read of slot `o`. -/
@[nospecialize] private def PrimitiveArm.term (fld : PropKey) (o : Nat) : PrimitiveArm ι → Tm
  | .length => .lenOf (.var o)
  | .proto p _ _ => .readAt fld (.makeAt .absent [SourceTypes.protoField] [.var p])

/-- `x.k` with `x` in slot `o` of a type with primitive shapes: a test of each
shape selecting its arm, then the object read. Each arm is JavaScript's read
for values of its shape, and the object read is its read for an object; a
value of a shape no arm names reaches the object read, where a primitive is
stuck, never misread. -/
@[nospecialize] def dispatchTerm (arms : List (Tag × (PrimitiveArm ι))) (fld : PropKey) (o : Nat) (object : Tm) : Tm :=
  arms.foldr (fun (tag, arm) rest => .ite (.test tag (.var o)) (arm.term fld o) rest) object

/-- `x.k(a…)` with `x` in slot `o` of a union type and the actuals `args`
already evaluated: per shape of `x`, as `dispatchTerm` reads it, the member
that shape reads, invoked with `x` as its receiver. An object's member is
bound to it (`memberHead`) where every object alternative holds `k` as a
member, and read as a field otherwise. -/
@[nospecialize] def dispatchCallTerm (G : PositiveGraphs.NormalGraph ι) (O : Ty ι)
    (arms : List (Tag × (PrimitiveArm ι))) (fld : PropKey) (o : Nat) (args : List Tm) : Tm :=
  let objects := O.filter fun l => arms.all fun (tag, _) => !decide (Answers G [l] tag true)
  let member := !objects.isEmpty &&
    objects.all fun l => (ProgramTyping.memberOf G [l] fld).isSome
  let object := if member
    then Tm.letE (.readAt fld (.var o)) (.makeAt (.bound (.var 0) (.var (o + 1)) []) [] [])
    else .readAt fld (.var o)
  arms.foldr (fun (tag, arm) rest =>
    .ite (.test tag (.var o)) (.invoke (arm.term fld o) (.var o) args) rest)
    (.invoke object (.var o) args)

/-- The member read of slot `o` of `K` at `A`, planned per label of the slot:
a primitive's label selects its arm by its known shape answers, and any other
is read as an object (`readCell`). -/
@[nospecialize] def memberReadPlan (G : PositiveGraphs.NormalGraph Tree) (K : List (Ty Tree)) (o : Nat)
    (fld : PropKey) (A : Ty Tree) (arms : List (Tag × (PrimitiveArm Tree))) : Compiler (DirectProof.Plan Tree) := do
  let some O := K[o]? | throw "internal member receiver slot mismatch"
  let N : Ty Tree := [← lower (SourceTypes.use .num)]
  let armPlan (L : List (Ty Tree)) (label : Tree) : PrimitiveArm Tree → Except String (DirectProof.Plan Tree)
    | .length => pure (DirectProof.node L (.lenOf (.var o)) N .lenStr [DirectProof.var L o [label]])
    | .proto p P R => do
      let [.refs gs [] ws _ _ _] := PositiveRules.expand G P
        | throw "a primitive's prototype contract must be a record"
      let some B := (gs ++ ws.filter (·.1 != lengthKey)).lookup fld
        | throw s!"read of a member '{fld}' the primitive's prototype contract does not name"
      let wrapper := DirectProof.node L (.makeAt .absent [SourceTypes.protoField] [.var p]) R .alloc
        [DirectProof.var L p P]
      pure (DirectProof.node L (.readAt fld wrapper.term) B (.readProto P) [wrapper])
  let object := Tm.readAt fld (.var o)
  let rec chain (L : List (Ty Tree)) (label : Tree) :
      List (Tag × (PrimitiveArm Tree)) → Compiler (DirectProof.Plan Tree)
    | [] => do return DirectProof.cast L A (← readCell G L fld (DirectProof.var L o [label]))
    | (tag, arm) :: rest => do
      let term := dispatchTerm ((tag, arm) :: rest) fld o object
      if decide (Answers G [label] tag true) then
        return DirectProof.node L term A .ifTrue [DirectProof.cast L A (← armPlan L label arm)]
      else if decide (Answers G [label] tag false) then
        return DirectProof.node L term A .ifFalse [← chain L label rest]
      else throw "a member read's receiver needs labels of one shape each"
  let children ← O.mapM fun label => chain (K.set o [label]) label arms
  return DirectProof.node K (dispatchTerm arms fld o object) A (.unionVar o) children

/-- The write node under context `H`, with the value in slot 0 and the
receiver, claimed at `B`, in slot `ri`. -/
@[nospecialize] def writeCell (G : PositiveGraphs.NormalGraph Tree) (H : List (Ty Tree)) (fld : PropKey)
    (B C : Ty Tree) (ri : Nat) : Compiler (DirectProof.Plan Tree) := do
  let term := Tm.writeAt fld (.var ri) (.var 0)
  match PositiveRules.expand G B with
  | [.refs fs [] vs [] _ _] =>
    let some D := fs.lookup fld
      | throw (if (vs.lookup fld).isSome then s!"write to a readonly field '{fld}'"
          else s!"write to a field '{fld}' the contract does not name")
    pure (DirectProof.node H term [Labels.nul] .write
      [DirectProof.var H ri B,DirectProof.cast H D (DirectProof.var H 0 C)])
  | _ =>
    if B.length ≤ 1 then throw "write receiver must name a cell contract"
    let alternatives ← B.mapM fun label => do
      let [.refs fs [] [] [] _ _] := PositiveRules.expand G [label]
        | throw "every write alternative must name a cell contract"
      let some D := fs.lookup fld
        | throw s!"write to a field '{fld}' an alternative does not name"
      pure (label,D)
    let children := alternatives.map fun (label,D) =>
      let branch := H.set ri [label]
      DirectProof.node branch term [Labels.nul] .write
        [DirectProof.var branch ri [label],DirectProof.cast branch D (DirectProof.var branch 0 C)]
    pure (DirectProof.node H term [Labels.nul] (.unionVar ri) children)

/-- Whether a write of `fld` to an object of type `B` may add the key: some
plain-object clause states it neither as a field, a view nor a method, and
none as a readonly optional field or a persistent forbidden own key. A copy
may extend a fresh object's finite allowed-key bound. The ordinary write
obligation checks writes at a forbidden key against the retained bound. -/
@[nospecialize] private def mayLack (G : PositiveGraphs.NormalGraph ι) (B : Ty ι) (fld : PropKey) : Bool :=
  let cs := PositiveRules.expand G B
  let optionalView := fun (os : List (OptionalField (Ty ι))) => os.any fun o => o.key == fld && o.readonly
  cs.any (fun c => match c with
    | .refs fs rs vs _ ms _ | .dict fs rs vs _ _ ms _ _ =>
      !((fs :: rs).flatten ++ vs).any (·.1 == fld) && !ms.any (·.key == fld)
    | _ => false) &&
  !cs.any fun c => match c with
    | .refs _ _ _ os _ ks | .dict _ _ _ _ os _ ks _ =>
      optionalView os || ks.any (fun K => !K.among && !K.admits fld)
    | _ => false

/-- Whether no value of a type owns `__proto__`: `Object.assign` sets a
source's `__proto__` on its target through the prototype's setter, which
replaces the prototype rather than adds the key a copy would. Each clause
gives no key (`srcOf`), or a key bound excludes it. -/
@[nospecialize] def ownsNoProto (G : PositiveGraphs.NormalGraph ι) (S : Ty ι) : Bool :=
  (PositiveRules.expand G S).all fun c => match ObjectMerge.srcOf c with
    | some sb => sb.never [] (.str "__proto__")
    | none => false

/-- The bindings in scope holding the object of the key-adding write site at
`span` whose receiver is `n` (`growSites`): each holder's slot and storage,
found by its name and declaring statement. `none` where the write is no site
or `n` is no holder in scope. A holder out of scope holds nothing code can
reach; one in scope that its name does not resolve to is refused. -/
@[nospecialize] def ownedSlots (scope : List (ScopeBinding Tree)) (span : Span) (n : String) :
    Compiler (Option (List (Nat × Storage Tree))) := do
  let some holders ← growthHolders span | return none
  let declares := fun (h : Holder) (b : ScopeBinding Tree) =>
    b.source == ({ name := h.1, span := some h.2 } : RequestJson.Descriptor)
  let bound : Holder → Option (Nat × Storage Tree) := fun h => match resolve scope h.1 with
    | some (i, storage) => if scope[i]?.any (declares h) then some (i, storage) else none
    | none => none
  if (holders.filter (·.1 == n)).all fun h => (bound h).isNone then return none
  let slots ← holders.foldlM (init := ([] : List (Nat × Storage Tree))) fun slots h => do
    match bound h with
    | some slot => pure (slots ++ [slot])
    | none =>
      if scope.any (declares h) then
        throw s!"internal extraction error: the holder '{h.1}' of an owned object is in scope under another binding of its name"
      pure slots
  return some slots

/-- A write statement that adds a key: `o.k = e` or `o["k"] = e` whose
receiver's claimed type may lack `k`. On a holder of an owned object
(`growSites`) it is the copy of the object with the key, rebound to every
holder's slot or cell, returned with the parts the write evaluates; any other
such write is refused, since another reference may hold the object and see
its keys change. -/
@[nospecialize] def growingWrite (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree)) (e : Fragment.Expr) :
    Compiler (Option (List (Nat × Storage Tree) × Fragment.Expr × PropKey × Option Fragment.Expr × Fragment.Expr)) := do
  let (receiver, fld, key, rhs) ← match e with
    | .write _ fld receiver rhs => pure (receiver, fld, none, rhs)
    | .indexWrite _ (some s) receiver key rhs => pure (receiver, PropKey.str s, some key, rhs)
    | .indexWrite _ none receiver key rhs => do
      let resolved ← comparisonsExpr fc key
      match ← keyField fc resolved (record := ← recordReceiver fc receiver)
          (dict := ← dictReceiver fc receiver) with
      | .field s => pure (receiver, PropKey.str s, some key, rhs)
      | _ => return none
    | _ => return none
  let G := SourceTypes.graph (← table)
  if !mayLack G (← exprType fc receiver) fld then return none
  let owned ← match receiver with
    | .var _ n => ownedSlots scope e.span n
    | _ => pure none
  let some slots := owned
    | if let .var _ n := receiver then
        if let some (i, _) := resolve scope n then
          if scope[i]?.any (·.param) then
            throw (locatedRefusal (← table) e.span .expressionClaim (parameterGrowth s!"a write of \
              '{fld}', a key the object's type does not state," n))
      throw (locatedRefusal (← table) e.span .expressionClaim
        s!"a write of '{fld}', a key the object's type does not state, may add it to an object \
          another reference holds, which would see the object's keys change: a key-adding write \
          is typed only on a local's own fresh object that nothing else has reached (not passed, \
          stored, captured, returned or bound to a binding other than a constant), outside any \
          loop its allocation does not enclose")
  if fld == .str "__proto__" then
    throw (locatedRefusal (← table) e.span .expressionClaim
      "a write of `__proto__` runs the prototype's setter: it replaces the prototype, and adds no key")
  return some (slots, receiver, fld, key, rhs)

/-- The object an allocation at a key of claim `K`, holding a value of `W`,
is of: per clause of `K`, the one field a singleton names or the dictionary
over a family's class (`ComputedKey.keyedClause`). -/
@[nospecialize] def keyedType (K W : Ty Tree) : Compiler (Ty Tree) := do
  let G := SourceTypes.graph (← table)
  let mut labels : List Tree := []
  for c in PositiveRules.expand G K do
    let some d := ComputedKey.keyedClause c W
      | throw "an allocation at a key known only at run time needs a key of strings, numbers or symbols"
    labels := labels ++ [← lower (SourceTypes.use d)]
  recordHints labels
  return labels.eraseDups

/-- A write statement at a key known only at run time on a record or a
dictionary: `o[k] = e` whose key's claim is no one key the source spells
(`computedKeyClaim`). On a holder of an owned object (`growSites`) it is the
copy of the object with an allocation at the key, rebound to every holder's
slot or cell, returned with the parts the write evaluates; through a
parameter it is refused on principle, and any other is refused, since another
reference may hold the object and see its keys change. -/
@[nospecialize] def computedGrowth (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree))
    (e : Fragment.Expr) :
    Compiler (Option (List (Nat × Storage Tree) × Fragment.Expr × Fragment.Expr × Fragment.Expr)) := do
  let .indexWrite p none receiver key rhs := e | return none
  if !(← recordReceiver fc receiver) then return none
  let G := SourceTypes.graph (← table)
  if !computedKeyClaim G (← exprType fc (← comparisonsExpr fc key)) then return none
  let owned ← match receiver with
    | .var _ n => ownedSlots scope p n
    | _ => pure none
  let some slots := owned
    | if let .var _ n := receiver then
        if let some (i, _) := resolve scope n then
          if scope[i]?.any (·.param) then
            throw (locatedRefusal (← table) p .expressionClaim
              (parameterGrowth "a write at a key known only at run time" n))
      throw (locatedRefusal (← table) p .expressionClaim
        "a write at a key known only at run time may add the key to an object another reference holds, which would see the object's keys change: a key-adding write is typed only on a local's own fresh object that nothing else has reached")
  return some (slots, receiver, key, rhs)

/-- The element at literal index `b` of the array `r` reads under `H`, from
its store: a required position at its type, an optional or rest position at
its type or `undefined`. -/
@[nospecialize] def elemReadPlan (G : PositiveGraphs.NormalGraph Tree) (H : List (Ty Tree))
    (r : DirectProof.Plan Tree) (b : UInt64) : Compiler (DirectProof.Plan Tree) := do
  let I : Ty Tree := [← lower (SourceTypes.use (.numLit b))]
  let store ← readCell G H SourceTypes.storeField r
  let [.list T []] := PositiveRules.expand G store.type | throw "an element read needs an array"
  let U : Ty Tree := [Labels.undef]
  let (E, rule) ← match ProgramCertificates.requiredAt T b, ProgramCertificates.optionalAt T b U with
    | some E, _ => pure (E, ProgramCertificates.Rule.elem)
    | none, some E => pure (E, .elemOpt U)
    | none, none => throw "an element read at an index no contract names"
  pure (DirectProof.node H (.elemAt store.term (.num b)) E rule [store, DirectProof.node H (.num b) I .numLit])


end
end Verification.SourceExtraction
