import Verification.Source.LoweringClosures
import Verification.Source.LoweringPlans

namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

namespace LoweringExpression

set_option maxHeartbeats 1000000

/-- A write of a slot binding inside term code: the term has no edge to
rebind the slot on, so later reads in the same term would see the old value. -/
@[nospecialize] def slotWriteRefusal (scope : List (ScopeBinding Tree)) (name : String) (pos : Span) :
    Compiler String := do
  match resolve scope name with
  | some (_, .slot _) =>
    let T ← table
    return locatedRefusal T pos .expressionClaim
      "a write of a local inside an expression compiled as one term (a guard or a closure's term code): the term has no step that rebinds the local's slot"
  | _ => return s!"assignment to '{name}', which is not a mutable local"

/-- Build compositional proofs for lambda bodies and source ternaries without
losing their individual claims. Requirements use the lexical context at the occurrence; synthetic let
slots are introduced only after the operand supplying their type is checked. -/
@[nospecialize] partial def closureExpr (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (e : Fragment.Expr) : Compiler (DirectProof.Plan Tree) := do
  -- `(a && b) && c` is `a && (b && c)`, and `||` likewise: JavaScript
  -- evaluates the operands in the same order and yields the same value either
  -- way, and read so, `c` sees what `a` and `b` answered. The inner operator
  -- is typed at the whole's claim, which covers every value it yields.
  if let .logical p andOp (.logical _ andOp' l1 l2) right := e then
    if andOp' == andOp then
      return ← closureExpr recursive fc scope Γ (.logical p andOp l1 (.logical p andOp l2 right))
  let A ← closureType fc e
  let G := SourceTypes.graph (← table)
  let prepared ← isPreparedAtom e
  if !prepared then
    if let some asserted := fc.exprCurrent.lookup e.span then
      for (fld, R) in asserted do
        match e with
        | .var _ name => observed scope Γ (snapshotName name (← stringKey fld)) ⟨"",some e.span⟩ e.span A fld R
        | _ => persistentObservation ⟨"",some e.span⟩ e.span A fld R
  let p ← match e with
  | .equality .. => throw "internal unresolved equality"
  | .block .. => throw "internal extraction error: statements outside a closure body"
  | .objectAssign .. => throw (locatedRefusal (← table) e.span .expressionClaim
      "Object.assign in a closure's term code is outside the fragment: its copies are graph nodes")
  | .var _ name =>
    match resolve scope name with
    | some (i, .value) | some (i, .slot _) => pure (DirectProof.var Γ i A)
    | some (i, .cell contract reference) =>
      if let some saved := (names scope).idxOf? (localSnapshotName name) then
        let some R := Γ[saved]? | throw "internal saved-local slot mismatch"
        pure (DirectProof.var Γ saved R)
      else
        pure (DirectProof.node Γ (.readAt valueField (.var i)) contract .read [DirectProof.var Γ i reference])
    | none => throw s!"unbound or uninitialized closure variable '{name}'"
  | .nullishAssign pos name namePos rhs =>
    -- The administrative assignment shares the source result claim: either
    -- chosen value must establish it. No synthetic producer fact is added.
    closureExpr recursive fc scope Γ (.coalesce pos (.var namePos name) (.assign pos name namePos rhs))
  | .assign _ name _ rhs => do
    let some (i, .cell contract reference) := resolve scope name
      | throw (← slotWriteRefusal scope name e.span)
    let a ← closureExpr recursive fc scope Γ rhs
    let C := a.type
    let H := C::Γ
    let term := Tm.writeAt valueField (.var (i+1)) (.var 0)
    let write := DirectProof.node H term [Labels.nul] .write
      [DirectProof.var H (i+1) reference, DirectProof.cast H contract (DirectProof.var H 0 C)]
    let done := DirectProof.letE H write (DirectProof.var ([Labels.nul]::H) 1 C)
    pure (DirectProof.letE Γ a done)
  | .lit _ v => do
    let t ← SourceTypes.value v
    let (B,r) ← match t with
      | .nul => pure ([Labels.nul],ProgramCertificates.Rule.nul)
      | .undef => pure ([Labels.undef],ProgramCertificates.Rule.undef)
      | .tru => pure ([Labels.tru],ProgramCertificates.Rule.truLit)
      | .fls => pure ([Labels.fls],ProgramCertificates.Rule.flsLit)
      -- A number has no fixed row: its singleton is interned like any other
      -- clause the program mentions.
      | .num b => do pure ([← lower (SourceTypes.use (.numLit b))],
          ProgramCertificates.Rule.numLit)
      | .str s => do pure ([← lower (SourceTypes.use (.strLit s))],
          ProgramCertificates.Rule.strLit)
      | _ => throw "unsupported closure literal"
    pure (DirectProof.node Γ t B r)
  | .shapeTest p tag equal e => do
    let operand ← closureExpr recursive fc scope Γ e
    inOperand p tag operand.type
    let result ← tagTestPlan G tag (operand.type::Γ) 0 equal A
    pure (DirectProof.letE Γ operand result)
  | .singletonTest _ tag equal testLeft left right => do
    let leftSpan := left.span
    let left ← closureExpr recursive fc scope Γ left
    let right ← closureExpr recursive fc (held ⟨"",some leftSpan⟩ :: scope) (left.type::Γ) right
    let H := right.type::left.type::Γ
    let result ← tagTestPlan G tag H (if testLeft then 1 else 0) equal A
    pure (DirectProof.letE Γ left (DirectProof.letE (left.type::Γ) right result))
  | .logical _ andOp left right => do
    let l ← closureExpr recursive fc scope Γ left
    let R ← byClause l.type
    let l := DirectProof.cast Γ R l
    let G := SourceTypes.graph (← table)
    if BranchRefinement.onlyBoolean G l.type then
      -- A Boolean's falsy value is `false` and its truthy one `true`, so the
      -- short-circuit arm is that constant, and the operator is a condition.
      let constant := fun (_ : List (ScopeBinding Tree)) H => pure
        (if andOp then DirectProof.node H .fls [Labels.fls] .flsLit
         else DirectProof.node H .tru [Labels.tru] .truLit)
      let rhs := fun ds types => closureExpr recursive fc ds types right
      conditionalPlan scope Γ A left l
        (if andOp then rhs else constant) (if andOp then constant else rhs)
    else
      -- `a && b` is `let x = a in (x ? b : x)`, and `a || b` is
      -- `let x = a in (x ? x : b)`, on `x`'s truthiness: the right operand
      -- runs where the left is truthy (`&&`) or falsy (`||`), and sees it so.
      let K := l.type :: Γ
      let H := (BranchRefinement.tagSlice G l.type .truthy andOp) :: Γ
      let r ← closureExpr recursive fc (savedOperandScope scope left) H right
      let own := DirectProof.var K 0 A
      pure (DirectProof.letE Γ l
        (← selectPlan G K 0 A .truthy (if andOp then r else own) (if andOp then own else r)))
  | .coalesce _ left right => do
    let l ← closureExpr recursive fc scope Γ left
    let R ← byClause l.type
    let l := DirectProof.cast Γ R l
    let G := SourceTypes.graph (← table)
    let K := l.type :: Γ
    let H := (BranchRefinement.tagSlice G l.type .isNullish true) :: Γ
    let r ← closureExpr recursive fc (savedOperandScope scope left) H right
    pure (DirectProof.letE Γ l (← selectPlan G K 0 A .isNullish r (DirectProof.var K 0 A)))
  | .optional _ mark receiver body => do
    -- `r?.b` is `let x = r in (x == null ? undefined : b)`, with `b` reading
    -- the saved receiver `x` by `chainName`, where it is not nullish: the
    -- shape `??` has with its arms exchanged.
    let r ← closureExpr recursive fc scope Γ receiver
    let R ← byClause r.type
    let r := DirectProof.cast Γ R r
    let G := SourceTypes.graph (← table)
    let K := r.type :: Γ
    let H := (BranchRefinement.tagSlice G r.type .isNullish false) :: Γ
    let b ← closureExpr recursive fc (held ⟨Fragment.chainName,some mark⟩ :: scope) H body
    pure (DirectProof.letE Γ r (← selectPlan G K 0 A .isNullish (DirectProof.node K .undef [Labels.undef] .undef) b))
  | .not _ a => do
    let a ← closureExpr recursive fc scope Γ a
    if BranchRefinement.onlyBoolean G a.type then
      pure (DirectProof.ifE G Γ A a
        (DirectProof.node Γ .fls [Labels.fls] .flsLit) (DirectProof.node Γ .tru [Labels.tru] .truLit))
    else
      -- `!x` of a value that is not a Boolean negates its truthiness.
      let K := a.type :: Γ
      pure (DirectProof.letE Γ a (← selectPlan G K 0 A .truthy
        (DirectProof.node K .fls [Labels.fls] .flsLit) (DirectProof.node K .tru [Labels.tru] .truLit)))
  | .cast _ annot a => do
    -- The value is the operand's; the claim at the cast follows from the
    -- operand's, and an annotation is one more type the operand must meet.
    let B ← exprType fc a
    let p ← closureExpr recursive fc scope Γ a
    if let some ty := annot then
      let T ← lower (Fragment.translate ty)
      let check := DirectProof.var (B::Γ) 0 T
      obligation e.span check.goal (some check) "cast-annotation" (held ⟨"",some a.span⟩ :: scope)
    pure (DirectProof.cast Γ A p)
  | .alloc _ ns es => do
    if es.length != ns.length then throw "allocation initializer count mismatch"
    let ps ← es.mapM fun a => closureExpr recursive fc scope Γ a
    -- A record naming exactly the literal's keys; a key bound, if claimed,
    -- admits every one of them, as the fresh object's own keys are exactly
    -- those. Such a bound is what lets the literal meet a readonly dictionary
    -- or an optional field it leaves out (`CoversKeys`, `CoversOptional`).
    -- Or a dictionary the literal is allocated at directly, each field an
    -- index may admit at exactly that index's type (`HasTyUsing.allocDict`): a
    -- writable index is never met through an own-key bound.
    let clause ← match PositiveRules.expand G A with
      | [.refs B [] [] [] [] ks] => do
        if B.length != ns.length then throw "allocation claim names different fields"
        if !ks.all (fun K => ns.all (fun n => K.admits n)) then
          throw "an allocation's key bound must admit every key it allocates"
        let B ← ns.mapM fun name => do
          let some D := B.lookup name | throw "allocation claim names different fields"
          pure (name,D)
        pure (PositiveNormalization.Clause.refs B [] [] [] [] ks)
      | [.dict B [] [] ix os [] [] cs] => do
        if B.length != ns.length then throw "allocation claim names different fields"
        if ns.contains SourceTypes.protoField then
          throw "a literal allocated at a dictionary holds no prototype"
        let B ← ns.mapM fun name => do
          let some D := B.lookup name | throw "allocation claim names different fields"
          pure (name,D)
        if !B.all (fun f => (ix ++ cs).all fun y => !y.1.may f.1 || f.2 == y.2) then
          throw "a literal allocated at a dictionary holds each field an index admits at that index's type"
        if !os.all (fun o => !ns.contains o.key && cs.all fun y => !y.1.may o.key ||
            o.type == y.2 || (G.plainTy y.2 && (PositiveRules.expand G y.2).isEmpty)) then
          throw "a literal allocated at a dictionary lacks each optional field, at a writable index's type there"
        pure (PositiveNormalization.Clause.dict B [] [] ix os [] [] cs)
      | _ => throw "allocation claim must name a record or dictionary contract"
    let B := match clause with
      | .refs B .. | .dict B .. => B
      | _ => []
    let Ref ← lower (SourceTypes.use clause)
    -- The calculus evaluates these initializers from left to right.
    let casts := (ps.zip (B.map Prod.snd)).map fun (p,D) => DirectProof.cast Γ D p
    pure (DirectProof.node Γ (.makeAt .absent ns (ps.map (·.term))) [Ref] .alloc casts)
  | .build _ ns es => do
    -- A chain of merges from a fresh accumulator: the fields before the
    -- first spread allocated together, each spread copied onto what is
    -- built so far as soon as its operand is evaluated, and each later run
    -- of fields allocated, then copied on too. One nested term evaluates the
    -- parts in source order.
    let merge (a b : DirectProof.Plan Tree) : Compiler (DirectProof.Plan Tree) := do
      let R ← mergeType a.type b.type
      pure (DirectProof.node Γ (.merge [] a.term b.term) R .merge [a, b])
    let claimed ← claimedFields A
    let group (fields : List (String × (DirectProof.Plan Tree))) : Compiler (DirectProof.Plan Tree) := do
      let fields := fields.map fun (k, p) => (k, match claimed.lookup k with
        | some D => DirectProof.cast Γ D p
        | none => p)
      let T ← groupType (fields.map Prod.fst) (fields.map (·.2.type))
      pure (DirectProof.node Γ (.makeAt .absent (fields.map (.str ·.1)) (fields.map (·.2.term))) T .alloc
        (fields.map Prod.snd))
    let mut acc : Option (DirectProof.Plan Tree) := none
    let mut fields : List (String × (DirectProof.Plan Tree)) := []
    for (n, a) in ns.zip es do
      let p ← closureExpr recursive fc scope Γ a
      match n with
      | some k => fields := fields ++ [(k, p)]
      | none =>
        let g ← group fields
        let base ← match acc with
          | none => pure g
          | some x => if fields.isEmpty then pure x else merge x g
        fields := []
        acc := some (← merge base p)
    let some x := acc | throw "internal: an object literal with spreads has none"
    let result ← if fields.isEmpty then pure x else merge x (← group fields)
    pure (DirectProof.cast Γ A result)
  | .read _ fld a => do
    let receiver := a
    let a ← throughBound Γ (← closureExpr recursive fc scope Γ a)
    let snapshot := match receiver with
      | .var _ name => (readSnapshot name fld).bind (names scope).idxOf?
      | _ => none
    if let some i := snapshot then
      let some R := Γ[i]? | throw "internal saved-read slot mismatch"
      pure (DirectProof.var Γ i R)
    else
      let K := a.type :: Γ
      let arms ← primitiveArms (held ⟨"",some receiver.span⟩ :: scope) K a.type fld
      -- An array's `length` is its store's, read as a number, as the graph
      -- reads it.
      if arms.isEmpty && fld == "length" && (storeOf G a.type).isSome then
        let store ← readCell G Γ SourceTypes.storeField a
        let N : Ty Tree := [← lower (SourceTypes.use .num)]
        pure (DirectProof.node Γ (.lenOf store.term) N .len [store])
      else if arms.isEmpty then readCell G Γ fld a
      else pure (DirectProof.letE Γ a (← memberReadPlan G K 0 fld A arms))
  | .index _ (some fld) receiver key => do
    -- The receiver, then the key, then the read: the key's own claim was
    -- resolved to the field, and is checked here like any operand's.
    let r ← throughBound Γ (← closureExpr recursive fc scope Γ receiver)
    let k ← closureExpr recursive fc (held ⟨"",some receiver.span⟩ :: scope) (r.type::Γ) key
    let H := k.type::r.type::Γ
    let arms ← primitiveArms (held ⟨"",some key.span⟩ :: held ⟨"",some receiver.span⟩ :: scope) H r.type fld
    let read ← if arms.isEmpty then readCell G H fld (DirectProof.var H 1 r.type)
      else memberReadPlan G H 1 fld A arms
    pure (DirectProof.letE Γ r (DirectProof.letE (r.type::Γ) k read))
  | .index _ none receiver key => do
    let r ← closureExpr recursive fc scope Γ receiver
    let k ← closureExpr recursive fc (held ⟨"",some receiver.span⟩ :: scope) (r.type::Γ) key
    let G := SourceTypes.graph (← table)
    let [.dict _ [] _ ix [] [] [] _] := PositiveRules.expand G r.type
      | throw "a dynamic index requires a dictionary receiver"
    -- The key's clause names the keys it reaches: a string any string key, a
    -- number a canonical numeric one, a symbol a symbol key. An index over
    -- as many keys reads it.
    let [c] := PositiveRules.expand G k.type
      | throw "a dynamic dictionary key must be a string, a number or a symbol"
    let some KK := [IndexKeys.strings, .numeric, .symbols].find? (PositiveNormalization.keyClause · == c)
      | throw "a dynamic dictionary key must be a string, a number or a symbol"
    let some (K, E) := (ix.find? (·.1 == KK)).orElse fun _ => ix.find? (fun (K, _) => KK.within K)
      | throw "no index of the dictionary constrains the dynamic key's keys"
    let H := k.type::r.type::Γ
    let read := DirectProof.node H (.indexAt (.var 1) (.var 0)) (E ++ [Labels.undef])
      (.indexDict K KK E [Labels.undef]) [DirectProof.var H 1 r.type, DirectProof.var H 0 k.type]
    pure (DirectProof.letE Γ r (DirectProof.letE (r.type::Γ) k read))
  | .indexWrite _ (some fld) receiver key rhs => do
    let B ← exprType fc receiver
    let r ← closureExpr recursive fc scope Γ receiver
    let k ← closureExpr recursive fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key
    let a ← closureExpr recursive fc (held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope) (k.type::B::Γ) rhs
    let H := a.type::k.type::B::Γ
    let write ← writeCell G H fld B a.type 2
    let done := DirectProof.letE H write (DirectProof.var ([Labels.nul]::H) 1 a.type)
    pure (DirectProof.letE Γ r (DirectProof.letE (B::Γ) k (DirectProof.letE (k.type::B::Γ) a done)))
  | .indexWrite _ none .. => throw "internal unresolved computed key"
  | .arith _ op l r => do
    -- The rule checks the operands pair by pair; the result is the family of
    -- its kind, whatever its value.
    let a ← closureExpr recursive fc scope Γ l
    let b ← closureExpr recursive fc (held ⟨"",some l.span⟩ :: scope) (a.type::Γ) r
    let H := a.type::Γ
    let N ← operatorResult op a.type b.type
    pure (DirectProof.letE Γ a
      (DirectProof.node H (.arith op (.var 0) b.term) N .arith [DirectProof.var H 0 a.type, b]))
  | .unary _ .typeof a => do
    -- `typeof a`: the operand once, then one selection per answer
    -- (`typeofTerm`), each arm the answer's string.
    let p ← closureExpr recursive fc scope Γ a
    let K := p.type :: Γ
    let answer := fun (s : String) => do
      let B := [← lower (SourceTypes.use (.strLit s))]
      pure (DirectProof.node K (.str s) B .strLit)
    let chain ← typeofAnswers.foldrM (fun (tag, s) rest => do
      selectPlan G K 0 A tag (DirectProof.cast K A (← answer s)) rest)
      (DirectProof.cast K A (← answer "function"))
    pure (DirectProof.letE Γ p chain)
  | .unary pos op a => do
    let p ← closureExpr recursive fc scope Γ a
    let (arith, c, C, rule) ← unaryOperation pos op p.type
    let H := p.type::Γ
    let N ← operatorResult arith p.type p.type
    pure (DirectProof.letE Γ p
      (DirectProof.node H (.arith arith (.var 0) c) N .arith
        [DirectProof.var H 0 p.type, DirectProof.node H c C rule]))
  | .inKeys p key o => do
    -- The key, then the object, then one selection per singleton of the key.
    let k ← closureExpr recursive fc scope Γ key
    let r ← closureExpr recursive fc (held ⟨"",some key.span⟩ :: scope) (k.type::Γ) o
    inOperand p (.hasKey (.str "")) r.type
    let keys ← inKeyList p k.type
    let H := r.type::k.type::Γ
    let test := fun (s : String) => tagTestPlan G (.hasKey (.str s)) H 0 true A
    let chain ← match keys.reverse with
      | [] => throw "internal: an `in` key without singletons"
      | last :: earlier => do
        earlier.reverse.foldrM (fun s rest => do selectPlan G H 1 A (.strEq s) (← test s) rest) (← test last)
    pure (DirectProof.letE Γ k (DirectProof.letE (k.type::Γ) r chain))
  | .comma _ l r => do
    -- The left operand is bound and never read; the claim at the comma
    -- follows from the right operand's.
    let a ← closureExpr recursive fc scope Γ l
    let b ← closureExpr recursive fc (held ⟨"",some l.span⟩ :: scope) (a.type::Γ) r
    pure (DirectProof.letE Γ a (DirectProof.cast (a.type::Γ) A b))
  | .update pos op (.var _ name) rhs post => do
    -- `x op= r`, `x++` of a local cell, as the statement form does: the
    -- cell's value read at its contract, the right side (the family's one
    -- for an increment), the operation, the write back at the contract, and
    -- the old or new value.
    let some (i, .cell contract reference) := resolve scope name
      | throw (← slotWriteRefusal scope name e.span)
    let targetClauses := PositiveRules.expand G contract
    if rhs.isNone && (targetClauses.isEmpty ||
        !(targetClauses.all ProgramTyping.numberClause || targetClauses.all ProgramTyping.bigintClause)) then
      throw s!"unsupported source expression at [{pos.1},{pos.2}): an increment needs a target of one numeric family, number or bigint"
    let read := DirectProof.node Γ (.readAt valueField (.var i)) contract .read [DirectProof.var Γ i reference]
    let K := contract :: Γ
    let c ← match rhs with
      | some r => closureExpr recursive fc (held ⟨"",some e.span⟩ :: scope) K r
      | none =>
        if !targetClauses.isEmpty && targetClauses.all ProgramTyping.bigintClause then do
          pure (DirectProof.node K (.bigint 1) [← lower (SourceTypes.use (.bigintLit 1))] .bigintLit)
        else do
          let b := (1.0 : Float).toBits
          pure (DirectProof.node K (.num b) [← lower (SourceTypes.use (.numLit b))] .numLit)
    let H := c.type :: K
    let N ← operatorResult op contract c.type
    let combine := DirectProof.node H (.arith op (.var 1) (.var 0)) N .arith
      [DirectProof.var H 1 contract, DirectProof.var H 0 c.type]
    let W := N :: H
    let write := DirectProof.node W (.writeAt valueField (.var (i+3)) (.var 0)) [Labels.nul] .write
      [DirectProof.var W (i+3) reference, DirectProof.cast W contract (DirectProof.var W 0 N)]
    let done := DirectProof.letE W write
      (if post then DirectProof.var ([Labels.nul]::W) 3 contract else DirectProof.var ([Labels.nul]::W) 1 N)
    pure (DirectProof.letE Γ read (DirectProof.letE K c (DirectProof.letE H combine done)))
  | .update .. => throw "compound assignment of other than a local inside a closed expression is outside the fragment"
  | .arrayLit _ elems spreads => do
    -- Reading a spread operand's elements is an array operation, which a
    -- closed expression does not have.
    if !spreads.isEmpty then throw "an array literal spread inside a closed expression is outside the fragment"
    -- The elements, in order, fill a fresh store, and the array object holds
    -- it with the prototype from its slot, then reads as the claimed array.
    let some S := storeOf G A | throw "an array literal needs an array claim"
    let [.list T []] := PositiveRules.expand G S | throw "an array literal needs one tuple contract"
    let proto ← prototypeSlot scope
    let some P := Γ[proto]? | throw "internal prototype slot mismatch"
    let ps ← elems.mapM fun a => closureExpr recursive fc scope Γ a
    let casts ← ps.zipIdx.mapM fun (p, i) => do
      let some D := ProgramTyping.positionTy T i | throw "an array literal has more elements than its claim"
      pure (DirectProof.cast Γ D p)
    let store := DirectProof.node Γ (.arrLit (ps.map (·.term))) S .arrLit casts
    let O ← arrayObject S
    let object := DirectProof.node Γ (.makeAt .absent [SourceTypes.storeField, SourceTypes.protoField]
      [store.term, .var proto]) O .alloc [store, DirectProof.var Γ proto P]
    pure (DirectProof.cast Γ A object)
  | .elemAt _ receiver key => do
    -- The receiver, then the key, both saved; the element is read from the
    -- receiver's store at the key's one index, or a string's code unit at
    -- the key's number.
    let r ← closureExpr recursive fc scope Γ receiver
    let k ← closureExpr recursive fc (held ⟨"",some receiver.span⟩ :: scope) (r.type::Γ) key
    let H := k.type::r.type::Γ
    if decide (Answers G r.type .isStr true) then
      let T : Ty Tree := [← lower (SourceTypes.use .str)]
      let read := DirectProof.node H (.elemAt (.var 1) (.var 0)) (T ++ [Labels.undef]) (.elemStr T [Labels.undef])
        [DirectProof.var H 1 r.type, DirectProof.var H 0 k.type]
      return DirectProof.letE Γ r (DirectProof.letE (r.type::Γ) k (DirectProof.cast H A read))
    let index ← arrayKeyTerm k.type
    let .num b := index | throw "internal array index term"
    let read ← elemReadPlan G H (DirectProof.var H 1 r.type) b
    pure (DirectProof.letE Γ r (DirectProof.letE (r.type::Γ) k (DirectProof.cast H A read)))
  | .elemWrite .. | .arrayAssign .. => throw "array writes inside a closed expression are outside the fragment"
  | .logicalAssign pos .nullish (.var np name) rhs =>
    closureExpr recursive fc scope Γ (.nullishAssign pos name np rhs)
  | .logicalAssign .. => throw "logical assignment inside a closed expression is outside the fragment"
  | .bindWithReceiver _ f receiver args => do
    if let some (.bindWithReceiver _ (.read _ fld (.var _ x)) (.var _ y) []) :=
        (← originalExpression) then
      if x == y && args.isEmpty &&
          (ProgramTyping.memberOf G (← exprType fc receiver) fld).isSome then
        -- The shared method-read operation has already bound this member
        -- to the same receiver. Its saved result is the bound function.
        return DirectProof.cast Γ A (← closureExpr recursive fc scope Γ f)
    -- `o.m.bind(o)` of a method member of `o`: the member read from the
    -- object, bound to that same object, is JavaScript's bound function
    -- calling what `o.m` held with `o` (`bindMember`), however it is later
    -- called. The object, then the member, are each read once; the second
    -- read of `o`, the receiver, has no effect.
    if let (.read _ fld o@(.var _ x), .var _ y, []) := (f, receiver, args) then
      if x == y && (ProgramTyping.memberOf G (← exprType fc o) fld).isSome then
        let r ← closureExpr recursive fc scope Γ o
        let _ ← closureExpr recursive fc scope Γ receiver
        let K := r.type :: Γ
        let ds := held ⟨"",some o.span⟩ :: scope
        let M ← exprType fc f
        let method := DirectProof.node K (memberHead G r.type fld (.var 0)) M (.bindMember [] [] []) []
        obligation f.span method.goal (some method) "expression-claim" ds
        return DirectProof.letE Γ r
          (DirectProof.node K (memberHead G r.type fld (.var 0)) A (.bindMember [] [] []) [])
    -- The target, the receiver and the prefix, each evaluated once and saved,
    -- then a forwarding descriptor holding the saved values: invoking it
    -- ignores its own receiver and calls the target with the saved one and the
    -- prefix before the new actuals (`CallCode.bound`).
    let callee ← closureExpr recursive fc scope Γ f
    let receiverPlan ← closureExpr recursive fc (held ⟨"",some f.span⟩ :: scope) (callee.type::Γ) receiver
    let startScope := held ⟨"",some receiver.span⟩::held ⟨"",some f.span⟩ :: scope
    let (plans,K,_) ← args.attach.foldlM (fun (ps,H,ds) ⟨arg,_⟩ => do
      let p ← closureExpr recursive fc ds H arg
      pure (ps ++ [p],p.type::H,held ⟨"",some arg.span⟩ :: ds))
      ([callee,receiverPlan],receiverPlan.type::callee.type::Γ,startScope)
    let G := SourceTypes.graph (← table)
    let n := args.length
    let boundTypes := (plans.drop 2).map (·.type)
    -- A fixed signature of the target leaves a fixed signature; a variadic one
    -- with an element rest leaves the positions the prefix did not take, then
    -- its rest, the prefix's positions past the fixed ones at the element.
    let (Rt, prefixTys, own, rule) ← match PositiveRules.expand G A with
      | [.arrs [⟨Rb,Ds,_,_⟩] []] => do
        let L ← match PositiveRules.expand G callee.type with
          | [.arrs L _] | [.callable _ _ L _] => pure L
          | _ => throw "bind target requires a single callable contract"
        let ⟨Rt,domains,result,effect⟩ ← selectSignature G L (boundTypes ++ Ds) receiverPlan.type
        if domains.length < n then throw "bind prefix exceeds the target's parameters"
        let own ← lower (SourceTypes.use (.arrs [⟨Rb, domains.drop n, result, effect⟩] []))
        pure (Rt, domains.take n, own, ProgramCertificates.Rule.bindE)
      | [.arrs [] [⟨Rb,_,_,_⟩]] => do
        let sigs := ProgramTyping.restSigs G callee.type
        let some ⟨Rt, (Ps, E), R, effect⟩ := (sigs.find? fun sig => receiverPlan.type.all sig.receiver.contains) <|> sigs.head?
          | throw "a variadic bound function needs a variadic target"
        let some El := PositiveRules.restElem G E
          | throw "a variadic bound function needs an element rest"
        let own ← lower (SourceTypes.use (.arrs [] [⟨Rb, (Ps.drop n, E), R, effect⟩]))
        pure (Rt, Ps.take n ++ List.replicate (n - Ps.length) El, own, ProgramCertificates.Rule.bindRestE)
      | _ => throw "bound function claim requires one free signature"
    -- The descriptor stores the slots as they are, so each is re-bound at the
    -- contract the selected signature gives it: the receiver, then the prefix.
    let receiverCopy := DirectProof.cast K Rt (DirectProof.var K n receiverPlan.type)
    let (copies, H) ← (List.range n).foldlM (fun (cs, H) i => do
      let some D := prefixTys[i]? | throw "internal bind prefix mismatch"
      let some B := boundTypes[i]? | throw "internal bind prefix mismatch"
      let c := DirectProof.cast H D (DirectProof.var H (n - 1 - i + cs.length) B)
      pure (cs ++ [c], D :: H))
      ([receiverCopy], Rt :: K)
    let bound := DirectProof.node H
      (.makeAt (.bound (.var (2*n+2)) (.var n) ((List.range n).map fun i => .var (n-1-i))) [] [])
      [own] rule []
    pure (saveOperands (plans ++ copies) (DirectProof.cast H A bound))
  | .applyWithReceiver _ f receiver list => do
    -- The target, the receiver and the list, saved in order. A null or
    -- undefined list gives no actuals; reading an array's elements is an array
    -- operation, which a closed expression does not have.
    let callee ← closureExpr recursive fc scope Γ f
    let K := callee.type :: Γ
    let receiverPlan ← closureExpr recursive fc (held ⟨"",some f.span⟩ :: scope) K receiver
    let H := receiverPlan.type :: K
    let ds := held ⟨"",some receiver.span⟩::held ⟨"",some f.span⟩ :: scope
    let (saved, J, dsJ) ← match list with
      | none => pure ([], H, ds)
      | some xs => do
        let lp ← closureExpr recursive fc ds H xs
        if !nullishList G lp.type then
          throw "an array argument list inside a closed expression is outside the fragment"
        pure ([lp], lp.type :: H, held ⟨"",some xs.span⟩ :: ds)
    let m := saved.length
    let L ← match PositiveRules.expand G callee.type with
      | [.arrs L _] | [.callable _ _ L _] => pure L
      | _ => throw ".apply target requires a single callable contract"
    let ⟨Rt,Ds,R,effect⟩ ← selectSignature G L [] receiverPlan.type
    let receiverCheck := DirectProof.cast J Rt (DirectProof.var J m receiverPlan.type)
    obligation receiver.span receiverCheck.goal (some receiverCheck) "method-receiver" dsJ
    let rule := match PositiveRules.expand G callee.type with
      | [.callable ..] => ProgramCertificates.Rule.callCallable
      | _ => .app
    let call := DirectProof.node J (.invoke (.var (m+1)) (.var m) []) R (rule effect)
      (DirectProof.var J (m+1) callee.type :: receiverCheck :: omittedPremises J Ds 0)
    pure (saveOperands ([callee, receiverPlan] ++ saved) call)
  | .callWithReceiver _ f receiver args => do
    let callee ← closureExpr recursive fc scope Γ f
    let K := callee.type :: Γ
    let receiverPlan ← closureExpr recursive fc (held ⟨"",some f.span⟩ :: scope) K receiver
    let H := receiverPlan.type :: K
    let ds := held ⟨"",some receiver.span⟩::held ⟨"",some f.span⟩ :: scope
    let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr recursive fc ds H a
    let L ← match PositiveRules.expand G callee.type with
      | [.arrs L _] | [.callable _ _ L _] => pure L
      | _ => throw ".call target requires a single callable contract"
    let ⟨Rt,Ds,R,effect⟩ ← selectSignature G L (actuals.map (·.type)) receiverPlan.type
    let rule := match PositiveRules.expand G callee.type with
      | [.callable ..] => ProgramCertificates.Rule.callCallable
      | _ => .app
    -- `.call` passes its first argument as the receiver.
    let receiverCheck := DirectProof.cast H Rt (DirectProof.var H 0 receiverPlan.type)
    obligation receiver.span receiverCheck.goal (some receiverCheck) "method-receiver" ds
    let call := DirectProof.node H (.invoke (.var 1) (.var 0) (actuals.map (·.term))) R (rule effect)
      (DirectProof.var H 1 callee.type
        :: receiverCheck
        :: ((actuals.zip Ds).map fun (a,D) => DirectProof.cast H D a)
          ++ omittedPremises H Ds actuals.length)
    pure (DirectProof.letE Γ callee (DirectProof.letE K receiverPlan call))
  | .invoke _ callee args spreads typeArgs => do
    -- The object, then a computed key, then the method read from the object,
    -- each saved; the actuals; the saved method invoked with the saved object.
    -- A method the object does not hold, such as an array's, is read from its
    -- prototype (`readCell`, `readProto`) at the member's scheme, and the claim
    -- at the call's instance is below it. An element as the method, or a
    -- spread's store, stays outside a closed expression.
    if !spreads.isEmpty then throw "a spread argument inside a closed expression is outside the fragment"
    let (o, fld, key) ← match callee with
      | .read _ fld o => pure (o, fld, none)
      | .index _ (some fld) o key => pure (o, fld, some key)
      | _ => throw "array operations inside a closed expression are outside the fragment"
    let r ← closureExpr recursive fc scope Γ o
    let K₀ := r.type :: Γ
    let ds₀ := held ⟨"",some o.span⟩ :: scope
    let (saved, K, ds) ← match key with
      | none => pure ([r], K₀, ds₀)
      | some key => do
        let k ← closureExpr recursive fc ds₀ K₀ key
        pure ([r,k], k.type :: K₀, held ⟨"",some key.span⟩ :: ds₀)
    let ri := saved.length - 1
    let M ← exprType fc callee
    explicitInstance e.span r.type M fld typeArgs
    let arms ← primitiveArms ds K r.type fld
    let method ← if (ProgramTyping.memberOf G r.type fld).isSome then
        -- A generic method's member, bound to its host, is its scheme; the
        -- call's claimed instance is below it.
        match ProgramTyping.memberSchemes G r.type fld with
        | S :: _ => pure (DirectProof.cast K M
            (DirectProof.node K (memberHead G r.type fld (.var ri)) S (.bindMember [] [] []) []))
        | [] => pure (DirectProof.node K (memberHead G r.type fld (.var ri)) M (.bindMember [] [] []) [])
      else if !arms.isEmpty then memberReadPlan G K ri fld M arms
      else DirectProof.cast K M <$> readCell G K fld (DirectProof.var K ri r.type)
    obligation callee.span method.goal (some method) "expression-claim" ds
    let H := M :: K
    let dsH := held ⟨"",some callee.span⟩ :: ds
    let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr recursive fc dsH H a
    let fixedFits := match PositiveRules.expand G M with
      | [.arrs L _] | [.callable _ _ L _] => L.any fun p => args.length ≤ p.arguments.length
      | _ => false
    let term := Tm.invoke (.var 0) (.var (ri+1)) (actuals.map (·.term))
    let call ← match PositiveRules.expand G M, ProgramTyping.restSigs G M with
      | _, sigs@(_ :: _) =>
        -- A variadic method: the fixed actuals at its parameters, trailing
        -- ones omitted as `undefined`, every further actual at its position
        -- in the rest.
        if fixedFits then throw "a call both a fixed and a variadic signature take is outside the fragment"
        let some ⟨Rt, (Ps, E), R, effect⟩ := (sigs.find? fun sig => r.type.all sig.receiver.contains) <|> sigs.head?
          | throw "internal variadic signature"
        let receiver := DirectProof.cast H Rt (DirectProof.var H (ri+1) r.type)
        obligation o.span receiver.goal (some receiver) "method-receiver" dsH
        let k := min actuals.length Ps.length
        let extra := actuals.drop k
        let positions ← extra.zipIdx.mapM fun (_, i) => match restPosition G E i with
          | some D => pure D
          | none => throw "an actual past the rest's positions"
        pure (DirectProof.node H term R
          (.callRest effect k (Ps.length - k) (extra.map fun _ => false) E)
          (DirectProof.var H 0 M :: receiver ::
            ((actuals.take k).zip Ps).map (fun (a,D) => DirectProof.cast H D a)
            ++ omittedPremises H Ps k ++ (extra.zip positions).map fun (a,D) => DirectProof.cast H D a))
      | [.arrs L _], [] | [.callable _ _ L _], [] =>
        let ⟨Rt,Ds,R,effect⟩ ← selectSignature G L (actuals.map (·.type)) r.type
        let receiver := DirectProof.cast H Rt (DirectProof.var H (ri+1) r.type)
        obligation o.span receiver.goal (some receiver) "method-receiver" dsH
        let rule := match PositiveRules.expand G M with
          | [.callable ..] => ProgramCertificates.Rule.callCallable
          | _ => .app
        pure (DirectProof.node H term R (rule effect)
          (DirectProof.var H 0 M :: receiver
            :: ((actuals.zip Ds).map fun (a,D) => DirectProof.cast H D a)
              ++ omittedPremises H Ds actuals.length))
      | _, _ => throw "a method call's target requires one callable contract"
    pure (saveOperands (saved ++ [method]) call)
  | .call _ f args spreads _ => do
    -- Reading a spread operand's elements is an array operation, which a
    -- closed expression does not have.
    if !spreads.isEmpty then throw "a spread argument inside a closed expression is outside the fragment"
    let callee ← closureExpr recursive fc scope Γ f
    -- A variadic signature serves a call no fixed arrow takes by arity: its
    -- fixed parameters, trailing ones omitted as `undefined`, then every
    -- further actual at its position in the rest.
    let fixedFits := match PositiveRules.expand G callee.type with
      | [.arrs L _] | [.callable _ _ L _] => L.any fun p => args.length ≤ p.arguments.length
      | _ => false
    match PositiveRules.expand G callee.type, ProgramTyping.restSigs G callee.type with
    | _, ⟨Rt, (Ps, E), R, effect⟩ :: _ =>
      if fixedFits then throw "a call both a fixed and a variadic signature take is outside the fragment"
      let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr recursive fc scope Γ a
      let k := min actuals.length Ps.length
      let extra := actuals.drop k
      let positions ← extra.zipIdx.mapM fun (_, i) => match restPosition G E i with
        | some D => pure D
        | none => throw "an actual past the rest's positions"
      pure (DirectProof.node Γ (.call callee.term (actuals.map (·.term))) R
        (.callRest effect k (Ps.length - k) (extra.map fun _ => false) E)
        (callee :: plainReceiver Γ Rt :: ((actuals.take k).zip Ps).map (fun (a,D) => DirectProof.cast Γ D a)
          ++ omittedPremises Γ Ps k ++ (extra.zip positions).map fun (a,D) => DirectProof.cast Γ D a))
    | [.arrs L _], [] | [.callable _ _ L _], [] =>
      let rule := match PositiveRules.expand G callee.type with
        | [.callable ..] => ProgramCertificates.Rule.callCallable
        | _ => .app
      let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr recursive fc scope Γ a
      let ⟨Rt,Ds,R,effect⟩ ← selectSignature G L (actuals.map (·.type))
      -- A plain call passes `undefined`: a signature that needs a receiver
      -- is a located obligation, apart from the call's own typing.
      if !admitsUndefined G Rt then
        let plan := plainReceiver Γ Rt
        obligation f.span plan.goal (some plan) "method-receiver" scope
      pure (DirectProof.node Γ (.call callee.term (actuals.map (·.term))) R (rule effect)
        (callee :: plainReceiver Γ Rt :: ((actuals.zip Ds).map fun (a,D) => DirectProof.cast Γ D a)
          ++ omittedPremises Γ Ds actuals.length))
    | _, _ =>
      if callee.type.length ≤ 1 then throw "callee must name a source arrow"
      -- Save callee first, then each actual, before splitting its immutable slot.
      let (_,_,actuals) ← args.attach.foldlM (fun (ctx,sc,ps) ⟨a,_⟩ => do
        let p ← closureExpr recursive fc sc ctx a
        pure (p.type::ctx,held ⟨"",some a.span⟩::sc,ps ++ [p]))
        (callee.type::Γ,held ⟨"",some f.span⟩ :: scope,[])
      let As := actuals.map (·.type)
      let alternatives ← callee.type.mapM fun label => do
        let [.arrs L _] := PositiveRules.expand G [label]
          | throw "every callee alternative must name a source arrow"
        let ⟨Rt,Ds,R,effect⟩ ← selectSignature G L As
        pure (label, (⟨Rt,Ds,R,effect⟩ : Arrow (Ty Tree)))
      let R := (alternatives.flatMap fun (_,sig) => sig.result).eraseDups
      let n := As.length
      let H := As.reverse ++ callee.type::Γ
      let term := Tm.call (.var n) ((List.range n).map fun i => .var (n-1-i))
      let children := alternatives.map fun (label,⟨Rt,Ds,result,effect⟩) =>
        let branch := As.reverse ++ [label]::Γ
        DirectProof.cast branch R (DirectProof.node branch term result (.app effect)
          (DirectProof.var branch n [label] :: plainReceiver branch Rt ::
            ((As.zip Ds).zipIdx.map fun ((A,D),i) =>
              DirectProof.cast branch D (DirectProof.var branch (n-1-i) A))
            ++ omittedPremises branch Ds n))
      pure (saveOperands (callee::actuals)
        (DirectProof.node H term R (.unionVar n) children))
  | .write _ fld receiver rhs => do
    let B ← exprType fc receiver
    let r ← closureExpr recursive fc scope Γ receiver
    let a ← closureExpr recursive fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) rhs
    let C := a.type
    let H := C::B::Γ
    let write ← writeCell G H fld B C 1
    let done := DirectProof.letE H write (DirectProof.var ([Labels.nul]::H) 1 C)
    pure (DirectProof.letE Γ r (DirectProof.letE (B::Γ) a done))
  | .ifBody _ cond thn els => do
    let H := Γ
    if let some (snapshot, read, tested) := readGuard scope cond then
      if readOnly thn && readOnly els then
        let saved ← closureExpr recursive fc scope H read
        let ds := held ⟨snapshot,some read.span⟩ :: scope
        let K := saved.type :: H
        let c ← closureExpr recursive fc ds K cond
        let body ← conditionalPlan ds K A tested c
          (fun names types => closureExpr recursive fc names types thn)
          (fun names types => closureExpr recursive fc names types els)
        pure (DirectProof.letE H saved body)
      else
        let c ← closureExpr recursive fc scope H cond
        conditionalPlan scope H A cond c
          (fun names types => closureExpr recursive fc names types thn)
          (fun names types => closureExpr recursive fc names types els)
    else
      let c ← closureExpr recursive fc scope H cond
      conditionalPlan scope H A cond c
        (fun names types => closureExpr recursive fc names types thn)
        (fun names types => closureExpr recursive fc names types els)
  | .withValue _pos fn initial functionType bagType => do
    -- The function's claim and its annotation are checked of the function
    -- the initializer is; the callable object is allocated with its code,
    -- checked at the annotation's signatures, one table entry per advertised
    -- overload (`Rule.callableGraph`).
    let fnType ← closureType fc fn
    let f ← LoweringClosures.graphClosure recursive fc scope Γ fn fnType
    let fplan := DirectProof.cast Γ fnType f
    obligation fn.span fplan.goal (some fplan) "expression-claim" scope
    let property ← closureExpr recursive fc scope Γ initial
    let F ← lower (Fragment.translate functionType)
    let PRef ← lower (Fragment.translate bagType)
    let G := SourceTypes.graph (← table)
    let [.arrs L _] := PositiveRules.expand G F | throw "initializer requires a free function annotation"
    let [.refs P [] []] := PositiveRules.expand G PRef
      | throw "initializer requires an invariant record annotation"
    let some values := allocationChildren property
      | throw "initializer requires a fresh object literal"
    let .alloc _ ns _ := initial | throw "initializer requires a fresh object literal"
    if values.length != P.length then throw "initializer literal does not match its annotation"
    -- Initializers stay in source order. An annotation may list the same fields
    -- in another order; pairing by position would silently rename their values.
    let P ← ns.mapM fun name => do
      let some D := P.lookup name | throw s!"initializer field '{repr name}' is absent from its annotation"
      pure (name,D)
    let fp := DirectProof.cast Γ F f
    let pp := DirectProof.cast Γ PRef property
    obligation fn.span fp.goal (some fp) "callable-function-annotation" scope
    obligation initial.span pp.goal (some pp) "callable-field-annotation" scope
    let code ← LoweringClosures.lambdaCode recursive fc scope Γ fn F (.annotated F)
    -- A variadic arrow's callable object has its own variadic signatures; the
    -- function annotation is reached by the cast below.
    let C ← if code.rest then do
        let [.arrs [] S] := PositiveRules.expand (SourceTypes.graph (← table)) code.type
          | throw "initializer requires a variadic signature"
        lower (SourceTypes.use (.callable P [] [] S))
      else lower (SourceTypes.use (.callable P [] L []))
    recordHints [C]
    let casts := (values.zip (P.map Prod.snd)).map fun (v,D) => DirectProof.cast Γ D v
    pure (DirectProof.node Γ
      (.makeAt (code.code code.kind) (P.map Prod.fst) (values.map (·.term))) [C]
      (.callableGraph code.arrays) (casts ++ code.capturePlans Γ))
  | .ctor _ lam statics => do
    -- A class value: its constructor's graph code, construct-only, checked at
    -- each construct signature with `undefined` in the receiver slot `new`
    -- passes, then the parameters, allocated with its code field and its
    -- static fields, each at the contract its claim states, in member order
    -- (`Rule.ctorGraph`).
    let .lambda _ none [] _ [] false (some _) _ := lam
      | throw "a class value is a constructor lambda with plain parameters"
    let P ← match PositiveRules.expand G A with
      | [.ctors _ _ P []] => pure P
      | _ => throw "a class value's claim must name its construct signatures and static fields"
    if P.map Prod.fst != statics.map Prod.fst then
      throw "a class value's claim must state exactly its static fields, in member order"
    let values ← statics.mapM fun (_, e) => closureExpr recursive fc scope Γ e
    let casts := (values.zip (P.map Prod.snd)).map fun (v, D) => DirectProof.cast Γ D v
    let code ← LoweringClosures.lambdaCode recursive fc scope Γ lam A (.ctor [Labels.undef])
    pure (DirectProof.node Γ
      (.makeAt (code.code .construct) (codeField :: P.map Prod.fst) (.nul :: values.map (·.term))) A
      (.ctorGraph [Labels.undef]) (casts ++ code.capturePlans Γ))
  | .construct _ f args spreads _ => do
    if !spreads.isEmpty then throw "a constructor spread inside a closed expression is outside the fragment"
    let callee ← closureExpr recursive fc scope Γ f
    let [.ctors L _ _ _ _] := PositiveRules.expand G callee.type
      | throw "`new` needs a value with construct signatures"
    let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr recursive fc scope Γ a
    -- As for a call: a signature declaring exactly the actuals written, or a
    -- longer one whose remaining positions admit `undefined`.
    let ⟨_, Ds, R, _⟩ ← selectSignature G (L.map fun (Ds, R) => ⟨[Labels.undef], Ds, R, .unrestricted⟩) (actuals.map (·.type))
    pure (DirectProof.node Γ (.construct callee.term (actuals.map (·.term))) R .construct
      (callee :: ((actuals.zip Ds).map fun (a,D) => DirectProof.cast Γ D a)
        ++ omittedPremises Γ Ds actuals.length))
  -- A closure's body is a graph, as a function body is: statements, or an
  -- expression `e`, the graph of `return e` (`graphClosure`).
  | .lambda .. => LoweringClosures.graphClosure recursive fc scope Γ e A
  let plan := DirectProof.cast Γ A p
  obligation e.span plan.goal (some plan) "expression-claim" scope
  -- Validate the supplied claim, but do not discard a stronger saved-read
  -- derivation needed for the enclosing return contract.
  match e with
  | .read _ fld (.var _ name) =>
    if (readSnapshot name fld).any (names scope).contains then return p else return plan
  | .var _ name =>
    if (names scope).contains (localSnapshotName name) then return p else return plan
  | _ => return plan

end LoweringExpression
end Verification.SourceExtraction
