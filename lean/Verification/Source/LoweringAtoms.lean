import Verification.Source.LoweringExpression
import Verification.Source.LoweringControl
import Verification.Source.LoweringOperands

namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

namespace LoweringAtoms

set_option maxHeartbeats 1000000

/-- An original expression's contents are checked after its value is produced,
before subsequent operations can change the heap. Saved-value reads carry no
new observation of their source expression. -/
@[nospecialize] partial def observeExprCurrent (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree)) (source : Span)
    (A : Ty Tree) (next : Target) : Compiler Target := do
  match fc.exprCurrent.lookup source with
    | none => pure next
    | some asserted =>
      -- An observation the cell's contract implies holds wherever the cell
      -- is read: a located inclusion (`persistentObservation`), as at a
      -- closure's entry, which knows nothing of the heap. Any other is a fact
      -- of this point, which every edge into it must establish.
      let T ← table
      let clauses := PositiveRules.expand (SourceTypes.graph T) A
      let invariant := fun (fld : PropKey) => do
        if clauses.isEmpty then none
        let ws ← clauses.mapM fun (c : PositiveNormalization.Clause (Ty Tree)) => match c with
          | PositiveNormalization.Clause.refs W [] [] [] [] [] => W.lookup fld
          | _ => none
        some ws.flatten.eraseDups
      let (uniform, pointwise) := asserted.partition fun (fld, R) =>
        (invariant fld).any (within T · R)
      for (fld, R) in uniform do persistentObservation ⟨"",some source⟩ source A fld R
      let facts ← pointwise.mapM fun (fld, R) => do return (⟨0,← contents R,fld⟩ : HeapFacts.Fact)
      checkpoint source (A::Γ) facts next (scope := held ⟨"",some source⟩ :: scope)

/-- Call lowering compiles its operands through the supplied atomic compiler. -/
@[nospecialize] private def compileCall
    (compile : List (ScopeBinding Tree) → List (Ty Tree) → Fragment.Expr → Target → Compiler Target)
    (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (e callee : Fragment.Expr) (args : List Fragment.Expr) (A : Ty Tree) (next : Target) : Compiler Target := do
  let original := (← originalExpression).getD e
  let savedReceiver ← match (← savedReceiver) with
    | none => pure none
    | some name => do
      let some (i, .value) := resolve scope name
        | throw "internal execution plan: missing saved call receiver"
      let some O := Γ[i]? | throw "internal execution plan: saved receiver type"
      pure (some (i, O))
  let sourceArgs := match original with
    | .call _ _ xs _ _ | .invoke _ _ xs _ _ | .callWithReceiver _ _ _ xs => xs
    | _ => args
  let operands := match e with
    | .callWithReceiver _ _ receiver _ => receiver :: args
    | _ => args
  let spreads := match e with
    | .call _ _ _ s _ | .invoke _ _ _ s _ => s
    | _ => []
  -- A method call saves the object, a computed key, then the method read
  -- from it; the method is the callee and the object the receiver. The
  -- saved slots sit where a plain call's one callee slot does.
  let method : Option (Fragment.Expr × Option Fragment.Expr × (Tm → Tm)) ← match e with
    | .invoke _ (.read _ fld o) _ _ typeArgs => do
      let O ← exprType fc o
      explicitInstance e.span O (← exprType fc callee) fld typeArgs
      let G := SourceTypes.graph (← table)
      pure (some (o, none, memberHead G O fld))
    | .invoke _ (.index _ (some fld) o key) _ _ typeArgs => do
      let O ← exprType fc o
      explicitInstance e.span O (← exprType fc callee) fld typeArgs
      let G := SourceTypes.graph (← table)
      pure (some (o, some key, memberHead G O fld))
    | .invoke _ (.elemAt _ o key) _ _ typeArgs => do
      if !typeArgs.isEmpty then
        throw (locatedRefusal (← table) e.span .schemeElimination
          ("explicit type arguments on an element call are outside the fragment: an element that " ++
            "is a generic closure is claimed at a quantified callable, which the claim format does not encode"))
      let K ← exprType fc key
      let index ← arrayKeyTerm K
      pure (some (o, some key, fun obj => .elemAt (.readAt SourceTypes.storeField obj) index))
    | .invoke .. => throw "a method call's target must name a field or an element"
    | _ => pure none
  let headType ← exprType fc callee
  let B ← match original, savedReceiver with
    | .invoke _ originalCallee _ _ _, some _ => exprType fc originalCallee
    | _, _ => pure headType
  -- A method of an object of a union whose alternatives read different
  -- members, `x.toString()` on `string | number`, is read and called in
  -- one step dispatched on the object (`dispatchCallTerm`), after the
  -- actuals: so no actual may run code.
  let dispatch : Option PropKey ← if savedReceiver.isSome then executionDispatch fc original
    else match e, method, callee with
    | .invoke _ _ _ [] _, some (o, none, _), .read _ fld _ => do
      let O ← exprType fc o
      let plain : Fragment.Expr → Bool := fun a => match a with
        | .var .. | .lit .. => true
        | _ => false
      let G := SourceTypes.graph (← table)
      pure (if O.length > 1 && B.length > 1 && args.all plain
          && (ProgramTyping.restSigs G B).isEmpty then some fld else none)
    | _, _, _ => pure none
  let headTys : List (Ty Tree) ← match method, dispatch with
    | none, _ => pure [headType]
    | some (o, _, _), some _ => do pure [← exprType fc o]
    | some (o, key, _), none => do
      let O ← exprType fc o
      let keyTy ← key.mapM (exprType fc)
      pure (B :: keyTy.toList ++ [O])
  let headScope := match method, dispatch with
    | none, _ => [held ⟨"",some callee.span⟩]
    | some (o, _, _), some _ => [held ⟨"",some o.span⟩]
    | some (o, key, _), none => held ⟨"",some callee.span⟩ ::
        (key.map fun k => held ⟨"",some k.span⟩).toList ++ [held ⟨"",some o.span⟩]
  let h := headTys.length
  -- Into a variadic callee a spread may be anywhere among the actuals past
  -- the fixed ones. The call reads a spread once every actual is evaluated;
  -- a spread followed by an actual that runs code is therefore copied where
  -- it is written, `[...xs]`, and the call spreads the copy, which nothing
  -- else can reach. Into fixed parameters each spread stands for a tuple's
  -- required positions, read once every actual is evaluated: no actual
  -- after the first spread may run code.
  let calleeGraph := SourceTypes.graph (← table)
  let restSignatures := ProgramTyping.restSigs calleeGraph B
  let variadic := !restSignatures.isEmpty
  -- A rest that is one tuple contract, an argument pack's instance, takes
  -- a spread as fixed parameters do: its tuple's positions.
  -- A rest that is a packed binder's argument lists takes one spread of the
  -- store of one of its values (`callPacked`).
  let packedRest := variadic && restSignatures.all fun ⟨_, (_, P), _, _⟩ =>
    P.any fun t => calleeGraph.parameterKinds t == some .packed
  let tupleRest := variadic && !packedRest && restSignatures.all fun ⟨_, (_, P), _, _⟩ =>
    (PositiveRules.restElem calleeGraph P).isNone
  let runsCode : Fragment.Expr → Bool := fun a => match a with
    | .var .. | .lit .. => false
    | _ => true
  let copied := if variadic && !tupleRest then spreads.filter fun i => (args.drop (i + 1)).any runsCode
    else []
  let spread := (!variadic || tupleRest) && !spreads.isEmpty
  let spreadOrder := spreads.eraseDups.mergeSort (· ≤ ·)
  if spread then
    let first := spreadOrder.headD args.length
    if (sourceArgs.drop (first + 1)).any runsCode then
      throw (locatedRefusal (← table) e.span .bindingAnnotation
        "a spread into fixed parameters followed by an actual that runs code is outside the fragment")
  let As₀ ← operands.mapM (exprType fc)
  -- A dense tuple keeps its exact positions when copied. Other arrays use
  -- the existing unbounded copy rule, whose result may have holes.
  let copyTypes ← copied.mapM fun i => do
    let G := SourceTypes.graph (← table)
    let some original := As₀[i]? | throw "a spread argument needs an operand"
    if let some S := storeOf G original then
      if let [.list T []] := PositiveRules.expand G S then
        if T.optional.isEmpty && T.rest.isNone then
          return (i, S)
    let some ⟨_, (_, P), _, _⟩ := (ProgramTyping.restSigs G B).head? | throw "a spread needs a variadic callee"
    let some E := PositiveRules.restElem G P
      | throw "a spread into a rest needs an element rest"
    if !E.contains Labels.undef then
      throw (locatedRefusal (← table) e.span .bindingAnnotation
        "a spread copied before a later actual runs needs a rest element type that admits `undefined`")
    let C ← lower (SourceTypes.use (.list ⟨[], [], some E, false, .dense⟩ []))
    recordHints [C]
    pure (i, [C])
  let As := As₀.zipIdx.map fun (A, i) =>
    (copyTypes.lookup i).getD A
  let n := As.length
  -- A spread stands for the required positions of its operand's tuple
  -- contract. Those elements are read here, after every other argument has
  -- been evaluated, which is where a call reads them; the operand is a name,
  -- so nothing is evaluated twice. No iterator of the source's own can be
  -- installed in this fragment, so the array's positions are what a spread
  -- yields (DESIGN.md, "Trust surface").
  let spreadElements : List (Nat × List (Ty Tree)) ← if !spread then pure [] else
    spreadOrder.mapM fun i => do
      let some arrayTy := As[i]? | throw "a spread argument needs an operand"
      let G := SourceTypes.graph (← table)
      let sourceStore := match PositiveRules.expand G arrayTy with
        | [.list ..] => some arrayTy
        | _ => storeOf G arrayTy
      let some S := sourceStore | throw "a spread argument needs a tuple contract"
      match PositiveRules.expand G S with
      | [.list T []] =>
        if !T.optional.isEmpty || T.rest.isSome then
          throw "a spread argument needs a tuple contract of required positions"
        pure (i, T.required)
      | _ => throw "a spread argument needs a tuple contract of required positions"
  let elements := spreadElements.flatMap (·.2)
  -- Each element's operand and its position in that operand's tuple.
  let sources : List (Nat × Nat) :=
    spreadElements.flatMap fun (i, Es) => (List.range Es.length).map (i, ·)
  let k := elements.length
  let anonymous := held ⟨"",some e.span⟩
  let temporaries := (operands.map fun a => held ⟨"",some a.span⟩).reverse ++ headScope
  let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
    (fun i => if i == 0 then 0 else i+n+h+k))⟩
  -- An actual sits above the elements a spread reads; a receiver, which is
  -- an operand and not an actual, sits below them all.
  -- A spread into fixed parameters is its elements, in order, where it is
  -- written.
  let argumentGraph := SourceTypes.graph (← table)
  let rawStore := fun i => match PositiveRules.expand argumentGraph (As[i]?.getD []) with
    | [.list ..] => true
    | _ => false
  let actuals := ((List.range args.length).foldl (fun (g, out) i =>
      let v := Tm.var (k + args.length - 1 - i)
      match spreadElements.lookup i with
      | some Es => (g + Es.length, out ++ (List.range Es.length).map fun j => Tm.var (k-1-(g+j)))
      | none =>
        (g, out ++ [if copied.contains i || (spreads.contains i && rawStore i) then .spread v
          else if spreads.contains i && variadic then .spread (.readAt SourceTypes.storeField v)
          else v])) (0, ([] : List Tm))).2
  let callEnv := elements.reverse ++ As.reverse ++ headTys ++ Γ
  let G := SourceTypes.graph (← table)
  let callScope := (List.replicate k anonymous) ++ temporaries ++ scope
  -- The alternatives' members, as the callee's claim names them, are the
  -- types the dispatched call is typed at.
  if dispatch.isSome then recordHints (B)
  let dispatchArms ← match dispatch, headTys.getLast? with
    | some fld, some O => primitiveArms callScope callEnv O fld
    | _, _ => pure []
  -- `.call` passes its first operand as the receiver; a plain call passes
  -- `undefined`.
  let callTerm := match savedReceiver with
    | some (i, O) => match dispatch with
      | some fld => dispatchCallTerm G O dispatchArms fld (k+n) actuals
      | none => Tm.invoke (.var (k+n)) (.var (k+n+h+i)) actuals
    | none => match e, dispatch, headTys.getLast? with
      | .callWithReceiver .., _, _ => Tm.invoke (.var (k+n)) (.var (k+n-1)) actuals
      | .invoke .., some fld, some O => dispatchCallTerm G O dispatchArms fld (k+n) actuals
      | .invoke .., _, _ => Tm.invoke (.var (k+n)) (.var (k+n+h-1)) actuals
      | _, _, _ => Tm.call (.var (k+n)) actuals
  -- The receiver the call passes, the `.call` operand or `undefined`, is
  -- checked where the call is made at the selected signature's receiver:
  -- a located obligation, apart from the call's own typing.
  -- The receiver's selected contract: a fixed signature taking these
  -- actuals, or the variadic signature the call uses.
  let receiverOf (Rr : Ty Tree) (actualTys : List (Ty Tree)) : Option (Ty Tree) :=
    if variadic then
      let sigs := ProgramTyping.restSigs G B
      ((sigs.find? fun sig => Rr.all sig.receiver.contains) <|> sigs.head?).map (·.receiver)
    else if spread then none
    else match PositiveRules.expand G B with
      | [.arrs L _] | [.callable _ _ L _] =>
        match selectSignature G L actualTys Rr with
        | .ok sig => some sig.receiver
        | .error _ => none
      | _ => none
  match savedReceiver with
  | some (i, O) =>
    if let some Rt := receiverOf O As then
      let plan := DirectProof.cast callEnv Rt (DirectProof.var callEnv (k+n+h+i) O)
      let source := (scope[i]?.bind (·.source.span)).getD original.span
      obligation source plan.goal (some plan) "method-receiver" callScope
  | none => match e, method with
    | .callWithReceiver _ _ r _, _ =>
      if let some R₀ := As.head? then
        if let some Rt := receiverOf R₀ (As.drop 1) then
          let plan := DirectProof.cast callEnv Rt (DirectProof.var callEnv (k+n-1) R₀)
          obligation r.span plan.goal (some plan) "method-receiver" callScope
    | .invoke .., some (o, _, _) =>
      if let some O := headTys.getLast? then
        if let some Rt := receiverOf O As then
          let plan := DirectProof.cast callEnv Rt (DirectProof.var callEnv (k+n+h-1) O)
          obligation o.span plan.goal (some plan) "method-receiver" callScope
    | _, _ =>
      if let some Rt := receiverOf [Labels.undef] As then
        if !admitsUndefined G Rt then
          let plan := DirectProof.cast callEnv Rt (DirectProof.node callEnv .undef [Labels.undef] .undef)
          obligation callee.span plan.goal (some plan) "method-receiver" callScope
  let call ← emitAt e.span callTerm (.bind drop) callEnv A
    (scope := (List.replicate k anonymous) ++ temporaries ++ scope)
  -- The reads run in position order, so they are emitted from the last back.
  let reads ← (List.range k).reverse.foldlM (fun next g => do
    let some E := elements[g]? | throw "a spread element has no contract"
    let some (i, j) := sources[g]? | throw "a spread element has no operand"
    let index ← indexTerm j
    let env := (elements.take g).reverse ++ As.reverse ++ headTys ++ Γ
    let source := if rawStore i then Tm.var (g+n-1-i)
      else .readAt SourceTypes.storeField (.var (g+n-1-i))
    emitAt e.span (.elemAt source index)
      (.bind next) env E "spread-element"
      (scope := (List.replicate g anonymous) ++ temporaries ++ scope)) call
  let right ← operands.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) => do
    let sc := (operands.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++
      headScope ++ scope
    let ctx := (As.take i).reverse ++ headTys ++ Γ
    if copied.contains i then
      -- The copy takes the operand's slot: the continuation sees the copied
      -- store where it would have seen the array.
      let some A := As₀[i]? | throw "a spread argument needs an operand"
      let m := (next.mapping.getD (List.range (ctx.length + 1))).map fun j =>
        if j == 0 then 0 else j + 1
      let some C := As[i]? | throw "a spread argument needs an operand"
      let inits ← match PositiveRules.expand (SourceTypes.graph (← table)) C with
        | [.list T []] =>
          if T.optional.isEmpty && T.rest.isNone then
            (List.range T.required.length).mapM fun j => do
              return Tm.elemAt (.readAt SourceTypes.storeField (.var 0)) (← indexTerm j)
          else pure [.spread (.readAt SourceTypes.storeField (.var 0))]
        | _ => throw "a spread copy needs an array store contract"
      let copy ← emitAt arg.span (.arrLit inits)
        (.bind ⟨next.label, some m⟩) (A :: ctx) C "spread-copy"
        (scope := held ⟨"",some arg.span⟩ :: sc)
      compile sc ctx arg ⟨copy.label, none⟩
    else compile sc ctx arg next) reads
  match method, dispatch with
  | none, _ => compile scope Γ callee right
  | some (o, _, _), some _ => compile scope Γ o right
  | some (o, key, readTerm), none =>
    -- The method is read from the saved object, below any saved key; a
    -- primitive's, by its shape (`dispatchTerm`).
    let saved := headTys.drop 1
    let objSlot := saved.length - 1
    let arms ← match callee, headTys.getLast? with
      | .read _ fld _, some O | .index _ (some fld) _ _, some O =>
        do pure (fld, ← primitiveArms (headScope.drop 1 ++ scope) (saved ++ Γ) O fld)
      | _, _ => pure ("", [])
    let term := if arms.2.isEmpty then readTerm (.var objSlot)
      else dispatchTerm arms.2 arms.1 objSlot (.readAt arms.1 (.var objSlot))
    let read ← emitAt callee.span term (.bind ⟨right.label, none⟩)
      (saved ++ Γ) B (scope := headScope.drop 1 ++ scope)
    let afterObject ← match key with
      | none => pure read
      | some key => do
        let some O := headTys.getLast? | throw "internal method call slots"
        compile (held ⟨"",some o.span⟩ :: scope) (O::Γ) key read
    compile scope Γ o afterObject

/-- Each expression leaves its result in slot zero and preserves the original
slots after it. Anonymous temporary slots cannot be named by source identifiers.
Mappings discard only the temporaries introduced by this expression. -/
@[nospecialize] partial def compileAtom (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (e : Fragment.Expr) (next : Target) : Compiler Target := do
  let A ← exprType fc e
  let prepared ← isPreparedAtom e
  let next ← if prepared then pure next else observeExprCurrent fc scope Γ e.span A next
  match _he : e with
  | .nullishAssign .. | .arrayAssign .. | .build .. | .objectAssign .. | .ifBody ..
    | .logical .. | .coalesce .. | .optional .. | .comma .. | .logicalAssign .. | .update .. =>
    throw "internal execution plan: compound source syntax reached atomic elaboration"
  | .equality .. => throw "internal unresolved equality"
  | .block .. => throw "internal extraction error: statements outside a closure body"
  | .var _ name =>
    match resolve scope name with
    | some (i, .value) | some (i, .slot _) => emitAt e.span (.var i) (.bind next) Γ A (scope := scope)
    -- A source read of a mutable local returns the cell's contents; the
    -- identity in the slot is never the value of a source expression.
    | some (i, .cell ..) => emitAt e.span (.readAt valueField (.var i)) (.bind next) Γ A (scope := scope)
    | none => throw s!"unbound or uninitialized source variable '{name}'"
  | .assign _ name _ rhs =>
    if let some (_, .slot contract) := resolve scope name then
      -- The value, checked at the contract, is the assignment's; the
      -- execution plan's continuation rebinds the slot to it
      -- (`executionEvaluate`), so no other path may compile it.
      if (← originalExpression).map (·.span) != some e.span then
        throw "internal execution plan: a write of a slot outside its execution plan"
      let C ← exprType fc rhs
      let checked ← emitAt e.span (.var 0) (.effect next) (C::Γ) contract "storage-contract"
        (scope := held ⟨"",some rhs.span⟩ :: scope)
      return ← compileAtom recursive fc scope Γ rhs checked
    let some (i, .cell ..) := resolve scope name
      | throw s!"assignment to '{name}', which is not a mutable local"
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else j+1))⟩
    -- As for a cell write: JavaScript's assignment yields the value written,
    -- the calculus's write yields null, so the value is saved and returned.
    -- The write itself is the storage-contract check: it types only when the
    -- value meets the contract the cell was declared with.
    let effects := held ⟨"",some rhs.span⟩ :: scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::Γ) A (scope := effects)
    let write ← emitAt e.span (.writeAt valueField (.var (i+1)) (.var 0)) (.effect result) (C::Γ) [Labels.nul]
      "storage-contract" (scope := effects)
    compileAtom recursive fc scope Γ rhs write
  | .lit _ v => emitAt e.span (← SourceTypes.value v) (.bind next) Γ A (scope := scope)
  | .read _ fld a =>
    let B ← exprType fc a
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    -- An array's `length` is its store's, read as a number; a primitive's
    -- member is read by its shape (`dispatchTerm`).
    let G := SourceTypes.graph (← table)
    -- `length` of a value that may be an array or something else:
    -- `Array.isArray` selects the built-in `readonly unknown[]`, whose length
    -- is its store's, and every other value reads `length` as it reads it.
    -- The test binds the value refined on each edge (`arraySlice`,
    -- `tagSlice`).
    if fld == "length" && B.any (fun l => arraysOnly G [l]) && !arraysOnly G B then
      let receiver := held ⟨"",some a.span⟩
      let u ← lower (SourceTypes.use .source)
      let store ← lower (SourceTypes.use (.list ⟨[], [], some [u], true, .sparse⟩ []))
      let R : Ty Tree := [← lower (SourceTypes.use (SourceTypes.arrayOf (← table) store true))]
      let S : Ty Tree := [store]
      let F := BranchRefinement.tagSlice G B .isArray false
      let drop2 := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
        (fun i => if i == 0 then 0 else i+2))⟩
      let length ← emitAt e.span (.lenOf (.var 0)) (.bind drop2) (S::R::Γ) A
        (scope := held ⟨"",some e.span⟩ :: receiver :: scope)
      let array ← emitAt e.span (.readAt SourceTypes.storeField (.var 0)) (.bind length) (R::Γ) S
        (scope := receiver :: scope)
      let arms ← primitiveArms (receiver :: scope) (F::Γ) F fld
      let other ← emitAt e.span (dispatchTerm arms fld 0 (.readAt fld (.var 0))) (.bind drop) (F::Γ) A
        (scope := receiver :: scope)
      -- The tested value is pushed on each edge; the slot it was saved in is
      -- dropped.
      let refined := fun (t : Target) => (⟨t.label, some ((t.mapping.getD (List.range (Γ.length+1))).map
        (fun i => if i == 0 then 0 else i+1))⟩ : Target)
      let test ← emitAt e.span (.var 0) (.tagBind .isArray (refined array) (refined other)) (B::Γ) B
        "tag-dispatch" (scope := receiver :: scope)
      return ← compileAtom recursive fc scope Γ a test
    -- `length` through a view admits an array: the read tests the receiver
    -- (`lenView`).
    let object := if fld == "length" && arraysOnly G B
      then Tm.lenOf (.readAt SourceTypes.storeField (.var 0))
      else if fld == "length" && lengthViewed G B then lengthRead 0 else .readAt fld (.var 0)
    let arms ← primitiveArms (held ⟨"",some a.span⟩ :: scope) (B::Γ) B fld
    -- An array's store is read in a node of its own, a field read, and its
    -- length in the next, which reads no heap: what was known of the heap
    -- is known after both.
    if fld == "length" && arraysOnly G B && arms.isEmpty then
      if let some S := storeOf G B then
        let drop2 := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
          (fun i => if i == 0 then 0 else i+2))⟩
        let length ← emitAt e.span (.lenOf (.var 0)) (.bind drop2) (S::B::Γ) A
          (scope := held ⟨"",some e.span⟩ :: held ⟨"",some a.span⟩ :: scope)
        let store ← emitAt e.span (.readAt SourceTypes.storeField (.var 0)) (.bind length) (B::Γ) S
          (scope := held ⟨"",some a.span⟩ :: scope)
        return ← compileAtom recursive fc scope Γ a store
    let node ← emitAt e.span (dispatchTerm arms fld 0 object) (.bind drop) (B::Γ) A
      (scope := held ⟨"",some a.span⟩ :: scope)
    compileAtom recursive fc scope Γ a node
  | .not _ a =>
    let B ← exprType fc a
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    -- A value that is not a Boolean is negated by its truthiness.
    let tested := if BranchRefinement.onlyBoolean (SourceTypes.graph (← table)) B then Tm.var 0
      else .test .truthy (.var 0)
    let node ← emitAt e.span (.ite tested .fls .tru) (.bind drop) (B::Γ) A
      (scope := held ⟨"",some a.span⟩ :: scope)
    compileAtom recursive fc scope Γ a node
  | .cast _ annot a =>
    -- The operand's value, retyped at the cast's own claim: the node proves
    -- the claim from the operand, and an annotation is one more type the
    -- operand must meet. Nothing here decides the assertion is true.
    let B ← exprType fc a
    if let some ty := annot then
      let T ← lower (Fragment.translate ty)
      let check := DirectProof.var (B::Γ) 0 T
      obligation e.span check.goal (some check) "cast-annotation" (held ⟨"",some a.span⟩ :: scope)
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let node ← emitAt e.span (.var 0) (.bind drop) (B::Γ) A "cast" (scope := held ⟨"",some a.span⟩ :: scope)
    compileAtom recursive fc scope Γ a node
  | .alloc _ ns operands =>
    let As ← operands.mapM (exprType fc)
    let n := As.length
    let temporaries := (operands.map fun a => held ⟨"",some a.span⟩).reverse
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+n))⟩
    let make ← emitAt e.span (.makeAt .absent ns ((List.range n).map fun i => .var (n-1-i)))
      (.bind drop) (As.reverse ++ Γ) A (scope := temporaries ++ scope)
    operands.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) =>
      compileAtom recursive fc
        ((operands.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++ scope)
        ((As.take i).reverse ++ Γ) arg next) make
  | .bindWithReceiver .. | .withValue .. | .lambda .. | .ctor .. =>
    let t ← LoweringExpression.closureExpr recursive fc scope Γ e
    emitAt e.span t.term (.bind next) Γ A (scope := scope)
  | .construct _ callee args spreads _ => do
    -- Execution planning saves the callee and actuals left to right. A spread
    -- before executable actuals is copied there; read its saved tuple here.
    if !spreads.isEmpty && (args.drop (spreads.headD args.length + 1)).any
        (fun a => match a with | .var .. | .lit .. => false | _ => true) then
      throw "a constructor spread before executable actuals requires an execution snapshot"
    let operands := callee :: args
    let As ← operands.mapM (exprType fc)
    let G := SourceTypes.graph (← table)
    -- A spread of other than a tuple of required positions goes to a variadic
    -- construct signature: `new` reads its store where it is written, as a
    -- call's spread into a rest is read (`constructRest`).
    let rawStore := fun (A : Ty Tree) => match PositiveRules.expand G A with
      | [.list ..] => true
      | _ => false
    let fixedTuple := fun (A : Ty Tree) =>
      let S := if rawStore A then some A else storeOf G A
      match S.map (PositiveRules.expand G) with
      | some [.list T []] => T.optional.isEmpty && T.rest.isNone
      | _ => false
    let variadicCtor := match PositiveRules.expand G (As.headD []) with
      | [.ctors _ (_ :: _) _ _ _] => true
      | _ => false
    if variadicCtor && spreads.any (fun i => !fixedTuple (As[i+1]?.getD [])) then
      let n := As.length
      let temporaries := (operands.map fun a => held ⟨"",some a.span⟩).reverse
      let actuals := (List.range args.length).map fun i =>
        let v := Tm.var (n-2-i)
        if spreads.contains i then
          if rawStore (As[i+1]?.getD []) then Tm.spread v else .spread (.readAt SourceTypes.storeField v)
        else v
      let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
        (fun i => if i == 0 then 0 else i+n))⟩
      recordHints (As.flatMap fun A => (storeOf G A).getD [])
      let construct ← emitAt e.span (.construct (.var (n-1)) actuals)
        (.bind drop) (As.reverse ++ Γ) A (scope := temporaries ++ scope)
      return ← operands.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) =>
        compileAtom recursive fc
          ((operands.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++ scope)
          ((As.take i).reverse ++ Γ) arg next) construct
    let spreadElements ← spreads.mapM fun i => do
      let some A := As[i+1]? | throw "a constructor spread names no operand"
      let S := match PositiveRules.expand G A with
        | [.list ..] => some A
        | _ => storeOf G A
      let some S := S | throw "a constructor spread needs a tuple contract"
      let [.list T []] := PositiveRules.expand G S
        | throw "a constructor spread needs a tuple contract of required positions"
      if !T.optional.isEmpty || T.rest.isSome then
        throw "a constructor spread needs a tuple contract of required positions"
      pure (i, T.required)
    let elements := spreadElements.flatMap (·.2)
    let sources : List (Nat × Nat) :=
      spreadElements.flatMap fun (i, Es) => (List.range Es.length).map (i, ·)
    let n := As.length
    let k := elements.length
    let temporaries := (operands.map fun a => held ⟨"",some a.span⟩).reverse
    let anonymous := held ⟨"",some e.span⟩
    let actuals := ((List.range args.length).foldl (fun (g, out) i =>
      match spreadElements.lookup i with
      | some Es => (g + Es.length, out ++ (List.range Es.length).map fun j => Tm.var (k-1-(g+j)))
      | none => (g, out ++ [Tm.var (k+n-2-i)])) (0, ([] : List Tm))).2
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+n+k))⟩
    let construct ← emitAt e.span (.construct (.var (k+n-1)) actuals)
      (.bind drop) (elements.reverse ++ As.reverse ++ Γ) A
      (scope := List.replicate k anonymous ++ temporaries ++ scope)
    let reads ← (List.range k).reverse.foldlM (fun next g => do
      let some E := elements[g]? | throw "a constructor spread element has no contract"
      let some (i,j) := sources[g]? | throw "a constructor spread element has no operand"
      let raw := match PositiveRules.expand G (As[i+1]?.getD []) with
        | [.list ..] => true
        | _ => false
      let source := Tm.var (g+n-2-i)
      let source := if raw then source else .readAt SourceTypes.storeField source
      emitAt e.span (.elemAt source (← indexTerm j)) (.bind next)
        ((elements.take g).reverse ++ As.reverse ++ Γ) E "constructor-spread-element"
        (scope := List.replicate g anonymous ++ temporaries ++ scope)) construct
    operands.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) =>
      compileAtom recursive fc
        ((operands.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++ scope)
        ((As.take i).reverse ++ Γ) arg next) reads
  | .shapeTest p tag equal operand =>
    let B ← exprType fc operand
    inOperand p tag B
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let test ← emitAt e.span (tagTestTerm tag equal 0) (.bind drop) (B::Γ) A
      (scope := held ⟨"",some operand.span⟩ :: scope)
    compileAtom recursive fc scope Γ operand test
  | .singletonTest _ tag equal testLeft left right =>
    let B ← exprType fc left
    let C ← exprType fc right
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let test ← emitAt e.span (tagTestTerm tag equal (if testLeft then 1 else 0)) (.bind drop) (C::B::Γ) A
      (scope := held ⟨"",some right.span⟩::held ⟨"",some left.span⟩ :: scope)
    let right ← compileAtom recursive fc (held ⟨"",some left.span⟩ :: scope) (B::Γ) right test
    compileAtom recursive fc scope Γ left right
  | .applyWithReceiver _ callee receiver list =>
    -- Function.prototype.apply: the target, the receiver and the list are
    -- saved in order; then the list's length and each index are read in order
    -- (CreateListFromArrayLike), and the target is invoked with the receiver
    -- and those elements. A missing, null or undefined list gives none. The
    -- list is never iterated: this is not the spread operation.
    let B ← exprType fc callee
    let R₀ ← exprType fc receiver
    let listTy ← list.mapM (exprType fc)
    let G := SourceTypes.graph (← table)
    -- A tuple of required positions is read index by index. An array of any
    -- length goes to a signature that takes only a rest: its store's positions
    -- are the actuals, `undefined` at a hole, as `CreateListFromArrayLike`
    -- reads them; nothing here iterates.
    let (elements, dynamic) : List (Ty Tree) × Bool ← match listTy with
      | none => pure ([], false)
      | some T =>
        if nullishList G T then pure ([], false) else
        let some S := storeOf G T
          | throw (locatedRefusal (← table) e.span .bindingAnnotation
              ".apply needs an array list, or a null or undefined one")
        match PositiveRules.expand G S with
        | [.list Tp []] =>
          if Tp.optional.isEmpty && Tp.rest.isNone then pure (Tp.required, false)
          else if Tp.required.isEmpty && Tp.optional.isEmpty &&
              (ProgramTyping.restSigs G B).any (fun ⟨_, (Ps, _), _, _⟩ => Ps.isEmpty) then
            pure ([], true)
          else throw (locatedRefusal (← table) e.span .bindingAnnotation
            ".apply with a list of unknown length needs a target taking only a rest parameter")
        | _ => throw (locatedRefusal (← table) e.span .bindingAnnotation
            ".apply needs an array list, or a null or undefined one")
    let reads := match listTy with
      | some T => !nullishList G T
      | none => false
    let k := elements.length
    let saved := (listTy.toList.reverse) ++ [R₀, B]
    let s := saved.length
    let N : Ty Tree := [← lower (SourceTypes.use .num)]
    -- Slots above the saved operands: the length, then each element read.
    let prepared := if reads then elements.reverse ++ [N] else []
    let p := prepared.length
    let anonymous := held ⟨"",some e.span⟩
    let operandScope := (list.toList.map fun a => held ⟨"",some a.span⟩) ++
      [held ⟨"",some receiver.span⟩, held ⟨"",some callee.span⟩]
    let callEnv := prepared ++ saved ++ Γ
    let callScope := List.replicate p anonymous ++ operandScope ++ scope
    let Rt ← if dynamic then
        let sigs := (ProgramTyping.restSigs G B).filter fun ⟨_, (Ps, _), _, _⟩ => Ps.isEmpty
        match (sigs.find? fun ⟨Rt,_,_,_⟩ => R₀.all Rt.contains) <|> sigs.head? with
        | some ⟨Rt,_,_,_⟩ => pure Rt
        | none => throw ".apply target requires a rest signature"
      else do
        let L ← match PositiveRules.expand G B with
          | [.arrs L _] | [.callable _ _ L _] => pure L
          | _ => throw ".apply target requires a single callable contract"
        let ⟨Rt,_,_,_⟩ ← selectSignature G L elements R₀
        pure Rt
    let receiverIndex := p + s - 2
    let receiverCheck := DirectProof.cast callEnv Rt (DirectProof.var callEnv receiverIndex R₀)
    obligation receiver.span receiverCheck.goal (some receiverCheck) "method-receiver" callScope
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+p+s))⟩
    -- The list is the slot below the length.
    let actuals := if dynamic then [Tm.spread (.readAt SourceTypes.storeField (.var 1))]
      else (List.range k).map fun j => Tm.var (k-1-j)
    let call ← emitAt e.span (.invoke (.var (p+s-1)) (.var receiverIndex) actuals) (.bind drop)
      callEnv A (scope := callScope)
    -- The reads run in position order, after the length, so they are emitted
    -- from the last back. The list is the slot just below the length.
    let afterLength ← (List.range k).reverse.foldlM (fun next j => do
      let some E := elements[j]? | throw "an element has no contract"
      let index ← indexTerm j
      let env := (elements.take j).reverse ++ N :: saved ++ Γ
      emitAt e.span (.elemAt (.readAt SourceTypes.storeField (.var (j+1))) index) (.bind next)
        env E "apply-element"
        (scope := List.replicate (j+1) anonymous ++ operandScope ++ scope)) call
    let prepare ← if reads then
        emitAt e.span (.lenOf (.readAt SourceTypes.storeField (.var 0))) (.bind afterLength)
          (saved ++ Γ) N "apply-length" (scope := operandScope ++ scope)
      else pure call
    let afterList ← match list with
      | none => pure prepare
      | some xs => compileAtom recursive fc (operandScope.drop 1 ++ scope) (saved.drop 1 ++ Γ) xs prepare
    let afterReceiver ← compileAtom recursive fc (held ⟨"",some callee.span⟩ :: scope) (B::Γ) receiver afterList
    compileAtom recursive fc scope Γ callee afterReceiver
  | .call _ callee args _ _ | .callWithReceiver _ callee _ args | .invoke _ callee args _ _ =>
    compileCall (compileAtom recursive fc) fc scope Γ e callee args A next
  | .arrayLit _ elems spreads =>
    -- The elements, in order, then the store they fill, then the array
    -- object holding it: two nodes, so the allocation's slots are variables.
    let G := SourceTypes.graph (← table)
    let some S := storeOf G A | throw "an array literal needs an array claim"
    let As ← elems.mapM (exprType fc)
    let n := As.length
    let temporaries := (elems.map fun a => held ⟨"",some a.span⟩).reverse
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+n+1))⟩
    let makeScope := held ⟨"",some e.span⟩ :: temporaries ++ scope
    let proto ← prototypeSlot makeScope
    let O ← arrayObject S
    -- Both nodes' derivations are known: the object holding the store and
    -- the prototype, and the store of the elements at their positions.
    let H := S :: As.reverse ++ Γ
    let some P := H[proto]? | throw "internal prototype slot mismatch"
    let make ← emitPlanned e.span (DirectProof.node H (arrayTerm proto) O .alloc
        [DirectProof.var H 0 S, DirectProof.var H proto P]) (.bind drop) H A (scope := makeScope)
    let K := As.reverse ++ Γ
    let storePlan ← if spreads.isEmpty then do
        let [.list T []] := PositiveRules.expand G S | throw "an array literal needs one tuple contract"
        let casts ← (List.range n).mapM fun i => do
          let some D := ProgramTyping.positionTy T i | throw "an array literal has more elements than its claim"
          let some Ai := As[i]? | throw "internal element slot mismatch"
          pure (DirectProof.cast K D (DirectProof.var K (n-1-i) Ai))
        pure (DirectProof.node K (.arrLit ((List.range n).map fun i => .var (n-1-i))) S .arrLit casts)
      else do
        -- With a spread, the store's length is not known: every position is
        -- at the claim's one element type, each plain element cast to it,
        -- each spread the store its operand holds (or is, for a copy).
        let [.list ⟨[], [], some E, _, _⟩ []] := PositiveRules.expand G S
          | throw (locatedRefusal (← table) e.span .bindingAnnotation
              "an array literal with a spread needs an array claim of one element type")
        let parts ← (List.range n).mapM fun i => do
          let some Ai := As[i]? | throw "internal element slot mismatch"
          let v := DirectProof.var K (n-1-i) Ai
          if spreads.contains i then
            match PositiveRules.expand G Ai with
            | [.list ..] => pure (true, v)
            | _ => pure (true, ← readCell G K SourceTypes.storeField v)
          else pure (false, DirectProof.cast K E v)
        pure (DirectProof.node K (.arrLit (parts.map fun (s, p) => if s then .spread p.term else p.term)) S
          (.arrParts E (parts.map (·.1))) (parts.map (·.2)))
    let store ← emitPlanned e.span storePlan (.bind make) K S (scope := temporaries ++ scope)
    elems.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) =>
      compileAtom recursive fc
        ((elems.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++ scope)
        ((As.take i).reverse ++ Γ) arg next) store
  | .elemAt _ receiver key =>
    let B ← exprType fc receiver
    let K ← exprType fc key
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    -- A string's code unit at the key's number; an array's element at its
    -- one index, from its store.
    let G := SourceTypes.graph (← table)
    let node ← if decide (Answers G B .isStr true) then
        emitAt e.span (Tm.elemAt (.var 1) (.var 0)) (.bind drop) (K::B::Γ) A (scope := temporaries)
      else do
        let index ← arrayKeyTerm K
        let .num b := index | throw "internal extraction error: an array key is a number"
        -- Planned where the receiver's contract names its store; otherwise
        -- the choice is open, and the node is searched.
        let plan? ← tryCatch (some <$> elemReadPlan G (K::B::Γ) (DirectProof.var (K::B::Γ) 1 B) b)
          (fun _ => pure none)
        match plan? with
        | some plan => emitPlanned e.span plan (.bind drop) (K::B::Γ) A (scope := temporaries)
        | none =>
          let term := Tm.elemAt (.readAt SourceTypes.storeField (.var 1)) index
          emitAt e.span term (.bind drop) (K::B::Γ) A (scope := temporaries)
    let right ← compileAtom recursive fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key node
    compileAtom recursive fc scope Γ receiver right
  | .elemWrite _ receiver key rhs =>
    -- The store is read, the element set, and the store written back: one
    -- write, so every alias sees the contract kept.
    let B ← exprType fc receiver
    let K ← exprType fc key
    let index ← arrayKeyTerm K
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+3))⟩
    let effects := held ⟨"",some rhs.span⟩::held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::K::B::Γ) A (scope := effects)
    let write ← emitAt e.span (.writeAt SourceTypes.storeField (.var 2)
        (.setElem (.readAt SourceTypes.storeField (.var 2)) index (.var 0)))
      (.effect result) (C::K::B::Γ) [Labels.nul] (scope := effects)
    let right ← compileAtom recursive fc (held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope) (K::B::Γ) rhs write
    let middle ← compileAtom recursive fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key right
    compileAtom recursive fc scope Γ receiver middle
  | .index _ (some fld) receiver key =>
    let B ← exprType fc receiver
    let K ← exprType fc key
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    let arms ← primitiveArms temporaries (K::B::Γ) B fld
    let node ← emitAt e.span (dispatchTerm arms fld 1 (.readAt fld (.var 1))) (.bind drop) (K::B::Γ) A
      (scope := temporaries)
    let right ← compileAtom recursive fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key node
    compileAtom recursive fc scope Γ receiver right
  | .index _ none receiver key =>
    let B ← exprType fc receiver
    let K ← exprType fc key
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    -- A key of string or number singletons reads, per singleton, the member
    -- its key names, as a literal key does (`keyedReadTerm`); any other key
    -- reads through an index.
    let G := SourceTypes.graph (← table)
    let term ← match keySingletons G K with
      | some keys => do
        let reads ← keys.mapM fun (tag, fld) => do
          let arms ← primitiveArms temporaries (K::B::Γ) B fld
          pure (tag, dispatchTerm arms fld 1 (.readAt fld (.var 1)))
        pure (keyedReadTerm reads 0)
      | none => pure (.indexAt (.var 1) (.var 0))
    let node ← emitAt e.span term (.bind drop) (K::B::Γ) A
      (scope := temporaries)
    let right ← compileAtom recursive fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key node
    compileAtom recursive fc scope Γ receiver right
  | .indexWrite _ (some fld) receiver key rhs =>
    let B ← exprType fc receiver
    let K ← exprType fc key
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+3))⟩
    let effects := held ⟨"",some rhs.span⟩::held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::K::B::Γ) A (scope := effects)
    let write ← emitAt e.span (.writeAt fld (.var 2) (.var 0)) (.effect result) (C::K::B::Γ) [Labels.nul]
      (scope := effects)
    let right ← compileAtom recursive fc (held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope) (K::B::Γ) rhs write
    let middle ← compileAtom recursive fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key right
    compileAtom recursive fc scope Γ receiver middle
  | .arith _ op l r =>
    let B ← exprType fc l
    let C ← exprType fc r
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some r.span⟩::held ⟨"",some l.span⟩ :: scope
    let node ← emitAt e.span (.arith op (.var 1) (.var 0)) (.bind drop) (C::B::Γ) A (scope := temporaries)
    let right ← compileAtom recursive fc (held ⟨"",some l.span⟩ :: scope) (B::Γ) r node
    compileAtom recursive fc scope Γ l right
  | .inKeys p key o =>
    -- The key, then the object, then the test of the key's singleton.
    let B ← exprType fc key
    let C ← exprType fc o
    inOperand p (.hasKey (.str "")) C
    let keys ← inKeyList p B
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some o.span⟩::held ⟨"",some key.span⟩ :: scope
    let node ← emitAt e.span (inKeysTerm keys 1 0) (.bind drop) (C::B::Γ) A (scope := temporaries)
    let right ← compileAtom recursive fc (held ⟨"",some key.span⟩ :: scope) (B::Γ) o node
    compileAtom recursive fc scope Γ key right
  | .unary _ .typeof a =>
    -- The operand, then its `typeof`, one tag test per answer.
    let B ← exprType fc a
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let node ← emitAt e.span (typeofTerm 0) (.bind drop) (B::Γ) A
      (scope := held ⟨"",some a.span⟩ :: scope)
    compileAtom recursive fc scope Γ a node
  | .unary pos op a =>
    -- The operand, then the constant of its family, then the operator.
    let B ← exprType fc a
    let (arith, c, C, _) ← unaryOperation pos op B
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some e.span⟩::held ⟨"",some a.span⟩ :: scope
    let node ← emitAt e.span (.arith arith (.var 1) (.var 0)) (.bind drop) (C::B::Γ) A (scope := temporaries)
    let constant ← emitAt e.span c (.bind node) (B::Γ) C (scope := held ⟨"",some a.span⟩ :: scope)
    compileAtom recursive fc scope Γ a constant
  | .indexWrite _ none .. => throw "internal unresolved computed key"
  | .write _ fld receiver rhs =>
    let B ← exprType fc receiver
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    -- JS assignment returns its evaluated RHS; the calculus write returns null.
    let effects := held ⟨"",some rhs.span⟩::held ⟨"",some receiver.span⟩ :: scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::B::Γ) A (scope := effects)
    let write ← emitAt e.span (.writeAt fld (.var 1) (.var 0)) (.effect result) (C::B::Γ) [Labels.nul]
      (scope := effects)
    let right ← compileAtom recursive fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) rhs write
    compileAtom recursive fc scope Γ receiver right

/-- Typed result of the saved method operation. -/
@[nospecialize] partial def methodPlanType (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (operation : SourceExecution.Operation) : Compiler (Ty Tree) := do
  match operation with
  | .methodRead original receiver key call =>
    return (← executionMethod fc scope Γ original receiver key call).1
  | .invokeSaved original _ _ _ => exprType fc original
  | _ => throw "internal execution plan: expected a method operation"

/-- The invocation uses the previously read member and evaluated receiver.
The call atom retains source metadata for spread and primitive dispatch checks. -/
@[nospecialize] partial def compileMethodOperation (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (operation : SourceExecution.Operation) (next : Target) : Compiler Target := do
  match operation with
  | .methodRead original receiver key call =>
    let (A, term) ← executionMethod fc scope Γ original receiver key call
    if let .bindWithReceiver .. := call then
      let B ← exprType fc original
      obligation original.span ⟨Γ,term,B⟩ none "expression-claim" scope
    emitAt original.span term (.bind next) Γ A (scope := scope)
  | .invokeSaved original prepared receiver method =>
    let .invoke pos _ args spreads typeArgs := prepared
      | throw "internal execution plan: expected a saved invocation"
    let call := Fragment.Expr.call pos (.var method.source method.name) args spreads typeArgs
    withSavedInvocation original receiver.name (compileAtom recursive fc scope Γ call next)
  | _ => throw "internal execution plan: expected a method operation"

/-- Compile compound conditions as short-circuit edges. The full source
expression still has an independent claimed typing obligation; the runtime
traverses its operands once instead of evaluating it and then replaying it. -/
@[nospecialize] partial def compileConditionAtom (recursive : RecursiveLowering) (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree))
    (Γ : List (Ty Tree)) (cond : Fragment.Expr) (yes no : Target) : Compiler Target := do
  let simple := do
    let A ← exprType fc cond
    if let some (snapshot, read, tested) := readGuard scope cond then
      -- Preserve the tested read until tag dispatch, so its heap link can
      -- justify the branch's current-content assertion. The singleton literal
      -- has no effects; every source operand still has its typing obligation.
      let B ← exprType fc read
      let ds := held ⟨snapshot,some read.span⟩ :: scope
      let K := B :: Γ
      let lift := fun (t : Target) =>
        ⟨t.label, some ((t.mapping.getD (List.range scope.length)).map (·+1))⟩
      let node ← emitBranch ds K tested A (lift yes) (lift no)
      let predicate ← compileAtom recursive fc ds K tested node
      compileAtom recursive fc scope Γ read predicate
    else
      let node ← emitBranch scope Γ cond A yes no
      compileAtom recursive fc scope Γ cond node
  -- For each singleton the split operand may be, in order: it is that one,
  -- and the other operand is too (strict equality is transitive where it
  -- holds). After every one failed, the split operand equals none of them
  -- (NaN, which equals nothing), so the operands differ. A test of a field
  -- read reads it again, which nothing between has written, and records its
  -- link, which lets the edge refine the object's arms (`fieldSlice`) and
  -- tells what the field holds.
  let dispatch := fun (p : Span) (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
      (split other : SplitOperand) (tags : List Tag) (yes no : Target) => do
    let G := SourceTypes.graph (← table)
    let width := scope.length
    let test := fun (Δ : List (Ty Tree)) (op : SplitOperand) (tag : Tag) (y n : Target) =>
      match op with
      | ((k, none), _) =>
        emitAt p (.var k) (.tagBind tag (branchMapping width (some k) y) (branchMapping width (some k) n))
          Δ (Δ[k]?.getD []) "tag-dispatch" (scope := scope)
      | ((k, some f), e) => do
        -- The read is saved and its copy tested, as a guard's saved read is:
        -- the copy states what the value is, and its link what the field holds.
        let R ← exprType fc e
        let drop := fun (t : Target) =>
          (⟨t.label, some ((t.mapping.getD (List.range width)).map (·+2))⟩ : Target)
        let dispatchNode ← emitAt p (.var 0) (.tagBind tag (drop y) (drop n)) (R::Δ) R "tag-dispatch"
          (scope := held ⟨"",some e.span⟩ :: scope)
        emitAt p (.readAt f (.var k)) (.bind dispatchNode) Δ R "tag-dispatch" (scope := scope)
    let refine := fun (Δ : List (Ty Tree)) (op : SplitOperand) (tag : Tag) (q : Bool) =>
      match op.1 with
      | (k, none) => Δ.set k (BranchRefinement.tagSlice G (Δ[k]?.getD []) tag q)
      | (k, some f) => Δ.set k (BranchRefinement.fieldSlice G (Δ[k]?.getD []) f tag q)
    let rec chain : List Tag → List (Ty Tree) → Compiler Target
      | [], _ => pure no
      | tag :: more, Δ => do
        -- Where the other operand cannot be this singleton, its test's true
        -- edge is never taken; it goes where the false one does, so that
        -- no target claims what the split operand holds on that path.
        let possible ← match other with
          | ((k, none), _) => pure !(BranchRefinement.tagSlice G ((refine Δ split tag true)[k]?.getD []) tag true).isEmpty
          | ((_, some _), e) => do
            pure !(BranchRefinement.tagSlice G (← exprType fc e) tag true).isEmpty
        let inner ← test (refine Δ split tag true) other tag (if possible then yes else no) no
        let next ← chain more (refine Δ split tag false)
        test Δ split tag inner next
    chain tags Γ
  match cond with
  | .arith p .eq l r =>
    match ← equalitySplit fc scope Γ l r with
    | some (split, other, tags) =>
      let start ← dispatch p scope Γ split other tags yes no
      -- The comparison itself runs first, as the source has it, with its
      -- obligations; its Boolean is dropped, and the dispatch re-reads the
      -- operands, which nothing between has written.
      let A ← exprType fc cond
      let width := scope.length
      let skip : Target := ⟨start.label, some ((start.mapping.getD (List.range width)).map (·+1))⟩
      let discard ← emitAt p (.var 0) (.effect skip) (A::Γ) A (scope := held ⟨"",some p⟩ :: scope)
      compileAtom recursive fc scope Γ cond discard
    | none =>
      match ← savedSplit fc scope l r with
      | none => simple
      | some (k, name, e, tags) =>
        -- The comparison's own claim is a supplemental obligation; the
        -- operand is evaluated once, into a slot above the scope, and the
        -- name, which no effect changes, is read where it is.
        let _ ← LoweringExpression.closureExpr recursive fc scope Γ cond
        let C ← exprType fc e
        let lift := fun (t : Target) =>
          ⟨t.label, some ((t.mapping.getD (List.range scope.length)).map (·+1))⟩
        let inner := held ⟨"",some e.span⟩ :: scope
        let start ← dispatch p inner (C::Γ) (((0, none)), e) (((k+1, none)), name) tags (lift yes) (lift no)
        compileAtom recursive fc scope Γ e start
  | .logical _ andOp left right =>
    let _ ← LoweringExpression.closureExpr recursive fc scope Γ cond
    -- Where `Array.isArray` holds, a record or `unknown` arm is the built-ins'
    -- `readonly unknown[]` (`arraySlice`).
    let arrays ← if arrayTested left then some <$> builtinArrayTy else pure none
    let H := conditionContext (SourceTypes.graph (← table)) scope Γ left andOp arrays
    let rhs ← compileConditionAtom recursive fc scope H right yes no
    compileConditionAtom recursive fc scope Γ left (if andOp then rhs else yes) (if andOp then no else rhs)
  | .not _ e =>
    let _ ← LoweringExpression.closureExpr recursive fc scope Γ cond
    compileConditionAtom recursive fc scope Γ e no yes
  | .read p f (.var _ name) =>
    -- The truthiness of a field of an immutable binding's object, where some
    -- arm of it leaves the field optional or unnamed, so that no fact about
    -- what the field holds is claimed (`IteratorResult` on `done`): the read,
    -- then a truthiness dispatch on its value, whose link to the field
    -- refines the object's arms on each edge (`fieldSlice`), as a
    -- discriminated union's are by a singleton test.
    match valueSlot scope name with
    | some k =>
      let G := SourceTypes.graph (← table)
      let T := Γ[k]?.getD []
      let fixes := fun (a : Tree) => (PositiveRules.expand G [a]).all fun c => match c with
        | .refs fs _ vs .. => (fs ++ vs).any (·.1 == f)
        | _ => false
      let refines := [true, false].any fun q =>
        (BranchRefinement.fieldSlice G T f .truthy q).length != T.length
      if refines && !T.all fixes then
        let A ← exprType fc cond
        let width := scope.length
        let drop := fun (t : Target) =>
          (⟨t.label, some ((t.mapping.getD (List.range width)).map (·+2))⟩ : Target)
        let dispatchNode ← emitAt p (.var 0) (.tagBind .truthy (drop yes) (drop no)) (A::Γ) A "tag-dispatch"
          (scope := held ⟨"",some p⟩ :: scope)
        emitAt p (.readAt f (.var k)) (.bind dispatchNode) Γ A "tag-dispatch" (scope := scope)
      else simple
    | none => simple
  | _ => simple

end LoweringAtoms
end Verification.SourceExtraction
