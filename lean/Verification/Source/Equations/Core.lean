import Verification.Source.Equations.Interning

/-! Section references follow `RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

mutual
/-- A source type as a union of trees in `ctx`. -/
partial def lowerType (ctx : Ctx) (term : Json) : M Union := do
  match ← str term "k" with
  | "atom" => atomLabels term
  | "literal" => mergeLiterals (← literalLabels term)
  | "unique" => uniqueLabels term
  | "union" | "intersection" => do
    let (U, meets) ← lowerArm ctx term
    unionOfArms ctx.site U meets
  | "parameter" =>
    fieldsExactly term ["k", "index", "span"]
    ctxValue ctx (.param (← (← field term "index").getNat?))
  | "self" =>
    fieldsExactly term ["k", "span"]
    ctxValue ctx .self
  | "binder" =>
    fieldsExactly term ["k", "name", "span"]
    let n ← str term "name"
    match ctx.binders.lookup n with
    | some b =>
      if b.pack && !b.packed then throw s!"{ctx.site}: an argument pack used as a value type"
      return b.value
    | none => throw s!"{ctx.site}: the type parameter {n} is not in scope"
  | "reference" => reference ctx term
  | "array" | "tuple" =>
    let readonly ← bool term "readonly"
    let store ← occurrence ctx "store" term (job := fun h c => .store h c term)
    let proto ← protoLabel
    return [mkApp (← arrayHead readonly proto) [[store]]]
  | "function" | "constructor" | "object" =>
    return [← occurrence ctx "literal" term (job := fun h c => .term h c term)]
  | "callable" =>
    fieldsExactly term ["k", "span"]
    return normUnion [← prim "function" (.arrs [] []), ← prim "constructor" (.ctors [])]
  | "scheme" =>
    let (names, packs, _) ← schemeBinders ctx.site term
    return [← occurrence ctx "scheme" term names (unitBinders names packs) fun h c => .scheme h c term]
  | "pack" => throw s!"{ctx.site}: a pack parameter outside a signature's rest"
  | k => throw s!"{ctx.site}: source type constructor '{k}' outside the graph fragment"

/-- A rest's type: a pack binder, or the pack of any number of actuals at an
element. -/
partial def lowerRest (ctx : Ctx) (term : Json) : M Union := do
  if kindOf term == some "pack" then
    fieldsExactly term ["k", "of", "span"]
    let operand ← field term "of"
    -- A declaration's own parameter: its argument, which every application
    -- completes with its array's argument lists (`packOf`).
    if kindOf operand == some "parameter" then
      return ← ctxValue ctx (.param (← (← field operand "index").getNat?))
    if kindOf operand != some "binder" then throw s!"{ctx.site}: a pack rest must name a type parameter"
    let n ← str operand "name"
    -- A binder whose argument lists are a placeholder of their own.
    if let some p := ctx.binders.lookup (packedName n) then return p.value
    match ctx.binders.lookup n with
    | some b =>
      if b.pack || b.packed then return b.value
      throw s!"{ctx.site}: a value parameter used as an argument pack"
    | none => throw s!"{ctx.site}: a pack parameter outside its generic method"
  return [← occurrence ctx "pack" term (job := fun h c => .pack h c [] (some term))]

/-- The built-in array prototype. -/
partial def protoLabel : M Tree := do
  let ds := (← get).doc
  if ds[0]?.any (ImplicitDependency.arrayProto.selects ·.identity) then
    return mkApp (← declHead 0) []
  let d : Draft := { name := "ArrayProto", kind := .proto, kinds := [] }
  let h ← alloc "proto" { d with body := some (.clauses [.refs [] [] []]) } fun _ => none
  return mkApp h []

/-- A declaration's head, its row lowered later. -/
partial def declHead (i : Nat) : M Nat := do
  let d := (← get).doc[i]!
  let kind := if ImplicitDependency.arrayProto.selects d.identity then HeadKind.proto else .declaration i
  alloc s!"decl|{i}" { name := d.name, kind, kinds := List.replicate d.parameters.size .value }
    fun h => some (.declaration h i)

/-- A reference: its arguments, one per parameter, applied to the
declaration's head or inlined into its alias. Its bounds are its written
application's (`writtenObligations`). -/
partial def reference (ctx : Ctx) (term : Json) : M Union := do
  let i ← referenceIndex term
  let argTerms := (← arr term "args").toList
  let supplied ← argTerms.mapM (lowerType ctx)
  let values ← application ctx i supplied
  -- A packed parameter's argument, its bound checked, is completed with its
  -- argument lists.
  let packed := (packedParameters (← get).doc[i]!.expression).eraseDups
  let values ← values.zipIdx.mapM fun (U, p) => do
    match packed.contains p, argTerms[p]? with
    | true, some t => return normUnion (U ++ (← packOf ctx t))
    | _, _ => return U
  instantiateDecl ctx i values

/-- The argument lists an argument of a packed parameter adds to it: an
array's or a tuple's, the lists a call collects into one of its arrays; none
for a packed binder or an enclosing declaration's packed parameter, whose
value holds them already; a binder's argument-list placeholder. Any other
instance is refused: its argument lists are no array's (PROGRAM-TYPING.md,
"Packed binders"). -/
partial def packOf (ctx : Ctx) (term : Json) : M Union := do
  let refuse := s!"{ctx.site}: the instance of a type parameter typing a value and a rest's argument list is no array or tuple type: the argument lists are an array or tuple type's, whose fresh arrays are its values"
  match kindOf term with
  | some "array" | some "tuple" => lowerRest ctx term
  | some "binder" =>
    let n ← str term "name"
    if let some p := ctx.binders.lookup (packedName n) then return p.value
    match ctx.binders.lookup n with
    | some b => if b.packed then return [] else throw refuse
    | none => throw refuse
  | some "parameter" =>
    let p ← (← field term "index").getNat?
    match ctx.decl with
    | some d =>
      if (packedParameters (← get).doc[d]!.expression).contains p then return []
      throw refuse
    | none => throw refuse
  | _ => throw refuse

/-- An application's arguments: one per parameter. A reference carries
every argument, the omitted ones completed with the defaults where the
reference is read; its bound obligations are the written application's
(`writtenObligations`). -/
partial def application (ctx : Ctx) (i : Nat) (supplied : List Union) : M (List Union) := do
  let d := (← get).doc[i]!
  if supplied.length != d.parameters.size then
    throw s!"{ctx.site}: {d.name} applied to {supplied.length} type arguments of {d.parameters.size}"
  return supplied

/-- A declaration at arguments: its head applied, or its alias inlined. An
alias met again before a constructor is an unguarded cycle (§8.3). -/
partial def instantiateDecl (ctx : Ctx) (i : Nat) (values : List Union) : M Union := do
  let d := (← get).doc[i]!
  if d.expression == .null then
    throw s!"{ctx.site}: {d.name} has no equation: each application states the type it denotes"
  if d.isHead then return [mkApp (← declHead i) values]
  if ctx.aliases.contains i then
    throw s!"{ctx.site}: unguarded alias cycle through {d.name}: a recursive alias must reach itself through an object, array, tuple or function type"
  let inner := { ctx with decl := some i, params := values.toArray, self := none }
  lowerType { inner with binders := [], aliases := i :: ctx.aliases } d.expression

/-- An intersection: meet labels over the product of the operands' unions
(§3.3). On ground rows only, where TypeScript reads a record met with a
function as one callable, that row is a literal head of its own. -/
partial def intersect (ctx : Ctx) (term : Json) : M Union := do
  fieldsExactly term ["k", "parts", "span"]
  let parts := (← (← arr term "parts").mapM (lowerType ctx)).toList
  meetOf parts (mentions [] term).isEmpty

/-- A type as the arms of its union: a union's arms, recursively, and an
intersection as one arm, whose meets are lowered without deciding emptiness;
whether the type has an intersection arm. `unionOfArms` decides emptiness for
the whole union. -/
partial def lowerArm (ctx : Ctx) (term : Json) : M (Union × Bool) := do
  match kindOf term with
  | some "union" =>
    let arms ← (← arr term "parts").toList.mapM (lowerArm ctx)
    return (← mergeLiterals (normUnion (arms.flatMap (·.1))), arms.any (·.2))
  | some "intersection" => return (← intersect ctx term, true)
  | _ => return (← lowerType ctx term, false)

/-- The intersection of unions (§3.3), as an arm of the union it is in: the
meet labels over their product, unless the operands are ground (`ground`)
and their rows clause rows: then, where TypeScript reads a record met with a
function as one callable, that row is a head of its own. An arm with no value
is empty here; its union decides whether the type has a value
(`unionOfArms`). -/
partial def meetOf (parts : List Union) (ground : Bool) : M Union := do
  if parts.any List.isEmpty then return []
  if parts.length == 1 then return parts[0]!
  if ground then
    if let some rows ← groundRows parts then
      let some last := rows.getLast? | throw "empty intersection"
      let met ← (rows.dropLast.foldrM sourceMeetLists last : Except String _)
      if met.isEmpty then return []
      let model := rows.dropLast.foldr meetLists last
      if met != model then return [← EquationLowering.ground "callable" met]
  return meetUnions parts

/-- The clauses of ground operands whose rows are clause rows, when every
operand's is. -/
partial def groundRows (parts : List Union) : M (Option (List (List (Clause (List Tree))))) := do
  let mut rows := []
  for U in parts do
    let mut cs := []
    for t in U do
      match t with
      | .app g args =>
        if !(← tryEnsure g) then return none
        match (← draft g).body with
        | some (.clauses c) => cs := cs ++ instantiateClauses c ((args.toList.map Types.toList))
        | _ => return none
      | _ => return none
    rows := rows ++ [cs]
  return some rows

/-- Lower a head's row now, if it is not being lowered. -/
partial def tryEnsure (h : Nat) : M Bool := do
  if (← draft h).body.isSome then return true
  if (← get).processing.contains h then return false
  match (← get).jobs.find? (·.head == h) with
  | some job =>
    modify fun s => { s with jobs := s.jobs.filter (·.head != h) }
    runJob job
    return true
  | none => return false

/-- A base's clauses in the deriving declaration's placeholders. Intersection
parts contribute all their clauses through the same source meet as bases. -/
partial def heritage (ctx : Ctx) (base : Json) : M (List (Clause (List Tree))) := do
  let labels ← lowerType ctx base
  labels.flatMapM (heritageTree ctx)

/-- Unfold a base application or meet its intersection parts. Parameter and
scheme rows cannot provide the statically declared members of a base. -/
partial def heritageTree (ctx : Ctx) (t : Tree) : M (List (Clause (List Tree))) := do
  match t with
  | .app g args =>
    if !(← tryEnsure g) then throw s!"{ctx.site}: cyclic heritage through {(← draft g).name}"
    match (← draft g).body with
    | some (.clauses cs) => return instantiateClauses cs (args.toList.map Types.toList)
    | _ => throw s!"{ctx.site}: a base whose row is not a clause row"
  | .meet parts =>
    let rows ← parts.toList.mapM (heritageTree ctx)
    rows.foldlM (fun acc row => (sourceMeetLists acc row : Except String _)) [.top]
  | .bound .. | .argument .. | .local .. | .var .. =>
    throw s!"{ctx.site}: a base that is a type parameter is outside heritage"

/-- An object type's clause. A
generic method is a head of its own, owned by the head whose row this is. -/
partial def objectClause (ctx : Ctx) (term : Json) : M (Clause (List Tree)) := do
  fieldsExactly term (objectMembers term)
  let hidden ← match term.getObjVal? "prototype" with
    | .ok t => do
      let P ← lowerType ctx t
      let keys ← (← arr t "fields").mapM fun f => do PropKey.decode (← field f "name")
      pure (some (P, keys.toList))
    | .error _ => pure none
  -- A host family's marker (HOST-FAMILIES.md, "The family contract"): a
  -- required readonly view of the model's `[[host]]` at the marker's string,
  -- which no allocation of the program owns.
  let marker ← match term.getObjVal? "host" with
    | .ok m => do
      let s ← m.getStr?
      pure [(Verification.hostKey, [← prim (Json.str s).compress (.strLit s)])]
    | .error _ => pure []
  let mut methods : List (MethodMembers.Sig (List Tree)) := []
  let mut all : Array (PropKey × List Tree × Bool × Bool) := #[]
  for f in ← arr term "fields" do
    let name ← PropKey.decode (← field f "name")
    if RequestJson.reservedKey name then
      throw s!"{ctx.site}: a declared member cannot use the model's internal key {repr name}"
    let ty ← field f "type"
    let optional ← bool f "optional"
    match (if optional then none else methodForms ty) with
    | some forms =>
      let mut calls : List (MethodArrow (List Tree)) := []
      let mut rests : List (MethodRestArrow (List Tree)) := []
      -- The types the host must meet, which every form states alike: the
      -- member states them once, for all its signatures.
      let mut receivers : Option (List (List Tree)) := none
      for form in forms do
        fieldsExactly form ["k", "receiver", "params", "rest", "result", "effect", "span"]
        let stated ← ((statedReceivers form).getD #[]).mapM (lowerType ctx)
        match receivers with
        | none => receivers := some stated.toList
        | some rs => if rs != stated.toList then
            throw s!"{ctx.site}: a method's signatures state its receiver unalike"
        let domains ← (← arr form "params").mapM (lowerType ctx)
        let rest ← field form "rest"
        let result ← lowerType ctx (← field form "result")
        let effect : CallEffects.Effect ← fromJson? (← field form "effect")
        if rest == .null then calls := calls ++ [⟨(), domains.toList, result, effect⟩]
        else rests := rests ++ [⟨(), (domains.toList, ← lowerRest ctx rest), result, effect⟩]
      methods := methods ++ [⟨name, calls, rests, [], receivers.getD []⟩]
    | none =>
      match (if optional then none else schemeMethod ty) with
      | some t =>
        let some o := ctx.owner | throw s!"{ctx.site}: a generic method outside a head"
        let (names, packs, _) ← (schemeBinders ctx.site t : Except String _)
        let owner ← draft o
        let key := (toJson name).compress
        let m ← alloc s!"method|{o}|{key}"
          { name := s!"{owner.name}.{key}", kind := .method o key, kinds := owner.kinds,
            binders := unitBinders names packs } fun m => some (.scheme m ctx t)
        let args := (List.range owner.kinds.length).map fun k => [Tree.argument k]
        methods := methods ++ [⟨name, [], [], [[mkApp m args]], []⟩]
      | none =>
        let value ← lowerType ctx ty
        all := all.push (name, value, ← bool f "readonly", optional)
  let fs := all.filterMap fun (n, v, r, o) => if o then none else some (n, v, r)
  let optional := all.toList.filterMap fun (n, v, r, o) =>
    if o then some (⟨n, r, v⟩ : OptionalField (List Tree)) else none
  let names := fs.toList.map (·.1) ++ optional.map (·.key) ++ methods.map (·.key)
  if names.eraseDups.length != names.length then throw s!"{ctx.site}: duplicate declaration field"
  let mut indexes : List (IndexKeys × List Tree) := []
  let mut cells : List (IndexKeys × List Tree) := []
  for (_, keys, index) in indexSignatures term do
    fieldsExactly index ["readonly", "value", "span"]
    let value ← lowerType ctx (← field index "value")
    indexes := indexes ++ [(keys, value)]
    if !(← bool index "readonly") then cells := cells ++ [(keys, value)]
  let writes := fs.toList.filterMap fun (name, value, readonly) =>
    if readonly then none else some (name, value)
  let views := fs.toList.filterMap (fun (name, value, readonly) =>
    if readonly then some (name, value) else none) ++ marker
  -- A family's stable members (HOST-FAMILIES.md, "Stable keys"): stated of a
  -- marked shape alone, each a required readonly member it states, distinct
  -- and at least one; the claims wire has no form for them.
  let stable ← match term.getObjVal? "stable" with
    | .ok s => do
      let names ← (← s.getArr?).toList.mapM fun n => do PropKey.decode n
      if marker.isEmpty then
        throw s!"{ctx.site}: a stable key is stated of a host family's marked shape alone"
      if names.isEmpty || names.eraseDups.length != names.length then
        throw s!"{ctx.site}: a shape's stable keys are distinct, and at least one"
      for k in names do
        unless fs.toList.any (fun (n, _, readonly) => n == k && readonly) do
          throw s!"{ctx.site}: the stable key {(toJson k).compress} is no required readonly member of its shape"
      pure names
    | .error _ => pure []
  let mut fixed : List (Arrow (List Tree)) := []
  let mut variadic : List (RestArrow (List Tree)) := []
  for call in ← arr term "calls" do
    fieldsExactly call ["k", "receiver", "params", "rest", "result", "effect", "span"]
    if (← str call "k") != "function" then throw s!"{ctx.site}: call signature is not a function"
    let recv ← field call "receiver"
    let receiver ← if recv == .null then pure [← top] else lowerType ctx recv
    let domains ← (← arr call "params").mapM (lowerType ctx)
    let rest ← field call "rest"
    let result ← lowerType ctx (← field call "result")
    let effect : CallEffects.Effect ← fromJson? (← field call "effect")
    if rest == .null then fixed := fixed ++ [⟨receiver, domains.toList, result, effect⟩]
    else variadic := variadic ++ [⟨receiver, (domains.toList, ← lowerRest ctx rest), result, effect⟩]
  if hidden.isSome && (!fixed.isEmpty || !variadic.isEmpty || !indexes.isEmpty) then
    throw s!"{ctx.site}: a prototype of hidden members is stated of a plain record only"
  if !marker.isEmpty && (hidden.isSome || !fixed.isEmpty || !variadic.isEmpty || !indexes.isEmpty) then
    throw s!"{ctx.site}: a host family's marker is stated of a plain record only"
  if fixed.isEmpty && variadic.isEmpty then
    if indexes.isEmpty then
      match hidden with
      | some (P, keys) =>
        return .refs writes [] (views ++ [(CallArguments.protoField, P)]) optional methods [⟨false, keys⟩]
      | none => return .refs writes [] views optional methods [] stable
    else return .dict writes [] views indexes optional methods [] cells
  else if !methods.isEmpty then throw s!"{ctx.site}: a callable object with methods needs a combined clause"
  else if !optional.isEmpty then throw s!"{ctx.site}: a callable object with an optional field needs a combined clause"
  else if !indexes.isEmpty || !views.isEmpty then
    throw s!"{ctx.site}: callable object with index or readonly field needs a combined clause"
  else if writes.isEmpty then return .arrs fixed variadic
  else return .callable writes [] fixed variadic

/-- A function type's clause. -/
partial def functionClause (ctx : Ctx) (term : Json) : M (Clause (List Tree)) := do
  fieldsExactly term ["k", "receiver", "params", "rest", "result", "effect", "span"]
  let recv ← field term "receiver"
  let receiver ← if recv == .null then pure [← top] else lowerType ctx recv
  let domains ← (← arr term "params").mapM (lowerType ctx)
  let restTerm ← field term "rest"
  let result ← lowerType ctx (← field term "result")
  let effect : CallEffects.Effect ← fromJson? (← field term "effect")
  if restTerm == .null then return .arrs [⟨receiver, domains.toList, result, effect⟩] []
  return .arrs [] [⟨receiver, (domains.toList, ← lowerRest ctx restTerm), result, effect⟩]

/-- The row a literal head's term states. -/
partial def termRow (ctx : Ctx) (term : Json) : M (GraphRow Tree (List Tree)) := do
  match ← str term "k" with
  | "object" => return .clauses [← objectClause ctx term]
  | "function" => return .clauses [← functionClause ctx term]
  | "constructor" =>
    -- A class value's type states its static fields (`statics`), each an
    -- invariant field of the class value, left out when it has none.
    let hasStatics := (term.getObjVal? "statics").isOk
    fieldsExactly term (["k", "params", "rest", "result", "effect", "span"] ++
      (if hasStatics then ["statics"] else []))
    let ps ← (← arr term "params").mapM (lowerType ctx)
    let restTerm ← field term "rest"
    let result ← lowerType ctx (← field term "result")
    let effect : CallEffects.Effect ← fromJson? (← field term "effect")
    -- A readonly one is a view, listed with `readonly: true`.
    let statics ← if !hasStatics then pure [] else do
      let fs ← arr term "statics"
      if fs.isEmpty then throw s!"{ctx.site}: a class value's empty static field list is left out"
      fs.toList.mapM fun f => do
        let readonly := (f.getObjVal? "readonly").isOk
        fieldsExactly f (["name", "type"] ++ (if readonly then ["readonly"] else []))
        if readonly then
          if (← field f "readonly") != .bool true then
            throw s!"{ctx.site}: a static field's readonly mark is `true`, left out otherwise"
        let key ← PropKey.decode (← field f "name")
        return (readonly, key, ← lowerType ctx (← field f "type"))
    let fields := statics.filterMap fun (ro, k, t) => if ro then none else some (k, t)
    let views := statics.filterMap fun (ro, k, t) => if ro then some (k, t) else none
    if restTerm == .null then return .clauses [.ctors [⟨(), ps.toList, result, effect⟩] [] fields [] views]
    return .clauses [.ctors [] [⟨(), (ps.toList, ← lowerRest ctx restTerm), result, effect⟩] fields [] views]
  | k => throw s!"{ctx.site}: no row for a '{k}' term"

/-- A pack parameter's bound, an array or a tuple of required positions: the
argument lists of any number of its element, or of its positions. -/
partial def packBound (ctx : Ctx) (bound : Json) : M Union := do
  match kindOf bound with
  | some "array" => return [← occurrence ctx "pack" (← field bound "element")
      (job := fun h c => .pack h c [] (some (bound.getObjValD "element")))]
  | some "tuple" =>
    if !(← arr bound "optional").isEmpty || (← field bound "rest") != .null then
      throw s!"{ctx.site}: the argument-pack bound is not represented; the contract cannot be erased"
    let required := (← arr bound "required").toList
    return [← occurrence ctx "packbound" bound (job := fun h c => .pack h c required none)]
  | _ => throw s!"{ctx.site}: the argument-pack bound is not represented; the contract cannot be erased"

/-- A scheme's row: its binders the head's locals, its bounds read outside
them (§3.1). -/
partial def schemeRow (ctx : Ctx) (term : Json) : M (GraphRow Tree (List Tree)) := do
  let (names, packs, resolution) ← (schemeBinders ctx.site term : Except String _)
  let bs ← arr term "binders"
  let inner : Ctx := { ctx with binders := (names.zipIdx.map fun ((n : String), (k : Nat)) =>
    (n, ({ pack := packs.contains n, value := [.local k] } : Binding))) ++ ctx.binders }
  let mut bounds : List (Tree × List Tree) := []
  for b in bs.toList do
    let n ← str b "name"
    let k := names.idxOf n
    let bound ← field b "bound"
    if bound == .null then
      if !packs.contains n then bounds := bounds ++ [(.local k, [← ground "source" sourceValueClauses])]
      continue
    if packs.contains n then
      bounds := bounds ++ [(.local k, ← packBound ctx bound)]
    else bounds := bounds ++ [(.local k, ← lowerType ctx bound)]
  let source := [← top]
  let binders := inner.binders.map fun (n, b) =>
    if b.pack then (n, b) else match b.value with
    | [_] => if names.contains n then
        (n, { b with value := meetUnions [b.value, source] })
      else (n, b)
    | _ => (n, b)
  let views := (inner.binders.zip binders).filterMap fun ((_, raw), (_, view)) => do
    let [p] := raw.value | none
    let [q] := view.value | none
    let B ← bounds.lookup p
    return (q, B)
  let inner := { inner with binders, bounds := ctx.bounds ++ bounds ++ views }
  let mut fixed : List (Arrow (List Tree)) := []
  let mut rests : List (RestArrow (List Tree)) := []
  -- Call signatures, or construct signatures (`new <T>(…) => R`), each an
  -- arrow's arguments, result and effect: a construct signature has no
  -- receiver.
  let sigs ← arr term "signatures"
  let construct := sigs.toList.any (kindOf · == some "constructor")
  if construct && !sigs.toList.all (kindOf · == some "constructor") then
    throw s!"{ctx.site}: a scheme of call and construct signatures together is outside the fragment"
  if construct && !resolution.isEmpty then
    throw s!"{ctx.site}: a resolution-qualified construct scheme is outside the fragment"
  for f in sigs do
    let recv ← if construct then do
        fieldsExactly f ["k", "params", "rest", "result", "effect", "span"]
        pure []
      else do
        fieldsExactly f ["k", "receiver", "params", "rest", "result", "effect", "span"]
        lowerType inner (← field f "receiver")
    let ps ← (← arr f "params").toList.mapM (lowerType inner)
    let restTerm ← field f "rest"
    let res ← lowerType inner (← field f "result")
    let effect : CallEffects.Effect ← fromJson? (← field f "effect")
    if restTerm == .null then fixed := fixed ++ [⟨recv, ps, res, effect⟩]
    else rests := rests ++ [⟨recv, (ps, ← lowerRest inner restTerm), res, effect⟩]
  return .scheme ((List.range names.length).map Tree.local) fixed bounds rests resolution construct

/-- A declaration's row: the source meet of its own members with its bases'
rows (§8.1, heritage). -/
partial def declarationRow (h i : Nat) : M (GraphRow Tree (List Tree)) := do
  let d := (← get).doc[i]!
  let n := d.parameters.size
  let args := (List.range n).map fun k => [Tree.argument k]
  let ctx : Ctx :=
    { decl := some i, params := args.toArray, self := some [mkApp h args], owner := some h,
      site := d.name }
  let own := d.expression
  let empty := kindOf own == some "object" &&
    ((own.getObjValAs? (Array Json) "fields").toOption.getD #[1]).isEmpty &&
    ((own.getObjValAs? (Array Json) "calls").toOption.getD #[1]).isEmpty &&
    (indexSignatures own).isEmpty && (own.getObjVal? "prototype").toOption.isNone &&
    (own.getObjVal? "host").toOption.isNone
  let mut rows ← if empty && !d.bases.isEmpty then pure [.top]
    else if kindOf own == some "object" then pure [← objectClause ctx own]
    else heritage ctx own
  for base in d.bases do
    let inherited ← heritage ctx base
    rows ← (sourceMeetLists rows inherited : Except String _)
    if rows.isEmpty then throw s!"{d.name}: {emptyMeet}"
  return .clauses rows

/-- A unit head's row: a scheme binding its binders, stating no signature.
The head owns the unit's binders (§8.1); the unit's type is read from its
annotations and a generic value's from its lowered type
(`GenericValue`), never from this row, so it states nothing further, and a
bound naming another binder of the unit (`U extends T`) needs no scheme bound
(the unit reads it as a meet, `SourceClaimJson.binderRows`). -/
partial def unitRow (_ctx : Ctx) (node : Json) : M (GraphRow Tree (List Tree)) := do
  let tps := (node.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
  let parameters ← tps.toList.mapM fun p => do
    let name ← str p "name"
    let resolution ← (fromJson? (← field p "resolution") : Except String (Option ResolutionWire.Slots))
    return (name, resolution)
  ResolutionWire.validateOwnership parameters
  let names := parameters.flatMap fun (n, s) => ResolutionWire.ownedNames n s
  return .scheme ((List.range names.length).map Tree.local) [] [] [] (ResolutionWire.groups parameters)

/-- Producer row `n`'s head, lifted over the binder names it mentions
freely; its row is a job. -/
partial def rowHead (n : Nat) : M Nat := do
  let P := (← get).rows
  let own := P.own[n]!
  alloc s!"row|{n}"
    { name := s!"row {n}", kind := if own.isEmpty then .literal else .scheme,
      kinds := P.free[n]!.map fun _ => .value,
      binders := own.map fun b => ⟨b, if P.packed[n]!.contains b then .packed else .value⟩ }
    fun h => some (.row h n)

/-- Producer row `n` as a label in `scope`: its head applied to what its free
binder names are there, a name out of scope its placeholder. The primitive
rows are the primitive heads. -/
partial def rowLabel (scope : List (String × Binding)) (n : Nat) : M Union := do
  let P := (← get).rows
  if n < 4 then return [mkApp n []]
  if n ≥ P.rows.size then throw s!"source claims: no row {n}"
  let h ← rowHead n
  let args ← P.free[n]!.mapM fun name => do
    match scope.lookup name with
    | some b => pure b.value
    | none => pure [← placeholder name .value]
  return [mkApp h args]

/-- Producer row `n`'s row: its free names its arguments, its own binders
its locals. -/
partial def rowBody (n : Nat) : M (GraphRow Tree (List Tree)) := do
  let P := (← get).rows
  let scope : List (String × Binding) :=
    (P.own[n]!.zipIdx.map fun (name, j) =>
      (name, ({ pack := false, value := [.local j], packed := P.packed[n]!.contains name } : Binding))) ++
    -- A packed binder's argument lists are its own row.
    (P.own[n]!.zipIdx.filterMap fun (name, j) => if P.packed[n]!.contains name then
      some (name ++ "#pack", ({ pack := false, value := [.local j] } : Binding)) else none) ++
    (P.free[n]!.zipIdx.flatMap fun (name, i) =>
      [(name, ({ pack := false, value := [.argument i] } : Binding)),
       (name ++ "#pack", ({ pack := false, value := [.argument i] } : Binding))])
  let row := P.rows[n]!
  -- Only type operands are unions. Scheme binder lists and bound pairs
  -- carry binding structure, so their enumeration is not a union spelling.
  let operands : List (List Json) := match row with
    | .clauses cs => cs.flatMap Clause.operands
    | .scheme _ sigs bounds rests _ _ =>
      sigs.flatMap Arrow.operands ++ bounds.map (·.2) ++ rests.flatMap RestArrow.operands
    | .param .. | .meet .. => [] -- producerRows refuses these row kinds.
  let lowered ← operands.mapM fun A => do return (A, ← claimUnion scope (.arr A.toArray))
  let own := P.own[n]!
  let binder (b : Json) : Tree := match (b.getObjValAs? String "binder").toOption.bind own.idxOf? with
    | some j => .local j
    | none => .local 0
  return row.map binder fun A => (lowered.lookup A).getD []

/-- The canonical order of source-claims labels, on their spelling: rows by
index, then declarations, intersections, arrays and binders, each by its
fields in order, lists lexicographically. -/
partial def claimCmp (a b : Json) : Ordering :=
  let rank (j : Json) : Nat := match j with
    | .num _ => 0
    | _ => if (j.getObjVal? "decl").isOk then 1 else if (j.getObjVal? "meet").isOk then 2
      else if (j.getObjVal? "array").isOk then 3 else 4
  let lex : Ordering → Ordering → Ordering := fun | .eq, o => o | o, _ => o
  let list (f : Json → Json → Ordering) : List Json → List Json → Ordering := fun as bs =>
    let rec go : List Json → List Json → Ordering
      | [], [] => .eq
      | [], _ :: _ => .lt
      | _ :: _, [] => .gt
      | a :: as, b :: bs => lex (f a b) (go as bs)
    go as bs
  let arr (j : Json) : List Json := ((j.getArr?).toOption.getD #[]).toList
  let labels (x y : Json) : Ordering := list claimCmp (arr x) (arr y)
  let field (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD (.arr #[])
  match rank a, rank b with
  | 0, 0 => compare ((a.getNat?).toOption.getD 0) ((b.getNat?).toOption.getD 0)
  | 1, 1 => lex (compare ((field a "decl").getNat?.toOption.getD 0) ((field b "decl").getNat?.toOption.getD 0))
      (list labels (arr (field a "args")) (arr (field b "args")))
  | 2, 2 => list labels (arr (field a "meet")) (arr (field b "meet"))
  | 3, 3 => lex (labels (field a "array") (field b "array"))
      (compare ((field a "readonly").getBool?.toOption.getD false) ((field b "readonly").getBool?.toOption.getD false))
  | 4, 4 => compare ((field a "binder").getStr?.toOption.getD "") ((field b "binder").getStr?.toOption.getD "")
  | r, s => compare r s

/-- A source-claims label: a `decl` application (arity full), a `meet`, an
`array` of its store, or a `binder`: the binder `scope` gives the name, else
its name placeholder. A `types` row index is the producer's row, which the
claims map in the same scope (`rowLabel`). -/
partial def claimLabel (scope : List (String × Binding)) (j : Json) : M Union := do
  let get? (name : String) : Option Json := (j.getObjVal? name).toOption
  match j with
  | .num _ => rowLabel scope (← j.getNat?)
  | .obj _ =>
    if let some k := get? "decl" then
      fieldsExactly j (if (j.getObjVal? "args").isOk then ["decl", "args"] else ["decl"])
      let i ← k.getNat?
      let ds := (← get).doc
      if i ≥ ds.size then throw s!"source claims: a declaration's label names no declaration: {i}"
      let spelled ← match j.getObjVal? "args" with
        | .ok a => do
          let a ← a.getArr?
          if a.isEmpty then throw "source claims: a nullary declaration's label leaves its arguments out"
          pure a.toList
        | .error _ => pure []
      let args ← spelled.mapM (claimUnion scope)
      if args.length != ds[i]!.parameters.size then
        throw s!"source claims: a declaration's label has one argument per parameter: {ds[i]!.name} has {ds[i]!.parameters.size}, given {args.length}"
      let ctx : Ctx := { binders := scope, site := "source claims" }
      let values ← application ctx i args
      instantiateDecl ctx i values
    else if let some ps := get? "meet" then
      fieldsExactly j ["meet"]
      let parts ← (← ps.getArr?).toList.mapM (claimUnion scope)
      if parts.length < 2 then throw "source claims: a meet has at least two parts"
      meetOf parts (parts.all (·.all fun t => !treeOpen t && !hasRigid t))
    else if let some s := get? "array" then
      fieldsExactly j ["array", "readonly"]
      let store ← claimUnion scope s
      return [mkApp (← arrayHead (← bool j "readonly") (← protoLabel)) [store]]
    else if let some n := get? "binder" then
      fieldsExactly j ["binder"]
      let n ← n.getStr?
      if n.isEmpty then throw "source claims: a binder's label names it"
      match scope.lookup n with
      | some b =>
        if b.pack && !b.packed then throw s!"source claims: the argument pack {n} used as a value type"
        return b.value
      | none =>
        -- A binder's argument lists, `T#pack`: a pack binder's own row.
        match (n.dropSuffix? "#pack").bind fun base => scope.lookup base.toString with
        | some b =>
          if b.pack then return b.value
          throw s!"source claims: the value binder {n} used as argument lists"
        | none => return [← placeholder n (if n.endsWith "#pack" then .packed else .value)]
    else throw s!"source claims: not a label: {j.compress}"
  | _ => throw s!"source claims: not a label: {j.compress}"

/-- A union of source-claims labels. -/
partial def claimUnion (scope : List (String × Binding)) (j : Json) : M Union := do
  let ls := (← j.getArr?).toList
  unless (ls.zip ls.tail).all (fun (a, b) => claimCmp a b == .lt) do
    throw "source claims: a label list is in canonical order, each label once"
  unionOfArms "source claims" (normUnion ((← ls.mapM (claimLabel scope)).flatten))
    (ls.any fun l => (l.getObjVal? "meet").isOk)
/-- Lower one pending row. -/
partial def runJob (job : Job) : M Unit := do
  let h := job.head
  if (← draft h).body.isSome then return
  modify fun s => { s with processing := h :: s.processing }
  let row ← match job with
    | .declaration h i => declarationRow h i
    | .term _ ctx term => termRow ctx term
    | .store _ ctx term =>
      let readonly ← bool term "readonly"
      let presence : ArrayPresence ← fromJson? (← field term "presence")
      if kindOf term == some "array" then
        fieldsExactly term ["k", "readonly", "presence", "element", "span"]
        let element ← lowerType ctx (← field term "element")
        pure (.clauses [.list ⟨[], [], some element, readonly, presence⟩ []])
      else
        fieldsExactly term ["k", "readonly", "presence", "required", "optional", "rest", "span"]
        let required ← (← arr term "required").toList.mapM (lowerType ctx)
        let optional ← (← arr term "optional").toList.mapM (lowerType ctx)
        let restTerm ← field term "rest"
        let rest ← if restTerm == .null then pure none else some <$> lowerType ctx restTerm
        pure (.clauses [.list ⟨required, optional, rest, readonly, presence⟩ []])
    | .pack _ ctx required rest =>
      let required ← required.mapM (lowerType ctx)
      let rest ← rest.mapM (lowerType ctx)
      pure (.clauses [.pack ⟨required, [], rest, false, .dense⟩ []])
    | .scheme _ ctx term => schemeRow ctx term
    | .unit _ ctx node => unitRow ctx node
    | .row _ n => rowBody n
  setBody h row
  modify fun s => { s with processing := s.processing.erase h }
end

/-- Lower every pending row. -/
partial def drain : M Unit := do
  match (← get).jobs with
  | [] => return
  | job :: rest =>
    modify fun s => { s with jobs := rest }
    runJob job
    drain


end Verification.EquationLowering
