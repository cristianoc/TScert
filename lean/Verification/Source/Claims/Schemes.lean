import Verification.Source.Claims.Wire
import Verification.Source.Claims.Diagnostics
import Verification.Source.FragmentTypes

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)
section
variable {ι : Type} [Labels ι]

private def claimHasScheme : ClaimType ι → Bool
  | .scheme .. => true
  | _ => false

def Function.hasScheme (f : Function ι) : Bool :=
  claimHasScheme f.result || f.params.any (claimHasScheme ·.type) ||
    f.entries.any (fun e => e.bindings.any (claimHasScheme ·.type)) ||
    f.expressions.any (claimHasScheme ·.type) || f.contracts.any (claimHasScheme ·.type)

/-- A generic module value: a generic module function, a generic class or a
generic imported value. `instantiate` gives, for ground arguments in claim
form, the value's type at those arguments and each binder's bound at them. -/
structure Instantiable where
  name : String
  pos : Span
  binders : List String
  resolution : List ResolutionSlots := []
  instantiate : List (String × Json) → SourceTypes.Lowering (Json × List (String × Option Json))

/-- A claim with the binder names `θ` names read as it gives them: the source
spells a binder by its name, and a unit or closure decides what the name
stands for (`EquationStore.rebind`). A nested scheme's own binders shadow. -/
partial def rebindClaim (T : EquationStore.State) (θ : List (String × List Tree)) : ClaimType Tree → ClaimType Tree
  | .labels A => .labels (rebindLabels T θ A)
  | .union ts => .union (ts.map (rebindClaim T θ))
  | .array e => .array (rebindClaim T θ e)
  | .scheme tps rc ps rest r effect =>
    let θ := θ.filter fun q => !EquationLowering.ownsName (tps.flatMap ResolutionWire.Binder.ownedNames) q.1
    .scheme (tps.map fun q => { q with bound := q.bound.map (rebindClaim T θ) }) (rebindClaim T θ rc)
      (ps.map (rebindClaim T θ)) (rest.map (rebindClaim T θ)) (rebindClaim T θ r) effect
  | c => c
where
  rebindLabels (T : EquationStore.State) (θ : List (String × List Tree)) (A : List Tree) : List Tree :=
    (A.flatMap (EquationStore.rebind T θ)).mergeSort Labels.le |>.eraseDups

/-- What a point asserts of each field, its binders read as `θ` gives them. -/
def rebindCurrent (T : EquationStore.State) (θ : List (String × List Tree)) (c : Option (CurrentFields Tree)) :
    Option (CurrentFields Tree) :=
  c.map (·.map fun (k, A) => (k, rebindClaim.rebindLabels T θ A))

namespace Scheme

/-- Ground a claim, interning any callable it contains. Only after substitution
does a rigid arrow such as `() => T` have a graph row. -/
private partial def groundIn (T : EquationStore.State) :
    ClaimType Tree → Except String (EquationStore.State × List Tree)
  | .union ts => do
      let (T, arms) ← ts.foldlM (fun (T, acc) t => do
        let (T, A) ← groundIn T t
        pure (T, acc ++ A)) (T, [])
      pure (T, arms.eraseDups.mergeSort Labels.le)
  | .labels A => pure (T, A)
  | .array e => do
      let (T, E) ← groundIn T e
      let (T, store) := EquationStore.intern T [.list ⟨[], [], some E, false, .readable⟩ []]
      let (T, array) := EquationStore.intern T [SourceTypes.arrayOf T store false]
      pure (T, [array])
  | .scheme [] rc ps rest r effect => do
      let (T, rc) ← groundIn T rc
      let (T, ps) ← ps.foldlM (fun (T, acc) p => do
        let (T, a) ← groundIn T p
        pure (T, acc ++ [a])) (T, [])
      let (T, r) ← groundIn T r
      let (T, clause) ← match rest with
        | none => pure (T, PositiveNormalization.Clause.arrs [⟨rc, ps, r, effect⟩] [])
        | some e => do
          -- A rest's type is the pack of any number of actuals at its element.
          let (T, E) ← groundIn T e
          let (T, pack) := EquationStore.intern T [.pack ⟨[], [], some E, false, .dense⟩ []]
          pure (T, PositiveNormalization.Clause.arrs [] [⟨rc, (ps, [pack]), r, effect⟩])
      let (T, l) := EquationStore.intern T [clause]
      pure (T, [l])
  | .param name => throw s!"still the rigid parameter '{name}'"
  | .scheme .. => throw "a scheme is not a ground type"
  | .unavailable reason => throw reason

private def groundOf (role : String) : ClaimType ι → Except String (List ι)
  | .array _ => throw s!"{role} requires grounding an array"
  | .union _ => throw s!"{role} requires grounding a union"
  | .labels A => pure A
  | .param name => throw s!"{role} is still the rigid parameter '{name}'"
  | .scheme .. => throw s!"{role} is a scheme, not a ground type"
  | .unavailable reason => throw reason

/-- Capture-avoiding: a nested scheme's own binders shadow the substitution. -/
private partial def subst (θ : List (String × (ClaimType ι))) : ClaimType ι → ClaimType ι
  | .array e => .array (subst θ e)
  | .union ts => .union (ts.map (subst θ))
  | .param name => (θ.lookup name).getD (.param name)
  | .scheme tps rc ps rest r effect =>
      let inner := θ.filter fun q => !EquationLowering.ownsName (tps.flatMap ResolutionWire.Binder.ownedNames) q.1
      .scheme (tps.map fun q => { q with bound := q.bound.map (subst inner) }) (subst inner rc) (ps.map (subst inner))
        (rest.map (subst inner)) (subst inner r) effect
  | c => c

/-- Explicit type arguments are a requirement on a call's instance: the call
is typed at the instance they state, binder by binder in declaration order,
even where another would fit. `θ` is the claimed instance, ground. -/
def explicitInstance (T : EquationStore.State) (pos : Span) (binders : List String)
    (written : List Json) (θ : List (String × List Tree)) :
    Except (DirectObligation.Failure Tree × EquationStore.State) EquationStore.State := do
  let refuse (reason : String) := (DirectObligation.Failure.refusal pos .schemeElimination reason, T)
  if written.length > binders.length then
    throw (refuse "more explicit type arguments than the callee has binders")
  let mut T := T
  for (binder, annotation) in binders.zip written do
    let (stated, grown) ← ((Fragment.translate annotation).run T).mapError refuse
    T := grown
    let some claimed := θ.lookup binder | throw (refuse s!"no type argument for '{binder}'")
    for (A, B) in [(stated, claimed), (claimed, stated)] do
      match withinResult T A B with
      | .established _ => pure ()
      | .notEstablished =>
        throw (refuse "the call's instance is not the one its explicit type arguments state")
      | .exhausted rounds visited =>
        throw (.exhausted ⟨pos, .schemeElimination, .subtyping pos A B⟩
          T.subtypeBudget.rounds rounds visited, T)
  return T

/-- Check a proposed resolution instance in the frozen source equations. The
associated types are computed by the descriptor checker, never supplied as
independent type arguments. The observation is `none` where the checked
observation is a family no source type names, and the result is `none` where
the certificate establishes only an observation. -/
def resolutionInstance (T : EquationStore.State) (source : Option (SchemeRow Tree))
    (sourceNames : List String) (A : List Tree) (certificate : ResolutionWire.Certificate) :
    Except String (Option (List Tree) × Option (List Tree)) := do
  let F ← EquationStore.freeze T
  let some context := F.store.resolution
    | throw "resolution instance requires the native descriptor domain"
  let c := context.1
  let labels := EquationLowering.closedUnion F.equations "resolution instance"
  let mut scope : List (SourceResolution.Binding F.equations) := []
  if let some raw := source then
    if sourceNames.length != raw.binders.length then
      throw "resolution scope names do not match its binders"
    let source : SchemeRow (EquationGraphs.Label F.equations.signature) := {
      binders := ← labels raw.binders
      signatures := []
      bounds := ← raw.bounds.mapM fun (b, U) => do
        return (← EquationLowering.closedLabel F.equations "resolution bound" b, ← labels U)
      resolution := raw.resolution }
    for group in source.resolution do
      let some name := sourceNames[group.input]? | throw "resolution input slot is missing"
      let some binding := SourceResolution.lexicalBinding c source name group
        | throw "invalid lexical resolution group"
      scope := scope ++ [binding.binding]
  let input ← labels A
  let some checked := SourceResolution.check c scope (StoreView.images F.store) 256 input certificate
    | throw "resolution certificate does not establish its input, observation and stable result"
  return (checked.observation.map (·.map (·.val)), checked.result.map (·.map (·.val)))

/-- A generic module value reached from a unit (a generic module function,
or a generic imported one): the unit's calls name its instances. Each call's
type arguments must be ground and name exactly its binders, and every bound,
at those arguments, must hold by the graph's certified subtyping. Each instance
is the signature at those arguments, a ground callable; the slot holds them
all as one callable with several signatures. A generic module function is
certified for every admissible instantiation by its own unit, and an imported
one is assumed at its declared type, so each instance, and their conjunction,
holds of the value. Returns the grown table, the slot's type in claim form,
and the spans of the callee reads and of the calls. A failure carries the table
its labels index: translating a bound may grow it. -/
def moduleInstances (T : EquationStore.State) (g : Instantiable)
    (unit : List Fragment.Stmt) (claims : Function Tree)
    (source : Option (SchemeRow Tree) := none) (sourceNames : List String := []) :
    Except ((DirectObligation.Failure Tree) × EquationStore.State)
      (EquationStore.State × Json × List Span × List Span) := do
  let refuse (pos : Span) (reason : String) : DirectObligation.Failure Tree × EquationStore.State :=
    (.refusal pos .schemeElimination reason, T)
  let hidden := g.resolution.flatMap (·.associated)
  let publicNames := g.binders.zipIdx.filterMap fun (n, i) => if hidden.contains i then none else some n
  let calls := (unit.flatMap Fragment.Stmt.callees).filter (·.2.2.1 == g.name)
  let graph (A : List Tree) : Json := Json.mkObj [("top", toJson false),
    ("atoms", toJson (A.map fun l => Json.mkObj [("a", toJson "graph"), ("label", toJson l)]))]
  let sites ← calls.flatMapM fun (pos, _, _, written) => do
    let occurrences := claims.expressions.filter (·.pos == pos)
    if occurrences.isEmpty then throw (refuse pos s!"a call to the generic function '{g.name}' needs its type arguments")
    occurrences.mapM fun e => do
      let some inst := e.instantiate
        | throw (refuse pos s!"a call to the generic function '{g.name}' needs its type arguments")
      let given := inst.map (·.name)
      if given.eraseDups.length != given.length then throw (refuse pos "duplicate type argument")
      if given.length != publicNames.length || given.any (!publicNames.contains ·) then
        throw (refuse pos s!"type arguments do not instantiate exactly the binders of '{g.name}'")
      let θ ← inst.flatMapM fun i => do
        let A ← (groundOf s!"the type argument for '{i.name}'" i.type).mapError (refuse pos)
        match g.resolution.find? (fun q => g.binders[q.input]? == some i.name), i.resolution with
        | none, none => pure [(i.name, A)]
        | some group, some evidence =>
          let (O, R) ← (resolutionInstance T source sourceNames A evidence.certificate).mapError (refuse pos)
          let some observation := g.binders[group.observation]? | throw (refuse pos "missing observation binder")
          -- An awaitable binder takes no result; a resolvable one needs it.
          let result ← match group.result with
            | none => pure []
            | some slot =>
              let some result := g.binders[slot]? | throw (refuse pos "missing result binder")
              let some R := R
                | throw (refuse pos "resolution certificate does not establish its input, observation and stable result")
              pure [(result, R)]
          match O with
          | some O => pure ([(i.name, A), (observation, O)] ++ result)
          -- An unnamed observation instantiates only a value whose type
          -- does not mention it (`unnamedObservation`).
          | none => pure ((i.name, A) :: result)
        | _, _ => throw (refuse pos "resolution evidence must match the source parameter's qualification")
      pure (pos, θ, written)
  let mut T := T
  let mut seen : List (List (String × List Tree)) := []
  let mut instances : List Json := []
  for (pos, θ, written) in sites do
    T ← explicitInstance T pos publicNames written θ
    if seen.contains θ then continue
    seen := seen ++ [θ]
    let ((callable, bounds), grown) ← ((g.instantiate (θ.map fun (n, A) => (n, graph A))).run T).mapError (refuse pos)
    T := grown
    -- **Unnamed observation.** A descriptor whose observation no source type
    -- names instantiates the value only where its type is the same at every
    -- observation: placing one changes nothing.
    for group in g.resolution do
      let some observation := g.binders[group.observation]? | throw (refuse pos "missing observation binder")
      if (θ.lookup observation).isNone then
        let ((placed, _), grown) ← ((g.instantiate ((θ ++ [(observation, [])]).map fun (n, A) => (n, graph A))).run T).mapError (refuse pos)
        T := grown
        if placed != callable then
          throw (refuse pos s!"the observation of this resolution instance is named by no source type, and the type of '{g.name}' reads it")
    for (n, bound) in bounds do
      if let some upper := bound then
        let some actual := θ.lookup n | throw (refuse pos s!"no type argument for '{n}'")
        let (required, grown) ← ((Fragment.translate upper).run T).mapError (refuse pos)
        T := grown
        let G := SourceTypes.graph T
        let obligation : DirectObligation.Located Tree :=
          ⟨pos, .schemeElimination, .subtyping pos actual required⟩
        match CertificateProducer.comparisonUsing G (StoreView.images T) actual required with
        | .established _ => pure ()
        | .notEstablished => throw (.obligation obligation, T)
        | .exhausted rounds visited =>
          throw (.exhausted obligation T.subtypeBudget.rounds rounds visited, T)
    let some atom := (callable.getObjVal? "atoms").toOption.bind (fun a => (a.getArr?.toOption.bind (·[0]?)))
      | throw (refuse pos s!"'{g.name}' is not one callable")
    instances := instances ++ [atom]
  let some first := instances.head? | throw (refuse g.pos s!"'{g.name}' has no call to instantiate")
  -- Instances that are graph labels, a signature with a pack rest, conjoin
  -- as one callable whose signatures are all of theirs.
  let graphLabel (atom : Json) : Option Tree := do
    if atom.getObjValD "a" != .str "graph" then none
    (fromJson? (atom.getObjValD "label")).toOption
  let callable ← match instances.mapM graphLabel with
    | some labels@(_ :: _ :: _) => do
      let G := SourceTypes.graph T
      let parts ← labels.mapM fun l => match PositiveRules.expand G [l] with
        | [.arrs L S] => pure (L, S)
        | _ => throw (refuse g.pos s!"'{g.name}' is not one callable")
      let (T', label) := EquationStore.intern T [.arrs (parts.flatMap (·.1)) (parts.flatMap (·.2))]
      T := T'
      pure (Json.mkObj [("a", toJson "graph"), ("label", toJson label)])
    | _ =>
      -- An instance with several signatures is a conjunction already: the
      -- whole is one conjunction of every instance's signatures.
      let parts := instances.flatMap fun i => (CellClaims.conjuncts i).toOption.getD [i]
      match parts with
      | [one] => pure one
      | one :: more => pure (one.setObjVal! "and" (toJson more))
      | [] => pure first
  return (T, Json.mkObj [("top", toJson false), ("atoms", toJson [callable])],
    calls.map (·.2.1), calls.map (·.1))

/-- A generic module value read as a value, not called: its slot is the scheme
its declaration states, `∀p⃗ ≤ β. Σ`, with its binders fresh parameter rows,
of call signatures for a function and of construct signatures for a class,
whose static fields the scheme does not state.
A generic module function is certified at every assignment of its binders, a
generic class's construct code by the initialization unit at every assignment
of the class's binders, and an imported one is assumed at its declared type,
so the value meets its signatures at every instance within the bounds, which
is scheme membership.
A bound reading another binder, a resolution-qualified binder and a binder
typing a rest are refused: the scheme row states none of them. Returns the
grown table and the slot's type in claim form. -/
def moduleScheme (T : EquationStore.State) (g : Instantiable) :
    Except String (EquationStore.State × Json) := do
  if !g.resolution.isEmpty then
    throw s!"'{g.name}' read as a value is a resolution-qualified scheme, which a scheme row does not state"
  let (T, ps) := EquationStore.binders T g.binders
  let graph (A : List Tree) : Json := Json.mkObj [("top", toJson false),
    ("atoms", toJson (A.map fun l => Json.mkObj [("a", toJson "graph"), ("label", toJson l)]))]
  let at_ (rows : List Tree) := g.binders.zip rows |>.map fun (n, l) => (n, graph [l])
  -- The bounds, read outside the binders.
  let ((_, bounds), T) ← g.instantiate (at_ ps) T
  let (T₁, top) := EquationStore.intern T [.source]
  let free (B : List Tree) : Bool :=
    B.any fun l => EquationStore.substitute (ps.map fun p => (p, top)) l != [l]
  let mut T := T₁
  let mut rows : List (Tree × List Tree) := []
  let mut reads : List Tree := []
  for (n, p) in g.binders.zip ps do
    let B ← match bounds.lookup n with
      | some (some upper) => do
        let (B, grown) ← (Fragment.translate upper).run T
        T := grown
        if free B then
          throw s!"a bound of '{g.name}' reads another of its binders, which a scheme row's bound does not"
        pure B
      | _ => pure [top]
    rows := rows ++ [(p, B)]
    -- A binder is read as its meet with its bound, as a generic closure's
    -- scheme reads it (`schemeRowOf`): at an instance within the bound, the
    -- meet is the instance.
    let G := SourceTypes.graph T
    if G.plainTy B then
      let (grown, m) := EquationStore.bounded T p (B.flatMap G) []
      T := grown
      reads := reads ++ [m]
    else reads := reads ++ [p]
  let ((callable, _), grown) ← g.instantiate (at_ reads) T
  let (A, grown) ← (Fragment.translate callable).run grown
  -- A generic function's call signatures, or a generic class's construct
  -- signatures, each an arrow's arguments, result and effect.
  let (L, S, construct) ← match PositiveRules.expand (SourceTypes.graph grown) A with
    | [.arrs L S] => pure (L, S, false)
    | [.ctors L S _ _ _] => pure (L.map (·.withReceiver []), S.map (·.withReceiver []), true)
    | _ => throw s!"'{g.name}' read as a value is not one callable or one class value"
  let (grown, label) := EquationStore.scheme grown ps L rows S construct
  return (grown, graph [label])

/-- A claim with a generic unit's binders read as their parameter rows, in
ground form. A claim that does not ground keeps the reason at its site, as
`ground` does, so only a site the extraction reads refuses. -/
private def atRows (θ : List (String × (ClaimType Tree))) (t : ClaimType Tree) :
    StateM EquationStore.State (ClaimType Tree) := modifyGet fun T =>
  let named := θ.filterMap fun (n, c) => match c with
    | .labels A => some (n, A)
    | _ => none
  match groundIn T (subst θ (rebindClaim T named t)) with
  | .ok (T, A) => (.labels A, T)
  | .error reason => (.unavailable reason, T)

/-! ### Generic closures as graph code

A generic closure is graph code at a scheme row (`HasTyUsing.funScheme`): its code
is checked once, at the scheme's signatures with the scheme's binders as
parameter rows, and a table entry holds at every assignment of the parameter
rows (`ProgramCertificates.CodesSound`), so at every instantiation. Here each
generic closure's claimed scheme becomes a scheme row whose binders are fresh
value parameter rows; every claim and annotation inside the closure reads its
binders as those rows; and a call of a scheme-typed local is claimed at the
instance the call names, which the checker relates to the scheme by a checked
instance. -/

/-- A generic closure of a unit's source: its span and its binders. -/
structure GenericClosure where
  span : Span
  binders : List Fragment.TypeParam

/-- The generic closures a source tree creates, outer before inner. -/
partial def genericClosures : Json → List GenericClosure
  | .arr xs => xs.toList.flatMap genericClosures
  | .obj kvs =>
    let j := Json.obj kvs
    let here : List GenericClosure :=
      if (j.getObjValAs? String "k").toOption == some "lambda" then
        match (j.getObjValAs? Span "pos").toOption,
            (j.getObjVal? "typeParams").toOption.bind (·.getArr?.toOption) with
        | some pos, some tps =>
          if tps.isEmpty then [] else
          match Fragment.decodeTypeParams tps.toList with
          | .ok binders => [⟨pos, binders⟩]
          | .error _ => []
        | _, _ => []
      else []
    here ++ kvs.toList.flatMap fun (_, v) => genericClosures v
  | _ => []

/-- Scheme rows made so far: a scheme claim, its enclosing binders already
read as rows, with its row and its binders' rows. -/
abbrev Registry (ι : Type) := List ((ClaimType ι) × ι × List (String × ι))

private abbrev SchemeM := StateT (EquationStore.State × (Registry Tree)) (Except String)

private def internS (c : PositiveNormalization.Clause (List Tree)) : SchemeM Tree :=
  modifyGet fun (T, reg) =>
    let (T, l) := EquationStore.intern T [c]
    (l, (T, reg))

/-- A parameter row `l` with a bound of rows `B`: the meet of the two when `B`
is of clause rows, the row itself otherwise. -/
private def boundedRow (l : Tree) (B : List Tree) : SchemeM Tree := do
  let (T, reg) ← get
  let G := SourceTypes.graph T
  if B.isEmpty || !G.plainTy B then return l
  let (T, m) := EquationStore.bounded T l (B.flatMap G) []
  set (T, reg)
  return m

mutual
/-- A claim, its binders already rows, in ground form: a scheme with binders
of its own is a scheme row, the same row for the same scheme. -/
private partial def groundT : ClaimType Tree → SchemeM (List Tree)
  | .labels A => pure A
  | .union ts => do
    let arms ← ts.mapM groundT
    pure (arms.flatten.eraseDups.mergeSort Labels.le)
  | .array e => do
    let E ← groundT e
    let store ← internS (.list ⟨[], [], some E, false, .readable⟩ [])
    let (T, _) ← get
    pure [← internS (SourceTypes.arrayOf T store false)]
  | .scheme [] rc ps rest r effect => do
    let rc ← groundT rc
    let ps ← ps.mapM groundT
    let r ← groundT r
    match rest with
    | none => pure [← internS (.arrs [⟨rc, ps, r, effect⟩] [])]
    | some e => do
      let E ← groundT e
      let pack ← internS (.pack ⟨[], [], some E, false, .dense⟩ [])
      pure [← internS (.arrs [] [⟨rc, (ps, [pack]), r, effect⟩])]
  | .scheme tps rc ps rest r effect => do
    return [(← schemeRowOf (.scheme tps rc ps rest r effect)).1]
  | .param name => throw s!"the rigid parameter '{name}' is not in scope"
  | .unavailable reason => throw reason

/-- Whether a claim names one of `names` as a binder. -/
private partial def mentions (names : List String) : ClaimType Tree → Bool
  | .param n => names.contains n
  | .union ts => ts.any (mentions names)
  | .array e => mentions names e
  | .scheme tps rc ps rest r _effect =>
    let names := names.filter fun n => !EquationLowering.ownsName (tps.flatMap ResolutionWire.Binder.ownedNames) n
    tps.any (fun q => q.bound.any (mentions names)) || mentions names rc || ps.any (mentions names) ||
      rest.any (mentions names) || mentions names r
  | _ => false

/-- The row of a scheme with binders: its binders fresh value parameter rows,
its signature over them. A binder with a bound of clause rows is read, in the
signature and inside the closure, as the meet of its row and its bound, as a
generic unit's is (`binderRows`): at every instantiation within the bound the
meet is the binder, and elsewhere the scheme promises nothing. Such a bound is
read outside the binders and is the scheme's bound too. A binder bounded by an
earlier one of the same scheme, `U extends T`, is the meet of the two
parameter rows, within `T`'s clauses if it has any (`dependentMeet`), as a
generic unit's is: its bound reads a binder, which the scheme's bounds do not,
so the meet alone states it. Returns the row and what each binder is read as. -/
private partial def schemeRowOf (t : ClaimType Tree) : SchemeM (Tree × List (String × Tree)) := do
  if let some (_, l, rows) := (← get).2.find? (·.1 == t) then return (l, rows)
  let .scheme tps rc ps rest r effect := t | throw "not a scheme"
  if tps.any (·.resolution.isSome) then
    throw "qualified callable requires descriptor scheme checking"
  let names := tps.map (·.name)
  -- A binder whose argument lists the scheme spells, `T#pack`, is packed:
  -- its lists are its own row's.
  let (T, reg) ← get
  let parts := rc :: ps ++ rest.toList ++ [r]
  let packed := names.filter fun n => parts.any fun c =>
    rebindClaim T [(n ++ "#pack", [.local 0])] c != c
  let (T, binders) := EquationStore.binders T names packed
  set (T, reg)
  let params := names.zip binders
  let meetRow (p : Tree) (cs : List (PositiveNormalization.Clause (List Tree))) (also : List Tree) :
      SchemeM Tree := do
    let (T, reg) ← get
    let (T, m) := EquationStore.bounded T p cs also
    set (T, reg)
    return m
  let mut rows : List (String × Tree) := []
  let mut bounds : List (Tree × List Tree) := []
  for ((n, l), p) in params.zip tps do
    match p.bound with
    | none =>
      let B := [← internS .source]
      rows := rows ++ [(n, ← boundedRow l B)]
      bounds := bounds ++ [(l, B)]
    | some (.param m) =>
      if !names.contains m then
        let B ← groundT (.param m)
        rows := rows ++ [(n, ← boundedRow l B)]
        bounds := bounds ++ [(l, B)]
      else match rows.lookup m with
        | some r =>
          match SourceTypes.dependentMeet (← get).1 r with
          | some (cs, also) => rows := rows ++ [(n, ← meetRow l cs also)]
          | none => rows := rows ++ [(n, l)]
        | none => throw "a type-parameter bound must name an earlier parameter"
    | some bound =>
      if mentions names bound then
        throw "a type-parameter bound is a ground type or an earlier type parameter"
      let B ← groundT bound
      rows := rows ++ [(n, ← boundedRow l B)]
      bounds := bounds ++ [(l, B)]
  -- A packed binder is its own row, in both components, unbounded: the
  -- scheme holds at each of its instances.
  rows := rows.map fun (n, r) => match params.lookup n with
    | some l => if packed.contains n then (n, l) else (n, r)
    | none => (n, r)
  rows := rows ++ params.filterMap fun (n, l) =>
    if packed.contains n then some (n ++ "#pack", l) else none
  let θ := rows.map fun (n, l) => (n, ClaimType.labels [l])
  -- A label the claim spells a binder in reads it as its row.
  let named (c : ClaimType Tree) : SchemeM (ClaimType Tree) := do
    return subst θ (rebindClaim (← get).1 (rows.map fun (n, l) => (n, [l])) c)
  let rc ← groundT (← named rc)
  let ps ← ps.mapM fun q => do groundT (← named q)
  let r ← groundT (← named r)
  let (sigs, rests) ← match rest with
    | none => pure ([⟨rc, ps, r, effect⟩], [])
    | some e => do
      let E ← groundT (← named e)
      let pack ← internS (.pack ⟨[], [], some E, false, .dense⟩ [])
      pure ([], [⟨rc, (ps, [pack]), r, effect⟩])
  let boundRows := bounds.filter fun (l, _) =>
    !(params.any fun (n, l') => l' == l && packed.contains n)
  let (T, reg) ← get
  let (T, label) := EquationStore.scheme T binders sigs boundRows rests
  -- The scheme binds parameters of its own: its binders, and each row read
  -- at them.
  let own := match StoreView.row T label with
    | .scheme bs .. => bs
    | _ => binders
  let ρ := binders.zip own
  let bound := rows.map fun (n, l) => (n, ((EquationStore.substitute ρ l).head?).getD l)
  set (T, reg ++ [(t, label, bound)])
  return (label, bound)
end

/-- The innermost scope, among `scopes`, strictly containing the span `p`. -/
private def scopeAt (scopes : List (Span × List (String × ι))) (outer : List (String × ι))
    (p : Span) : List (String × ι) :=
  let inside := scopes.filter fun (q, _) => q.1 ≤ p.1 && p.2 ≤ q.2 && q != p
  match inside.foldl (fun (best : Option (Span × List (String × ι))) x => match best with
      | some b => if x.1.2 - x.1.1 < b.1.2 - b.1.1 then some x else some b
      | none => some x) none with
  | some (_, rows) => rows
  | none => outer

/-- A unit's claims with its generic closures' schemes as scheme rows, each
claim inside a closure reading the closure's binders as that row's binders,
and a call of a scheme-typed local claimed at the instance it names. `outer`
reads the unit's own binders, if any, as their rows. Returns the grown
table, the claims and the binder scope of each closure. -/
def closureRows (T : EquationStore.State) (outer : List (String × Tree))
    (closures : List GenericClosure) (calls : List (Span × Span × String × List Json))
    (c : Function Tree) :
    Except String (EquationStore.State × (Function Tree) × List (Span × List (String × Tree))) := do
  let asClaims (rows : List (String × Tree)) : List (String × (ClaimType Tree)) :=
    rows.map fun (n, l) => (n, .labels [l])
  let run : SchemeM ((Function Tree) × List (Span × List (String × Tree))) := do
    -- Each closure's scheme, outer closures first: a closure's binders are
    -- in scope for the closures inside it.
    let mut scopes : List (Span × List (String × Tree)) := []
    for gc in closures do
      let enclosing := scopeAt scopes outer gc.span
      let some e := c.expressions.find? (·.pos == gc.span)
        | throw "a generic closure has no claim"
      let .scheme tps _ _ _ _ _ := e.type
        | throw "a generic closure is claimed at no scheme"
      if tps.map (·.name) != gc.binders.map (·.name) then
        throw "a generic closure's claimed scheme names other binders than its own"
      if gc.binders.any fun b => (enclosing.lookup b.name).isSome then
        throw "a generic closure's binder hides an enclosing binder of its name"
      -- The enclosing binders read as the claims inside the closure read
      -- them (`go` below), in graph labels too: the same scheme, the same
      -- row, so the closure's annotations read its binders as its claim's.
      let t := subst (asClaims enclosing)
        (rebindClaim (← get).1 (enclosing.map fun (n, l) => (n, [l])) e.type)
      let (_, rows) ← schemeRowOf t
      scopes := scopes ++ [(gc.span, rows ++ enclosing)]
    -- A call of a local whose claim is a scheme: its callee is claimed at the
    -- instance the call names.
    let mut instances : List ((String × Span) × (ClaimType Tree)) := []
    let mut namedCalls : List (String × Span) := []
    for (p, q, _, _) in calls do
      for e in c.expressions.filter (·.pos == p) do
        let some inst := e.instantiate | continue
        if inst.any (·.resolution.isSome) then
          throw "qualified type arguments require descriptor checking"
        let some callee := c.expressions.find? (fun x => x.pos == q && x.point == e.point) | continue
        let θ := asClaims (scopeAt scopes outer q)
        let .scheme tps rc ps rest r effect := subst θ callee.type | continue
        if tps.isEmpty then continue
        let given := inst.map (·.name)
        if given.eraseDups.length != given.length || given.length != tps.length ||
            given.any (fun n => !(tps.map (·.name)).contains n) then
          throw "type arguments do not instantiate exactly the scheme's binders"
        let θp := asClaims (scopeAt scopes outer p)
        -- A bounded binder is read as a meet row, so its instance is the meet
        -- of the type arguments of the row's parameters with the row's
        -- clauses: the clause row an instance table maps the meet row to
        -- (`meetOk`), in the order it reads them.
        let args := inst.map fun i => (i.name, subst θp i.type)
        let (sl, rows) ← schemeRowOf (.scheme tps rc ps rest r effect)
        let binders := match StoreView.row (← get).1 sl with
          | .scheme bs .. => bs
          | _ => []
        let nameOf := binders.zip (tps.map (·.name))
        let θi ← args.mapM fun (n, U) => do
          let some l := rows.lookup n | pure (n, U)
          let .meet b cs also := StoreView.row (← get).1 l | pure (n, U)
          let st ← get
          let meet : SchemeM (Option Tree) := do
            let Us ← (b :: also).mapM fun q => do
              let some m := nameOf.lookup q | throw "a meet row's parameter is no binder of its scheme"
              let some A := args.lookup m | throw s!"no type argument for '{m}'"
              groundT A
            let (T, reg) ← get
            let G := SourceTypes.graph T
            if !Us.all G.plainTy then return none
            let cs := PositiveRules.meetMany (Us.map (PositiveRules.clausesOf G) ++ [cs])
            if cs.isEmpty then return none
            let (T, l) := EquationStore.intern T cs
            set (T, reg)
            return some l
          match meet.run st with
          | .ok (some l, st) => set st; pure (n, .labels [l])
          | _ => pure (n, U)
        instances := instances ++ [((e.point,q), .scheme [] (subst θi rc) (ps.map (subst θi))
          (rest.map (subst θi)) (subst θi r) effect)]
        namedCalls := namedCalls ++ [(e.point,p)]
    let named (at_ : Span) : List (String × List Tree) :=
      (scopeAt scopes outer at_).map fun (n, l) => (n, [l])
    let go (at_ : Span) (t : ClaimType Tree) : SchemeM (ClaimType Tree) := do
      let st ← get
      match (groundT (subst (asClaims (scopeAt scopes outer at_)) (rebindClaim st.1 (named at_) t))).run st with
      | .ok (A, st) => set st; pure (.labels A)
      | .error reason => pure (.unavailable reason)
    let current (at_ : Span) (c : Option (CurrentFields Tree)) : SchemeM (Option (CurrentFields Tree)) := do
      return rebindCurrent (← get).1 (named at_) c
    let entry (e : Entry Tree) : SchemeM (Entry Tree) := do
      return { e with bindings := ← e.bindings.mapM fun b => do
        return { b with type := ← go (e.start, e.start + 1) b.type,
                        current := ← current (e.start, e.start + 1) b.current } }
    let params ← c.params.mapM fun b => do return { b with type := ← go (0, 0) b.type }
    let result ← go (0, 0) c.result
    let entries ← c.entries.mapM entry
    let contracts ← c.contracts.mapM fun b => do return { b with type := ← go b.pos b.type }
    let expressions ← c.expressions.mapM fun e => do
      let type ← go e.pos ((instances.lookup (e.point,e.pos)).getD e.type)
      let instantiate ← if namedCalls.contains (e.point,e.pos) then pure none else
        e.instantiate.mapM (·.mapM fun i => do return { i with type := ← go e.pos i.type })
      return { e with type, instantiate, current := ← current e.pos e.current }
    return ({ c with params, result, entries, expressions, contracts }, scopes)
  let ((c, scopes), (T, _)) ← run.run (T, [])
  return (T, c, scopes)

/-- A source annotation in claim form with each binder read as its row: the
unit's binders by `θ`, a generic closure's, inside it, by its scope. A graph
atom's label is read so too (`EquationStore.rebind`), becoming as many atoms as the
union it reads as. -/
partial def annotationAtScopes (T : EquationStore.State) (scopes : List (Span × List (String × Tree)))
    (θ : List (String × Tree)) : Json → Json
  | .arr xs => .arr (xs.map (annotationAtScopes T scopes θ))
  | .obj kvs =>
    let j := Json.obj kvs
    match (j.getObjValAs? String "a").toOption, (j.getObjValAs? String "name").toOption with
    | some "param", some name =>
      match θ.lookup name with
      | some l => if j == Json.mkObj [("a", toJson "param"), ("name", toJson name)] then
          Json.mkObj [("a", toJson "graph"), ("label", toJson l)] else j
      | none => j
    | _, _ =>
      let θ := if (j.getObjValAs? String "k").toOption == some "lambda" then
          match (j.getObjValAs? Span "pos").toOption.bind (fun p => scopes.lookup p) with
          | some rows => rows
          | none => θ
        else θ
      let atom (a : Json) : List Json :=
        match (a.getObjValAs? String "a").toOption, (a.getObjVal? "label").toOption.bind
            (fun l => (fromJson? l : Except String Tree).toOption) with
        | some "graph", some l =>
          (EquationStore.rebind T (θ.map fun (n, r) => (n, [r])) l).map fun r =>
            Json.mkObj [("a", toJson "graph"), ("label", toJson r)]
        | _, _ => [annotationAtScopes T scopes θ a]
      Json.mkObj (kvs.toList.map fun (k, v) =>
        (k, if k == "typeParams" then v
          else if k == "atoms" then (match v with
            | .arr xs => .arr (xs.toList.flatMap atom).toArray
            | v => v)
          else annotationAtScopes T scopes θ v))
  | j => j

end Scheme

/-- A generic unit's claims with each binder read as its parameter row
(`rows`): the unit is then an ordinary graph request over those rows, which
the graph checker certifies at every assignment of them
(`Parametricity.accepted_at`). The instantiations its calls state are read
the same way, so a call of a generic module function at a binder names the
instance at that binder's row. -/
def Function.atRows (c : Function Tree) (T : EquationStore.State) (rows : List (String × Tree)) :
    EquationStore.State × (Function Tree) :=
  let θ := rows.map fun (n, l) => (n, ClaimType.labels [l])
  let named := rows.map fun (n, l) => (n, [l])
  let go := Scheme.atRows θ
  let current (x : Option (CurrentFields Tree)) : StateM EquationStore.State (Option (CurrentFields Tree)) := do
    return rebindCurrent (← get) named x
  let entry (e : Entry Tree) : StateM EquationStore.State (Entry Tree) := do
    return { e with bindings := ← e.bindings.mapM fun b => do
      return { b with type := ← go b.type, current := ← current b.current } }
  let run : StateM EquationStore.State (Function Tree) := do
    let params ← c.params.mapM fun b => do return { b with type := ← go b.type }
    let result ← go c.result
    let entries ← c.entries.mapM entry
    let contracts ← c.contracts.mapM fun b => do return { b with type := ← go b.type }
    let expressions ← c.expressions.mapM fun e => do
      let type ← go e.type
      let instantiate ← e.instantiate.mapM (·.mapM fun i => do return { i with type := ← go i.type })
      return { e with type, instantiate, current := ← current e.current }
    let arrows ← c.arrows.mapM (·.mapM fun a => do
      let rows ← a.rows.mapM fun r => do
        let expressions ← r.expressions.mapM fun e => do
          return { e with type := ← go e.type, current := ← current e.current }
        let entries ← r.entries.mapM entry
        let contracts ← r.contracts.mapM fun b => do return { b with type := ← go b.type }
        return { r with expressions, entries, contracts }
      return { a with rows })
    return { c with params, result, entries, expressions, contracts, arrows }
  let (c, T) := run.run T
  (T, c)



/-- The label that stands for each of a generic unit's binders: its owned
parameter (`binders`, the unit head's), met with its bound when the bound is
a type of clause rows, `T extends { length: number }` read as `T ⊓ { length:
number }`, or when the bound is an earlier binder, `U extends T` read as
`U ⊓ T` (`SourceTypes.dependentMeet`). Every assignment of the parameter is
an instance: one within the bound is the binder itself, and the body is
certified at all of them. Compound bounds retain their intersection; a union
with common parameter parts factors those parts before forming the row. -/
def binderRows (T : EquationStore.State) (binders : List (String × Tree × Option (List Tree))) :
    Except String (EquationStore.State × List (String × Tree)) := do
  let owner := binders.map fun (n, p, _) => (p, n)
  let (rows, T) ← (binders.foldlM (fun (rows : List (String × Tree)) (n, p, bound) => do
    let general (B : List Tree) : SourceTypes.Lowering Tree := do
      match SourceTypes.boundParts (← get) B with
      | some (cs, parts) => SourceTypes.bounded p cs parts
      | none => match B with
        | [q] => pure (EquationGraphs.canonMeet [p, q])
        | _ => throw "a binder's union bound requires common parameter parts"
    let row : Tree ← match bound with
      | none => pure p
      | some [q] =>
        match (owner.lookup q).bind fun m => rows.lookup m with
        | some r => match SourceTypes.dependentMeet (← get) r with
          | some (cs, also) => SourceTypes.bounded p cs also
          | none => pure p
        | none => general [q]
      | some B => general B
    return rows ++ [(n, row)]) []).run T
  return (T, rows)

/-- Whether a source function's tree declares type parameters below its own:
a generic closure, whose binders the unit's rows do not stand for. -/
partial def nestedBinders : Json → Bool
  | .arr xs => xs.any nestedBinders
  | .obj kvs =>
    -- A class's binders are its declaring unit's, not a closure's.
    let isClass := kvs.toList.lookup "k" == some (.str "ctor")
    kvs.toList.any fun (k, v) =>
      (k == "typeParams" && !isClass && v != Json.arr #[]) || nestedBinders v
  | _ => false

/-- The ctor nodes' binder lists in a tree. -/
private partial def ctorBinderLists : Json → List Json
  | .arr xs => xs.toList.flatMap ctorBinderLists
  | .obj kvs =>
    let here := if kvs.toList.lookup "k" == some (.str "ctor") then
        match kvs.toList.lookup "typeParams" with
        | some (.arr ps) => ps.toList
        | _ => []
      else []
    here ++ kvs.toList.flatMap fun (_, v) => ctorBinderLists v
  | _ => []

/-- The names the top-level code binds generic classes to. -/
def genericClassNames (j : Json) : List String :=
  match j with
  | .arr sts => sts.toList.flatMap fun st =>
    match (st.getObjVal? "bindings").toOption with
    | some (.arr bs) => bs.toList.filterMap fun b =>
      match (b.getObjVal? "init").toOption with
      | some init =>
        if (init.getObjValAs? String "k").toOption == some "ctor" &&
            ((init.getObjVal? "typeParams").toOption.bind (·.getArr?.toOption)).any (!·.isEmpty)
        then (b.getObjValAs? String "name").toOption else none
      | none => none
    | _ => []
  | _ => []

/-- The binders of the generic classes the module's top-level code declares:
the initialization unit's, read as parameter rows. One spelling is one row,
so two classes may share a binder's name only with the same bound. -/
def classBinders (j : Json) : Except String (List Fragment.TypeParam) := do
  let mut out : List Fragment.TypeParam := []
  for p in ctorBinderLists j do
    let tp ← Fragment.decodeTypeParam p
    match out.find? (·.name == tp.name) with
    | some q => if q.bound != tp.bound || q.resolution != tp.resolution then
        throw s!"two generic classes bind '{tp.name}' with different contracts"
    | none => out := out ++ [tp]
  ResolutionWire.validateOwnership (out.map fun p => (p.name, p.resolution))
  return out


end

end Verification.SourceClaimJson
