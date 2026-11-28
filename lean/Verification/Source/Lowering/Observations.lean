import Verification.Source.Lowering.State
import Verification.Source.Lowering.Types

/-! Emits graph nodes and checks source heap observations. -/
namespace Verification.SourceElaboration
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

section
variable {ι : Type} [Labels ι]

/-- A term that cannot throw: a value, or a slot, which holds one. Every other
node inside a `try` names its handler. -/
private def cannotThrow : Tm → Bool
  | .var _ => true
  | t => isVal t

/-- The handler a node emitted now names: the current one, its target's slots
read from the thrown value's (0) and from the `try`'s scope, which the node's
scope ends with, past the node's own `Γ.length - n` inner slots. -/
@[nospecialize] private def nodeHandler (Γ : List (Ty Tree)) (t : Tm) : Compiler (Option Target) := do
  match ← currentHandler with
  | none => return none
  | some (entry, n) =>
    if cannotThrow t then return none
    if Γ.length < n then
      throw "internal lowering error: a node inside a try is outside the try's scope"
    let inner := Γ.length - n
    return some ⟨entry.label, some ((entry.mapping.getD (List.range (n+1))).map
      fun i => if i == 0 then 0 else i + inner)⟩

@[nospecialize] def emit (t : Tm) (k : Continuation) (Γ : List (Ty Tree)) (A : Ty Tree) :
    Compiler Target := do
  let handler ← nodeHandler Γ t
  appendNode ⟨t,k,handler⟩ ⟨Γ,A⟩

/-- Record this node's source map entry. Explanatory only; never part of the
certified request. The context must be describable binding for binding: a
context this cannot name is a lowering bug, not a slot number for a reader,
so it fails here rather than reaching a message. -/
@[nospecialize] def emitAt (pos : Span) (t : Tm) (k : Continuation) (Γ : List (Ty Tree)) (A : Ty Tree)
    (role : String := "node-typing") (environmentStart : Option SourcePoint := none)
    (scope : List (ScopeBinding Tree) := []) : Compiler Target := do
  -- Every write the lowering emits is a node's term: one at a reserved key
  -- needs a proto-free receiver (`reservedWriteCheck`).
  if let .writeAt fld (.var i) _ := t then
    reservedWriteCheck pos (Γ[i]?.getD []) (errorOwnedKey fld)
  let target ← emit t k Γ A
  if scope.length != Γ.length then
    throw s!"internal lowering error: source map covers {scope.length} of {Γ.length} bindings at {pos.1}"
  if let some b := scope.find? (!·.source.describes) then
    throw s!"internal lowering error: undescribed binding '{b.source.name}' at {pos.1}"
  recordNodeSource target ⟨pos,role,environmentStart,sources scope⟩
  return target

/-- A node whose derivation the lowering knows: its plan, cast to the node's
claim, joins the search's known evidence, so the node is not searched. -/
@[nospecialize] def emitPlanned (pos : Span) (plan : DirectProof.Plan Tree) (k : Continuation)
    (Γ : List (Ty Tree)) (A : Ty Tree) (role : String := "node-typing")
    (scope : List (ScopeBinding Tree) := []) : Compiler Target := do
  recordNodePlan (DirectProof.cast Γ A plan)
  emitAt pos plan.term k Γ A role (scope := scope)

/-- The separation of a unit's module cells, the slots `cells` at depth `d`
each with its binding's name: the field `value` of each apart from the field
`value` of every cell of another binding. The initialization unit allocates
each module cell fresh, so two are two locations; a unit assumes it of its
entry (`Request.entrySeparation`), and every statement entry restates it. -/
@[nospecialize] def moduleCellFacts (d : Nat) (cells : List (Nat × String)) : List HeapSeparation.Fact :=
  cells.filterMap fun (i, name) =>
    if d ≤ i then none else
    let partners := cells.filterMap fun (j, other) =>
      if other == name || d ≤ j then none else some (d - 1 - j, [valueField])
    if partners.isEmpty then none else some ⟨d - 1 - i, some [valueField], partners⟩

@[nospecialize] def moduleCellSeparation (d : Nat) (cells : List (Nat × String)) : HeapSeparation.Separation :=
  HeapSeparation.norm d (moduleCellFacts d cells)

/-- Whether a slot of `scope` may state a separation fact (`separationFacts`). -/
@[nospecialize] def separating (scope : List (ScopeBinding ι)) : Bool :=
  scope.any (·.allocated)

/-- The separation each statement entry restates, so that an allocation's
freshness survives the reset of knowledge at a cut; every incoming edge
proves it, from the allocation or from the cut before.

A value allocated at a binding (`allocated`: a `let`'s private cell, a
`for...of` loop's iterator, a constant whose initializer allocates) has own
locations that lie past the heap the allocation started in, so they differ
from the field locations of every value bound before it
(`HeapSeparation.allocate`). Each entry states, for every slot bound before
the allocation, the fields its record named then (`apart`, where known) apart
from the allocated value's own locations:

- all of them, where the slot still holds the value it held then: no
  assignment and no key-adding write rebinds it;
- those its type names, where the slot may come to hold a value allocated
  later, which that later allocation separates from them: a slot a
  key-adding write rebinds to its copy, or any slot where the allocated value
  is no source value (`reachable` false), so no assignment gives it to the
  slot.

A closure's capture states none: its entry knows nothing of the allocation.
Module cells are two apart by the unit's entry assumption
(`moduleCellFacts`). Addressed by level at the context's depth. -/
@[nospecialize] def separationFacts (commonFields : Ty ι → List PropKey) (rebound : ScopeBinding ι → Bool)
    (scope : List (ScopeBinding ι)) (Γ : List (Ty ι)) : HeapSeparation.Separation :=
  let depth := Γ.length
  let slots := scope.toArray
  -- Each slot type's common fields, computed once, where some slot may
  -- state a fact.
  let commons : Array (List PropKey) := if separating scope then (Γ.map commonFields).toArray else #[]
  let common (j : Nat) : List PropKey := commons[j]?.getD []
  -- The context's slot indices, from the innermost.
  let indices := List.range depth
  HeapSeparation.norm depth <| moduleCellFacts depth (scope.zipIdx.filterMap fun (b,i) =>
    b.moduleCell.map (i, ·)) ++ scope.zipIdx.flatMap fun (b,i) =>
    if !b.allocated || b.captured || depth ≤ i then [] else
    let olders := b.apart.map fun older => (older.map commonFields).toArray
    -- Each slot bound before the allocation (an older slot, or, for an
    -- assigned parameter's cell, another parameter), with the fields its
    -- record named then, and whether it still holds its value of then.
    let partners := indices.filterMap fun j =>
      slots[j]?.bind fun other =>
      if !(j > i || (b.param && other.param && i != j)) then none else
      let assigned := match other.storage with | .slot _ => true | .value | .cell .. | .early .. => false
      if assigned && b.reachable then none else
      let fields := if j > i then
          match olders.bind (·[j - i - 1]?) with
          | some fieldsB => (common j).filter fieldsB.contains
          | none => common j
        else common j
      if fields.isEmpty then none else some (!assigned && !rebound other, (depth - 1 - j, fields))
    ⟨depth - 1 - i, none, partners.filterMap fun (kept, p) => if kept then some p else none⟩ ::
      if (common i).isEmpty then [] else
      [⟨depth - 1 - i, some (common i), partners.filterMap fun (kept, p) => if kept then none else some p⟩]

/-- `separationFacts` at the store, each type's common fields computed once
while the store is unchanged (`commonFieldsOf`), a slot rebound where it
holds the object of a key-adding write (`growSites`). -/
@[nospecialize] def separationAt (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree)) :
    Compiler HeapSeparation.Separation := do
  let types := if separating scope then Γ ++ scope.flatMap (·.apart.getD []) else []
  let holders ← rebindingHolders
  let rebound := fun (b : ScopeBinding Tree) => holders.any fun (n, p) => b.source == ⟨n, some p⟩
  return separationFacts (← commonFieldsOf types) rebound scope Γ

/-- A checkpoint is an actual no-op graph node. Every incoming edge must
justify its supplied current-heap assertion, including backedges. -/
@[nospecialize] def checkpoint (pos : Span) (Γ : List (Ty Tree)) (facts : HeapFacts.Facts)
    (next : Target) (entry : Option SourcePoint := none) (scope : List (ScopeBinding Tree) := []) :
    Compiler Target := do
  let separation ← if entry.isSome then separationAt scope Γ else pure {}
  if facts.isEmpty && separation.facts.isEmpty then return next
  let t ← emitAt pos .nul (.effect next) Γ [Labels.nul] "heap-observation" entry scope
  recordAssertion t ⟨facts,[],[],separation,[],[]⟩
  return t

@[nospecialize] def contents (A : Ty Tree) : Compiler (List HeapFacts.Atom) := do
  let T ← table
  if !RequestJson.validTy (StoreView.valid T) A then throw "invalid current-content type label"
  let some R := HeapKnowledge.atoms (SourceTypes.graph T) A
    | throw "current-content predicate must be a supported primitive predicate"
  return R

/-- Record a source obligation with its source map, under the same invariant as
`emitAt`: every context binding must be describable in the words of the source. -/
@[nospecialize] def obligation (pos : Span) (j : ProgramCertificates.Sequent Tree) (plan : Option (DirectProof.Plan Tree))
    (role : String) (scope : List (ScopeBinding Tree)) : Compiler Unit := do
  if scope.length != j.context.length then
    throw s!"internal lowering error: source map covers {scope.length} of {j.context.length} bindings at {pos.1}"
  if scope.any (!·.source.describes) then
    throw s!"internal lowering error: undescribed binding at {pos.1}"
  recordObligation ⟨pos,j,plan,role,sources scope⟩

/-- Ordinary lambda proofs cannot retain transient heap observations across
calls. Require their declared storage contract to imply such an observation
uniformly; this is a located proof obligation, never a discarded assertion. -/
@[nospecialize] def persistentObservation (d : Descriptor) (pos : Span) (A : Ty Tree)
    (fld : PropKey) (R : Ty Tree) : Compiler Unit := do
  -- The obligation below is an inclusion of types, so the observed type needs
  -- only to be one this table names. It does not need a supported primitive predicate:
  -- that is what a primitive assertion on an edge needs, and this is not one.
  if !RequestJson.validTy (StoreView.valid (← table)) R then throw "invalid current-content type label"
  obligation pos ⟨[A], .readAt fld (.var 0), R⟩ none "heap-observation" [held d]

/-- Where `Array.isArray` holds, the labels `arraySlice` keeps of `A`, and the
builtins's `readonly unknown[]`, `R`, for the records and `unknown` it does not:
the refinement the edge's observation establishes. -/
@[nospecialize] def arrayRefine (G : PositiveGraphs.NormalGraph ι) (A R : Ty ι) : Ty ι :=
  -- A label of no array or of indexed dictionaries is dropped: where the
  -- graph states the built-ins, an array owns the prototype key a dictionary
  -- does not (`BranchRefinement.not_array_of_indexed`).
  let sliced := (BranchRefinement.tagSlice G A .isArray true).filter fun a => !(G.plain a && G.builtins.isSome &&
    (G a).all fun c => ProgramTyping.tagClause .isArray c == some false || BranchRefinement.indexedDict c)
  -- A label each clause of which owns no array, or is a record that may be
  -- one without being one, gives way to the built-ins' array.
  let kept := sliced.filter fun a => !(G.plain a && (G a).all fun c =>
    ProgramTyping.tagClause .isArray c == some false ||
      (c.carriesInvariant && ProgramTyping.tagClause .isArray c != some true))
  if kept.length == sliced.length then sliced else kept ++ R

/-- The built-in `readonly unknown[]`: the array shape over a possibly sparse
spine of `unknown`. -/
@[nospecialize] def builtinArrayTy : Compiler (Ty Tree) := do
  let u ← lower (SourceTypes.use .source)
  let spine ← lower (SourceTypes.use (.list ⟨[], [], some [u], true, .sparse⟩ []))
  return [← lower (SourceTypes.use (SourceTypes.arrayOf (← table) spine true))]

/-- The labels of the kinds of a JavaScript value (`sourceKinds`), where a
slot of `Γ` holds `unknown`, whose tests keep its kinds; none otherwise. -/
@[nospecialize] def sourceKindLabels (Γ : List (Ty Tree)) : Compiler (List Tree) := do
  let G := SourceTypes.graph (← table)
  if Γ.any (·.any fun a => G.plain a && G a == [.source]) then
    (BranchRefinement.sourceKinds : List (PositiveNormalization.Clause (List Tree))).mapM fun k => lower (SourceTypes.use k)
  else return []

/-- What a tag test answering `q` keeps of `A`: `tagSlice`, and where
`Array.isArray` holds, `arrayRefine`. -/
@[nospecialize] def tagRefine (A : Ty Tree) (tag : Tag) (q : Bool) : Compiler (Ty Tree) := do
  let G := SourceTypes.graph (← table)
  if tag == .isArray && q then return arrayRefine G A (← builtinArrayTy)
  else return BranchRefinement.tagSlice G A tag q

/-- The atom of a test's answer whose refinement of a field's contract `C` is
within the type `A` a claim states the field holds, of the tests whose answer
depends on the value alone, where no primitive predicate states `A`: a
`typeof` test that fails leaves objects beside primitives. The atom is an
assertion every edge into the point must establish; choosing it proves
nothing. -/
@[nospecialize] def answerAtoms (C A : Ty Tree) : Compiler (Option (List HeapFacts.Atom)) := do
  let (T, gen) ← tableAt
  let G := SourceTypes.graph T
  let tags := [Tag.isArray, .isFun, .typeofObject, .isRef, .truthy, .isNum, .isStr, .isBool, .isBigint, .isSymbol]
  -- First the answers whose slice of `C` is within `A`, the one keeping
  -- most of `C` first, the weakest
  -- assertion; then `Array.isArray`'s refinement, which also admits the
  -- built-ins' array, so that it is chosen only where no slice is.
  let answers ← (tags.flatMap fun tag => [true, false].map (tag, ·)).filterMapM fun (tag, q) => do
    let S := BranchRefinement.tagSlice G C tag q
    -- An answer no value of `C` gives describes no value the field holds.
    if !S.isEmpty && S != C then
      if ← withinAt T gen S A then return some (S.length, tag, q)
    return none
  if let some (_, tag, q) := answers.foldl (fun best x => match best with
      | some b => if x.1 > b.1 then some x else best
      | none => some x) none then
    return some [.tag tag q]
  let R ← tagRefine C .isArray true
  let refined ← if R != C then withinAt T gen R A else pure false
  if refined || BranchRefinement.arraySlice G C A then return some [.tag .isArray true]
  return none

/-- The atoms a claim that a field holds `A` asserts, where the field's
contract is `C` (when every record states it): a primitive predicate; else a
test's answer, where no nullish exclusion of `C` is within `A`; else the
nullish exclusions `A` implies. -/
@[nospecialize] def fieldAtoms (C : Option (Ty Tree)) (A : Ty Tree) :
    Compiler (Option (List HeapFacts.Atom)) := do
  let (T, gen) ← tableAt
  let G := SourceTypes.graph T
  if let some atoms := HeapKnowledge.atoms G A then return some atoms
  let answer ← match C with
    | some C =>
      if ← [Tag.isUndef, .isNul, .isNullish].anyM (fun tag => withinAt T gen (BranchRefinement.tagSlice G C tag false) A)
      then pure none else answerAtoms C A
    | none => pure none
  return answer.orElse fun _ => HeapKnowledge.nullishAtoms G A

/-- A statement witness asserts the origin of its saved value: read from the
root binding through the path's one field, or from the witness of the path's
prefix through its last field. Every incoming edge checks each link together
with the witness's context type. -/
@[nospecialize] def witnessLinks (fc : SourceClaims.Function Tree) (pos : SourcePoint) (scope : List (ScopeBinding Tree)) : Compiler HeapLinks.Links := do
  scope.zipIdx.filterMapM fun (b,j) => do
    let some (root, path) := b.witness | return none
    let some field := path.getLast? | return none
    let some _ ← witnessClaimHere fc pos root path | return none
    let some i := valueSlot scope root | return none
    let some r ← (if path.length == 1 then pure (some i) else do
        let some _ ← witnessClaimHere fc pos root path.dropLast | return none
        return scope.findIdx? (·.witness == some (root, path.dropLast)) : Compiler (Option Nat))
      | return none
    -- A path witness states the result of an ordinary property read,
    -- including undefined at an absent key. The source root's type and
    -- explicit presence tests state own-key requirements independently.
    -- Keeping this relation uniform across entries permits a narrowed
    -- witness to reuse the same checked read relation.
    return some ⟨r,j,false,field,true⟩

/-- Mutable entry types are assertions about contents, not reference types.
Supported primitive assertions are checked on every incoming edge. Other claims
must follow from the stable storage contract; no claim is silently dropped. -/
@[nospecialize] def entryFacts (fc : SourceClaims.Function Tree) (pos : SourcePoint) (scope : List (ScopeBinding Tree)) :
    Compiler HeapFacts.Facts := do
  let cs := (fc.entryCurrent.lookup pos).getD []
  let vars := (fc.envs.lookup pos).getD []
  scope.zipIdx.foldlM (fun facts (b,i) => do
    let mut facts := facts
    let cellOf : Option (Ty Tree × Ty Tree) ← match b.storage with
      | .cell contract reference => pure (some (contract, reference))
      -- An early binding's claim describes its contents once initialized:
      -- a claim narrower than the contract is a fact, which excludes the
      -- marker, and every incoming edge proves it.
      | .early stored reference _ => pure (some (← initializedContract stored, reference))
      | _ => pure none
    if let some (contract, reference) := cellOf then
      let some candidate := vars.lookup b.source.name
        | throw s!"missing claimed binding '{b.source.name}' at {pos}"
      let A ← SourceClaims.resolve (← table) candidate
      let G := SourceTypes.graph (← table)
      let early := match b.storage with | .early .. => true | _ => false
      -- A claim the contract is within states nothing of the contents.
      let (T, gen) ← tableAt
      if contract.all A.contains || (← withinAt T gen contract A) then
        -- An early cell's contents may still be the marker: no observation.
        if !early then persistentObservation b.source (pos,pos+1) reference valueField A
      else
        match HeapKnowledge.atoms G A with
        | some atoms => facts := facts ++ [⟨i,ValueSets.ofAtoms atoms,valueField⟩]
        | none =>
          match HeapKnowledge.nullishAtoms G A with
          | some atoms => facts := facts ++ [⟨i,ValueSets.ofAtoms atoms,valueField⟩]
          | none =>
            if early then throw s!"the claim for the early binding '{b.source.name}' at {pos} is no primitive fact of its contents"
            persistentObservation b.source (pos,pos+1) reference valueField A
    match cs.lookup b.source.name with
    | none => return facts
    | some asserted =>
      -- One assertion per named field of the record this binding holds.
      -- A field claim outside the primitive predicate vocabulary is not
      -- dropped: the storage contract must imply it, as above.
      let (T, gen) ← tableAt
      let reference ← match b.storage with
        | .value | .slot _ =>
          let some candidate := vars.lookup b.source.name
            | throw s!"missing claimed binding '{b.source.name}' at {pos}"
          SourceClaims.resolve T candidate
        | .cell contract _ | .early contract _ _ => pure contract
      -- What every record the binding may hold stores at `fld`: an
      -- observation within it follows from the contract alone, as at a
      -- closure's entry, which knows nothing of the heap.
      let clauses := PositiveRules.expand (SourceTypes.graph T) reference
      let invariant := fun (fld : PropKey) => do
        if clauses.isEmpty then none
        let ws ← clauses.mapM (fun c => declaredRead c fld)
        some ws.flatten.eraseDups
      for (path, A) in asserted do
        if !RequestJson.validTy (StoreView.valid T) A then throw "invalid current-content type label"
        match path with
        | [fld] =>
          match b.storage with
          | .cell .. | .early .. =>
            -- Slot i is the private holder, not the object inside it. A field
            -- observation cannot be attached to the holder's own value field.
            persistentObservation b.source (pos,pos+1) reference fld A
          | .value | .slot _ =>
            let held := (← witnessClaimWith T (withinAt T gen) fc pos b.source.name [fld]).isSome &&
                scope.any (fun w => w.witness == some (b.source.name, [fld]))
            let implied ← if held then pure false else match invariant fld with
              | some C => withinAt T gen C A
              | none => pure false
            if held then
              pure ()
            else if implied then
              persistentObservation b.source (pos,pos+1) reference fld A
            else match ← fieldAtoms (invariant fld) A with
            | some atoms => facts := facts ++ [⟨i,ValueSets.ofAtoms atoms,fld⟩]
            | none => persistentObservation b.source (pos,pos+1) reference fld A
        | _ =>
          -- A path of two members or more is read only as its witness's
          -- claim (`witnessClaim`), which every incoming edge checks with
          -- its links; where the entry holds no witness of it, the
          -- assertion is the premise of nothing the checker derives.
          pure ()
      return facts) []

/-- A dot cannot occur in a source binding identifier, so these names designate
administrative read snapshots without colliding with source variables. -/
def snapshotName (name field : String) : String := name ++ "." ++ field
/-- The snapshot a read of a named field may be saved in: a string field's.
A symbol-keyed read (`xs[marker]`) is never saved; it is read where it is. -/
def readSnapshot (name : String) : PropKey → Option String
  | .str field => some (snapshotName name field)
  | .sym _ => none
/-- A snapshot is named by a string field. Source syntax reads only string
keys, so a symbol key asserted for a snapshot is refused, not encoded: no
string spelling of it is distinct from every string key. -/
def stringKey : PropKey → Except String String
  | .str name => .ok name
  | .sym _ => .error "a symbol-keyed field has no source snapshot"
-- A saved local value is different from a field of the object it contains.
-- This prefix cannot begin a source identifier or a name.field snapshot.
def localSnapshotName (name : String) : String := ".local:" ++ name
def isSnapshot (name : String) : Bool := name.any (· == '.')

@[nospecialize] def observed (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (snapshot : String) (d : Descriptor) (pos : Span) (A : Ty Tree)
    (fld : PropKey) (R : Ty Tree) : Compiler Unit := do
  if let some i := nameIndex scope snapshot then
    let plan := DirectProof.var Γ i R
    obligation pos plan.goal (some plan) "heap-observation" scope
  else
    persistentObservation d pos A fld R

end
end Verification.SourceElaboration
