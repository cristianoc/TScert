import Verification.Source.Lowering.State
import Verification.Source.Lowering.Types

/-! Emits graph nodes and checks source heap observations. -/
namespace Verification.SourceExtraction
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
      throw "internal extraction error: a node inside a try is outside the try's scope"
    let inner := Γ.length - n
    return some ⟨entry.label, some ((entry.mapping.getD (List.range (n+1))).map
      fun i => if i == 0 then 0 else i + inner)⟩

@[nospecialize] def emit (t : Tm) (k : Continuation) (Γ : List (Ty Tree)) (A : Ty Tree) :
    Compiler Target := do
  let handler ← nodeHandler Γ t
  appendNode ⟨t,k,handler⟩ ⟨Γ,A⟩

/-- Record this node's source map entry. Explanatory only; never part of the
certified request. The context must be describable binding for binding: a
context this cannot name is an extraction bug, not a slot number for a reader,
so it fails here rather than reaching a message. -/
@[nospecialize] def emitAt (pos : Span) (t : Tm) (k : Continuation) (Γ : List (Ty Tree)) (A : Ty Tree)
    (role : String := "node-typing") (environmentStart : Option Nat := none)
    (scope : List (ScopeBinding Tree) := []) : Compiler Target := do
  let target ← emit t k Γ A
  if scope.length != Γ.length then
    throw s!"internal extraction error: source map covers {scope.length} of {Γ.length} bindings at {pos.1}"
  if let some b := scope.find? (!·.source.describes) then
    throw s!"internal extraction error: undescribed binding '{b.source.name}' at {pos.1}"
  recordNodeSource target ⟨pos,role,environmentStart,sources scope⟩
  return target

/-- The fields every record of a type names: where each of its clauses is a
record naming them, the locations of an object of the type. -/
@[nospecialize] private def commonFields (G : Verification.PositiveGraphs.NormalGraph ι) (A : Ty ι) : List PropKey :=
  match PositiveRules.expand G A with
  | .refs fs _ _ _ _ _ :: _ =>
    (fs.map Prod.fst).eraseDups.filter (HeapExpressionRules.fieldOperand (PositiveRules.expand G A))
  | _ => []

/-- A node whose derivation the lowering knows: its plan, cast to the node's
claim, joins the search's known evidence, so the node is not searched. -/
@[nospecialize] def emitPlanned (pos : Span) (plan : DirectProof.Plan Tree) (k : Continuation)
    (Γ : List (Ty Tree)) (A : Ty Tree) (role : String := "node-typing")
    (scope : List (ScopeBinding Tree) := []) : Compiler Target := do
  recordNodePlan (DirectProof.cast Γ A plan)
  emitAt pos plan.term k Γ A role (scope := scope)

/-- The cells this lowering allocated sit at locations no other object in
scope has: a private cell's identity never becomes a source value, and every
record-typed slot holds something else. Stated at each cut so the allocation's
freshness survives the reset of knowledge there; every incoming edge proves
it, from the allocation or from the cut before. What the allocation proves is
about the fields the older slots' records named then (`apart`), whatever a
later test narrowed them to, and about the objects allocated after it, other
cells and fresh constants; an object a later call returned may be any
object. -/
@[nospecialize] def distinctLinks (G : Verification.PositiveGraphs.NormalGraph ι) (scope : List (ScopeBinding ι))
    (Γ : List (Ty ι)) : HeapLinks.Links :=
  scope.zipIdx.flatMap fun (b,i) =>
    match b.storage with
    | .cell .. | .early .. =>
      -- A captured cell was allocated before the closure's entry, which
      -- knows nothing of that allocation.
      if b.captured then [] else
      Γ.zipIdx.flatMap fun (A,j) =>
        if i == j then [] else
        let other := scope[j]?
        let isCell := other.any fun o => match o.storage with | .cell .. | .early .. => true | .value | .slot _ => false
        let fields :=
          if j > i || (b.param && other.any (·.param)) then
            -- Older than the cell: the fields its record named when the cell
            -- was allocated, where that is known.
            match b.apart with
            | some older =>
              match older[j - i - 1]? with
              | some B => (commonFields G A).filter (commonFields G B).contains
              | none => []
            | none => commonFields G A
          else if isCell || other.any (·.fresh) then commonFields G A
          else []
        fields.map fun f => (⟨i,j,false,valueField,true,f,false⟩ : HeapLinks.Link)
    | .value | .slot _ => []

/-- A checkpoint is an actual no-op graph node. Every incoming edge must
justify its supplied current-heap assertion, including backedges. -/
@[nospecialize] def checkpoint (pos : Span) (Γ : List (Ty Tree)) (facts : HeapFacts.Facts)
    (next : Target) (entry : Option Nat := none) (scope : List (ScopeBinding Tree) := []) :
    Compiler Target := do
  let G := SourceTypes.graph (← table)
  let links := if entry.isSome then distinctLinks G scope Γ else []
  if facts.isEmpty && links.isEmpty then return next
  let t ← emitAt pos .nul (.effect next) Γ [Labels.nul] "heap-observation" entry scope
  recordAssertion t ⟨facts,[],links⟩
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
    throw s!"internal extraction error: source map covers {scope.length} of {j.context.length} bindings at {pos.1}"
  if scope.any (!·.source.describes) then
    throw s!"internal extraction error: undescribed binding at {pos.1}"
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

/-- The atom of a test's answer whose refinement of a field's contract `C` is
within the type `A` a claim states the field holds, of the tests whose answer
depends on the value alone, where no primitive predicate states `A`: a
`typeof` test that fails leaves objects beside primitives. The atom is an
assertion every edge into the point must establish; choosing it proves
nothing. -/
@[nospecialize] def answerAtoms (C A : Ty Tree) : Compiler (Option (List HeapFacts.Atom)) := do
  let T ← table
  let G := SourceTypes.graph T
  let tags := [Tag.isArray, .isFun, .typeofObject, .isRef, .truthy, .isNum, .isStr, .isBool, .isBigint, .isSymbol]
  -- First the answers whose slice of `C` is within `A`, the one keeping
  -- most of `C` first, the weakest
  -- assertion; then `Array.isArray`'s refinement, which also admits the
  -- built-ins' array, so that it is chosen only where no slice is.
  let answers := tags.flatMap fun tag => [true, false].filterMap fun q =>
    let S := BranchRefinement.tagSlice G C tag q
    -- An answer no value of `C` gives describes no value the field holds.
    if !S.isEmpty && S != C && within T S A then
      some (S.length, tag, q)
    else none
  if let some (_, tag, q) := answers.foldl (fun best x => match best with
      | some b => if x.1 > b.1 then some x else best
      | none => some x) none then
    return some [.tag tag q]
  let R ← tagRefine C .isArray true
  if (R != C && within T R A) || BranchRefinement.arraySlice G C A then return some [.tag .isArray true]
  return none

/-- The atoms a claim that a field holds `A` asserts, where the field's
contract is `C` (when every record states it): a primitive predicate; else a
test's answer, where no nullish exclusion of `C` is within `A`; else the
nullish exclusions `A` implies. -/
@[nospecialize] def fieldAtoms (C : Option (Ty Tree)) (A : Ty Tree) :
    Compiler (Option (List HeapFacts.Atom)) := do
  let T ← table
  let G := SourceTypes.graph T
  if let some atoms := HeapKnowledge.atoms G A then return some atoms
  let answer ← match C with
    | some C =>
      if [Tag.isUndef, .isNul, .isNullish].any (fun tag => within T (BranchRefinement.tagSlice G C tag false) A)
      then pure none else answerAtoms C A
    | none => pure none
  return answer.orElse fun _ => HeapExpressionRules.nullishAtoms G A

/-- The declared result of a named record property, including absence for an
optional key. This only selects a persistent proof obligation. -/
private def declaredRead (c : PositiveNormalization.Clause (Ty Tree)) (fld : PropKey) : Option (Ty Tree) :=
  match c with
  | .refs W [] vs os _ _ =>
    (W.lookup fld).orElse fun _ => (vs.lookup fld).orElse fun _ =>
      (os.find? (fun o => o.key == fld)).map (fun o => o.type ++ [Labels.undef])
  | .dict _ _ _ ds _ _ _ cs =>
    ((ds ++ cs).find? (HeapExpressionRules.stringIndex · fld)).map (fun d => d.2 ++ [Labels.undef])
  | _ => none

/-- Mutable entry types are assertions about contents, not reference types.
Supported primitive assertions are checked on every incoming edge. Other claims
must follow from the stable storage contract; no claim is silently dropped. -/
@[nospecialize] def entryFacts (fc : SourceClaims.Function Tree) (pos : Nat) (scope : List (ScopeBinding Tree)) :
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
      | .early stored reference => pure (some (← initializedContract stored, reference))
      | _ => pure none
    if let some (contract, reference) := cellOf then
      let some candidate := vars.lookup b.source.name
        | throw s!"missing claimed binding '{b.source.name}' at {pos}"
      let A ← SourceClaims.resolve (← table) candidate
      let G := SourceTypes.graph (← table)
      let early := match b.storage with | .early .. => true | _ => false
      if contract.all A.contains then
        -- An early cell's contents may still be the marker: no observation.
        if !early then persistentObservation b.source (pos,pos+1) reference valueField A
      else
        match HeapKnowledge.atoms G A with
        | some atoms => facts := facts ++ [⟨i,atoms,valueField⟩]
        | none =>
          match HeapExpressionRules.nullishAtoms G A with
          | some atoms => facts := facts ++ [⟨i,atoms,valueField⟩]
          | none =>
            if early then throw s!"the claim for the early binding '{b.source.name}' at {pos} is no primitive fact of its contents"
            persistentObservation b.source (pos,pos+1) reference valueField A
    match cs.lookup b.source.name with
    | none => return facts
    | some asserted =>
      -- One assertion per named field of the record this binding holds.
      -- A field claim outside the primitive predicate vocabulary is not
      -- dropped: the storage contract must imply it, as above.
      let T ← table
      let reference ← match b.storage with
        | .value | .slot _ =>
          let some candidate := vars.lookup b.source.name
            | throw s!"missing claimed binding '{b.source.name}' at {pos}"
          SourceClaims.resolve T candidate
        | .cell contract _ | .early contract _ => pure contract
      -- What every record the binding may hold stores at `fld`: an
      -- observation within it follows from the contract alone, as at a
      -- closure's entry, which knows nothing of the heap.
      let clauses := PositiveRules.expand (SourceTypes.graph T) reference
      let invariant := fun (fld : PropKey) => do
        if clauses.isEmpty then none
        let ws ← clauses.mapM (fun c => declaredRead c fld)
        some ws.flatten.eraseDups
      for (fld, A) in asserted do
        if !RequestJson.validTy (StoreView.valid T) A then throw "invalid current-content type label"
        match b.storage with
        | .cell .. | .early .. =>
          -- Slot i is the private holder, not the object inside it. A field
          -- observation cannot be attached to the holder's own value field.
          persistentObservation b.source (pos,pos+1) reference fld A
        | .value | .slot _ =>
          if (invariant fld).any (within T · A) then
            persistentObservation b.source (pos,pos+1) reference fld A
          else match ← fieldAtoms (invariant fld) A with
          | some atoms => facts := facts ++ [⟨i,atoms,fld⟩]
          | none => persistentObservation b.source (pos,pos+1) reference fld A
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
  if let some i := (names scope).idxOf? snapshot then
    let plan := DirectProof.var Γ i R
    obligation pos plan.goal (some plan) "heap-observation" scope
  else
    persistentObservation d pos A fld R

end
end Verification.SourceExtraction
