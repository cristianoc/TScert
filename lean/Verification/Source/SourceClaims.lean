import Verification.Source.SourceTypes

/-! Producer-independent claims for the current bounded fragment. Candidates
contain calculus type labels, never producer JSON. A decoding failure is retained
until a claim is used: exporters may include unrelated unsupported bindings such
as implicit `this`; those failures must never be interpreted as a type. -/
namespace Verification.SourceClaims
open ProgramTyping LabelStore

abbrev Candidate (ι : Type) := Except String (Ty ι)

/-- An affine index shift over source names (`Σ c·t + offset`). -/
structure ShiftRef where
  terms : List ((String × List String × HeapKnowledge.Term.Kind) × Int) := []
  offset : Int := 0
  deriving Repr, BEq, Inhabited

def ShiftRef.zero : ShiftRef := ⟨[], 0⟩

/-- A variable of a proposed quantified fact's body (ARITHMETIC.md,
"Quantified clauses"): the index, the element at it, or a term rooted at a
value binding's name, its path the named fields read from it in turn. -/
inductive BodyRef where
  | index
  | elem
  | offset (delta : Nat)
  | project (kind : HeapKnowledge.Term.Kind) (path : List String)
  | parallel (name : String) (path : List String) (shift : ShiftRef) (kind : HeapKnowledge.Term.Kind) (elemPath : List String)
  | term (name : String) (path : List String) (kind : HeapKnowledge.Term.Kind)
  deriving Repr, Inhabited

inductive ElemTargetRef where
  | self (elemPath : List String)
  | parallel (name : String) (path : List String) (shift : ShiftRef) (elemPath : List String)
  deriving Repr, Inhabited

inductive BodyClaim where
  | linear (terms : List (BodyRef × Int)) (bound : Int)
  | ne (terms : List (BodyRef × Int)) (bound : Int)
  | either (left right : BodyClaim)
  | guarded (target : ElemTargetRef) (tag : HeapKnowledge.GuardTag) (body : BodyClaim)

/-- An element read proposed at a statement entry, with its guards. -/
abbrev ElementClaim := List (String × List String × HeapKnowledge.GuardTag) × String × String × String

/-- An affine index bound `base + offset` (or constant `offset` when `base = none`). -/
abbrev BoundClaim := Option (String × List String × HeapKnowledge.Term.Kind) × Int

/-- A proposed quantified fact: its leading guards, an array a value binding's name and path
read, the start and stop bounds of its index interval, and its body's facts `Σ c·x ≤ d`. -/
abbrev EveryClaim := List (String × List String × HeapKnowledge.GuardTag) ×
  (String × List String) × BoundClaim × BoundClaim × List BodyClaim

/-- A proposed spine separation: its guards, each a value binding's name, a
path and a tag (ARITHMETIC.md, "Guarded clauses"), then two pairs of a value
binding's name and a path. -/
abbrev SpinesApartClaim := List (String × List String × HeapKnowledge.GuardTag) ×
  (String × List String) × (String × List String)

/-- A clause proposed at an entry: a guarded linear fact or a disjunction. -/
inductive ClauseClaim where
  | linear (guards : List (String × List String × HeapKnowledge.GuardTag))
      (terms : List (String × List String × HeapKnowledge.Term.Kind × Int)) (bound : Int)
  | either (left right : ClauseClaim)

/-- Claims attached to one execution point. Source spans locate the syntax
inside that point; separate copies of a finalizer have separate point IDs. -/
structure PointData (ι : Type) where
  exprs : List (Span × Candidate ι) := []
  envs : List (Nat × List (String × Candidate ι)) := []
  entryCurrent : List (Nat × List (String × List (List PropKey × Ty ι))) := []
  exprCurrent : List (Span × List (PropKey × Ty ι)) := []
  /-- At a statement entry, the bounds a guard states: an array binding's name
  and an index binding's. -/
  entryBounds : List (Nat × List (String × String × Bool)) := []
  /-- At a statement entry, the linear facts the producer proposes: its
  guards, each a value binding's name, a path and a tag (ARITHMETIC.md,
  "Guarded clauses"), then terms of value bindings' names with integer
  coefficients, and a bound. -/
  entryFacts : List (Nat × List ClauseClaim) := []
  /-- At a statement entry, the quantified facts the producer proposes. -/
  entryEvery : List (Nat × List EveryClaim) := []
  /-- At a statement entry, the region facts the producer proposes: pairs of
  value bindings' names (FOOTPRINTS.md, "Element regions"). -/
  entryApart : List (Nat × List (String × String)) := []
  /-- At a statement entry, the spine separations the producer proposes,
  each guarded (ARITHMETIC.md, "Spine separation"). -/
  entrySpinesApart : List (Nat × List SpinesApartClaim) := []
  /-- At a statement entry, the read links proposed: `(cell, value, field)`,
  stating that `value` holds the value read from `cell.field`. -/
  entryLinks : List (Nat × List (String × String × String)) := []
  /-- At a statement entry, the element reads proposed: `(guards, value, array, index)`. -/
  entryElements : List (Nat × List ElementClaim) := []
  /-- At a statement entry, the guarded field-read facts proposed:
  `(guards, value, object, field)`. -/
  entryFieldReads : List (Nat × List (List (String × List String × HeapKnowledge.GuardTag) × String × String × String)) := []

/-- Replacement claims for the sites a closure signature owns. Absence of a
current-content assertion replaces that assertion too. -/
def PointData.overlay (base row : PointData ι) : PointData ι :=
  { exprs := row.exprs ++ base.exprs.filter (fun p => !(row.exprs.map Prod.fst).contains p.1)
    envs := row.envs ++ base.envs.filter (fun p => !(row.envs.map Prod.fst).contains p.1)
    entryCurrent := row.entryCurrent ++ base.entryCurrent.filter (fun p =>
      !(row.envs.map Prod.fst).contains p.1)
    exprCurrent := row.exprCurrent ++ base.exprCurrent.filter (fun p =>
      !(row.exprs.map Prod.fst).contains p.1)
    entryBounds := row.entryBounds ++ base.entryBounds.filter (fun p =>
      !(row.envs.map Prod.fst).contains p.1)
    entryFacts := row.entryFacts ++ base.entryFacts.filter (fun p =>
      !(row.envs.map Prod.fst).contains p.1)
    entryEvery := row.entryEvery ++ base.entryEvery.filter (fun p =>
      !(row.envs.map Prod.fst).contains p.1)
    entryApart := row.entryApart ++ base.entryApart.filter (fun p =>
      !(row.envs.map Prod.fst).contains p.1)
    entrySpinesApart := row.entrySpinesApart ++ base.entrySpinesApart.filter (fun p =>
      !(row.envs.map Prod.fst).contains p.1)
    entryLinks := row.entryLinks ++ base.entryLinks.filter (fun p =>
      !(row.envs.map Prod.fst).contains p.1)
    entryElements := row.entryElements ++ base.entryElements.filter (fun p =>
      !(row.envs.map Prod.fst).contains p.1)
    entryFieldReads := row.entryFieldReads ++ base.entryFieldReads.filter (fun p =>
      !(row.envs.map Prod.fst).contains p.1) }

/-- A lifetime storage contract is keyed by its initializer and binding name.
Every execution copy of the declaration uses this same proposal. -/
abbrev Contracts (ι : Type) := List ((Span × String) × Candidate ι)

/-- What one closure body claims under one advertised signature. -/
structure Overlay (ι : Type) extends PointData ι where
  points : List (String × PointData ι) := []
  contracts : Contracts ι := []

structure Function (ι : Type) where
  name : String
  namePos : Span
  params : List (String × Candidate ι)
  ret : Candidate ι
  envs : List (Nat × List (String × Candidate ι))
  exprs : List (Span × Candidate ι)
  entryCurrent : List (Nat × List (String × List (List PropKey × Ty ι))) := []
  exprCurrent : List (Span × List (PropKey × Ty ι)) := []
  entryBounds : List (Nat × List (String × String × Bool)) := []
  entryFacts : List (Nat × List ClauseClaim) := []
  entryEvery : List (Nat × List EveryClaim) := []
  entryApart : List (Nat × List (String × String)) := []
  entrySpinesApart : List (Nat × List SpinesApartClaim) := []
  entryLinks : List (Nat × List (String × String × String)) := []
  entryElements : List (Nat × List ElementClaim) := []
  entryFieldReads : List (Nat × List (List (String × List String × HeapKnowledge.GuardTag) × String × String × String)) := []
  /-- The source closure's interior obligations, one per claimed signature. -/
  arrowClaims : List (Span × List (Overlay ι)) := []
  /-- The declaring unit's parameter rows for each internal constructor scheme. -/
  ctorBinders : List (Span × List ι) := []
  /-- The complete point table survives selection and nested closure checking. -/
  points : List (String × PointData ι) := []
  contracts : Contracts ι := []
  /-- The footprint proposed for a declaration's signature, which its unit
  certifies; the initialization unit's lets everything change. -/
  footprint : Footprints.Closed := .top
  /-- Whether the footprint is proposed on a throw too. -/
  onThrow : Bool := false
  /-- The footprint proposed for the signatures of the function a
  declaration returns (`resultWithFootprint`), which its unit's returns
  certify. -/
  resultFootprint : Footprints.Closed := .top
  /-- Call position `p` (`0` for `this`, `i + 1` for the `i`-th parameter)
  proposed by the pass to be returned unchanged at every reachable return
  (`IndexFact.same 0 (p + 1)`), which its unit's returns certify. -/
  returnAlias : Option Nat := none
  /-- At a flow node's entry, the execution points of the nodes reachable
  from it, computed where first read; `none` where the lowering states none. -/
  reachable : Option (Thunk (List String)) := none

/-- Select one execution point for expression lowering. A missing point has
no claims, so an obligation there fails instead of borrowing another copy's. -/
def Function.atPoint (f : Function ι) (point : String) : Function ι :=
  let row := (f.points.lookup point).getD {}
  { f with
    envs := row.envs
    exprs := row.exprs
    entryCurrent := row.entryCurrent
    exprCurrent := row.exprCurrent
    entryBounds := row.entryBounds
    entryFacts := row.entryFacts
    entryEvery := row.entryEvery
    entryApart := row.entryApart
    entrySpinesApart := row.entrySpinesApart
    entryLinks := row.entryLinks
    entryElements := row.entryElements
    entryFieldReads := row.entryFieldReads }

/-- A signature overlay retains other bodies' claims, while replacing its own
sites in every execution point. -/
def Function.withOverlay (f : Function ι) (row : Overlay ι) : Function ι :=
  let points := (f.points.map Prod.fst ++ row.points.map Prod.fst).eraseDups.map fun id =>
    (id, ((f.points.lookup id).getD {}).overlay ((row.points.lookup id).getD {}))
  let active := (PointData.mk f.exprs f.envs f.entryCurrent f.exprCurrent f.entryBounds f.entryFacts f.entryEvery f.entryApart f.entrySpinesApart f.entryLinks f.entryElements f.entryFieldReads).overlay
    row.toPointData
  { f with
    exprs := active.exprs
    envs := active.envs
    entryCurrent := active.entryCurrent
    exprCurrent := active.exprCurrent
    entryBounds := active.entryBounds
    entryFacts := active.entryFacts
    entryEvery := active.entryEvery
    entryApart := active.entryApart
    entrySpinesApart := active.entrySpinesApart
    entryLinks := active.entryLinks
    entryElements := active.entryElements
    entryFieldReads := active.entryFieldReads
    points := points
    contracts := row.contracts ++ f.contracts.filter (fun p => !(row.contracts.map Prod.fst).contains p.1) }

/-- Labels are checked against the request's own store, so even a direct
caller cannot turn a label the store lacks into its empty default. -/
def resolve (T : EquationStore.State) (c : Candidate EquationGraphs.Tree) : Except String (Ty EquationGraphs.Tree) := do
  let A := EquationStore.sourceRows T (← c)
  if RequestJson.validTy (StoreView.valid T) A then pure A
  else throw "source claim contains an out-of-range type label"

end Verification.SourceClaims
