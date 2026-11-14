import Verification.Programs.ExpressionClaims
import Verification.Programs.DirectObligation
import Verification.Programs.ArgumentRegionCertificates
-- SourceResolution.lean constructs the qualified body checker from the retained
-- source signature and proves the descriptor evidence used by source instances.
import Verification.Source.SourceResolution

namespace Verification.SourceExtraction
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open LabelStore
open EquationGraphs (Tree)

/-- What the source says of one code request's graph, as of a unit's: its
source map, its required assertions, its statement entries' candidate facts
and its cuts. -/
structure CodeSource where
  sourceMap : SourceMap := []
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  candidates : List (Nat × List HeapKnowledge.IndexAtom) := []
  cuts : List Nat := []

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

structure SourceRequest (σ ι : Type) [Labels ι] [StoreView σ ι] extends Request σ ι where
  /-- The enclosing generic signature, retained through label freezing. -/
  sourceScheme : Option (PositiveGraphs.SchemeRow ι) := none
  /-- Constructed from the frozen descriptor domain and source signature. -/
  qualification : Option (RequestJson.QualifiedBody (RequestJson.graph toRequest)
    (StoreView.images toRequest.types)) := none
  obligations : List (ExpressionClaims.Required ι)
  sourceMap : SourceMap := []
  /-- What each point requires: a statement entry's written invariant, its
  bindings' types and contents and its witnesses' links, an observation's
  facts, the entry's precondition. Every one is entailed by the knowledge the
  point's evidence carries (`checkAssertions`). -/
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  /-- The index facts the producer supplies at each statement entry: search
  only, kept at an entry where every edge into it establishes them. -/
  candidates : List (Nat × List HeapKnowledge.IndexAtom) := []
  /-- Statement entries; absent assertions mean empty knowledge. -/
  cuts : List Nat := []
  /-- Labels the program mentions but no claim does: search hints only. -/
  hints : List ι := []
  /-- One per code request, in its order. -/
  codeSources : List CodeSource := []
  /-- Plans for nodes the lowering knows how to derive: search hints only. -/
  nodePlans : List (DirectProof.Plan ι) := []
  /-- The footprint the unit's declaration claims, which its graph must
  establish (`checkRequestResult`). -/
  footprint : Footprints.Closed := .top
  /-- Whether the declaration claims its footprint on a throw too, which its
  graph must establish as well. -/
  onThrow : Bool := false
  /-- Whether the declaration promises a fresh result: each normal return's
  value has an array store the run allocated, which its graph must establish
  (`effectResult`). -/
  fresh : Bool := false
  /-- The bound and the store regions the declaration's stated frame lets
  change, each an input slot and a path of fields read from it
  (`"x[*]": "any"`, `"x.f[*]": "any"`), which its graph must establish off
  those stores (`regionalResult`). -/
  regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion) := none
  /-- The facts the declaration states at its returns (`Fragment.Fn.ensures`),
  position `0` the result and `q + 1` input slot `q`'s entry value, which
  each return of its graph must establish (`ensuresResult`). -/
  ensures : List HeapKnowledge.IndexFact := []
  /-- Whether the declaration is async, as the source states (`Fragment.Fn`):
  its footprint is then `top` (`RequestJson.asyncEffects`). -/
  async : Bool
  /-- The effect the declaration's result annotation states, as the source
  states it (`Fragment.Fn`): the claim must lie within it
  (`RequestJson.statedWithin`). -/
  stated : Option CallEffects.Effect

@[nospecialize] def SourceRequest.codeHints (r : SourceRequest σ ι) : List RequestJson.CodeHints :=
  r.codeSources.map fun c => ⟨c.sourceMap, c.assertions, c.candidates, c.cuts⟩

/-- Search hints only: the primitives and the labels the request mentions, so
a coercion does not consider every unrelated signature in the table. The
consumer still checks against the complete graph and the exact request. -/
@[nospecialize] def SourceRequest.searchLabels (r : SourceRequest σ ι) : List ι :=
  let roots := [Labels.nul,Labels.tru,Labels.fls,Labels.undef] ++ r.result ++ r.inputs.flatten ++ r.hints ++
    r.promise.toList.flatMap (fun (p : Bool × Nat × Ty ι) => p.2.2) ++
    -- Each claimed type once (`keepFirst`, by its object where shared),
    -- then its labels: the same labels in the same first order.
    (keepFirst {} (r.claims.flatMap fun (c : PointClaim ι) => c.type :: c.context)).2.toList.flatten ++
    -- A closure's code is searched with the request's vocabulary: what its
    -- claims mention is part of it (a generic closure's binder rows).
    r.codes.flatMap (fun (q : RequestJson.CodeRequest ι) => q.claims.flatMap (fun (c : PointClaim ι) => c.type ++ c.context.flatten)) ++
    r.obligations.flatMap (fun (o : ExpressionClaims.Required ι) => o.sequent.type ++ o.sequent.context.flatten)
  -- Readonly array coercions depend on the store's element unions two levels
  -- below the object. Close the vocabulary over the reachable graph,
  -- stopping at the fixpoint, where a step adds no label, or at the store's
  -- bound on labels: an equation graph's rows reach infinitely many. Each
  -- label's row is read once, in the step after it is added: the labels an
  -- earlier one reaches are already known.
  Id.run do
    let (seen, first) := keepFirst {} roots
    let mut seen := seen
    let mut known := first
    let mut frontier := first
    for _ in List.range (StoreView.bound r.types) do
      if known.size ≥ StoreView.bound r.types then break
      -- A meet row's clauses name a type the store may hold as a row of its
      -- own, a bounded binder's bound: a read through the binder is at it.
      let (seen', fresh) := keepFirst seen (frontier.toList.flatMap (fun i =>
        let row := StoreView.row r.types i
        row.union.flatMap (fun c => (RequestJson.clauseTypes c).flatten) ++
        (match row with
          | .meet _ cs _ => (StoreView.lookup r.types cs).toList
          | _ => [])))
      if fresh.isEmpty then break
      seen := seen'
      known := known ++ fresh
      frontier := fresh
    return known.toList

end

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

@[nospecialize] def SourceRequest.checker (r : SourceRequest σ ι) :
    HeapExpressionRules.Checker (RequestJson.graph r.toRequest) (StoreView.images r.types) :=
  match r.qualification with
  | none => HeapExpressionRules.Checker.ordinary _ _
  | some q => q.checker

/-- The labels a qualified body's check reads as one another; search proposes
comparisons through them. -/
@[nospecialize] def SourceRequest.aliases (r : SourceRequest σ ι) : List (ι × ι) :=
  match r.qualification with
  | none => []
  | some q => q.aliases

/-- Unqualified bodies permit every assignment; qualified bodies permit the
instances of their retained source signature. -/
def SourceRequest.Admits (r : SourceRequest σ ι) (η : PositiveGraphs.MixedAssignment ι) : Prop :=
  match r.qualification with
  | none => True
  | some q => q.Admits η

/-- Evidence order is source declaration order, independent of export order. -/
structure Bundle (ι : Type) where
  functions : List (Response ι)
  obligations : List (List (ProgramCertificates.Evidence ι))

/-- Candidate provenance of the store regions a unit's statement excepts, read
by no proof: at its entry each region's input slot holds it; elsewhere every
slot may hold any region; each pass removes a fact no incoming edge or
handler establishes, until none does. `ArgumentRegionGraph.checkNodes`
decides whether the result holds on every edge. -/
@[nospecialize] def regionPass (regions : List Footprints.ArgumentStoreRegion)
    (nodes : List ((ControlFlow.Node × ControlFlow.NodeEvidence ι) × Nat))
    (table : Array (List GraphCode.ArgumentPathTracking.Fact)) : Array (List GraphCode.ArgumentPathTracking.Fact) :=
  nodes.foldr (fun ((node, _), l) table =>
    let F := table.getD l []
    let origins := GraphCode.ArgumentRegionGraph.nodeOrigins regions F node.expression
    let out := if GraphCode.pushes node.continuation then GraphCode.ArgumentPathTracking.afterPush F origins else F
    let table := (CertificateProducer.successors node.continuation).foldl (fun table t =>
      table.modify t.label fun D => D.filter fun f => out.contains { f with slot := PointClaims.slot t.mapping f.slot }) table
    match node.handler with
    | some t => table.modify t.label fun D => D.filter fun f =>
        (GraphCode.ArgumentPathTracking.shift F).contains { f with slot := PointClaims.slot t.mapping f.slot }
    | none => table) table

@[nospecialize] def regionIterate (regions : List Footprints.ArgumentStoreRegion)
    (nodes : List ((ControlFlow.Node × ControlFlow.NodeEvidence ι) × Nat)) :
    Nat → Array (List GraphCode.ArgumentPathTracking.Fact) → Option (Array (List GraphCode.ArgumentPathTracking.Fact))
  | 0, _ => none
  | fuel + 1, table =>
    let next := regionPass regions nodes table
    if next = table then some table else regionIterate regions nodes fuel next

@[nospecialize] def regionTable (P : ControlFlow.Program) (C : ControlFlow.Certificate ι) (start : Nat)
    (regions : List Footprints.ArgumentStoreRegion) : List (List GraphCode.ArgumentPathTracking.Fact) :=
  let nodes := (P.zip C).zipIdx
  -- Each region's root, its position's own value, and the region itself.
  let roots := (regions.map fun r => (⟨r.position, []⟩ : Footprints.ArgumentStoreRegion)).eraseDups
  let candidates := (roots ++ regions).eraseDups
  let init := (nodes.map fun ((_, c), l) =>
    if l = start then roots.map fun r => ⟨r.position, r⟩
    else (List.range (ControlFlow.entry c).length).flatMap fun j => candidates.map fun r => ⟨j, r⟩).toArray
  ((regionIterate regions nodes (P.length + 2) init).map Array.toList).getD []

/-- Candidate fresh facts of a regional body, read by no proof: every slot,
as a fresh value and as a fresh cell, at each label but the entry, which has
none; each pass removes, at a node that does not keep its cells, its cell
facts, and at each destination what its edge does not establish, until none
does; without a fixpoint, none at all. `ArgumentRegionGraph.checkNodes`
decides whether the result holds at every node and on every edge. -/
@[nospecialize] def freshTablesPass [DecidableEq ι] (G : PositiveGraphs.NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (nodes : List ((ControlFlow.Node × ControlFlow.NodeEvidence ι) × Nat))
    (tables : Array (List Nat) × Array (List Nat)) : Array (List Nat) × Array (List Nat) :=
  nodes.foldr (fun ((node, c), l) (values, cells) =>
    let F := values.getD l []
    let C := cells.getD l []
    let C := if GraphCode.ArgumentRegionGraph.cellsKept G images sums Φ F C c node.expression node.handler.isSome
      then C else []
    let cells := cells.set! l C
    let outF := GraphCode.ArgumentRegionGraph.freshOut G images sums F C c node.expression
    let outC := GraphCode.ArgumentRegionGraph.cellOut F C node.expression
    let FS := GraphCode.slotSet F
    let CS := GraphCode.slotSet C
    let edge := fun (D : List Nat) (S : Std.HashSet Nat) (out : Bool) (t : ControlFlow.Target) =>
      GraphCode.freshKept D S (GraphCode.pushes node.continuation) out t.mapping
    let (values, cells) := (CertificateProducer.successors node.continuation).foldl (fun (values, cells) t =>
      (values.modify t.label fun D => edge D FS outF t, cells.modify t.label fun D => edge D CS outC t)) (values, cells)
    match node.handler with
    | some t =>
      (values.modify t.label fun D => GraphCode.freshKept D FS true false t.mapping,
        cells.modify t.label fun D => GraphCode.freshKept D CS true false t.mapping)
    | none => (values, cells)) tables

@[nospecialize] def freshTablesIterate [DecidableEq ι] (G : PositiveGraphs.NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (nodes : List ((ControlFlow.Node × ControlFlow.NodeEvidence ι) × Nat)) :
    Nat → Array (List Nat) × Array (List Nat) → Option (Array (List Nat) × Array (List Nat))
  | 0, _ => none
  | fuel + 1, tables =>
    let next := freshTablesPass G images sums Φ nodes tables
    if next = tables then some tables else freshTablesIterate G images sums Φ nodes fuel next

/-- The field names the regions of a body's calls read through one field:
the fields whose freshness its fresh-field facts range over. -/
def regionNames (C : ControlFlow.Certificate ι) : List String :=
  (C.flatMap fun c => match ExpressionEffects.selectedEffect c.expression with
    | some eff => eff.regions.filterMap fun r => match r.path with
      | [f] => some f
      | _ => none
    | none => []).eraseDups

/-- One pass over candidate fresh fields, the fresh values fixed: at each
node the pairs its slots' types do not keep stable are removed, and at each
destination what its edge does not establish. -/
@[nospecialize] def freshFieldsPass [DecidableEq ι] (G : PositiveGraphs.NormalGraph ι) (names : List String)
    (values : Array (List Nat)) (nodes : List ((ControlFlow.Node × ControlFlow.NodeEvidence ι) × Nat))
    (fields : Array (List (Nat × String))) : Array (List (Nat × String)) :=
  nodes.foldr (fun ((node, c), l) fields =>
    let F := values.getD l []
    let Fs := (fields.getD l []).filter fun p =>
      HeapExpressionRules.stableFirst G (ControlFlow.entry c) p.1 p.2 ||
        GraphCode.ArgumentRegionFresh.nullishSlot G (ControlFlow.entry c) p.1
    let fields := fields.set! l Fs
    let out := GraphCode.ArgumentRegionGraph.fieldOut names F Fs node.expression
    let fields := (CertificateProducer.successors node.continuation).foldl (fun fields t =>
      fields.modify t.label fun D => D.filter fun p =>
        GraphCode.ArgumentRegionGraph.fieldSlot Fs out (GraphCode.pushes node.continuation)
          (PointClaims.slot t.mapping p.1) p.2) fields
    match node.handler with
    | some t => fields.modify t.label fun D => D.filter fun p => match PointClaims.slot t.mapping p.1 with
      | 0 => false
      | j + 1 => Fs.contains (j, p.2)
    | none => fields) fields

@[nospecialize] def freshFieldsIterate [DecidableEq ι] (G : PositiveGraphs.NormalGraph ι) (names : List String)
    (values : Array (List Nat)) (nodes : List ((ControlFlow.Node × ControlFlow.NodeEvidence ι) × Nat)) :
    Nat → Array (List (Nat × String)) → Option (Array (List (Nat × String)))
  | 0, _ => none
  | fuel + 1, fields =>
    let next := freshFieldsPass G names values nodes fields
    if next = fields then some fields else freshFieldsIterate G names values nodes fuel next

@[nospecialize] def freshTables [DecidableEq ι] (G : PositiveGraphs.NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (P : ControlFlow.Program) (C : ControlFlow.Certificate ι) (start : Nat) :
    GraphCode.ArgumentRegionFresh.FreshTables :=
  let nodes := (P.zip C).zipIdx
  let init := (nodes.map fun ((_, c), l) =>
    if l = start then [] else List.range (ControlFlow.entry c).length).toArray
  match freshTablesIterate G images sums Φ nodes (2 * P.length + 2) (init, init) with
  | some (values, cells) =>
    -- Fresh fields, inferred after the values and cells and apart from
    -- them: without a fixed point, none.
    let names := regionNames C
    let fields := if names.isEmpty then [] else
      let start' := (nodes.map fun ((_, c), l) => if l = start then [] else
        (List.range (ControlFlow.entry c).length).flatMap fun j => names.map fun f => (j, f)).toArray
      match freshFieldsIterate G names values nodes (2 * P.length + 2) start' with
      | some fields => fields.toList
      | none => []
    ⟨values.toList, cells.toList, fields, names⟩
  | none => ⟨[], [], [], []⟩

/-- **The regional check** of a unit's graph, at a bound `Φ` and store
regions, each an input slot and a path: its runs stay within `Φ` off the
stores the regions select at entry, on a throw too where `exc`
(`ArgumentRegionGraph.checkNodes`), its provenance table and fresh facts
inferred (`regionTable`, `freshTables`), none of them at the entry. With no
regions it is a second certificate of a claimed footprint (`effectResult`). -/
@[nospecialize] def regionalChecked (r : SourceRequest σ ι) (c : Response ι) (Φ : Footprints.Closed)
    (regions : List Footprints.ArgumentStoreRegion) (exc : Bool) : Bool :=
  let P := GraphCode.program (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
  let table := regionTable P c.certificate r.start regions
  let ft := freshTables (RequestJson.graph r.toRequest) (StoreView.images r.types) c.readSummaries Φ P
    c.certificate r.start
  GraphCode.ArgumentPathTracking.checkEntry (GraphCode.ArgumentPathTracking.atLabel table r.start) &&
    ((GraphCode.factsAt ft.values r.start).isEmpty && (GraphCode.factsAt ft.cells r.start).isEmpty) &&
    (GraphCode.ArgumentRegionGraph.fieldsAt ft.fields r.start).isEmpty &&
    GraphCode.ArgumentPathTracking.checkEntryFields (RequestJson.graph r.toRequest) r.inputs regions &&
    GraphCode.ArgumentRegionGraph.checkNodes (RequestJson.graph r.toRequest) (StoreView.images r.types)
      c.readSummaries Φ regions table ft exc P c.certificate

/-- A unit's claimed footprint and fresh result, established by its own graph
and certificate. An async unit's footprint is `top` and it promises no fresh
result, required before anything else. The footprint letting everything
change, without a fresh result or a footprint on a throw, holds of every run;
any other claim is established node by node
(`GraphCode.compositionalChecked`), or, without a fresh result, by a graph of
pure nodes, which preserves the heap, for a unit returning a plain result
under the ordinary checker. A fresh result is established node by node
whatever the footprint, as `GraphCode.effectCheckedResult` does for code.
Where those refuse, a unit promising no fresh result is checked by the
regional check with no regions (`regionalChecked`), whose stores the body
allocated rebase to none. -/
@[nospecialize] def effectResult (r : SourceRequest σ ι) (c : Response ι) : ProgramCertificates.CheckResult ι Unit :=
  (ProgramCertificates.CheckResult.ofBool (RequestJson.asyncEffects r.async r.footprint &&
    (!r.async || !r.fresh) &&
    RequestJson.statedWithin r.async r.footprint r.onThrow r.fresh r.stated)).bind fun _ =>
  if r.footprint = .top ∧ r.onThrow = false ∧ r.fresh = false then pure () else
    (ProgramCertificates.CheckResult.ofBool (r.qualification.isNone && (r.footprint != .top || r.fresh))).bind fun _ =>
    (ProgramCertificates.CheckResult.ofBool (!r.fresh && r.program.all fun n => Purity.pureTerm n.expression)).orElse fun _ =>
    (GraphCode.compositionalCheckedResult (RequestJson.graph r.toRequest) (StoreView.images r.types) c.readSummaries
      r.footprint r.fresh r.onThrow r.start r.program c.certificate).orElse fun _ =>
    ProgramCertificates.CheckResult.ofBool (!r.fresh && regionalChecked r c r.footprint [] r.onThrow)

/-- The store regions a unit's statement excepts (`"x[*]": "any"`), each an
input slot's own store: none, or a graph of a unit that is neither generic,
async, nor promising a fresh result, all of whose runs stay within the
statement's bound off the stores those slots hold at entry, on a throw too
where the statement says so (`regionalChecked`). -/
@[nospecialize] def regionalResult (r : SourceRequest σ ι) (c : Response ι) : ProgramCertificates.CheckResult ι Unit :=
  match r.regional with
  | none => pure ()
  | some (Φ, regions) =>
    ProgramCertificates.CheckResult.ofBool (r.qualification.isNone && !r.async && !r.fresh &&
      regionalChecked r c Φ regions (r.stated.any (·.onThrow)))

/-- A graph is the code its node lists describe. -/
theorem program_nodes (P : Program) :
    GraphCode.program (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) = P := by
  induction P with
  | nil => rfl
  | cons node P ih =>
    cases node
    simp only [GraphCode.program, List.map_cons, List.zip_cons_cons] at ih ⊢
    rw [ih]

/-- The source region represented by a graph, for checks on synthetic nodes. -/
def sourceMapRegion (sourceMap : SourceMap) : Option SourceMapEntry :=
  sourceMap.foldl (fun found next => match found, next with
    | none, next => next
    | found, none => found
    | some a, some b => some (SourceMapEntry.mk
        (min a.pos.1 b.pos.1, max a.pos.2 b.pos.2) "certificate-check" none [])) none

end

section
open EquationStore

/-! ### Requests over the frozen equations -/


/-- Translate labels through their JSON representation. Strict decoding
refuses a label outside the frozen equations. -/
private def relabel {α β : Type} [ToJson α] [FromJson β] [ToJson β] (a : α) : Except String β :=
  decodeStrict "request" (toJson a)

/-- A type read as `F`'s, through `relabel`, each type's once. -/
private abbrev Relabeled (F : Frozen) :=
  StateT (Std.HashMap (Ty Tree) (Ty (CheckedLabel F.equations F.primitive))) (Except String)

private def typeOver (F : Frozen) (A : Ty Tree) : Relabeled F (Ty (CheckedLabel F.equations F.primitive)) := do
  if let some B := (← get).get? A then return B
  let B ← relabel A
  modify fun cache => cache.insert A B
  return B

/-- A sequent read as `F`'s: its context's and its type's labels through
`typeOver`. -/
private def sequentOver (F : Frozen) (j : ProgramCertificates.Sequent Tree) :
    Relabeled F (ProgramCertificates.Sequent (CheckedLabel F.equations F.primitive)) := do
  return ⟨← j.context.mapM (typeOver F), j.term, ← typeOver F j.type⟩

/-- A plan read as `F`'s: each goal through `sequentOver`, each rule through
`relabel`. -/
private partial def planOver (F : Frozen) :
    DirectProof.Plan Tree → Relabeled F (DirectProof.Plan (CheckedLabel F.equations F.primitive))
  | .rule j r ps => do return .rule (← sequentOver F j) (← relabel r) (← ps.mapM (planOver F))
  | .cast j p => do return .cast (← sequentOver F j) (← planOver F p)

/-- The obligations, point claims and node plans of a request read as `F`'s,
each type relabeled once. -/
private def partsOver (F : Frozen) (r : SourceRequest EquationStore.State Tree) :
    Except String (List (ExpressionClaims.Required (CheckedLabel F.equations F.primitive)) ×
      List (PointClaim (CheckedLabel F.equations F.primitive)) ×
      List (DirectProof.Plan (CheckedLabel F.equations F.primitive))) :=
  (do
    let obligations ← r.obligations.mapM fun o => do
      return ({ pos := o.pos, sequent := ← sequentOver F o.sequent, plan := ← o.plan.mapM (planOver F),
                role := o.role, context := o.context } : ExpressionClaims.Required _)
    let claims ← r.claims.mapM fun (c : PointClaim Tree) => do
      return (⟨← c.context.mapM (typeOver F), ← typeOver F c.type⟩ : PointClaim _)
    let nodePlans ← r.nodePlans.mapM (planOver F)
    return (obligations, claims, nodePlans) : Relabeled F _).run' {}

/-- An extracted unit's request over the frozen equations. The program is
the extracted one; every label is read as `F`'s. -/
def SourceRequest.over (F : Frozen) (r : SourceRequest EquationStore.State Tree) :
    Except String (SourceRequest (Checked F.equations F.primitive)
      (CheckedLabel F.equations F.primitive)) := do
  let sourceScheme ← r.sourceScheme.mapM fun s => do
    return ({
      binders := ← relabel s.binders
      signatures := ← relabel s.signatures
      bounds := ← relabel s.bounds
      variadic := ← relabel s.variadic
      resolution := s.resolution } : PositiveGraphs.SchemeRow (CheckedLabel F.equations F.primitive))
  -- The obligations, point claims and node plans, every type relabeled
  -- once (`partsOver`).
  let (obligations, claims, nodePlans) ← partsOver F r
  let result ← relabel r.result
  let promise ← r.promise.mapM fun (asserts, slot, T) => do return (asserts, slot, ← relabel T)
  let inputs ← relabel r.inputs
  let codes ← relabel r.codes
  let hints ← relabel r.hints
  let request : RequestJson.Request (Checked F.equations F.primitive) (CheckedLabel F.equations F.primitive) :=
    { types := F.store, program := r.program, claims := claims, result := result, start := r.start,
      inputs := inputs, codes := codes, promise := promise, entrySeparation := r.entrySeparation,
      entryIndices := r.entryIndices }
  let qualification ← sourceScheme.mapM fun s => do
    let some context := F.store.resolution
      | throw "qualified source signature requires the native descriptor domain"
    let some body := SourceResolution.bodyChecking context.1 context.2 s (StoreView.images F.store)
      | throw "invalid descriptor groups in the source signature"
    return body
  return { toRequest := request, sourceScheme, qualification, obligations := obligations, sourceMap := r.sourceMap,
           assertions := r.assertions, candidates := r.candidates, cuts := r.cuts, hints := hints, codeSources := r.codeSources,
           nodePlans := nodePlans, footprint := r.footprint, onThrow := r.onThrow, fresh := r.fresh, regional := r.regional,
           ensures := r.ensures,
           async := r.async, stated := r.stated }

end

end Verification.SourceExtraction
