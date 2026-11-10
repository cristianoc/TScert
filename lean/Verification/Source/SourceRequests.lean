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
    r.claims.flatMap (fun (c : PointClaim ι) => c.type ++ c.context.flatten) ++
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

/-- Each point's required assertion, in a unit's graph and in each of its
codes', is entailed by the knowledge the point's evidence carries, which may
state more: a statement entry's knowledge holds what every edge into it
establishes, each edge checked by the graph's check. -/
def checkGraphAssertions (assertions : List (Nat × HeapKnowledge.Knowledge))
    (C : ControlFlow.Certificate ι) : Bool :=
  assertions.all fun (l,k) => match C[l]? with
    | none => false
    | some n => HeapKnowledge.check (KnowledgeExpand.expand (fun _ => none) n.knowledge) k none

@[nospecialize] def checkAssertions (r : SourceRequest σ ι) (c : Response ι) : Bool :=
  checkGraphAssertions r.assertions c.certificate &&
  r.codeSources.length == c.codes.length &&
  (r.codeSources.zip c.codes).all fun (q, C) => checkGraphAssertions q.assertions C

/-- Each stated assertion is entailed by the knowledge its node carries: every
environment and heap meeting the node's knowledge meet the assertion. -/
def AssertionsEntailed (assertions : List (Nat × HeapKnowledge.Knowledge))
    (C : ControlFlow.Certificate ι) : Prop :=
  ∀ l k, (l, k) ∈ assertions → ∃ n, C[l]? = some n ∧
    ∀ ρ h, HeapKnowledge.Holds n.knowledge ρ h → HeapKnowledge.Holds k ρ h

omit [Labels ι] in
theorem checkGraphAssertions_entailed
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {C : ControlFlow.Certificate ι}
    (h : checkGraphAssertions assertions C = true) : AssertionsEntailed assertions C := by
  intro l k hlk
  simp only [checkGraphAssertions, List.all_eq_true] at h
  have hk := h (l, k) hlk
  cases hn : C[l]? with
  | none => simp [hn] at hk
  | some n =>
    simp only [hn] at hk
    refine ⟨n, rfl, fun ρ heap hold => ?_⟩
    have hx := KnowledgeExpand.expand_holds (ctx := fun _ => none) (fun _ _ hc => by cases hc) hold
    exact HeapKnowledge.check_sound hk hx

/-- The assertions of a unit's graph and of each of its codes are entailed. -/
def RequestAssertionsEntailed (r : SourceRequest σ ι) (c : Response ι) : Prop :=
  AssertionsEntailed r.assertions c.certificate ∧
    ∀ q C, (q, C) ∈ r.codeSources.zip c.codes → AssertionsEntailed q.assertions C

theorem checkAssertions_entailed {r : SourceRequest σ ι} {c : Response ι}
    (h : checkAssertions r c = true) : RequestAssertionsEntailed r c := by
  simp only [checkAssertions, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨checkGraphAssertions_entailed h.1.1, fun q C hm => checkGraphAssertions_entailed (h.2 (q, C) hm)⟩

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
    let edge := fun (D : List Nat) (S : List Nat) (out : Bool) (t : ControlFlow.Target) =>
      D.filter fun i => GraphCode.freshSlot S (GraphCode.pushes node.continuation) out (PointClaims.slot t.mapping i)
    let (values, cells) := (CertificateProducer.successors node.continuation).foldl (fun (values, cells) t =>
      (values.modify t.label fun D => edge D F outF t, cells.modify t.label fun D => edge D C outC t)) (values, cells)
    match node.handler with
    | some t =>
      let handle := fun (D : List Nat) (S : List Nat) =>
        D.filter fun i => GraphCode.freshSlot S true false (PointClaims.slot t.mapping i)
      (values.modify t.label fun D => handle D F, cells.modify t.label fun D => handle D C)
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

theorem effectResult_preserving {r : SourceRequest σ ι} {c : Response ι}
    (h : (effectResult r c).accepted = true)
    (he : r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true) :
    r.qualification = none ∧
      ((r.fresh = false ∧ r.program.all (fun n => Purity.pureTerm n.expression) = true) ∨
        GraphCode.compositionalChecked (RequestJson.graph r.toRequest) (StoreView.images r.types) c.readSummaries
          r.footprint r.fresh r.onThrow r.start r.program c.certificate = true ∨
        (r.fresh = false ∧ regionalChecked r c r.footprint [] r.onThrow = true)) := by
  have hn : ¬(r.footprint = .top ∧ r.onThrow = false ∧ r.fresh = false) := by
    rintro ⟨h1, h2, h3⟩
    rcases he with he | he | he
    · exact he h1
    · rw [h2] at he; cases he
    · rw [h3] at he; cases he
  simp only [effectResult, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, Bool.and_eq_true] at h
  replace h := h.2
  simp only [hn, if_false, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, ProgramCertificates.CheckResult.accepted_orElse,
    Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.or_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, by simpa only [or_assoc, GraphCode.compositionalChecked] using h.2⟩

/-- **An async unit's footprint is `top`** where its effect is checked. -/
theorem effectResult_async {r : SourceRequest σ ι} {c : Response ι}
    (h : (effectResult r c).accepted = true) (ha : r.async = true) : r.footprint = .top := by
  simp only [effectResult, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, Bool.and_eq_true] at h
  simpa [RequestJson.asyncEffects, ha] using h.1.1.1

/-- **A stated unit's claim is within its statement** where its effect is
checked: the statement adds a guarantee (a footprint below `top`, or a fresh
result), the claim's footprint is within the statement's, on a throw too
where the statement says so, it promises a fresh result where the statement
does, and the unit is not async. -/
theorem effectResult_stated {r : SourceRequest σ ι} {c : Response ι}
    (h : (effectResult r c).accepted = true) {s : CallEffects.Effect} (hs : r.stated = some s)
    (hreg : s.regions = []) :
    r.async = false ∧ (s.footprint ≠ .top ∨ s.fresh = true) ∧ r.footprint.le s.footprint = true ∧
      (s.onThrow = true → r.onThrow = true) ∧ (s.fresh = true → r.fresh = true) := by
  simp only [effectResult, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, Bool.and_eq_true] at h
  have hw := h.1.2
  rw [hs] at hw
  simp only [RequestJson.statedWithin, hreg, List.isEmpty_nil, Bool.not_true, Bool.false_or, Bool.or_false,
    Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, Bool.or_eq_true] at hw
  obtain ⟨⟨⟨⟨ha, htop⟩, hle⟩, ho⟩, hf⟩ := hw
  refine ⟨ha, htop, hle, fun hso => ?_, fun hsf => ?_⟩
  · rcases ho with ho | ho
    · rw [hso] at ho; cases ho
    · exact ho
  · rcases hf with hf | hf
    · rw [hsf] at hf; cases hf
    · exact hf

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

/-- A unit's postcondition, established by its own graph: none, or facts of
its result and of its inputs' entry values, which each return its graph may
reach entails (`GraphCode.returnsEnsure`), for a unit checked by the ordinary
checker. -/
@[nospecialize] def ensuresResult (r : SourceRequest σ ι) (c : Response ι) : ProgramCertificates.CheckResult ι Unit :=
  if r.ensures.isEmpty then pure () else
    (ProgramCertificates.CheckResult.ofBool r.qualification.isNone).bind fun _ =>
      GraphCode.returnsEnsureResult (RequestJson.graph r.toRequest) r.program c.certificate r.ensures r.start

theorem ensuresResult_checked {r : SourceRequest σ ι} {c : Response ι}
    (h : (ensuresResult r c).accepted = true) (he : r.ensures ≠ []) :
    r.qualification = none ∧
      GraphCode.returnsEnsure (RequestJson.graph r.toRequest) r.program c.certificate r.ensures r.start = true := by
  have hn : r.ensures.isEmpty = false := by simpa using he
  simp only [ensuresResult, hn, Bool.false_eq_true, if_false, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, GraphCode.returnsEnsureResult_accepted, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at h
  exact h

/-- Validate one unit, sharing its checked code table with supplemental obligations. -/
@[nospecialize] def checkRequestResult (r : SourceRequest σ ι) (c : Response ι)
    (es : List (ProgramCertificates.Evidence ι)) : ProgramCertificates.CheckResult ι Unit :=
  (verifyResult r.toRequest c r.checker).bind fun table =>
    (ProgramCertificates.CheckResult.ofBool (checkAssertions r c)).bind fun _ =>
    (effectResult r c).bind fun _ =>
    (ensuresResult r c).bind fun _ =>
    (regionalResult r c).bind fun _ =>
    ExpressionClaims.checkAllResult (RequestJson.graph r.toRequest) (StoreView.images r.types)
      (StoreView.valid r.types) r.obligations es (GraphCode.admits table) c.readSummaries

theorem checkRequestResult_accepted_iff (r : SourceRequest σ ι) (c : Response ι)
    (es : List (ProgramCertificates.Evidence ι)) :
    (checkRequestResult r c es).accepted = true ↔
      verify r.toRequest c r.checker = true ∧ checkAssertions r c = true ∧
      (effectResult r c).accepted = true ∧ (ensuresResult r c).accepted = true ∧
      (regionalResult r c).accepted = true ∧
      ∃ table, codeTable r.toRequest c = some table ∧
        ExpressionClaims.checkAllUsing (RequestJson.graph r.toRequest) (StoreView.images r.types)
          (StoreView.valid r.types) r.obligations es (GraphCode.admits table) c.readSummaries = true := by
  rw [checkRequestResult, ProgramCertificates.CheckResult.accepted_bind_value,
    Option.any_eq_true]
  constructor
  · rintro ⟨table, ht, hc⟩
    obtain ⟨hv, htable⟩ := (verifyResult_hasTable _ _ _ r.checker).mp ht
    simp only [ProgramCertificates.CheckResult.accepted_bind,
      ProgramCertificates.CheckResult.accepted_ofBool, Bool.and_eq_true] at hc
    exact ⟨hv, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, table, htable, hc.2.2.2.2⟩
  · rintro ⟨hv, ha, hf, hens, hreg, table, ht, ho⟩
    refine ⟨table, (verifyResult_hasTable _ _ _ r.checker).mpr ⟨hv, ht⟩, ?_⟩
    simp only [ProgramCertificates.CheckResult.accepted_bind,
      ProgramCertificates.CheckResult.accepted_ofBool, Bool.and_eq_true]
    exact ⟨ha, hf, hens, hreg, ho⟩

@[nospecialize] def checkRequestsResult (rs : List (SourceRequest σ ι)) (b : Bundle ι) :
    ProgramCertificates.CheckResult ι Unit :=
  (ProgramCertificates.CheckResult.ofBool (rs.length == b.functions.length &&
    rs.length == b.obligations.length)).bind fun _ =>
  ProgramCertificates.CheckResult.allLocated ((rs.zip b.functions).zip b.obligations) .request
    fun ((r,c),es) => checkRequestResult r c es

/-- The part of `checkRequestResult` a unit's search leaves to be checked: a
response its search returned (`RequestJson.produceResponseUsing`) has passed
`verifyResult` there, its code table being its codes' entries in order, so
its assertions, effect, postcondition, store regions and obligations remain.
Search only: acceptance is `checkRequestsResult`. -/
@[nospecialize] def searchedRequestResult (r : SourceRequest σ ι) (c : Response ι)
    (es : List (ProgramCertificates.Evidence ι)) : ProgramCertificates.CheckResult ι Unit :=
  (ProgramCertificates.CheckResult.ofBool (checkAssertions r c)).bind fun _ =>
  (effectResult r c).bind fun _ =>
  (ensuresResult r c).bind fun _ =>
  (regionalResult r c).bind fun _ =>
  ExpressionClaims.checkAllResult (RequestJson.graph r.toRequest) (StoreView.images r.types)
    (StoreView.valid r.types) r.obligations es (GraphCode.admits (r.toRequest.codes.map (·.entry)))
    c.readSummaries

/-- `checkRequestsResult` over responses their searches returned
(`searchedRequestResult`). Search only. -/
@[nospecialize] def searchedRequestsResult (rs : List (SourceRequest σ ι)) (b : Bundle ι) :
    ProgramCertificates.CheckResult ι Unit :=
  (ProgramCertificates.CheckResult.ofBool (rs.length == b.functions.length &&
    rs.length == b.obligations.length)).bind fun _ =>
  ProgramCertificates.CheckResult.allLocated ((rs.zip b.functions).zip b.obligations) .request
    fun ((r,c),es) => searchedRequestResult r c es

@[nospecialize] def checkRequests (rs : List (SourceRequest σ ι)) (b : Bundle ι) : Bool :=
  (checkRequestsResult rs b).accepted

theorem checkRequests_eq (rs : List (SourceRequest σ ι)) (b : Bundle ι) :
    checkRequests rs b = (rs.length == b.functions.length && rs.length == b.obligations.length &&
      ((rs.zip b.functions).zip b.obligations).all (fun ((r,c),es) => (checkRequestResult r c es).accepted)) := by
  rw [checkRequests, checkRequestsResult, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, ProgramCertificates.CheckResult.accepted_allLocated]

theorem checkRequests_one {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (h : checkRequests rs b = true) {r c es}
    (hm : ((r,c),es) ∈ (rs.zip b.functions).zip b.obligations) :
    (checkRequestResult r c es).accepted = true := by
  rw [checkRequests_eq] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 ((r,c),es) hm

/-- Exact bundle lengths give every requested unit its supplemental evidence. -/
theorem checkRequests_pair {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions) :
    ∃ es, ((r,c),es) ∈ (rs.zip b.functions).zip b.obligations ∧
      (checkRequestResult r c es).accepted = true := by
  have counts := h
  rw [checkRequests_eq] at counts
  have lengths := (Bool.and_eq_true_iff.mp counts).1
  simp only [Bool.and_eq_true, beq_iff_eq] at lengths
  have hl : (rs.zip b.functions).length = b.obligations.length := by
    simp only [List.length_zip, ← lengths.1, lengths.2, Nat.min_self]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  have hib : i < b.obligations.length := hl ▸ (List.getElem?_eq_some_iff.mp hi).1
  let es := b.obligations[i]'hib
  have hz : ((rs.zip b.functions).zip b.obligations)[i]? = some ((r,c),es) :=
    List.getElem?_zip_eq_some.mpr ⟨hi, by simp [es, hib]⟩
  have hm' := List.mem_of_getElem? hz
  exact ⟨es, hm', checkRequests_one h hm'⟩

/-- **Async definitions are certified at `top`** (L6 of the method effects
design): in an accepted bundle, an async unit claims the footprint letting
every location change, and so does every async code its graph creates. The
completion kind is the source's (`Fragment.Fn.async`, `Expr.lambda`). -/
theorem checkRequests_async {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions) :
    (r.async = true → r.footprint = .top) ∧
      ∀ q ∈ r.codes, q.async = true → q.entry.row.effect.footprint = .top := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
  obtain ⟨-, -, heff, -, -, table, ht, -⟩ := (checkRequestResult_accepted_iff _ _ _).mp hunit
  exact ⟨effectResult_async heff, fun q hq ha => RequestJson.codeTable_async ht hq ha⟩

/-- An accepted unit's stated assertions are entailed by its certificate. -/
theorem checkRequests_assertions_at {rs : List (SourceRequest σ ι)} {b : (Bundle ι)}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions) :
    RequestAssertionsEntailed r c := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
  exact checkAssertions_entailed ((checkRequestResult_accepted_iff _ _ _).mp hunit).2.1

/-- A generic body is safe at every assignment admitted by its source signature. -/
theorem checkRequests_safe_at {rs : List (SourceRequest σ ι)} {b : (Bundle ι)}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions)
    (η : PositiveGraphs.MixedAssignment ι) (admitted : r.Admits η) (n W heap ρ)
    (he : EnvOk (reassign (RequestJson.graph r.toRequest) η) r.inputs ρ n W) (hw : WorldAdm W)
    (hh : HeapOk n W heap) (hsep : HeapSeparation.Holds r.entrySeparation ρ)
    (hidx : HeapKnowledge.IndexHolds r.entryIndices ρ heap) :
    SafeGraph (excOf (reassign (RequestJson.graph r.toRequest) η)) r.program
      (ControlFlow.GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument ρ)) n W heap
      (.at r.start ρ) := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
  have checked := ((checkRequestResult_accepted_iff _ _ _).mp hunit).1
  cases hq : r.qualification with
  | none =>
    simp only [SourceRequest.checker, hq] at checked
    exact verify_safe_at checked η n W heap ρ he hw hh hsep hidx
  | some q =>
    simp only [SourceRequest.checker, hq, QualifiedBody.checker] at checked
    simp only [SourceRequest.Admits, hq, QualifiedBody.Admits] at admitted
    obtain ⟨θ, As, length, allowed, bounded, rfl⟩ := admitted
    exact verify_qualified_safe_at q.source q.domain q.body q.aliases q.aliases_sound q.check_eq checked
      θ As length allowed bounded n W heap ρ he hw hh hsep hidx

/-- A graph is the code its node lists describe. -/
theorem program_nodes (P : Program) :
    GraphCode.program (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler)) = P := by
  induction P with
  | nil => rfl
  | cons node P ih =>
    cases node
    simp only [GraphCode.program, List.map_cons, List.zip_cons_cons] at ih ⊢
    rw [ih]

theorem regionalResult_checked {r : SourceRequest σ ι} {c : Response ι}
    (h : (regionalResult r c).accepted = true) {Φ : Footprints.Closed} {regions : List Footprints.ArgumentStoreRegion}
    (hr : r.regional = some (Φ, regions)) :
    r.qualification = none ∧ regionalChecked r c Φ regions (r.stated.any (·.onThrow)) = true := by
  simp only [regionalResult, hr, ProgramCertificates.CheckResult.accepted_ofBool, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1, h.2⟩

/-- **A graph the regional check accepts meets its frame**: run as the code
it describes from any environment of values its inputs admit, on normal
return, and on a throw where `exc`, every location of its entry heap but
the stores its regions select at entry is within `Φ` of its entry
contents. -/
theorem regionalChecked_at {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions) (hq : r.qualification = none)
    {Φ : Footprints.Closed} {regions : List Footprints.ArgumentStoreRegion} {exc : Bool}
    (hreg : regionalChecked r c Φ regions exc = true)
    (η : PositiveGraphs.MixedAssignment ι) (n W heap) (L : List Tm) (d : Tm)
    (he : EnvOk (reassign (RequestJson.graph r.toRequest) η) r.inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W heap)
    (hsep : HeapSeparation.Holds r.entrySeparation (envOf L d))
    (hidx : HeapKnowledge.IndexHolds r.entryIndices (envOf L d) heap) :
    HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
      (ControlFlow.GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' _ => Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) heap h')
      (fun h' => exc = true → Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) heap h') n W heap
      (.goto (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        r.start L d) := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
  obtain ⟨checked, -⟩ := (checkRequestResult_accepted_iff _ _ _).mp hunit
  simp only [regionalChecked, Bool.and_eq_true] at hreg
  obtain ⟨⟨⟨⟨hstart, hfresh⟩, hfieldStart⟩, hfields⟩, hnodes⟩ := hreg
  simp only [SourceRequest.checker, hq] at checked
  rw [verify_eq] at checked
  simp only [Bool.and_eq_true] at checked
  have hx := checked.2
  split at hx
  · rename_i table ht
    let G := RequestJson.graph r.toRequest
    let images := StoreView.images r.types
    have hcodes : ProgramCertificates.CodesSound (reassign G η) (GraphCode.admits table) :=
      fun e he η' => codeTable_sound ht e he η'
    have hsums := Parametricity.summariesSound_reassign G η images (codeTable_summaries ht)
    have hacc := (Parametricity.accept_reassign G η images r.goal r.program r.claims c.certificate
      r.start r.inputs (GraphCode.admits table) c.readSummaries r.entrySeparation r.entryIndices).trans hx
    simp only [CertificateProducer.acceptUsing_eq, Bool.and_eq_true] at hacc
    have hP := program_nodes r.program
    have hc := hacc.2
    rw [← hP] at hc
    have hgraph : checkGraphUsing (sums := c.readSummaries) (reassign G η) (images.reassign η) r.goal
        (GraphCode.program (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler)))
        c.certificate (GraphCode.admits table) = true := by
      have hchecked := hc
      simp only [checkEntryUsing_eq, Bool.and_eq_true] at hchecked
      exact hchecked.1
    rw [← GraphCode.ArgumentRegionGraph.checkNodes_reassign G images c.readSummaries η] at hnodes
    exact GraphCode.ArgumentRegionGraph.goto_bounded hc hcodes hsums
      (GraphCode.ArgumentRegionGraph.checkNodes_sound hgraph hcodes hsums hnodes) hstart
      (by simpa only [Bool.and_eq_true] using hfresh) hfieldStart
      (by rw [GraphCode.ArgumentRegionGraph.checkEntryFields_reassign]; exact hfields)
      n W heap L d he hw hh hsep hidx
  · contradiction

/-- **A unit claiming a footprint meets it.** A unit claiming a footprint
other than the one letting everything change, or claiming it on a throw, or
promising a fresh result, run as the code its graph describes from any
environment of values its inputs admit, is safe; on normal return the heap
it leaves is within its footprint of its entry heap, and the value it
returns has an array store at or above the entry heap's length where it
promises a fresh result; the heap a throw leaves is within its footprint
where it claims `onThrow`. -/
theorem checkRequests_footprint_at {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions)
    (heffect : r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true)
    (η : PositiveGraphs.MixedAssignment ι) (n W heap) (L : List Tm) (d : Tm)
    (he : EnvOk (reassign (RequestJson.graph r.toRequest) η) r.inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W heap) (hvalues : ∀ v ∈ L, isVal v = true) (hd : isVal d = true)
    (hsep : HeapSeparation.Holds r.entrySeparation (envOf L d))
    (hidx : HeapKnowledge.IndexHolds r.entryIndices (envOf L d) heap) :
    HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
      (ControlFlow.GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' v => r.footprint.Holds heap h' ∧ (r.fresh = true → Footprints.FreshAt heap.length v))
      (fun h' => r.onThrow = true → r.footprint.Holds heap h') n W heap
      (.goto (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        r.start L d) := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
  obtain ⟨checked, -, heff, -⟩ := (checkRequestResult_accepted_iff _ _ _).mp hunit
  obtain ⟨hq, hp⟩ := effectResult_preserving heff heffect
  rw [← or_assoc] at hp
  rcases hp with hp | ⟨hfr, hreg⟩
  rotate_left
  · -- The regional check with no regions: within the footprint everywhere.
    exact HeapObservations.SafePostExc.weaken
      (fun _ _ hq => ⟨Footprints.ArgumentStoreRegionsWithin.nil_holds hq, fun hf => by rw [hfr] at hf; cases hf⟩)
      (fun _ hq ho => Footprints.ArgumentStoreRegionsWithin.nil_holds (hq ho))
      (regionalChecked_at h hm hq hreg η n W heap L d he hw hh hsep hidx)
  simp only [SourceRequest.checker, hq] at checked
  rw [verify_eq] at checked
  simp only [Bool.and_eq_true] at checked
  have hx := checked.2
  split at hx
  · rename_i table ht
    let G := RequestJson.graph r.toRequest
    let images := StoreView.images r.types
    have hcodes : ProgramCertificates.CodesSound (reassign G η) (GraphCode.admits table) :=
      fun e he η' => codeTable_sound ht e he η'
    have hsums := Parametricity.summariesSound_reassign G η images (codeTable_summaries ht)
    have hacc := (Parametricity.accept_reassign G η images r.goal r.program r.claims c.certificate
      r.start r.inputs (GraphCode.admits table) c.readSummaries r.entrySeparation r.entryIndices).trans hx
    simp only [CertificateProducer.acceptUsing_eq, Bool.and_eq_true] at hacc
    have hP := program_nodes r.program
    have hc := hacc.2
    rw [← hP] at hc
    have hs := GraphCode.goto_safe hc hcodes hsums n W heap L d he hw hh hsep hidx
    rcases hp with ⟨hfresh, hp⟩ | hp
    · -- A pure graph keeps the heap a prefix at every step, a raise included.
      have hp : ∀ e ∈ r.program.map (·.expression), Purity.pureTerm e = true := by
        intro e he
        obtain ⟨node, hn, rfl⟩ := List.mem_map.mp he
        exact List.all_eq_true.mp hp node hn
      exact HeapObservations.SafePostExc.weaken
        (fun _ _ h => ⟨Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _)
          ((CallEffects.Effect.post_ofFootprint _ .undef [] _ _ _).mp h), fun hf => by rw [hfresh] at hf; cases hf⟩)
        (fun _ h _ => Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _) h)
        (CallEffects.pure_safe_exc (r := .undef) (args := []) (.goto hp hvalues hd) hs)
    · rw [← hP] at hp
      erw [← GraphCode.compositionalChecked_reassign G images c.readSummaries η, GraphCode.compositionalChecked_eq] at hp
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hp
      have hgraph : checkGraphUsing (sums := c.readSummaries) (reassign G η) (images.reassign η) r.goal
          (GraphCode.program (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))) c.certificate (GraphCode.admits table) = true := by
        have hchecked := hc
        simp only [checkEntryUsing_eq, Bool.and_eq_true] at hchecked
        exact hchecked.1
      have hb := GraphCode.goto_bounded hc hcodes hsums (GraphCode.nodes_of_checked hgraph hcodes hsums hp.2) hp.1
        n W heap L d he hw hh hsep hidx
      exact HeapObservations.SafePostExc.weaken (fun _ _ hq => hq) (fun _ hq => hq) hb
  · contradiction

/-- **A unit stating a postcondition meets it.** A unit whose declaration
states facts of its result and its inputs (`ensures`), run as the code its
graph describes from any environment of values its inputs admit, is safe,
and every value it returns meets the facts, with the inputs' entry values,
in the heap it returns in. -/
theorem checkRequests_ensures_at {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions) (hens : r.ensures ≠ [])
    (η : PositiveGraphs.MixedAssignment ι) (n W heap) (L : List Tm) (d : Tm)
    (he : EnvOk (reassign (RequestJson.graph r.toRequest) η) r.inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W heap)
    (hsep : HeapSeparation.Holds r.entrySeparation (envOf L d))
    (hidx : HeapKnowledge.IndexHolds r.entryIndices (envOf L d) heap) :
    HeapObservations.SafePost (excOf (reassign (RequestJson.graph r.toRequest) η))
      (ControlFlow.GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' v => GraphCode.EnsuresAt r.ensures h' (push v (envOf L d))) n W heap
      (.goto (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        r.start L d) := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
  obtain ⟨checked, -, -, hres, -⟩ := (checkRequestResult_accepted_iff _ _ _).mp hunit
  obtain ⟨hq, hret⟩ := ensuresResult_checked hres hens
  simp only [SourceRequest.checker, hq] at checked
  rw [verify_eq] at checked
  simp only [Bool.and_eq_true] at checked
  have hx := checked.2
  split at hx
  · rename_i table ht
    let G := RequestJson.graph r.toRequest
    let images := StoreView.images r.types
    have hcodes : ProgramCertificates.CodesSound (reassign G η) (GraphCode.admits table) :=
      fun e he η' => codeTable_sound ht e he η'
    have hsums := Parametricity.summariesSound_reassign G η images (codeTable_summaries ht)
    have hacc := (Parametricity.accept_reassign G η images r.goal r.program r.claims c.certificate
      r.start r.inputs (GraphCode.admits table) c.readSummaries r.entrySeparation r.entryIndices).trans hx
    simp only [CertificateProducer.acceptUsing_eq, Bool.and_eq_true] at hacc
    have hP := program_nodes r.program
    have hc := hacc.2
    rw [← hP] at hc
    have hret' : GraphCode.returnsEnsure (reassign G η)
        (GraphCode.program (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler)))
        c.certificate r.ensures r.start = true := by
      rw [GraphCode.returnsEnsure_reassign, hP]; exact hret
    exact GraphCode.goto_ensures hc hcodes hsums hret' n W heap L d he hw hh hsep hidx
  · contradiction

/-- **A unit stating an effect meets it** (`Modifies<P, T>`; SOURCE-ELABORATION.md,
"Stated effects"): run as the code its graph describes from any environment
of values its inputs, its annotated parameters, admit, it is safe; on normal
return the heap it leaves is within its statement's footprint of its entry
heap, and the value it returns has an array store at or above the entry
heap's length where the statement promises a fresh result; the heap a throw
leaves is within the statement's footprint where the statement says so. -/
theorem checkRequests_stated_at {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions)
    {s : CallEffects.Effect} (hs : r.stated = some s) (hreg : s.regions = [])
    (η : PositiveGraphs.MixedAssignment ι) (n W heap) (L : List Tm) (d : Tm)
    (he : EnvOk (reassign (RequestJson.graph r.toRequest) η) r.inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W heap) (hvalues : ∀ v ∈ L, isVal v = true) (hd : isVal d = true)
    (hsep : HeapSeparation.Holds r.entrySeparation (envOf L d))
    (hidx : HeapKnowledge.IndexHolds r.entryIndices (envOf L d) heap) :
    HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
      (ControlFlow.GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' v => s.footprint.Holds heap h' ∧ (s.fresh = true → Footprints.FreshAt heap.length v))
      (fun h' => s.onThrow = true → s.footprint.Holds heap h') n W heap
      (.goto (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        r.start L d) := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
  obtain ⟨-, -, heff, -⟩ := (checkRequestResult_accepted_iff _ _ _).mp hunit
  obtain ⟨-, htop, hle, hthrow, hfresh⟩ := effectResult_stated heff hs hreg
  have heffect : r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true := by
    rcases htop with htop | htop
    · refine .inl fun hr => htop ?_
      rw [hr] at hle
      cases hsf : s.footprint with
      | mk v st =>
        rw [hsf] at hle
        cases v <;> cases st <;> simp_all [Footprints.Closed.top, Footprints.Closed.le, Footprints.Change.le, Footprints.Change.rank, Footprints.Change.onValue, Footprints.Change.onStore]
    · exact .inr (.inr (hfresh htop))
  exact HeapObservations.SafePostExc.weaken
    (fun h' _ hq => ⟨Footprints.Closed.Holds.mono hle hq.1, fun hsf => hq.2 (hfresh hsf)⟩)
    (fun h' hq ho => Footprints.Closed.Holds.mono hle (hq (hthrow ho)))
    (checkRequests_footprint_at h hm heffect η n W heap L d he hw hh hvalues hd hsep hidx)

/-- **A unit stating store regions meets them** (`"x[*]": "any"`;
SOURCE-ELABORATION.md, "Stated effects"): run as the code its graph describes
from any environment of values its inputs admit, it is safe; on normal
return, and on a throw where its statement says so, every location of its
entry heap but the stores its region slots hold at entry is within the
statement's bound of its entry contents. -/
theorem checkRequests_regional_at {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions)
    {Φ : Footprints.Closed} {regions : List Footprints.ArgumentStoreRegion} (hr : r.regional = some (Φ, regions))
    (η : PositiveGraphs.MixedAssignment ι) (n W heap) (L : List Tm) (d : Tm)
    (he : EnvOk (reassign (RequestJson.graph r.toRequest) η) r.inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W heap)
    (hsep : HeapSeparation.Holds r.entrySeparation (envOf L d))
    (hidx : HeapKnowledge.IndexHolds r.entryIndices (envOf L d) heap) :
    HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
      (ControlFlow.GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' _ => Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) heap h')
      (fun h' => r.stated.any (·.onThrow) = true →
        Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) heap h') n W heap
      (.goto (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        r.start L d) := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
  obtain ⟨-, -, -, -, hreg, -⟩ := (checkRequestResult_accepted_iff _ _ _).mp hunit
  obtain ⟨hq, hchecked⟩ := regionalResult_checked hreg hr
  exact regionalChecked_at h hm hq hchecked η n W heap L d he hw hh hsep hidx

/-- The source region represented by a graph, for checks on synthetic nodes. -/
def sourceMapRegion (sourceMap : SourceMap) : Option SourceMapEntry :=
  sourceMap.foldl (fun found next => match found, next with
    | none, next => next
    | found, none => found
    | some a, some b => some (SourceMapEntry.mk
        (min a.pos.1 b.pos.1, max a.pos.2 b.pos.2) "certificate-check" none [])) none

/-- Diagnostic provenance selects an actual source point or its enclosing graph region. -/
@[nospecialize] def validationOrigin (r : SourceRequest σ ι) (frames : List ProgramCertificates.CheckFrame) :
    Option SourceMapEntry :=
  match frames with
  | [.node label] => ((r.sourceMap[label]?).bind id) <|> sourceMapRegion r.sourceMap
  | [.code index, .node label] =>
      ((r.codeSources[index]?).bind fun code =>
        ((code.sourceMap[label]?).bind id) <|> sourceMapRegion code.sourceMap) <|> sourceMapRegion r.sourceMap
  | [.code index] => ((r.codeSources[index]?).bind fun code => sourceMapRegion code.sourceMap) <|>
      sourceMapRegion r.sourceMap
  | [.obligation index] => (r.obligations[index]?).map fun q =>
      SourceMapEntry.mk q.pos q.role none []
  | [] | .node _ :: _ | .code _ :: _ | .obligation _ :: _ | .request _ :: _ => sourceMapRegion r.sourceMap

/-- Report the retained comparison through the source map; validation is not rerun. -/
@[nospecialize] def validationFailure (rs : List (SourceRequest σ ι))
    (checked : ProgramCertificates.CheckResult ι Unit) (fallback : String) : String := Id.run do
  let some stop := checked.exhaustion | return fallback
  let .request index :: frames := stop.frames | return "exhausted certificate check has no enclosing source request"
  let some r := rs[index]? | return "exhausted certificate check names no source request"
  let some origin := validationOrigin r frames | return "exhausted certificate check has no source region"
  let p := StoreView.projection r.types (stop.source ++ stop.target).eraseDups
  return RequestJson.withDiagnostic "subtype search exhausted during certificate validation; result is inconclusive"
    ([("kind",toJson "direct-obligation"),("phase",toJson "certificate-check"),
      ("outcome",toJson (DiagnosticOutcome.exhausted stop.limit stop.rounds stop.visited)),
      ("id",toJson s!"subtype:{origin.pos.1}:{origin.pos.2}"),
      ("sourceMap",toJson { origin with context := [] }),
      ("judgment",(DirectObligation.Judgment.subtyping origin.pos (p.shown stop.source) (p.shown stop.target)).toJson),
      ("fuel",toJson (0 : Nat))] ++ p.fields)

end

section
open EquationStore

/-! ### Requests over the frozen equations -/

deriving instance ToJson, FromJson for DirectProof.Plan

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
