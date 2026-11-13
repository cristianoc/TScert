import Verification.Programs.ArgumentRegionCertificates
import Verification.Programs.SinglePass

/-! # Tolerant frames: the regional check of one node

`run` makes the regional check node by node (`SinglePass.run`, "A regional
check at this node"): `ArgumentRegionGraph.checkNode` over tables it builds
for the node and its targets (`SinglePass.sparse`), at the node's evidence.
The existing soundness theorem, `ArgumentRegionGraph.checkNodes_sound`, is
about the whole graph, its premise the certificate checker's acceptance
(`checkGraphUsing`), from which it reads each node's typing
(`ControlFlow.graph_node`). `checkNode_sound` is its per-node core: from the
node's own typing (`ExpressionOk`) and its check, the node's conjunct of
`NodesWithin` (`NodeWithinAt`). `nodesWithin_of` assembles it over a graph. -/
namespace Verification.GraphCode.ArgumentRegionGraph
open ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules Footprints
open PositiveCertificates (InstanceImageCheck)
open CertificateProducer (successors)
open ArgumentRegionFresh (FreshValue FreshHold FreshTables FreshWithin FieldFresh FieldsHold)

variable {ι : Type} [DecidableEq ι]

/-- **A node's regional obligation** at label `l` over the tables: the
conjunct of `NodesWithin` at one node. -/
def NodeWithinAt (G : NormalGraph ι) (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (ft : FreshTables) (exc : Bool) (l : Nat) (node : Node)
    (c : NodeEvidence ι) : Prop :=
  ∃ origins outF outC outFs,
    NodeWithin G Φ regions c node.expression (ArgumentPathTracking.atLabel table l) (factsAt ft.values l)
      (fieldsAt ft.fields l) origins (node.handler.isSome || exc) ∧
    ArgumentPathTracking.checkEdges table (ArgumentPathTracking.atLabel table l) origins node.continuation = true ∧
    ArgumentPathTracking.checkHandler table (ArgumentPathTracking.atLabel table l) node.handler = true ∧
    FreshWithin G c node.expression (factsAt ft.values l) (factsAt ft.cells l) outF outC node.handler.isSome ∧
    edgesFresh ft.values (factsAt ft.values l) outF false node.continuation = true ∧
    edgesFresh ft.cells (factsAt ft.cells l) outC false node.continuation = true ∧
    FieldsWithin G c node.expression (factsAt ft.values l) (fieldsAt ft.fields l) outFs ∧
    edgesFields ft.fields (fieldsAt ft.fields l) outFs node.continuation = true ∧
    ∀ target, node.handler = some target →
      handlerFresh ft.values (factsAt ft.values l) target = true ∧
      handlerFresh ft.cells (factsAt ft.cells l) target = true ∧
      handlerFields ft.fields (fieldsAt ft.fields l) target = true

/-- **The regional check of one node is sound from the node's own typing**:
where `checkNode` accepts node `l` at its evidence `c` and the node's term
is typed at `c` (`ExpressionOk`), with the summaries checked, the node
meets its regional obligation over the tables (`NodeWithinAt`): the
regional bound and the result's origins (`checkCopy_sound`,
`checkRead_sound`, or a step effect, `stepEffects_ok` with
`nodeWithin_of_step`), the fresh values and cells (`checkFresh_sound`), the
fresh fields (`fieldsCheck_sound`), and the tables' transfer along the
node's edges and handler. -/
theorem checkNode_sound {G : NormalGraph ι} {images : InstanceImageCheck G}
    {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion}
    {table : List (List ArgumentPathTracking.Fact)} {ft : FreshTables} {exc : Bool} {l : Nat} {node : Node}
    {c : NodeEvidence ι}
    (hp : checkNode G images sums Φ regions table ft exc l node c = true)
    (ht : ExpressionOk G c node.expression) (hsums : ProgramCertificates.SummariesSound G images sums) :
    NodeWithinAt G Φ regions table ft exc l node c := by
  simp only [checkNode, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hkeep, hefl⟩, hhfl⟩, hedge⟩, hhandler⟩, hfresh⟩, hef⟩, hec⟩, hhf⟩, hp⟩ := hp
  have hscope : ProgramCertificates.checkScope (entry c).length node.expression = true := by
    have h0 := hfresh
    simp only [checkFresh, Bool.and_eq_true] at h0
    exact h0.1
  refine ⟨nodeOrigins regions (ArgumentPathTracking.atLabel table l) node.expression, _, _, _, ?_, hedge, hhandler,
    checkFresh_sound hfresh ht hsums, hef, hec, fieldsCheck_sound hkeep hscope ht, hefl, fun target htarget => ?_⟩
  rotate_right
  · rw [htarget] at hhf hhfl
    simp only [Bool.and_eq_true] at hhf
    exact ⟨hhf.1, hhf.2, hhfl⟩
  cases ho : nodeOrigins regions (ArgumentPathTracking.atLabel table l) node.expression with
  | cons r rs =>
    simp only [ho, Bool.or_eq_true] at hp ⊢
    rcases hp with hcopy | hread
    · exact checkCopy_sound hcopy ht
    · exact checkRead_sound hread ht
  | nil =>
    simp only [ho] at hp ⊢
    obtain ⟨se, hse, hwithin⟩ := List.any_eq_true.mp hp
    exact nodeWithin_of_step (stepEffects_ok hse ht hsums) hwithin

/-! ## Agreement of a node's tables with the graph's

`run` checks each node over tables it builds for the node and its targets:
at the node its regional facts on entry, at a target what the node
establishes there (a loop head's given facts at a head). The graph's
tables, read at each node's entry, agree at the node and are at most what
each predecessor establishes at a target (`RegionState.meet`). Every check
of `checkNode` reads a target's entry by `all` over it, so a smaller
target entry keeps it accepted (`checkNode_mono`). -/

section Mono

theorem all_sub {α : Type} {xs ys : List α} {p : α → Bool} (hs : ∀ x ∈ ys, x ∈ xs) (h : xs.all p = true) :
    ys.all p = true :=
  List.all_eq_true.mpr fun x hx => List.all_eq_true.mp h x (hs x hx)

theorem checkEdges_mono {T T' : List (List ArgumentPathTracking.Fact)} {facts : List ArgumentPathTracking.Fact}
    {origins : List ArgumentStoreRegion} {k : Continuation}
    (hs : ∀ t ∈ successors k, ∀ f ∈ ArgumentPathTracking.atLabel T' t.label, f ∈ ArgumentPathTracking.atLabel T t.label)
    (h : ArgumentPathTracking.checkEdges T facts origins k = true) :
    ArgumentPathTracking.checkEdges T' facts origins k = true := by
  unfold ArgumentPathTracking.checkEdges ArgumentPathTracking.checkMap at *
  exact List.all_eq_true.mpr fun t ht => all_sub (hs t ht) (List.all_eq_true.mp h t ht)

theorem checkHandler_mono {T T' : List (List ArgumentPathTracking.Fact)} {facts : List ArgumentPathTracking.Fact}
    {x : Option Target}
    (hs : ∀ t, x = some t → ∀ f ∈ ArgumentPathTracking.atLabel T' t.label, f ∈ ArgumentPathTracking.atLabel T t.label)
    (h : ArgumentPathTracking.checkHandler T facts x = true) : ArgumentPathTracking.checkHandler T' facts x = true := by
  unfold ArgumentPathTracking.checkHandler ArgumentPathTracking.checkMap at *
  cases x with
  | none => rfl
  | some t =>
    simp only [Option.toList, List.all_cons, List.all_nil, Bool.and_true] at h ⊢
    exact all_sub (hs t rfl) h

theorem edgesFresh_mono {V V' : List (List Nat)} {F : List Nat} {out ret : Bool} {k : Continuation}
    (hs : ∀ t ∈ successors k, ∀ i ∈ factsAt V' t.label, i ∈ factsAt V t.label)
    (h : edgesFresh V F out ret k = true) : edgesFresh V' F out ret k = true := by
  unfold edgesFresh at *
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨List.all_eq_true.mpr fun t ht => all_sub (hs t ht) (List.all_eq_true.mp h.1 t ht), h.2⟩

theorem handlerFresh_mono {V V' : List (List Nat)} {F : List Nat} {t : Target}
    (hs : ∀ i ∈ factsAt V' t.label, i ∈ factsAt V t.label) (h : handlerFresh V F t = true) :
    handlerFresh V' F t = true := by
  unfold handlerFresh at *
  exact all_sub hs h

theorem edgesFields_mono {V V' : List (List (Nat × String))} {Fs : List (Nat × String)} {out : List String}
    {k : Continuation} (hs : ∀ t ∈ successors k, ∀ p ∈ fieldsAt V' t.label, p ∈ fieldsAt V t.label)
    (h : edgesFields V Fs out k = true) : edgesFields V' Fs out k = true := by
  unfold edgesFields at *
  exact List.all_eq_true.mpr fun t ht => all_sub (hs t ht) (List.all_eq_true.mp h t ht)

theorem handlerFields_mono {V V' : List (List (Nat × String))} {Fs : List (Nat × String)} {t : Target}
    (hs : ∀ p ∈ fieldsAt V' t.label, p ∈ fieldsAt V t.label) (h : handlerFields V Fs t = true) :
    handlerFields V' Fs t = true := by
  unfold handlerFields at *
  exact all_sub hs h

/-- **A node's tables against the graph's**: equal at the node `l`, and at
each target of its continuation and handler the graph's entry within the
node's (each of the provenance, fresh value, fresh cell and fresh field
tables); the field names equal. -/
structure TablesAgree (T T' : List (List ArgumentPathTracking.Fact)) (ft ft' : FreshTables) (l : Nat)
    (node : Node) : Prop where
  facts : ArgumentPathTracking.atLabel T' l = ArgumentPathTracking.atLabel T l
  values : factsAt ft'.values l = factsAt ft.values l
  cells : factsAt ft'.cells l = factsAt ft.cells l
  fields : fieldsAt ft'.fields l = fieldsAt ft.fields l
  names : ft'.names = ft.names
  targets : ∀ t, t ∈ successors node.continuation ∨ node.handler = some t →
    (∀ f ∈ ArgumentPathTracking.atLabel T' t.label, f ∈ ArgumentPathTracking.atLabel T t.label) ∧
    (∀ i ∈ factsAt ft'.values t.label, i ∈ factsAt ft.values t.label) ∧
    (∀ i ∈ factsAt ft'.cells t.label, i ∈ factsAt ft.cells t.label) ∧
    (∀ p ∈ fieldsAt ft'.fields t.label, p ∈ fieldsAt ft.fields t.label)

/-- **The regional check over a node's tables holds over the graph's**:
where the tables agree (`TablesAgree`), `checkNode` accepting over the
node's tables accepts over the graph's. -/
theorem checkNode_mono {G : NormalGraph ι} {images : InstanceImageCheck G}
    {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion}
    {T T' : List (List ArgumentPathTracking.Fact)} {ft ft' : FreshTables} {exc : Bool} {l : Nat} {node : Node}
    {c : NodeEvidence ι} (ha : TablesAgree T T' ft ft' l node)
    (h : checkNode G images sums Φ regions T ft exc l node c = true) :
    checkNode G images sums Φ regions T' ft' exc l node c = true := by
  have hk := fun t ht => ha.targets t (.inl ht)
  have hx := fun t ht => ha.targets t (.inr ht)
  simp only [checkNode, Bool.and_eq_true] at h ⊢
  rw [ha.facts, ha.values, ha.cells, ha.fields, ha.names]
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, edgesFields_mono (fun t ht => (hk t ht).2.2.2) h2⟩, ?_⟩,
    checkEdges_mono (fun t ht => (hk t ht).1) h4⟩, checkHandler_mono (fun t ht => (hx t ht).1) h5⟩, h6⟩,
    edgesFresh_mono (fun t ht => (hk t ht).2.1) h7⟩, edgesFresh_mono (fun t ht => (hk t ht).2.2.1) h8⟩, ?_⟩, h10⟩
  · cases hh : node.handler with
    | none => rfl
    | some t =>
      rw [hh] at h3
      exact handlerFields_mono (hx t hh).2.2.2 h3
  · cases hh : node.handler with
    | none => rfl
    | some t =>
      rw [hh] at h9
      simp only [Bool.and_eq_true] at h9 ⊢
      exact ⟨handlerFresh_mono (hx t hh).2.1 h9.1, handlerFresh_mono (hx t hh).2.2.1 h9.2⟩

/-- **The meet is within each predecessor's facts** (`SinglePass.RegionState.meet`):
each of its four tables is within the corresponding table of every state it
meets, the agreement `TablesAgree.targets` reads at a node other than a
head. -/
theorem meet_sub {rs : List SinglePass.RegionState} {r : SinglePass.RegionState} (hr : r ∈ rs) :
    (∀ x ∈ (SinglePass.RegionState.meet rs).facts, x ∈ r.facts) ∧
    (∀ x ∈ (SinglePass.RegionState.meet rs).values, x ∈ r.values) ∧
    (∀ x ∈ (SinglePass.RegionState.meet rs).cells, x ∈ r.cells) ∧
    (∀ x ∈ (SinglePass.RegionState.meet rs).fields, x ∈ r.fields) := by
  cases rs with
  | nil => cases hr
  | cons q qs =>
    simp only [SinglePass.RegionState.meet, List.mem_filter, List.all_eq_true, List.contains_iff_mem]
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨fun x hx => hx.1, fun x hx => hx.1, fun x hx => hx.1, fun x hx => hx.1⟩
    · exact ⟨fun x hx => by simpa using hx.2 r hr, fun x hx => by simpa using hx.2 r hr,
        fun x hx => by simpa using hx.2 r hr, fun x hx => by simpa using hx.2 r hr⟩

end Mono

end Verification.GraphCode.ArgumentRegionGraph
