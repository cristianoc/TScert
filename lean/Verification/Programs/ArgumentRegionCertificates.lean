import Verification.Programs.ArgumentRegionGraph

/-! Executable regional graph checks. Candidate provenance is checked at the
entry and on every edge. The supported effects are closed footprints and
receiver-store calls on tracked entry values. -/
namespace Verification.GraphCode.ArgumentRegionGraph
open ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules Footprints
open PositiveCertificates (InstanceImageCheck)

/-- A node covered by the existing closed-footprint rules. -/
@[nospecialize] def checkClosedNode [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (c : NodeEvidence ι) (t : Tm) (thr : Bool) : Bool :=
  ProgramCertificates.checkScope (entry c).length t &&
    (!thr || throwsWithin G images sums Φ [] c t) &&
    (((ExpressionEffects.check G (entry c) t || writeWithinAt G Φ c t) ||
      (decide ((ProgramCertificates.claim c.expression).term = t) &&
        (ProgramCertificates.checkTreeUsing G images c.expression (sums := sums) ||
          PromiseCalls.requiresTree G images (entryFacts G c) (fun _ => false) sums c.expression) &&
        selectedWithinAt Φ [] c.expression)) || ExpressionEffects.emptyType G (result c))

theorem checkClosedNode_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion} {facts : List ArgumentPathTracking.Fact}
    {c : NodeEvidence ι} {t : Tm} {thr : Bool}
    (hc : checkClosedNode G images sums Φ c t thr = true)
    (ht : ExpressionOk G c t) (hsums : ProgramCertificates.SummariesSound G images sums) :
    NodeWithin G Φ regions c t facts [] thr := by
  simp only [checkClosedNode, Bool.and_eq_true] at hc
  apply nodeWithin_of_closed (nodeWithin_of_checked hc.1.1 hc.2 ?_ ht hsums)
  intro hthr
  simpa [hthr] using hc.1.2

/-- A copy's origins: every region its slot holds. The node check verifies
the slot and scope. -/
def copyOrigins (facts : List ArgumentPathTracking.Fact) (t : Tm) : List ArgumentStoreRegion :=
  match t with
  | .var i => (facts.filter fun f => f.slot == i).map (·.region)
  | _ => []

@[nospecialize] def checkCopy [DecidableEq ι] (c : NodeEvidence ι)
    (facts : List ArgumentPathTracking.Fact) (t : Tm) (rs : List ArgumentStoreRegion) : Bool :=
  match t with
  | .var i => decide (i < (entry c).length) && rs.all fun r => facts.contains ⟨i, r⟩
  | _ => false

theorem checkCopy_sound [DecidableEq ι] {G : NormalGraph ι} {Φ : Footprints.Closed}
    {regions : List ArgumentStoreRegion} {facts : List ArgumentPathTracking.Fact}
    {c : NodeEvidence ι} {t : Tm} {rs : List ArgumentStoreRegion} {thr : Bool}
    (hc : checkCopy c facts t rs = true) (ht : ExpressionOk G c t) :
    NodeWithin G Φ regions c t facts rs thr := by
  intro n W h ρ initial input hb hf he hi hk hw hh _
  cases t <;> simp only [checkCopy, Bool.false_eq_true] at hc
  rename_i i
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem] at hc
  have hv : isVal (ρ i) = true :=
    (meaning_value (he.2 i _ (List.getElem?_eq_getElem hc.1))).1
  have hs := HeapObservations.erase (HeapObservations.consequence
    (fun _ _ _ hu => hu.1) (fun _ _ h => h) (ht n W h ρ he hi hk hw hh))
  simp only [instantiate, Nat.sub_zero] at hs ⊢
  cases n with
  | zero => trivial
  | succ n =>
    apply HeapObservations.SafePostExc.value hv (safe_value_mem hv hs)
    exact ⟨hb, fun r hr => hf ⟨i, r⟩ (hc.2 r hr)⟩

/-- **The stable-read node rule**'s candidates: a read of a traversed field
`f` of a tracked slot holding a position's entry value names the region
`(x, [f])`, for each such position. The node check verifies them. -/
def readOrigins (regions : List ArgumentStoreRegion) (facts : List ArgumentPathTracking.Fact) (t : Tm) :
    List ArgumentStoreRegion :=
  match t with
  | .readAt (.str f) (.var i) =>
    (facts.filter fun g => g.slot == i && g.region.path.isEmpty &&
      (ArgumentPathTracking.stableFields regions).contains (g.region.position, f)).map
      fun g => ⟨g.region.position, [f]⟩
  | _ => []

/-- A node's candidate origins: a copy's, and a stable read's. -/
def nodeOrigins (regions : List ArgumentStoreRegion) (facts : List ArgumentPathTracking.Fact) (t : Tm) :
    List ArgumentStoreRegion :=
  copyOrigins facts t ++ readOrigins regions facts t

@[nospecialize] def checkRead [DecidableEq ι] (c : NodeEvidence ι) (regions : List ArgumentStoreRegion)
    (facts : List ArgumentPathTracking.Fact) (t : Tm) (rs : List ArgumentStoreRegion) : Bool :=
  match t with
  | .readAt (.str f) (.var i) => decide (i < (entry c).length) && !rs.isEmpty && rs.all fun r =>
      r.path == [f] && facts.contains ⟨i, ⟨r.position, []⟩⟩ &&
        (ArgumentPathTracking.stableFields regions).contains (r.position, f)
  | _ => false

/-- What a field read of an object whose field location holds `u` steps to. -/
private theorem read_step {h : Heap} {x : Val} {f : String} {u : Val}
    (hv : HeapKnowledge.readPath h x [f] = some u) : Step h (.readAt (.str f) x) h u := by
  cases x <;> simp [HeapKnowledge.readPath] at hv
  rename_i flds code oid
  cases hl : flds.lookup (.str f) with
  | none => simp [hl] at hv
  | some l =>
    cases hlv : h[l]? with
    | none => simp [hl, hlv] at hv
    | some w =>
      simp only [hl, hlv, Option.some.injEq] at hv
      subst hv
      exact (HeapFacts.ReadGave.present hl hlv).step

/-- A read of a traversed field of a tracked slot holding positions' entry
values reads the field's entry value (`read_now`): its result holds each
region `(x, [f])`'s entry value. -/
theorem checkRead_sound [DecidableEq ι] {G : NormalGraph ι} {Φ : Footprints.Closed}
    {regions : List ArgumentStoreRegion} {facts : List ArgumentPathTracking.Fact}
    {c : NodeEvidence ι} {t : Tm} {rs : List ArgumentStoreRegion} {thr : Bool}
    (hc : checkRead c regions facts t rs = true) (ht : ExpressionOk G c t) :
    NodeWithin G Φ regions c t facts rs thr := by
  intro n W h ρ initial input hb hf he hi hk hw hh hst
  unfold checkRead at hc
  split at hc
  · rename_i f i
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, List.contains_iff_mem,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
    obtain ⟨⟨hlt, hne⟩, hall⟩ := hc
    have hs := HeapObservations.erase (HeapObservations.consequence
      (fun _ _ _ hu => hu.1) (fun _ _ h => h) (ht n W h ρ he hi hk hw hh))
    have hinst : instantiate 0 ρ (.readAt (.str f) (.var i)) = .readAt (.str f) (ρ i) := by
      simp [instantiate]
    rw [hinst] at hs ⊢
    cases n with
    | zero => trivial
    | succ n =>
      -- each origin reads, at the current heap, the value the read gives
      have hread : ∀ r ∈ rs, ∃ v, isVal v = true ∧
          HeapKnowledge.readPath initial (input r.position) r.path = some v ∧
          HeapKnowledge.readPath h (ρ i) [f] = some v := by
        intro r hr
        obtain ⟨⟨hpath, hfact⟩, hfld⟩ := hall r hr
        rw [hpath]
        exact ArgumentPathTracking.read_now hf hfact hfld (hst (Nat.succ_pos n)) (Nat.succ_pos n) hh
      obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil rs hne
      obtain ⟨u, hval, -, hu⟩ := hread r0 hr0
      have step := read_step hu
      rcases hs with (⟨hv0, _⟩ | hth) | ⟨U, h', t', hx', hU, st, hh', hs'⟩
      · simp [isVal] at hv0
      · exact absurd step hth.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st step
        refine .inr ⟨U, _, _, hx', hU, st, hh', ?_⟩
        cases n with
        | zero => trivial
        | succ m =>
          refine HeapObservations.SafePostExc.value hval (safe_value_mem hval hs') ⟨hb, fun r hr => ?_⟩
          obtain ⟨v, -, h₀v, hv⟩ := hread r hr
          rw [hu] at hv
          cases hv
          exact h₀v
  · cases hc

/-- All branch targets and handlers must justify their proposed facts. -/
@[nospecialize] def checkNode [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (exc : Bool)
    (l : Nat) (node : Node) (c : NodeEvidence ι) : Bool :=
  let facts := ArgumentPathTracking.atLabel table l
  let origins := nodeOrigins regions facts node.expression
  let thr := node.handler.isSome || exc
  ArgumentPathTracking.checkEdges table facts origins node.continuation &&
    ArgumentPathTracking.checkHandler table facts node.handler &&
    match origins with
    | _ :: _ => checkCopy c facts node.expression origins || checkRead c regions facts node.expression origins
    | [] => checkClosedNode G images sums Φ c node.expression thr ||
        (decide ((ProgramCertificates.claim c.expression).term = node.expression) &&
          checkReceiverCall G images sums Φ regions facts c thr)

/-- The first node failing the same check used for certification. Its label
can be mapped through a source map by the declaration diagnostic. Shape and
entry failures belong to the enclosing declaration's diagnostic. -/
@[nospecialize] def firstRefusedNode [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (exc : Bool)
    (P : Program) (C : Certificate ι) : Option ((Node × NodeEvidence ι) × Nat) :=
  (P.zip C).zipIdx.find? fun ((node, c), l) => !checkNode G images sums Φ regions table exc l node c

theorem firstRefusedNode_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion}
    {table : List (List ArgumentPathTracking.Fact)} {exc : Bool}
    {P : Program} {C : Certificate ι} {node : Node} {c : NodeEvidence ι} {l : Nat}
    (hf : firstRefusedNode G images sums Φ regions table exc P C = some ((node, c), l)) :
    P[l]? = some node ∧ C[l]? = some c ∧
      checkNode G images sums Φ regions table exc l node c = false := by
  have hm := List.mem_of_find?_eq_some hf
  have hz := List.mem_zipIdx_iff_getElem?.mp hm
  have hc := List.getElem?_zip_eq_some.mp hz
  exact ⟨hc.1, hc.2, by simpa using (List.find?_some hf)⟩

/-- The table covers precisely the program and certificate being checked. -/
@[nospecialize] def checkNodes [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (exc : Bool)
    (P : Program) (C : Certificate ι) : Bool :=
  decide (P.length = C.length) && decide (table.length = P.length) &&
    (P.zip C).zipIdx.all fun ((node, c), l) => checkNode G images sums Φ regions table exc l node c

/-- Regional graph checking is independent of type-parameter assignment. -/
theorem checkNodes_reassign [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (η : MixedAssignment ι) (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (exc : Bool) (P : Program) (C : Certificate ι) :
    checkNodes (reassign G η) (images.reassign η) sums Φ regions table exc P C =
      checkNodes G images sums Φ regions table exc P C := by
  simp only [checkNodes, checkNode, checkClosedNode, checkReceiverCall, throwsWithin,
    Parametricity.checkTree_reassign, entryFacts_reassign, Parametricity.requiresTree_reassign,
    ExpressionEffects.emptyType]
  rfl

theorem checkNodes_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion} {table : List (List ArgumentPathTracking.Fact)}
    {exc : Bool} {Rty : Goal ι} {P : Program} {C : Certificate ι} {codes}
    (hg : checkGraphUsing (sums := sums) G images Rty P C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (hsums : ProgramCertificates.SummariesSound G images sums)
    (hc : checkNodes G images sums Φ regions table exc P C = true) :
    NodesWithin G Φ regions P C table exc := by
  intro l node c hn hcert
  simp only [checkNodes, Bool.and_eq_true] at hc
  have hz : (P.zip C)[l]? = some (node, c) := List.getElem?_zip_eq_some.mpr ⟨hn, hcert⟩
  have hm : ((node, c), l) ∈ (P.zip C).zipIdx := List.mem_zipIdx_iff_getElem?.mpr hz
  have hp := List.all_eq_true.mp hc.2 _ hm
  obtain ⟨actual, ha, ht, -⟩ := graph_node hg hcodes hsums hcert
  cases hn.symm.trans ha
  simp only [checkNode, Bool.and_eq_true] at hp
  refine ⟨nodeOrigins regions (ArgumentPathTracking.atLabel table l) node.expression, ?_, hp.1.1, hp.1.2⟩
  cases ho : nodeOrigins regions (ArgumentPathTracking.atLabel table l) node.expression with
  | cons r rs =>
    simp only [ho, Bool.or_eq_true] at hp ⊢
    rcases hp.2 with hcopy | hread
    · exact checkCopy_sound hcopy ht
    · exact checkRead_sound hread ht
  | nil =>
    simp only [ho] at hp ⊢
    rcases Bool.or_eq_true_iff.mp hp.2 with hclosed | hcall
    · exact checkClosedNode_sound hclosed ht hsums
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcall
      rw [← hcall.1]
      exact checkReceiverCall_sound hcall.2 hsums

/-- Ordinary entry safety and regional obligations form one executable check. -/
@[nospecialize] def checkEntry [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι))
    (codes : CodeEntry ι → Bool) (table : List (List ArgumentPathTracking.Fact)) (exc : Bool)
    (entrySeparation : HeapSeparation.Separation := {}) (entryIndices : List HeapKnowledge.IndexAtom := []) : Bool :=
  checkEntryUsing (sums := sums) (entrySeparation := entrySeparation) (entryIndices := entryIndices)
    G images Rty P C start inputs codes &&
    ArgumentPathTracking.checkEntry (ArgumentPathTracking.atLabel table start) &&
    ArgumentPathTracking.checkEntryFields G inputs regions &&
    checkNodes G images sums Φ regions table exc P C

theorem checkEntryFields_reassign [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (inputs : List (Ty ι)) (regions : List ArgumentStoreRegion) :
    ArgumentPathTracking.checkEntryFields (reassign G η) inputs regions =
      ArgumentPathTracking.checkEntryFields G inputs regions := rfl

theorem checkEntry_reassign [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (η : MixedAssignment ι) (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι))
    (codes : CodeEntry ι → Bool) (table : List (List ArgumentPathTracking.Fact)) (exc : Bool)
    (entrySeparation : HeapSeparation.Separation) (entryIndices : List HeapKnowledge.IndexAtom) :
    checkEntry (reassign G η) (images.reassign η) sums Φ regions Rty P C start inputs codes table exc
      entrySeparation entryIndices =
    checkEntry G images sums Φ regions Rty P C start inputs codes table exc entrySeparation entryIndices := by
  simp only [checkEntry, Parametricity.checkEntry_reassign, checkNodes_reassign, checkEntryFields_reassign]

/-- Successful executable checking establishes the graph's regional bound.
There is no semantic node-obligation premise. -/
theorem checkEntry_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion} {Rty : Goal ι} {E K C start inputs codes}
    {table : List (List ArgumentPathTracking.Fact)} {exc : Bool}
    {entrySeparation : HeapSeparation.Separation} {entryIndices : List HeapKnowledge.IndexAtom}
    (hc : checkEntry G images sums Φ regions Rty (program E K) C start inputs codes table exc
      entrySeparation entryIndices = true)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (hsums : ProgramCertificates.SummariesSound G images sums)
    (n W h L d) (he : EnvOk G inputs (envOf L d) n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hsep : HeapSeparation.Holds entrySeparation (envOf L d))
    (hidx : HeapKnowledge.IndexHolds entryIndices (envOf L d) h) :
    HeapObservations.SafePostExc (excOf G) (GoalHolds G Rty (Rty.argument (envOf L d)))
      (fun h' _ => ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      (fun h' => exc = true → ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      n W h (.goto E K start L d) := by
  simp only [checkEntry, Bool.and_eq_true] at hc
  have hg := hc.1.1.1
  simp only [checkEntryUsing_eq, Bool.and_eq_true] at hg
  exact goto_bounded hc.1.1.1 hcodes hsums
    (checkNodes_sound hg.1 hcodes hsums hc.2) hc.1.1.2 hc.1.2
    n W h L d he hw hh hsep hidx

end Verification.GraphCode.ArgumentRegionGraph
