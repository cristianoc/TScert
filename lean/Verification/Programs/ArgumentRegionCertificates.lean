import Verification.Programs.ArgumentRegionGraph

/-! Executable regional graph checks. Candidate provenance is checked at the
entry and on every edge. A node is a provenance step (a slot copy, a stable
read) or a step whose local effect the common check includes in the stated
frame (`stepWithin`): a step within the closed bound, a call at its
signature's frame, an element write. -/
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

/-- A heap within a closed bound on its own locations is within it. -/
theorem holdsOn_length {c : Footprints.Closed} {h h' : Heap}
    (hp : c.HoldsOn (· < h.length) h h') : c.Holds h h' := by
  rw [Footprints.Closed.holds_iff]
  exact ⟨hp.1, fun l v hv => hp.2 l v (List.getElem?_eq_some_iff.mp hv).1 hv⟩

/-- A step within the closed bound: its frame is the bound's. -/
def closedStep (Φ : Footprints.Closed) : StepEffect := ⟨fun _ => none, Φ.fp, Φ.fp⟩

theorem closedStep_ok [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {c : NodeEvidence ι} {t : Tm} {thr : Bool}
    (hc : checkClosedNode G images sums Φ c t thr = true)
    (ht : ExpressionOk G c t) (hsums : ProgramCertificates.SummariesSound G images sums) :
    StepOk G c t (closedStep Φ) thr := by
  simp only [checkClosedNode, Bool.and_eq_true] at hc
  have hn := nodeWithin_of_checked (F := []) (thr := thr) hc.1.1 hc.2 (fun hthr => by
    have hx := hc.1.2; rw [hthr] at hx; simpa using hx) ht hsums
  intro n W h ρ he hi hk hw hh
  refine ⟨ρ, ?_, ?_⟩
  · intro p s hs; simp [closedStep] at hs
  apply HeapObservations.SafePostExc.weaken _ _
    (hn n W h ρ h.length (Nat.le_refl _) (fun _ hi => nomatch hi) he hi hk hw hh)
  · intro h' _ hq
    exact Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp (holdsOn_length hq.1))
  · intro h' hq hthr
    exact Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp (holdsOn_length (hq hthr)))

/-- A call's positions' slots: the receiver's, and each actual's that is a
slot. -/
def callSlots (r : Tm) (args : List Tm) (p : Nat) : Option Nat :=
  if p = 0 then (match r with
    | .var j => some j
    | _ => none) else match args[p - 1]? with
    | some (.var j) => some j
    | _ => none

/-- The frame `ReceiverGrows` states: every old location but the receiver's
store kept. -/
def grownFrame : Footprint := [(.field 0 arrayStoreKey, .any)]

theorem grown_post {e : CallEffects.Effect} {r : Tm} {args : List Tm} {h h' : Heap}
    (hw : e.within r args h h') (hg : CallEffects.ReceiverGrows r h h') :
    Post grownFrame (CallEffects.callEnv r args) h h' := by
  refine ⟨hw.1, fun l v hv => ?_⟩
  rcases hg l v hv with hs | ⟨hs, ls, ls', -, hl', -⟩
  · exact ⟨v, hs, .inl rfl⟩
  · refine ⟨.arr ls', hl', .inr ⟨(.field 0 arrayStoreKey, .any), by simp [grownFrame], ?_, trivial⟩⟩
    simpa [Region.mem, CallEffects.callEnv, Footprints.storeOf] using hs

/-- A call at its selected signature: its frame at the call's positions, on
normal return the narrower `grownFrame` where the signature states
`receiverGrows`; on a throw its frame, which it must state then. -/
@[nospecialize] def callStep [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (c : NodeEvidence ι) (t : Tm) (thr : Bool) : Option StepEffect :=
  if decide ((ProgramCertificates.claim c.expression).term = t) &&
      (ProgramCertificates.checkTreeUsing G images c.expression (sums := sums) ||
        PromiseCalls.requiresTree G images (entryFacts G c) (fun _ => false) sums c.expression) &&
      ExpressionEffects.selectedOperands c.expression && (!thr || ExpressionEffects.selectedThrows c.expression) then
    match t, ExpressionEffects.selectedEffect c.expression with
    | .invoke _ r args, some eff =>
      if !thr || eff.onThrow then
        some ⟨callSlots r args, if eff.receiverGrows then grownFrame else eff.frame, eff.frame⟩
      else none
    | _, _ => none
  else none

theorem callStep_ok [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {c : NodeEvidence ι} {t : Tm} {thr : Bool} {se : StepEffect}
    (hc : callStep G images sums c t thr = some se)
    (hsums : ProgramCertificates.SummariesSound G images sums) :
    StepOk G c t se thr := by
  intro n W h ρ he _ hk hw hh
  unfold callStep at hc
  split at hc
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨hterm0, htree⟩, hops⟩, hthrows⟩ := hcond
    subst hterm0
    split at hc
    · rename_i fn receiver args eff hterm heff
      split at hc
      · rename_i hthrow
        cases hc
        have hs : HeapObservations.SafePostExc (excOf G)
            (meaning G (ProgramCertificates.claim c.expression).type)
            (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term))
              (ExpressionEffects.actualsOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term)) h)
            (fun h' => thr = true → eff.excPost
              (ExpressionEffects.receiverOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term))
              (ExpressionEffects.actualsOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term)) h h')
            n W h (instantiate 0 ρ (ProgramCertificates.claim c.expression).term) := by
          rcases Bool.or_eq_true_iff.mp htree with htree | hreq
          · cases ht : thr
            · apply HeapObservations.SafePostExc.of_post (fun _ hf => by cases hf)
              exact ExpressionEffects.selected_sound c.expression htree hops heff
                (ProgramCertificates.codesSound_none _) hsums he hw hh
            · have hx : ExpressionEffects.selectedThrows c.expression = true := by
                simpa [ht] using hthrows
              exact HeapObservations.SafePostExc.weaken (fun _ _ h => h) (fun _ h _ => h)
                (ExpressionEffects.selected_sound_exc c.expression htree hops hx heff
                  (ProgramCertificates.codesSound_none _) hsums he hw hh)
          · obtain ⟨eff', heff', hs⟩ := PromiseCalls.requiresTree_sound_exc
              (ProgramCertificates.codesSound_none _) hsums c.expression hreq
            rw [heff] at heff'; cases heff'
            exact HeapObservations.SafePostExc.weaken (fun _ _ h => h) (fun _ h _ => h)
              (hs he hk hw hh)
        rw [hterm] at hs ⊢
        refine ⟨CallEffects.callEnv (instantiate 0 ρ receiver) (args.map (instantiate 0 ρ)), ?_, ?_⟩
        · intro p s hp
          simp only [callSlots] at hp
          split at hp
          · rename_i hp0
            split at hp
            · cases hp; simp [CallEffects.callEnv, hp0, instantiate]
            · cases hp
          · rename_i hp0
            split at hp
            · rename_i j hj
              cases hp
              simp [CallEffects.callEnv, hp0, List.getD, List.getElem?_map, hj, instantiate]
            · cases hp
        · simp only [ExpressionEffects.receiverOf, ExpressionEffects.actualsOf, instantiate,
            instantiateArgs_eq_map] at hs ⊢
          apply HeapObservations.SafePostExc.weaken _ _ hs
          · intro h' v hp
            cases hg : eff.receiverGrows
            · simp only [Bool.false_eq_true, ↓reduceIte]; exact hp.1
            · simp only [↓reduceIte]; exact grown_post hp.1 (hp.2.2.2.2.2.1 hg).1
          · intro h' hp hthr
            have hon : eff.onThrow = true := by
              simp only [Bool.or_eq_true, Bool.not_eq_true'] at hthrow
              rcases hthrow with ht | ht
              · rw [hthr] at ht; cases ht
              · exact ht
            exact hp hthr hon
      · cases hc
    · cases hc
  · cases hc

/-- An element write: its frame at the node's slots (`writeFrame`). -/
def writeStepEffect (i : Nat) : StepEffect := ⟨some, ExpressionEffects.writeFrame i, ExpressionEffects.writeFrame i⟩

theorem writeStep_ok [DecidableEq ι] {G : NormalGraph ι} {c : NodeEvidence ι} {t : Tm} {thr : Bool} {i : Nat}
    (hc : ExpressionEffects.writeStep G (entry c) t = some i) (ht : ExpressionOk G c t) :
    StepOk G c t (writeStepEffect i) thr := by
  intro n W h ρ he hi hk hw hh
  refine ⟨ρ, fun p s hp => by cases hp; rfl, ?_⟩
  have hs := HeapObservations.erase (HeapObservations.consequence
    (fun _ _ _ hu => hu.1) (fun _ _ h => h) (ht n W h ρ he hi hk hw hh))
  exact HeapObservations.SafePostExc.weaken (fun _ _ h => h) (fun _ h _ => h)
    (ExpressionEffects.writeStep_sound hc he hh hs)

/-- A node's local effects: within the closed bound, a call's, an element
write's. -/
@[nospecialize] def stepEffects [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (c : NodeEvidence ι) (t : Tm) (thr : Bool) : List StepEffect :=
  (if checkClosedNode G images sums Φ c t thr then [closedStep Φ] else []) ++
    (callStep G images sums c t thr).toList ++
    ((ExpressionEffects.writeStep G (entry c) t).map writeStepEffect).toList

theorem stepEffects_ok [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {c : NodeEvidence ι} {t : Tm} {thr : Bool} {se : StepEffect}
    (hm : se ∈ stepEffects G images sums Φ c t thr)
    (ht : ExpressionOk G c t) (hsums : ProgramCertificates.SummariesSound G images sums) :
    StepOk G c t se thr := by
  simp only [stepEffects, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · split at hm
    · rename_i hc
      cases List.mem_singleton.mp hm
      exact closedStep_ok hc ht hsums
    · cases hm
  · exact callStep_ok (Option.mem_toList.mp hm) hsums
  · obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp (Option.mem_toList.mp hm)
    exact writeStep_ok hi ht

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

@[nospecialize] def checkRead [DecidableEq ι] (G : NormalGraph ι) (c : NodeEvidence ι) (regions : List ArgumentStoreRegion)
    (facts : List ArgumentPathTracking.Fact) (t : Tm) (rs : List ArgumentStoreRegion) : Bool :=
  match t with
  | .readAt (.str f) (.var i) => decide (i < (entry c).length) && !rs.isEmpty &&
      (match (entry c)[i]? with
        | some A => HeapExpressionRules.fieldOperand (expand G A) (.str f)
        | none => false) &&
      rs.all fun r =>
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
    (hc : checkRead G c regions facts t rs = true) (ht : ExpressionOk G c t) :
    NodeWithin G Φ regions c t facts rs thr := by
  intro n W h ρ initial input hb hf he hi hk hw hh hst
  unfold checkRead at hc
  split at hc
  · rename_i f i
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, List.contains_iff_mem,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
    obtain ⟨⟨⟨hlt, hne⟩, hfo⟩, hall⟩ := hc
    have hpresent : (Footprints.fieldsOf (ρ i)).lookup (.str f) ≠ none := by
      split at hfo
      · rename_i A hA
        obtain ⟨_, flds, code, oid, l, _, hobj, hl, -⟩ := HeapExpressionRules.fieldOperand_sound hfo (he.2 i A hA)
        simp [hobj, Footprints.fieldsOf, hl]
      · cases hfo
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
        exact ArgumentPathTracking.read_now hf hfact hfld (hst (Nat.succ_pos n)) (Nat.succ_pos n) hh hpresent
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
    | _ :: _ => checkCopy c facts node.expression origins || checkRead G c regions facts node.expression origins
    | [] => (stepEffects G images sums Φ c node.expression thr).any fun se => stepWithin Φ regions facts se thr

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
  simp only [checkNodes, checkNode, stepEffects, callStep, checkClosedNode, checkRead, throwsWithin,
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
    obtain ⟨se, hse, hwithin⟩ := List.any_eq_true.mp hp.2
    exact nodeWithin_of_step (stepEffects_ok hse ht hsums) hwithin

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
