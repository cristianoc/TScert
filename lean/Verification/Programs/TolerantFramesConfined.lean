import Verification.Programs.TolerantFramesComposeYields
import Verification.Semantics.AdmissibleCells

/-! # Tolerant frames: unconditional soundness of checked local-object confinement

When `SinglePass.run` accepts with `confinement = some conf`, `SinglePass.run`
has checked `framed == conf.framed` and `SinglePass.checkWalkConfinement` on
every visited node of the walk. This module composes `LocalConfinement.checkNode_sound_normal`
and `LocalConfinement.checkNode_sound_handler` with the single pass's walk
infrastructure (`TolerantFramesComposeYields`, `TolerantFramesGuaranteeWalk`)
to prove the exact ordinary `Target.GraphGuarantee` with zero client trust.

`run_sound_pass` then dispatches `Target.RunCall.Accepts` between the unframed
theorem (`run_sound_checked_unframed`) and the confined theorem
(`run_sound_checked_confined`), proving `Target.RunSound ι`. -/

namespace Verification.TolerantFrames
open Verification Verification.SinglePass Verification.ProgramTyping Verification.ControlFlow
open Verification.PositiveGraphs Verification.PositiveRules Verification.ProgramCertificates
open Verification.LabelStore Verification.PositiveCertificates Verification.CertificateProducer
open Verification.GraphCode Verification.Confinement Verification.LocalConfinement Verification.HeapObservations

section Helpers
variable {ι : Type} [DecidableEq ι]

/-- Every normal exit of `SinglePass.Exit.ofNode` is listed by `LocalConfinement.normalExits`. -/
private theorem mem_normalExits_of_exit {node : Node} {t : Target} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    (h : SinglePass.Exit.normal t pushed observed promote ∈ SinglePass.Exit.ofNode node) :
    (t, pushed) ∈ LocalConfinement.normalExits node := by
  cases node with
  | mk expr cont hand =>
    cases hand <;> cases cont <;> simp [SinglePass.Exit.ofNode, LocalConfinement.normalExits] at h ⊢
    all_goals (try simp_all)
    all_goals (rcases h with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> simp)

private theorem mem_program_expr {E : List Tm} {K : List (Continuation × Option Target)} {node : Node}
    (h : node ∈ GraphCode.program E K) : node.expression ∈ E := by
  obtain ⟨⟨e, k, x⟩, hz, rfl⟩ := List.mem_map.mp h
  exact (List.of_mem_zip hz).1

/-- If `SinglePass.framedAt conf.framed l = some Ss`, then `l ∈ conf.framedNodes`
and `Ss` is the singleton `[confinedFootprint (conf.at l).owned (conf.at l).ownedArr]`. -/
private theorem framedAt_confined {conf : LocalConfinement.Table} {l : Nat} {Ss : List Footprints.Footprint}
    (h : SinglePass.framedAt conf.framed l = some Ss) :
    l ∈ conf.framedNodes ∧ Ss = [Confinement.confinedFootprint (conf.at l).owned (conf.at l).ownedArr] := by
  simp only [SinglePass.framedAt, Option.map_eq_some_iff] at h
  obtain ⟨⟨l', Ss'⟩, hfind, hSs⟩ := h
  simp only at hSs
  subst hSs
  have hmem := List.mem_of_find?_eq_some hfind
  have heq : l' = l := by
    have := List.find?_some hfind
    simpa only [beq_iff_eq] using this
  subst heq
  simp only [LocalConfinement.Table.framed, List.mem_filterMap] at hmem
  obtain ⟨l₀, hl₀, hpair⟩ := hmem
  split at hpair
  · cases hpair
  · simp only [Option.some.injEq, Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨hl₀, rfl⟩

/-- `checkWalkConfinement` guarantees the start node's confinement entry is empty. -/
private theorem start_empty_of_walkConfinement {G : NormalGraph ι} {I : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {P : Program} {claims : List (PointClaim ι)}
    {start : Nat} {conf : LocalConfinement.Table} {w : SinglePass.Walk ι}
    (h : SinglePass.checkWalkConfinement G I codes sums P claims start conf w = true) :
    conf.at start = {} := by
  simp only [SinglePass.checkWalkConfinement, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

/-- `checkWalkConfinement` gives `claims[l]? = some cl` and `LocalConfinement.checkNode = true`
for every visited label whose `P[l]?` and recorded `stepped` are known. -/
private theorem checkNode_of_walkConfinement {G : NormalGraph ι} {I : InstanceImageCheck G}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {P : Program} {claims : List (PointClaim ι)}
    {start : Nat} {conf : LocalConfinement.Table} {w : SinglePass.Walk ι}
    (h : SinglePass.checkWalkConfinement G I codes sums P claims start conf w = true)
    {l : Nat} {lw : SinglePass.LabelWalk ι} {node : Node} {st : SinglePass.Stepped ι}
    (hlw : w.labels[l]? = some lw) (hvis : lw.visited = true)
    (hP : P[l]? = some node) (hst : lw.stepped = some st) :
    ∃ cl, claims[l]? = some cl ∧
      LocalConfinement.checkNode G I codes sums claims conf l node cl st.stepK st.stepDeriv = true := by
  simp only [SinglePass.checkWalkConfinement, Bool.and_eq_true] at h
  have hlt : l < P.length := by
    cases hlt : decide (l < P.length) with
    | true => exact of_decide_eq_true hlt
    | false =>
      have : P[l]? = none := List.getElem?_eq_none (by simpa using hlt)
      rw [this] at hP; cases hP
  have hall := List.all_eq_true.mp h.2 l (List.mem_range.mpr hlt)
  simp only [hlw, hvis, ↓reduceIte, hP, hst] at hall
  cases hcl : claims[l]? with
  | none => rw [hcl] at hall; cases hall
  | some cl =>
    rw [hcl] at hall
    exact ⟨cl, rfl, hall⟩

end Helpers

section ConfinedWalk
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- Node assertion with the walk's mark, entry heap lower bound, and local
confinement invariant. -/
def confinedPreA (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ε : HeapKnowledge.EntryState)
    (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge)
    (conf : LocalConfinement.Table) (widthFn : Nat → Nat) : Nat → Assertion :=
  fun l ρ m s =>
    marked (passPreA G w startNames ε ctx stated) l ρ m s ∧
    ε.heap.length ≤ s.h.length ∧
    LocalConfinement.ConfinedAt conf widthFn l ρ ε.heap.length s.h

/-- Node assertion adding regional field stability (`StableNow`) on top of
`confinedPreA`. -/
def confinedPreU (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ε : HeapKnowledge.EntryState)
    (ctx : Nat → List (Ty ι)) (stated : Nat → Option HeapKnowledge.Knowledge)
    (conf : LocalConfinement.Table) (widthFn : Nat → Nat) (fields : List (Nat × String)) (h₀ : Heap) :
    Nat → Assertion :=
  fun l ρ m s =>
    confinedPreA G w startNames ε ctx stated conf widthFn l ρ m s ∧
    GraphCode.ArgumentPathTracking.StableNow fields ε.env h₀ s.W

omit [DecidableEq ι] [Hashable ι] in
theorem confinedPreU_adminClosed {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ε : HeapKnowledge.EntryState} {ctx : Nat → List (Ty ι)}
    {stated : Nat → Option HeapKnowledge.Knowledge} {conf : LocalConfinement.Table}
    {widthFn : Nat → Nat} {fields : List (Nat × String)} {h₀ : Heap} {m : Nat} :
    AdminClosed (confinedPreU G w startNames ε ctx stated conf widthFn fields h₀) m := by
  intro l ρ s s' ha hh ⟨⟨hmk, hlen, hcf⟩, hst⟩
  have hpu := passPreU_adminClosed (G := G) (w := w) (startNames := startNames) (ε := ε)
    (ctx := ctx) (stated := stated) (fields := fields) (h₀ := h₀) (m := m) l ρ s s' ha hh ⟨hmk, hst⟩
  exact ⟨⟨hpu.1, hh ▸ hlen, hh ▸ hcf⟩, hpu.2⟩

/-- **Every checked node delivers `confinedPreA`**, using `LocalConfinement.checkNode_sound_normal`
and `LocalConfinement.checkNode_sound_handler` to discharge both `framedK` at
framed nodes and `ConfinedAt` at every normal and exceptional exit. -/
theorem nodesChecked_confined {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {pc : PassChecker G images} {P : Program}
    {claims : List (PointClaim ι)} {w : Walk ι} {startNames : List Nat}
    {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
    {fresh : Nat → Nat} {stated : Nat → Option HeapKnowledge.Knowledge}
    {conf : LocalConfinement.Table} {ε : HeapKnowledge.EntryState} {Tres : Fam} {m : Nat}
    (hT : TraversedA G w startNames given ctx edgesIn fresh stated)
    (hheads : HeadsEntered G w startNames ε given m)
    (hnear : LinearNearFuelEq)
    (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    (htbP : ∀ node ∈ P, Confinement.TmRefsBelow ε.heap.length node.expression)
    (hacc : ∀ l, w.visited l → ∃ r : NodeChecked G images codes pc P w startNames ctx l,
      ∃ ys,
        NodeYieldedR G w startNames ε ctx stated given edgesIn Tres m l r.node r.c r.entry r.st ys
          (framedK (ε := ε) (framedFOf conf.framed) (framedSOf conf.framed) l r.st.stepK) ∧
        claims[l]? = some r.c ∧
        LocalConfinement.checkNode G images codes sums claims conf l r.node r.c r.st.stepK r.st.stepDeriv = true) :
    NodesChecked P (confinedPreA G w startNames ε ctx stated conf
        (fun lbl => ((claims[lbl]?).map (·.context.length)).getD 0))
      (excOf G) Tres (fun _ => True) (fun _ => True) m := by
  let widthFn : Nat → Nat := fun lbl => ((claims[lbl]?).map (·.context.length)).getD 0
  intro l ρ s ⟨⟨hp, hm⟩, hm₀, hcf⟩
  obtain ⟨na, ys, hY, hcl, hchk⟩ := hacc l hp.1.1.1
  have hS : StateHolds G na.entry (w.implies l) startNames ε ρ m s := na.hentry ▸ hp.1.1.2
  have he : EnvOk G na.c.context ρ s.n s.W := na.hctx ▸ hp.1.2
  have hwl : widthFn l = na.c.context.length := by simp [widthFn, hcl]
  refine ⟨na.node, na.hP, fun hr hρ => ?_⟩
  obtain ⟨-, hkS, -, cn, ce, hparts⟩ := stepChecked_parts na.hstep hS na.wf na.below na.width he hcodes na.sums
  have hjY := hY.judged ρ s _ _ hS he hkS (hparts.1 hr hρ)
  obtain ⟨hj, ho⟩ := nodeObligationsR_of_partsY
    (pre := confinedPreA G w startNames ε ctx stated conf widthFn)
    (Ξres := excOf G) (Tres := Tres) (Qres := fun _ => True) (Rres := fun _ => True) (x := na.node.handler)
    (Rn := fun _ => True) (Re := fun _ => True)
    hparts he hjY
    (fun _ _ _ hv => nodeShape_of na.hshape hv)
    (fun s' v hadm hv hF hy he' hout hrun _ => by
      obtain ⟨k, hkn, hsteps⟩ := hrun
      have hρ' : ∀ i, RefsOk s'.W (ρ i) := RootsOk.admissible hadm hρ
      have htb : Confinement.TmRefsBelow ε.heap.length na.node.expression :=
        htbP na.node (List.mem_of_getElem? na.hP)
      obtain ⟨hfr, hexits_cf⟩ := LocalConfinement.checkNode_sound_normal hchk hcodes hsums hwl he he'
        hρ hρ' hkS hm₀ htb hcf hv hr hsteps hkn
      have hK : framedK (ε := ε) (framedFOf conf.framed) (framedSOf conf.framed) l na.st.stepK (push v ρ) s'.h := by
        intro hFl
        unfold framedFOf at hFl
        cases hfa : SinglePass.framedAt conf.framed l with
        | none => rw [hfa] at hFl; cases hFl
        | some Ss =>
          obtain ⟨hmem_fr, rfl⟩ := framedAt_confined hfa
          have hsupp : ∀ T ∈ framedSOf conf.framed l, Footprints.Supported T ρ s.h s'.h := by
            intro T hTmem
            simp only [framedSOf, hfa, Option.getD_some, List.mem_singleton] at hTmem
            subst hTmem
            exact hfr hmem_fr
          exact framedKept_holds hkS hsupp
      have hshape := nodeShape_of na.hshape (he'.2 0 _ rfl)
      have hm' : m ≤ s'.h.length := Nat.le_trans hm hadm.length_le
      have hm₀' : ε.heap.length ≤ s'.h.length := Nat.le_trans hm₀ hadm.length_le
      by_cases hk : na.node.continuation = .ret
      · rw [hk]
        exact ⟨hY.ret hk ρ s' v hv hF he' hy, trivial⟩
      · refine normalTarget_of_exits
          (Fn := fun ρ' m' s'' => ρ' = push v ρ ∧ s'' = s' ∧
            (StateHolds G ⟨na.st.result :: na.entry.names, na.st.store, na.entry.fresh⟩ (w.implies l)
                startNames ε ρ' m' s'' ∧
              PromiseCalls.YieldsOk G ys ρ s''.n s''.W (ρ' 0) ∧
              HeapKnowledge.Holds na.st.stepOut ε ρ' s''.h ∧
              ∃ k, k < s.n ∧ Steps k s.h (instantiate 0 ρ na.node.expression) s''.h (ρ' 0)) ∧
            framedK (ε := ε) (framedFOf conf.framed) (framedSOf conf.framed) l na.st.stepK ρ' s''.h)
          (fun t p o q hmem => by
            intro s'' v'' hv'' ⟨hρeq, hseq, hF'', hK''⟩ he'' hobs
            have hv_eq : v'' = v := by
              have h0 := congrFun hρeq 0
              simpa [push] using h0
            subst hseq hv_eq
            have hed := hY.exits t p o q hmem ρ s hS he hkS hm hr s'' v'' hv'' ⟨hF'', hK''⟩ he'' hobs
            have hpa := passPreA_of_edgeAJ hT hheads hnear hed
            have hcf' := hexits_cf t p (mem_normalExits_of_exit hmem)
            exact ⟨⟨hpa, hm'⟩, hm₀', hcf'⟩)
          (fun h => absurd h hk)
          (fun _ => trivial) s' v hv ⟨rfl, rfl, ⟨hF, hy, hout, ⟨k, hkn, hsteps⟩⟩, hK⟩ he' hshape)
    (fun s' e hadm hFe he' hsc hx _ => by
      cases hh : na.node.handler with
      | none => exact ⟨hx, trivial⟩
      | some t =>
        have hed := hY.handler t hh ρ s' e hFe he' hsc hx
        have hpa := passPreA_of_edgeAJ hT hheads hnear hed
        have hcf' := LocalConfinement.checkNode_sound_handler hchk hh (m₀ := ε.heap.length) (h := s'.h)
          (ρ := PointClaims.mapEnv t.mapping (push e ρ))
        exact ⟨⟨hpa, Nat.le_trans hm hadm.length_le⟩, Nat.le_trans hm₀ hadm.length_le, hcf'⟩)
  exact ⟨_, _, cn, ce, _, _, hj, ho.toPlain (fun _ => trivial) (fun _ => trivial)⟩

omit [DecidableEq ι] [Hashable ι] in
/-- Lift `NodesChecked` from `confinedPreA` to `confinedPreU` by adjoining
`StableNow`. -/
theorem nodesChecked_confined_U {P : Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat}
    {ε : HeapKnowledge.EntryState} {ctx : Nat → List (Ty ι)} {stated : Nat → Option HeapKnowledge.Knowledge}
    {conf : LocalConfinement.Table} {widthFn : Nat → Nat} {Ξres Tres : Fam} {m : Nat}
    (hw : NodesChecked P (confinedPreA G w startNames ε ctx stated conf widthFn) Ξres Tres
      (fun _ => True) (fun _ => True) m)
    (fields : List (Nat × String)) (h₀ : Heap) :
    NodesChecked P (confinedPreU G w startNames ε ctx stated conf widthFn fields h₀) Ξres Tres
      (fun _ => True) (fun _ => True) m :=
  (nodesCheckedR_stable (Ret := fun _ _ _ _ => True) (RetE := fun _ _ _ _ => True)
    (S := fun s => GraphCode.ArgumentPathTracking.StableNow fields ε.env h₀ s.W)
    (fun _ _ ha hs => hs.transfer ha.1 ha.2) hw.toR).toPlain

end ConfinedWalk

section ConfinedSound
variable {ι : Type} [Labels ι]

/-- **THE GRAPH THEOREM for a confined run**: when `c.confinement = some conf`
and `c.AcceptsWalk after`, `SinglePass.run` checked `c.framed = conf.framed`
and `checkWalkConfinement` on every visited node. Threading `ConfinedAt`
through `confinedPreU` yields the exact ordinary `Target.GraphGuarantee`. -/
theorem run_sound_checked_confined (hrun : RunTraversedC ι) (hyield : NodesYield ι) (hnear : LinearNearFuelEq)
    (hreg : RegionsHeld ι) {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I}
    {after : Answered G} {admits : MixedAssignment ι → Prop} {conf : LocalConfinement.Table}
    (hacc : c.AcceptsWalk after) (hconf : c.confinement = some conf)
    (hscope : Target.CheckerScope G I c.passChecker admits)
    (hcodes : CodesSound G c.codes) (hsums : SummariesSound G I after.summaries.toList)
    (hfields : ∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
      GraphCode.ArgumentPathTracking.checkEntryFields G c.inputs regions = true) :
    Target.GraphGuarantee G admits c.P c.start c.goal c.inputs c.entrySeparation c.entryIndices c.assertions
      c.bound c.ensures (Target.regionOf c.regional) := by
  have hp : RunPremises G I c after admits := ⟨hacc, hscope, hcodes, hsums, hfields⟩
  obtain ⟨r, hchk⟩ := hrun G I c after hacc hsums
  obtain ⟨dead, hd, hgiven, hmerging, σ, reach, hw, hweq, hst_eq⟩ := hchk
  obtain ⟨hfr_eq, hwc⟩ := confinement_of_accepts hacc hconf hw
  have hstart_empty : conf.at c.start = {} := start_empty_of_walkConfinement hwc
  let widthFn : Nat → Nat := fun lbl => ((c.claims[lbl]?).map (·.context.length)).getD 0
  have hnode_conf : ∀ l (hl : r.w.visited l),
      c.claims[l]? = some (r.node l hl).c ∧
      LocalConfinement.checkNode G I c.codes after.summaries.toList c.claims conf l
        (r.node l hl).node (r.node l hl).c (r.node l hl).st.stepK (r.node l hl).st.stepDeriv = true := by
    intro l hl
    have hl' : (ofPass σ.walk (passHeads c)).visited l := hweq ▸ hl
    obtain ⟨lw, hlw, hvis⟩ := hl'
    have hstep_rec := hst_eq l hl
    simp only [hlw, Option.bind_some] at hstep_rec
    obtain ⟨cl, hcl, hchk_l⟩ := checkNode_of_walkConfinement hwc hlw hvis (r.node l hl).hP hstep_rec
    -- Show `cl = (r.node l hl).c` using `NodeExitTrace`
    obtain ⟨_, env, _, _, _, _, _, _, _, hclaimed, _, _, _, _, _, _, _, _, hrc, _⟩ := (hd l hl).2
    have hlt : l < c.claims.length := by
      cases h : decide (l < c.claims.length) with
      | true => exact of_decide_eq_true h
      | false =>
        have : c.claims[l]? = none := List.getElem?_eq_none (by simpa using h)
        rw [this] at hcl; cases hcl
    have hcl_eq : cl = (r.node l hl).c := by
      have h1 : c.claims[l] = cl := by
        have := List.getElem?_eq_getElem hlt
        rw [hcl] at this
        exact Option.some.inj this.symm
      rw [hrc, hclaimed]
      simpa [hlt] using h1.symm
    subst hcl_eq
    exact ⟨hcl, hchk_l⟩
  have hwalk_of : ∀ (η : MixedAssignment ι), admits η → ∀ (ε : HeapKnowledge.EntryState) (m : Nat),
      (∀ node ∈ c.P, Confinement.TmRefsBelow ε.heap.length node.expression) →
      NodesChecked c.P (confinedPreA (reassign G η) r.w (List.range c.inputs.length) ε r.ctx r.stated conf widthFn)
        (excOf (reassign G η)) (GoalHolds (reassign G η) c.goal (c.goal.argument ε.env))
        (fun _ => True) (fun _ => True) m := by
    intro η hη ε m htbP
    obtain ⟨pc', hpc⟩ := scope_reassign hscope hη
    refine nodesChecked_confined (pc := pc') (r.traversed.reassign η) (headsEntered_of_recorded r.heads) hnear
      (codesSound_reassign hcodes η) (Parametricity.summariesSound_reassign G η I hsums) htbP fun l hl => ?_
    obtain ⟨ys, hY⟩ := hyield G I c after admits hp r
      ⟨dead, hd, hgiven, hmerging, σ, reach, hw, hweq, hst_eq⟩ η hη ε m l hl
    obtain ⟨hcl, hchk_l⟩ := hnode_conf l hl
    refine ⟨nodeChecked_reassign hpc (r.node l hl), ys, ?_, hcl, ?_⟩
    · rw [hfr_eq] at hY; exact hY
    · exact (LocalConfinement.checkNode_reassign G η I c.codes after.summaries.toList c.claims conf l
        (r.node l hl).node (r.node l hl).c (r.node l hl).st.stepK (r.node l hl).st.stepDeriv).trans hchk_l
  have hstable : ∀ (η : MixedAssignment ι), admits η →
      ∀ Φ regions exc, Target.regionOf c.regional = some (Φ, regions, exc) →
        ∀ ρ (s : IndexedHeap), EnvOk (reassign G η) c.inputs ρ s.n s.W →
          GraphCode.ArgumentPathTracking.StableNow (GraphCode.ArgumentPathTracking.stableFields regions) ρ s.h s.W := by
    intro η _ Φ regions exc hr ρ s he
    exact GraphCode.ArgumentPathTracking.checkEntryFields_sound
      ((checkEntryFields_reassign G η c.inputs regions).trans (hfields Φ regions exc hr)) he s.pos s.ok
  have hstartU : ∀ (η : MixedAssignment ι) (hη : admits η) {ρ : Env} {m : Nat} {s : IndexedHeap},
      EnvOk (reassign G η) c.inputs ρ s.n s.W → HeapSeparation.Holds c.entrySeparation ρ →
      HeapKnowledge.IndexHolds ⟨ρ, s.h⟩ c.entryIndices ρ s.h → m ≤ s.h.length →
      confinedPreU (reassign G η) r.w (List.range c.inputs.length) ⟨ρ, s.h⟩ r.ctx r.stated conf widthFn
        (regionFields (Target.regionOf c.regional)) s.h c.start ρ m s := by
    intro η hη ρ m s hv hs hi hm
    refine ⟨⟨⟨r.start.entered η ρ m s hv hs hi, hm⟩, Nat.le_refl _,
      LocalConfinement.confinedAt_empty (width := widthFn) hstart_empty⟩, ?_⟩
    cases hr : Target.regionOf c.regional with
    | none => intro p hp'; simp [regionFields] at hp'
    | some reg =>
      obtain ⟨Φ, regions, exc⟩ := reg
      simpa [regionFields] using hstable η hη Φ regions exc hr ρ s hv
  have hlabelled := assertionsLabelled_of_checked labelsChecked G I c after admits hp r
  have hgg : GraphGuarantee G admits c.P c.start c.goal c.inputs c.entrySeparation c.entryIndices c.assertions
      c.bound c.ensures (Target.regionOf c.regional) :=
    { safe := fun η hη n W h ρ he hPn hρ => by
        obtain ⟨hv, hs, hi, ha, ho⟩ := he
        cases n with
        | zero => exact hρ
        | succ n =>
          let s : IndexedHeap := ⟨n + 1, W, h, Nat.zero_lt_succ _, ha, ho⟩
          have htbP : ∀ node ∈ c.P, Confinement.TmRefsBelow h.length node.expression :=
            fun node hm => Confinement.refsOk_tmRefsBelow ho (hPn node hm)
          exact graph_safe_at (nodesChecked_confined_U (hwalk_of η hη ⟨ρ, h⟩ 0 htbP)
              (regionFields (Target.regionOf c.regional)) h)
            confinedPreU_adminClosed (hstartU η hη (s := s) hv hs hi (by simp)) hPn hρ
      bounded := fun Φ Ψ fr hb E K hP η hη n W h L d _ he hgo _ _ => by
        obtain ⟨hv, hs, hi, ha, ho⟩ := he
        have htbP : ∀ node ∈ c.P, Confinement.TmRefsBelow h.length node.expression :=
          fun node hm => Confinement.refsOk_tmRefsBelow ho ((GraphCode.goto_refs hgo).1 node.expression (mem_program_expr (hP.symm ▸ hm)))
        have hkeep := footprintKept_of_walk hp (fun l hl => (hd l hl).1) hη hb ⟨envOf L d, h⟩ h
        exact keeps_postExc (hP ▸ nodesChecked_confined_U (hwalk_of η hη ⟨envOf L d, h⟩ h.length htbP)
            (regionFields (Target.regionOf c.regional)) h)
          confinedPreU_adminClosed (nodesKeep_anti (fun _ _ _ hu => hu.1.1.1.1) (hP ▸ hkeep)) (fun _ _ _ h => h)
          n W h _ _ .goto ha ho (GraphCode.goto_refs hgo).1 (GraphCode.goto_refs hgo).2
          (fun hq ha' ho' => hstartU η hη (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
          (.inr (Footprints.Closed.Holds.refl Φ h))
      ensured := fun hne E K hP η hη n W h L d _ he hgo => by
        obtain ⟨hv, hs, hi, ha, ho⟩ := he
        have htbP : ∀ node ∈ c.P, Confinement.TmRefsBelow h.length node.expression :=
          fun node hm => Confinement.refsOk_tmRefsBelow ho ((GraphCode.goto_refs hgo).1 node.expression (mem_program_expr (hP.symm ▸ hm)))
        have hret := returnsEnsured_of_walk hp (fun l hl => (hd l hl).1) hη hne ⟨envOf L d, h⟩ 0
        unfold ReturnsEnsured at hret
        rw [← hP] at hret
        exact (keeps_postExc (hP ▸ nodesChecked_confined_U (hwalk_of η hη ⟨envOf L d, h⟩ 0 htbP)
            (regionFields (Target.regionOf c.regional)) h)
          confinedPreU_adminClosed (nodesKeep_anti (fun _ _ _ hu => hu.1.1.1.1) hret) (fun _ _ _ h => h)
          n W h _ _ .goto ha ho (GraphCode.goto_refs hgo).1 (GraphCode.goto_refs hgo).2
          (fun hq ha' ho' => hstartU η hη (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
          trivial).post
      regionally := fun Φ regions exc hr E K hP η hη n W h L d _ he hgo => by
        obtain ⟨hv, hs, hi, ha, ho⟩ := he
        have htbP : ∀ node ∈ c.P, Confinement.TmRefsBelow h.length node.expression :=
          fun node hm => Confinement.refsOk_tmRefsBelow ho ((GraphCode.goto_refs hgo).1 node.expression (mem_program_expr (hP.symm ▸ hm)))
        obtain ⟨X, hX⟩ := hreg G I c after admits hp r
          ⟨dead, hd, hgiven, hmerging, σ, reach, hw, hweq, hst_eq⟩ η hη Φ regions exc hr
        have hcat := Footprints.intrinsicClasses_ok ho (GraphCode.goto_refs hgo).2
        have hf : regionFields (Target.regionOf c.regional) = GraphCode.ArgumentPathTracking.stableFields regions := by
          simp [regionFields, hr]
        exact keeps_postExc (hP ▸ nodesChecked_confined_U (hwalk_of η hη ⟨envOf L d, h⟩ h.length htbP)
            (regionFields (Target.regionOf c.regional)) h)
          confinedPreU_adminClosed (nodesKeep_anti (fun _ _ _ hu => ⟨hu.1.1.1.1, hf ▸ hu.2⟩) (hP ▸ (hX ⟨envOf L d, h⟩ h hcat).2))
          (fun _ _ _ h => h) n W h _ _ .goto ha ho (GraphCode.goto_refs hgo).1 (GraphCode.goto_refs hgo).2
          (fun hq ha' ho' => hstartU η hη (s := ⟨n, W, h, hq, ha', ho'⟩) hv hs hi (by simp))
          (hX ⟨envOf L d, h⟩ h hcat).1
      asserted := fun η hη n W h ρ he hPn hρ l k hl j h' ρ' hj hrun => by
        obtain ⟨hv, hs, hi, ha, ho⟩ := he
        cases n with
        | zero => omega
        | succ n =>
          let s : IndexedHeap := ⟨n + 1, W, h, Nat.zero_lt_succ _, ha, ho⟩
          have htbP : ∀ node ∈ c.P, Confinement.TmRefsBelow h.length node.expression :=
            fun node hm => Confinement.refsOk_tmRefsBelow ho (hPn node hm)
          obtain ⟨s', he', hp'⟩ := reached_pre (nodesChecked_confined_U (hwalk_of η hη ⟨ρ, h⟩ 0 htbP)
              (regionFields (Target.regionOf c.regional)) h)
            confinedPreU_adminClosed (hstartU η hη (s := s) hv hs hi (by simp)) hPn hρ hrun hj
          exact he' ▸ hp'.1.1.1.2 k (hlabelled l k hl hp'.1.1.1.1.1.1) }
  exact GraphGuarantee.toTarget (accepts_source hacc) hgg

/-- **THE GRAPH THEOREM of the single pass**: dispatches `Target.RunCall.Accepts`
between the unframed walk (`run_sound_checked_unframed`) and the checked
local-confinement walk (`run_sound_checked_confined`). -/
theorem run_sound_pass (hrec : RecordsSound ι) (hchk : RecordsChecked ι) (hyield : NodesYield ι)
    (hnear : LinearNearFuelEq) (hreg : RegionsHeld ι) : Target.RunSound ι := by
  intro G I c after admits ⟨hacc, hmode⟩ hscope hcodes hsums hfields
  rcases hmode with hcf | hnf
  · cases hconf : c.confinement with
    | none => rw [hconf] at hcf; cases hcf
    | some conf =>
      exact run_sound_checked_confined (run_traversedC hrec hchk) hyield hnear hreg hacc hconf hscope hcodes hsums hfields
  · exact run_sound_checked_unframed (run_traversedC hrec hchk) hyield hnear hreg hacc hnf hscope hcodes hsums hfields

end ConfinedSound

end Verification.TolerantFrames
