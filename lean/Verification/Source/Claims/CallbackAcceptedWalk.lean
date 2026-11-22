import Verification.Source.Claims.CallbackRecordedVisits
import Verification.Programs.TolerantFramesSinglePassSound

namespace Verification.SourceClaimJson.CallbackEffectInference
open PositiveRules ProgramTyping SinglePass TolerantFrames PositiveGraphs PositiveCertificates CertificateProducer
open Footprints RequestJson SourceElaboration GraphCode ProgramCertificates ControlFlow LabelStore HeapObservations PointClaims

variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

def gradedWalk (c : TolerantFrames.Target.RunCall G I) :=
  runWalk G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions c.cuts c.candidates
    c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers c.reference c.debugNode
    c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation c.observe c.tracing
    c.observeEntry c.regional true

theorem gradedWalk_origin {c : TolerantFrames.Target.RunCall G I} {σ : WalkState ι G} {reach}
    (plain : c.framed = []) (walk : gradedWalk c = .ok (σ,reach)) :
    ∃ env : WalkEnv ι G I, env.grading = true ∧ env.nodes = c.P.toArray ∧ env.claimed = c.claims.toArray ∧
      env.codes = c.codes ∧ LabelRecordOrigin env σ.walk σ.answers ∧
      RunCall.walk c = .ok (σ.unrecorded,reach) := by
  have align := runWalk_ungraded G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions c.cuts
    c.candidates c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers c.reference
    c.debugNode c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation c.observe
    c.tracing c.observeEntry c.regional
  change (gradedWalk c).map _ = _ at align
  rw [walk] at align
  have ordinary : RunCall.walk c = .ok (σ.unrecorded,reach) := by
    unfold RunCall.walk
    rw [plain]
    exact align.symm
  unfold gradedWalk runWalk at walk
  rw [setup_graded] at walk
  cases hs : RunCall.setup c with
  | error err =>
    unfold RunCall.setup at hs
    rw [plain] at hs
    rw [hs] at walk
    contradiction
  | ok p =>
    obtain ⟨env,σ0⟩ := p
    have cfg := setup_ok hs
    unfold RunCall.setup at hs
    rw [plain] at hs
    rw [hs] at walk
    simp only [Except.map,bind,Except.bind] at walk
    cases hd : drive (visit G I {env with grading := true}) (env.n+1) σ0 with
    | error err =>
      rw [hd] at walk
      contradiction
    | ok last =>
      rw [hd] at walk
      cases walk
      obtain ⟨counts,trace,h0⟩ := cfg.state
      rw [h0] at hd
      exact ⟨{env with grading := true},rfl,cfg.nodes,cfg.claims,cfg.codes,drive_from_setup_labelRecordOrigin _ rfl hd,ordinary⟩

theorem acceptedWalk_nodes {c : TolerantFrames.Target.RunCall G I} {after admits} {r : RunWalkA G I c}
    (hp : RunPremises G I c after admits) (identity : admits G.env)
    (plain : c.framed = []) (hc : WalkChecked c r) (ε : HeapKnowledge.EntryState) (m : Nat) :
    NodesChecked c.P (marked (passPreA G r.w (List.range c.inputs.length) ε r.ctx r.stated))
      (excOf G) (GoalHolds G c.goal (c.goal.argument ε.env)) (fun _ => True) (fun _ => True) m := by
  have hy : NodesYield ι := nodesYield_of subtypeAnswersAll (exitsYield_of_kept
    (fun _ _ _ _ _ _ _ hc => hc.startWrittenImpliesStated))
  apply nodesChecked_of_walkJ r.traversed _ (headsEntered_of_recorded r.heads) linearNearFuelEq
  refine stepEdgesSound_of_yields (images := I) (pc := c.passChecker) ?_ hp.2.2.1
  intro l hl
  obtain ⟨ys,hY⟩ := hy G I c after admits hp r hc G.env identity ε m l hl
  exact ⟨r.node l hl,ys,hY.toPlain fun _ _ hF => by simp [framedFOf, SinglePass.framedAt,plain] at hF⟩

/-- The graded records from the successful ordinary callback pass bound each
completed evaluation within the invocation's finite semantic budget. -/
theorem boundedRecordedExitSound_of_accepted {q : CodeRequest ι} {c : TolerantFrames.Target.RunCall G I}
    {σ : WalkState ι G} {reach after admits entry limit} {s : IndexedHeap}
    (hp : RunPremises G I c after admits) (identity : admits G.env)
    (plain : c.framed = []) (walk : gradedWalk c = .ok (σ,reach))
    (programEq : c.P = GraphCode.program q.entry.exprs q.entry.conts)
    (claimsEq : c.claims = q.claims) (startEq : c.start = q.entry.start)
    (envOK : EnvOk G c.inputs entry s.n s.W) (roots : RootsOk s.W entry)
    (separation : HeapSeparation.Holds c.entrySeparation entry)
    (indices : HeapKnowledge.IndexHolds ⟨entry,s.h⟩ c.entryIndices entry s.h)
    (room : limit ≤ s.n)
    (width : (codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine).length ≤ c.inputs.length) :
    BoundedRecordedExitSound G q σ.walk.visits entry s.h limit := by
  have origins :
      let nodes := GraphCode.program q.entry.exprs q.entry.conts
      let inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine
      let roots := (List.range inputs.length).map fun i => ({ position := i, path := [] } : ArgumentSpineRegion)
      let entries := q.claims.map fun c => ({ sequent := some ⟨c.context, .undef, c.type⟩, edges := [] } : NodeEvidence ι)
      ∀ {k h l ρ}, Execution nodes k s.h (.at q.entry.start entry) h (.at l ρ) →
        k < limit → ArgumentPathTracking.Holds ((certifiedRootTable nodes q.entry.start inputs.length (regionTable nodes entries q.entry.start roots)).toArray.getD l []) ρ entry s.h := by
    dsimp only
    intro k h l ρ reached _
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
    apply certifiedRootTable_reached (run := reached)
    intro i hi
    exact (meaning_value (envOK.2 i _ (List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hi width)))).1
  obtain ⟨env,graded,enodes,eclaims,ecodes,origin,ordinary⟩ := gradedWalk_origin plain walk
  have hv := visitsRecord_of (ι := ι) (visitsRest_of (exitsPushOk_of exitsWidth)
    (visitsSettle_of (visitStepPrefix_of_exitStep exitStepPrefix)) visitsImplications) visitExits_answers_prefix
  obtain ⟨r,checked⟩ := run_traversedC (recordsSound_of setupRecords_of hv) (recordsChecked_of setupRecords_of hv)
    G I c after hp.1 hp.2.2.2.1
  have checkedAgain := checked
  obtain ⟨_,hnode,_,_,raw,count,hraw,walkEq,recordStep⟩ := checked
  rw [ordinary] at hraw
  cases hraw
  have hweq : r.w = ofPass σ.walk (passHeads c) := walkEq
  obtain ⟨_,_,ordinary',_,ah⟩ := walk_of_accepts walkStopsRefuse hp.1
  rw [ordinary] at ordinary'
  cases ordinary'
  have asums : SummariesSound G I σ.answers.summaries.toList := ah ▸ hp.2.2.2.1
  let ε : HeapKnowledge.EntryState := ⟨entry,s.h⟩
  let pre := marked (passPreA G r.w (List.range c.inputs.length) ε r.ctx r.stated)
  have initialPre : pre q.entry.start entry 0 s := by
    rw [← startEq]
    exact ⟨r.start.entered G.env _ _ _ envOK separation indices,Nat.zero_le _⟩
  have nodes := acceptedWalk_nodes hp identity plain checkedAgain ε 0
  have down : AdminClosed pre 0 := fun _ _ _ _ ha hh h => ⟨passPreA_adminClosed _ _ _ _ ha hh h.1, by rw [hh]; exact h.2⟩
  have src := accepts_source hp.1
  have table := enodes.trans (congrArg List.toArray programEq)
  have checkedClaim (l) (hl : r.w.visited l) : env.claimed[l]! = (r.node l hl).c := by
    obtain ⟨raw, env', before, en', sd', ex', _, _, hn, hcl, _, _, _, _, _, _, _,
      hnode, hclaim, _⟩ := (hnode l hl).2
    rw [eclaims,hclaim,hcl]
  have width : c.claims.length = c.P.length := by
    obtain ⟨env0,σ0,hs,_,_⟩ := returnedWalk_setup_inv ordinary
    simpa using (setup_ok hs).claimed
  have claimAt (l) (hl : r.w.visited l) : q.claims[l]? = some (r.node l hl).c := by
    have inside := (List.getElem?_eq_some_iff.mp (r.node l hl).hP).1
    rw [← checkedClaim l hl,eclaims,← claimsEq]
    rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,List.getElem?_toArray,
      List.getElem?_eq_getElem (by omega : l < c.claims.length)]
    rfl
  let nAt := r.node
  have aligned : ∀ l hl, (σ.walk.labels[l]?).bind (·.stepped) = some (nAt l hl).st := recordStep
  have c1 : ∀ l hl, env.claimed[l]! = (nAt l hl).c ∧ q.claims[l]? = some (nAt l hl).c :=
    fun l hl => ⟨checkedClaim l hl,claimAt l hl⟩
  have typed : ∀ l ρ st, pre l ρ 0 st → passPreT G r.w (List.range c.inputs.length) ε r.ctx l ρ 0 st :=
    fun _ _ _ h => h.1.1
  clear_value nAt
  generalize hw : r.w = proofWalk at nAt aligned c1 typed
  rw [hweq] at hw
  subst proofWalk
  generalize hP : c.P = P at nAt aligned c1 nodes src
  rw [programEq] at hP
  subst P
  generalize hcode : c.codes = checker at nAt aligned c1
  rw [← ecodes] at hcode
  subst checker
  intro l node h ρ k reached hn j hfinal t steps fits ex ends
  exact boundedRecordedExitSound_of_walk origin graded (ecodes ▸ hp.2.2.1) asums nAt aligned table c1
    room nodes down initialPre typed src roots origins reached hn steps fits ex ends

/-- Every normal or exceptional completion covered by the accepted
invocation's world satisfies the computed footprint at that exit. -/
theorem inferChecked_execution_of_accepted {q : CodeRequest ι} {c : TolerantFrames.Target.RunCall G I}
    {σ : WalkState ι G} {reach after admits entry limit} {s : IndexedHeap}
    (hp : RunPremises G I c after admits) (identity : admits G.env)
    (plain : c.framed = []) (walk : gradedWalk c = .ok (σ,reach))
    (programEq : c.P = GraphCode.program q.entry.exprs q.entry.conts)
    (claimsEq : c.claims = q.claims) (startEq : c.start = q.entry.start)
    (envOK : EnvOk G c.inputs entry s.n s.W) (roots : RootsOk s.W entry)
    (separation : HeapSeparation.Holds c.entrySeparation entry)
    (indices : HeapKnowledge.IndexHolds ⟨entry,s.h⟩ c.entryIndices entry s.h)
    (room : limit ≤ s.n)
    (width : (codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine).length ≤ c.inputs.length)
    {out hfinal state} (inferred : inferChecked G q σ.walk.visits = .ok out)
    (run : Execution (GraphCode.program q.entry.exprs q.entry.conts) limit s.h (.at q.entry.start entry) hfinal state)
    (exit : CallEffects.Completion) (v : Val)
    (done : state = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    ∃ bound, out.get exit = some bound ∧ Footprints.Post bound entry s.h hfinal := by
  apply inferChecked_execution_bounded inferred _ run exit v done
  intro l node h ρ k reached hn j h' t steps fits ex ends
  exact boundedRecordedExitSound_of_accepted hp identity plain walk programEq claimsEq startEq
    envOK roots separation indices room width reached hn steps fits ex ends

end Verification.SourceClaimJson.CallbackEffectInference
