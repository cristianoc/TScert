import Verification.Source.Claims.CallbackEffectStepSound
import Verification.Source.Claims.CallbackVisitMembership
import Verification.Programs.TolerantFramesDriverVisitRest
import Verification.Programs.TolerantFramesInvocation

namespace Verification.SourceClaimJson.CallbackEffectInference
open ControlFlow GraphCode Footprints ProgramTyping RequestJson SourceElaboration
open PositiveCertificates PositiveGraphs PositiveRules CallEffects CertificateProducer HeapObservations ProgramCertificates

/-- Concrete evidence needed from the ordinary walk at a reached label.
The record is built with precisely the derivation and knowledge interpreted here. -/
structure ReachedVisit {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]
    (G : NormalGraph ι) (records : Array SinglePass.VisitRecord) (l : Nat) (node : Node)
    (pt : PointClaim ι) (ρ : Env) (h : Heap) (j : Nat) where
  images : InstanceImageCheck G
  codes : CodeEntry ι → Bool
  sums : List (ReadSummary ι)
  state : SinglePass.State
  knowledge : HeapKnowledge.Knowledge
  deriv : ProgramCertificates.Evidence ι
  fresh : Bool
  member : SinglePass.VisitRecord.of G images codes l node pt state sums knowledge deriv fresh ∈ records.toList
  codesOK : CodesSound G codes
  sumsOK : SummariesSound G images sums
  n : Nat
  W : WorldT n
  ε : HeapKnowledge.EntryState
  env : EnvOk G pt.context ρ n W
  know : HeapKnowledge.Holds knowledge ε ρ h
  adm : WorldAdm W
  heap : HeapOk n W h
  safe : Safe (excOf G) (meaning G pt.type) n W h (instantiate 0 ρ node.expression)
  budget : j < n

private theorem prefixLength {P k h s h' s'} (run : Execution P k h s h' s') : h.length ≤ h'.length := by
  induction run with
  | refl => exact Nat.le_refl _
  | next tr _ ih =>
    apply Nat.le_trans _ ih
    cases tr <;> first | exact Nat.le_refl _ | exact step_length_le (by assumption)

open TolerantFrames PointClaims

/-- Readback at the checked node chosen by the ordinary walk. Matching
the final label's step suffices even if several visits produced records. -/
theorem reachedVisit_of_checkedNode {ι : Type} [LabelStore.Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}
    {env : SinglePass.WalkEnv ι G I} {w : SinglePass.Walk ι} {after : Answered G} {l : Nat}
    (origin : LabelRecordOrigin env w after) (graded : env.grading = true)
    (codes : CodesSound G env.codes) (sums : SummariesSound G I after.summaries.toList)
    {heads ctx P start pc} (na : NodeChecked G I env.codes pc P (ofPass w heads) start ctx l)
    {lab : SinglePass.LabelWalk ι} (label : w.labels[l]? = some lab) (visited : lab.visited = true)
    (matched : lab.stepped = some na.st) (nodeEq : env.nodes[l]! = na.node)
    (claimEq : env.claimed[l]! = na.c)
    {ρ : Env} {s : IndexedHeap} {j : Nat} (budget : j < s.n)
    {ε : HeapKnowledge.EntryState} {m : Nat}
    (context : EnvOk G na.c.context ρ s.n s.W)
    (refs : RefsOk s.W (instantiate 0 ρ na.node.expression)) (roots : RootsOk s.W ρ)
    (holds : StateHolds G ((ofPass w heads).entry l) ((ofPass w heads).implies l) start ε ρ m s) :
    Nonempty (ReachedVisit G w.visits l na.node na.c ρ s.h j) := by
  obtain ⟨before,en,sd,reg,hs,rfl,hpre,r,hr,hm⟩ := origin l lab label visited
  have eq : sd.st = na.st := Option.some.inj matched
  rw [← na.hentry] at holds
  obtain ⟨_,know,_,cn,ce,parts⟩ := stepChecked_parts na.hstep holds na.wf na.below na.width context codes na.sums
  obtain ⟨_,cert⟩ := SinglePass.visitStep_record G I env _ _ _ _ hs
  rw [cert] at hr
  simp only [SinglePass.stepCheck,graded,ite_true,Option.some.injEq] at hr
  subst r
  rw [nodeEq,claimEq,eq] at hm
  exact ⟨⟨I,env.codes,_,en.entry,_,_,_,by simpa using hm,codes,(fun x hx => sums x (hpre.mem x hx)),
    s.n,s.W,ε,context,know,s.adm,s.ok,(parts.1 refs roots).post.erase,budget⟩⟩

private theorem graph_inv_run_refs {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) :
    ∀ {k h st h' st'}, Transitions P k h st h' st' → ∀ (s : IndexedHeap), s.h = h → k < s.n →
      (∀ node ∈ P, RefsOk s.W node.expression) → StateRefs s.W st →
      GraphInv pre Ξres Tres Qres Rres m s.n s.W s.h st →
      ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        StateRefs s'.W st' ∧ GraphInv pre Ξres Tres Qres Rres m s'.n s'.W s'.h st' := by
  intro k h st h' st' hst
  induction hst with
  | refl => intro s hs _ _ rr hinv; exact ⟨s, Admissible.refl s, hs, rfl, rr, hinv⟩
  | next tr _ ih =>
    intro s hs hk hPr hr hinv
    obtain ⟨n, W, h₀, pos, adm, ok⟩ := s
    simp only at hs hk hPr hr hinv ⊢
    subst hs
    cases n with
    | zero => omega
    | succ j =>
      rcases graph_step hnodes hdown adm ok hPr hr hinv with (⟨v, rfl, -⟩ | ⟨v, rfl, -⟩) | ⟨U, h₁, st₁, hx, hu, tr', hh, hrs, hi⟩
      · cases tr
      · cases tr
      · obtain ⟨rfl, rfl⟩ := transition_det tr tr'
        obtain ⟨s', ha, he, hn, hinv'⟩ := ih ⟨j, U, _, by omega, hu, hh⟩ rfl (by simp only; omega)
          (fun node hm => RefsOk_mono hx (RefsOk_trunc _ (hPr node hm))) hrs hi
        exact ⟨s', Admissible.trans ⟨Nat.le_succ j, hx⟩ ha, he, by simp only at hn; omega, hinv'⟩

/-- Recover both the node assertion and its exact remaining world index. -/
theorem reachedVisitWorld {P start entry l ρ k h m pre Ξ T Q R} {s : IndexedHeap}
    (nodes : NodesChecked P pre Ξ T Q R m) (down : AdminClosed pre m)
    (initial : pre start entry m s) (refs : ∀ node ∈ P, RefsOk s.W node.expression)
    (roots : ∀ i, RefsOk s.W (entry i))
    (reached : Execution P k s.h (.at start entry) h (.at l ρ)) (room : k < s.n) :
    ∃ next : IndexedHeap, next.h = h ∧ next.n + k = s.n ∧ RootsOk next.W ρ ∧ pre l ρ m next := by
  have translate {k h a h' b} (r : Execution P k h a h' b) : Transitions P k h a h' b := by
    induction r with
    | refl => exact .refl
    | next st _ ih => exact .next st ih
  obtain ⟨next,_,hh,hn,rr,inv⟩ := graph_inv_run_refs nodes down (translate reached) s rfl room refs roots
    (fun _ _ _ => initial)
  exact ⟨next,hh,hn,rr,inv next.pos next.adm next.ok⟩

theorem boundedRecordedExitSound_of_reachedVisits {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]
    {G : NormalGraph ι} {q : CodeRequest ι} {records entry initial limit}
    (visits : ∀ {l node h ρ k}, Execution (GraphCode.program q.entry.exprs q.entry.conts)
      k initial (.at q.entry.start entry) h (.at l ρ) →
      (GraphCode.program q.entry.exprs q.entry.conts)[l]? = some node →
      ∀ j, k + 1 + j + 1 ≤ limit → ∃ pt, q.claims[l]? = some pt ∧
        Nonempty (ReachedVisit G records l node pt ρ h j))
    (origins :
      let nodes := GraphCode.program q.entry.exprs q.entry.conts
      let inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine
      let roots := (List.range inputs.length).map fun i => ({ position := i, path := [] } : ArgumentSpineRegion)
      let entries := q.claims.map fun c => ({ sequent := some ⟨c.context, .undef, c.type⟩, edges := [] } : NodeEvidence ι)
      ∀ {k h l ρ}, Execution nodes k initial (.at q.entry.start entry) h (.at l ρ) →
        k < limit → ArgumentPathTracking.Holds ((certifiedRootTable nodes q.entry.start inputs.length (regionTable nodes entries q.entry.start roots)).toArray.getD l []) ρ entry initial) :
    BoundedRecordedExitSound G q records entry initial limit := by
  intro l node h ρ k reached hn j h' t steps room ex ends
  obtain ⟨pt,hpt,⟨v⟩⟩ := visits reached hn j room
  have facts := origins reached (by omega)
  let record := SinglePass.VisitRecord.of G v.images v.codes l node pt v.state v.sums v.knowledge v.deriv v.fresh
  have extend (prior) (hp : Footprints.Post prior entry initial h) :=
    stepCertificate_extends (fresh := SinglePass.recvFresh node v.state) (d := v.deriv) ex v.codesOK v.sumsOK
      v.env v.know v.adm v.heap v.safe hp facts v.budget steps ends
  have prefixPost : Footprints.Post Closed.top.fp entry initial h :=
      Closed.post_iff.mpr (Closed.holds_iff.mp (Closed.holds_top.mpr (prefixLength reached)))
  obtain ⟨w,hw,_,keeps⟩ := extend _ prefixPost
  refine ⟨record,v.member,rfl,pt,w,hpt,hw,?_,keeps⟩
  intro prior hp
  obtain ⟨other,ho,post,-⟩ := extend _ hp
  cases hw.symm.trans ho
  exact post

/-- A graded walk's checked nodes supply every visit of a bounded concrete
run. The path table and typed entry assertion are independently checkable. -/
theorem boundedRecordedExitSound_of_walk {ι : Type} [LabelStore.Labels ι]
    {G : NormalGraph ι} {I : InstanceImageCheck G} {q : CodeRequest ι}
    {env : SinglePass.WalkEnv ι G I} {w : SinglePass.Walk ι} {after : Answered G}
    (origin : LabelRecordOrigin env w after) (graded : env.grading = true)
    (codes : CodesSound G env.codes) (sums : SummariesSound G I after.summaries.toList)
    {heads ctx start pc} {ε : HeapKnowledge.EntryState}
    (nodeAt : ∀ l, (ofPass w heads).visited l →
      NodeChecked G I env.codes pc (GraphCode.program q.entry.exprs q.entry.conts) (ofPass w heads) start ctx l)
    (matchStep : ∀ l hl, (w.labels[l]?).bind (·.stepped) = some (nodeAt l hl).st)
    (nodeTable : env.nodes = (GraphCode.program q.entry.exprs q.entry.conts).toArray)
    (claims : ∀ l hl, env.claimed[l]! = (nodeAt l hl).c ∧ q.claims[l]? = some (nodeAt l hl).c)
    {entry limit m pre Ξ T Q R} {s : IndexedHeap} (room : limit ≤ s.n)
    (nodes : NodesChecked (GraphCode.program q.entry.exprs q.entry.conts) pre Ξ T Q R m)
    (down : AdminClosed pre m) (initialPre : pre q.entry.start entry m s)
    (typed : ∀ l ρ h, pre l ρ m h → passPreT G (ofPass w heads) start ε ctx l ρ m h)
    (source : (GraphCode.program q.entry.exprs q.entry.conts).all
      (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (roots : RootsOk s.W entry)
    (origins :
      let nodes := GraphCode.program q.entry.exprs q.entry.conts
      let inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine
      let roots := (List.range inputs.length).map fun i => ({ position := i, path := [] } : ArgumentSpineRegion)
      let entries := q.claims.map fun c => ({ sequent := some ⟨c.context, .undef, c.type⟩, edges := [] } : NodeEvidence ι)
      ∀ {k h l ρ}, Execution nodes k s.h (.at q.entry.start entry) h (.at l ρ) →
        k < limit → ArgumentPathTracking.Holds ((certifiedRootTable nodes q.entry.start inputs.length (regionTable nodes entries q.entry.start roots)).toArray.getD l []) ρ entry s.h) :
    BoundedRecordedExitSound G q w.visits entry s.h limit := by
  refine boundedRecordedExitSound_of_reachedVisits (G := G) (q := q) (records := w.visits) ?_ origins
  intro l node h ρ k reached hn j fits
  obtain ⟨next,hh,hnk,rr,assertion⟩ := reachedVisitWorld nodes down initialPre
    (program_source_refsOk source s.W) roots reached (by omega)
  obtain ⟨⟨hl,state⟩,context⟩ := typed l ρ next assertion
  let na := nodeAt l hl
  have eq : na.node = node := Option.some.inj (na.hP.symm.trans hn)
  obtain ⟨lab,labAt,visited⟩ := hl
  have aligned := matchStep l ⟨lab,labAt,visited⟩
  simp only [labAt,Option.bind_some] at aligned
  have nodeEq : env.nodes[l]! = na.node := by
    rw [nodeTable, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray, na.hP]
    rfl
  have context' : EnvOk G na.c.context ρ next.n next.W := na.hctx ▸ context
  have refs := node_refs (program_source_refsOk source next.W na.node (List.mem_of_getElem? na.hP)) rr
  obtain ⟨c,hc⟩ := claims l ⟨lab,labAt,visited⟩
  refine ⟨na.c,hc,?_⟩
  subst h
  subst node
  exact reachedVisit_of_checkedNode origin graded codes sums na labAt visited aligned nodeEq c (by omega)
    context' refs rr state

end Verification.SourceClaimJson.CallbackEffectInference
