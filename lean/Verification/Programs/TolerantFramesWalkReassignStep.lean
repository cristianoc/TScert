import Verification.Programs.TolerantFramesWalkReassignCall
import Verification.Programs.TolerantFramesWalkReassignSelect
import Verification.Programs.TolerantFramesStepLinkSound

/-! # Tolerant frames: a node's step at a reassignment, its searches as oracles

`checkedStep` takes the evidence of a step from the direct call or the
search `expressionEffectUsing`, then applies its checker's `select` to that
evidence and checks its tree (`checkedStep_ok`: the step's acceptance is
`StepAccepted` at the returned evidence). The searches are oracles here:
their results are not required to be equal at `reassign G η`. What carries
a node's step to `reassign G η` is that the evidence returned at `G`, once
`select` and the tree check run on it, is accepted at `reassign G η` too
(`stepAccepted_reassign`): `select` is the same result there
(`PassCheckerReassign`, proved for the ordinary checker by
`ordinarySelect_reassign` and for a qualified body by
`Parametricity.checkBodyStep_reassign` at a body subtyping of the reassigned
graph with the same check), and the tree check, the preservation test and
the step's facts are the same functions there.

`StepChecked` is a step's acceptance with its searches as oracles: the
conditions `checkedStep_ok` reads, at some evidence and some answers whose
read summaries stay checked. `stepChecked_of_step` gives it from an
accepted `checkedStep` at `G`; `stepChecked_reassign` carries it to
`reassign G η`, the answers reassigned.

Parts of the searches' results the pass uses without a check of this
module: the derivation `deriv` the search returns (the step's
`stepDeriv`, read by the footprint check behind `derivChecked`), and the
answers the searches return (the subtype cache, whose entries the pass
reads back as results, and the read summaries, kept checked by
`DirectKeepsSummaries` and `SearchKeepsSummaries` at `G`). -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Transport
variable {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι) (images : InstanceImageCheck G)

/-- A pass checker at `reassign G η` whose `select` is the same result as
`pc`'s at `G`, and which checks the step's tree where `pc` does. -/
def PassCheckerReassign (pc : PassChecker G images) (pc' : PassChecker (reassign G η) (images.reassign η)) : Prop :=
  pc'.selectChecks = pc.selectChecks ∧ ∀ j k e codes sums,
    (pc'.checker.select j k e codes sums).value = (pc.checker.select j k e codes sums).value

/-- **The ordinary checker at a reassignment** (`ordinarySelect_reassign`). -/
theorem passCheckerReassign_ordinary : PassCheckerReassign G η images .ordinary .ordinary :=
  ⟨rfl, fun j k e codes sums => by
    simp only [PassChecker.checker]
    rw [ordinarySelect_reassign]⟩

/-- **A qualified body's checker at a reassignment**: at a body subtyping
of the reassigned graph with the same check (`Parametricity.checkBodyStep_reassign`;
a qualified checker's `select` is its `run`). -/
theorem passCheckerReassign_qualified (body : BodySubtyping G) (body' : BodySubtyping (reassign G η))
    (same : body'.check = body.check)
    (ord : ∀ {A B p}, checkUsing G images A B p = true → body.check A B p = true) :
    PassCheckerReassign G η images (.qualified body ord)
      (.qualified body' fun h => by
        rw [same]; exact ord ((Parametricity.check_reassign G η images _ _ _).symm.trans h)) :=
  ⟨rfl, fun j k e codes sums =>
    Parametricity.checkBodyStep_reassign G η images body body' same ord
      (fun h => by rw [same]; exact ord ((Parametricity.check_reassign G η images _ _ _).symm.trans h)) j k e codes sums⟩

omit [DecidableEq ι] in
theorem kOf_reassign (c : PointClaim ι) (entry : SinglePass.State) (ms : List Nat) (whole : Bool) :
    kOf (reassign G η) c entry ms whole = kOf G c entry ms whole := rfl

theorem copiedOf_reassign (c : PointClaim ι) (entry : SinglePass.State) (t : Tm) :
    copiedOf (reassign G η) c entry t = copiedOf G c entry t := rfl

theorem passTreeCheck_reassign {pc : PassChecker G images} {pc' : PassChecker (reassign G η) (images.reassign η)}
    (hs : pc'.selectChecks = pc.selectChecks) (kE : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (e : StepEvidence ι) :
    passTreeCheck pc' kE codes sums e = passTreeCheck pc kE codes sums e := by
  unfold passTreeCheck
  rw [hs]
  split
  · rfl
  · rw [Parametricity.checkTree_reassign G η images _ codes sums, Parametricity.requiresTree_reassign]

theorem passWholeCheck_reassign (kE : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (pre : Option (ProgramCertificates.Evidence ι)) :
    passWholeCheck (reassign G η) (images.reassign η) kE codes sums pre = passWholeCheck G images kE codes sums pre := by
  cases pre with
  | none => rfl
  | some p => simp only [passWholeCheck, Parametricity.requiresTree_reassign]

theorem passPreserving_reassign (j : Sequent ι) (kE : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    passPreserving (reassign G η) (images.reassign η) j kE e codes sums = passPreserving G images j kE e codes sums := by
  simp only [passPreserving, callKeepsHeap, Parametricity.elementsCall_reassign, Parametricity.requiresCall_reassign,
    Parametricity.freshCall_reassign, Parametricity.ownCall_reassign, Parametricity.keepsCall_reassign]

/-- **The evidence a search returned at `G`, re-checked, is accepted at
`reassign G η`**: where the pass accepts the step at `G` at the evidence
`effect` (`StepAccepted`: the selected output, the tree check, the result,
the store after the step), it accepts it at `reassign G η` with a checker
whose `select` is the same result there. -/
theorem stepAccepted_reassign {pc : PassChecker G images} {pc' : PassChecker (reassign G η) (images.reassign η)}
    (hpc : PassCheckerReassign G η images pc pc') {codes : CodeEntry ι → Bool} {c : PointClaim ι} {node : Node}
    {entry : SinglePass.State} {ms : List Nat} {fresh : Nat} {effect : StepEvidence ι}
    {sums₀ sums : List (ReadSummary ι)} {st : Stepped ι}
    (h : StepAccepted G images pc codes c node entry ms fresh effect sums₀ sums st) :
    StepAccepted (reassign G η) (images.reassign η) pc' codes c node entry ms fresh effect sums₀ sums st := by
  obtain ⟨out, pre, hsel, htree, hres, hfr, hcp, hef, hpres, hwrit⟩ := h
  refine ⟨out, pre, ?_, ?_, hres, hfr, hcp, hef, ?_, ?_⟩
  · rw [hpc.2, kOf_reassign]; exact hsel
  · rw [passTreeCheck_reassign G η images hpc.1, kOf_reassign]; exact htree
  · intro hp
    rw [passPreserving_reassign, kOf_reassign] at hp
    exact hpres hp
  · intro hp
    rw [passPreserving_reassign, kOf_reassign] at hp
    obtain ⟨out', hwc, hsel', hrest⟩ := hwrit hp
    refine ⟨out', ?_, ?_, hrest⟩
    · rw [passWholeCheck_reassign, kOf_reassign]; exact hwc
    · rw [hpc.2, kOf_reassign]; exact hsel'

end Transport

section Oracle
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **A step accepted with its searches as oracles**: a copy of a slot at
the claim's type, the store unchanged; or `StepAccepted` at some evidence
`effect`, the call layers reading the summaries of some answers `a0` and the
selection those of the final answers `ans`, where the summaries of `a0` and
`ans` are checked when the entry's are. The conditions `checkedStep_ok`
reads, without the searches' results. -/
def StepChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (pc : PassChecker G images)
    (codes : CodeEntry ι → Bool) (c : PointClaim ι) (node : Node) (entry : SinglePass.State) (ms : List Nat)
    (fresh : Nat) (answers ans : Answered G) (st : Stepped ι) : Prop :=
  (∃ x, copiedOf G c entry node.expression = some x ∧ st.result = x ∧ st.store = entry.store ∧
      st.fresh = fresh ∧ st.copied = true ∧ st.stepK = {} ∧ st.stepOut = {} ∧ ans = answers) ∨
    (copiedOf G c entry node.expression = none ∧ ∃ (effect : StepEvidence ι) (a0 : Answered G),
      StepAccepted G images pc codes c node entry ms fresh effect a0.summaries.toList ans.summaries.toList st ∧
      (SummariesSound G images answers.summaries.toList →
        SummariesSound G images a0.summaries.toList ∧ SummariesSound G images ans.summaries.toList))

/-- **An accepted step is accepted with its searches as oracles**, where
the direct call and the search keep the summary table checked. -/
theorem stepChecked_of_step {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool}
    {aliases : List (ι × ι)} {pc : PassChecker G images} {undefTy : Option (Ty ι)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {ms : List Nat} {fresh : Nat}
    {answers : Answered G} {st : Stepped ι} {stats : StepStats} {ans : Answered G}
    (h : checkedStep G images pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh
      answers = (Except.ok st, stats, ans))
    (hdir : DirectKeepsSummaries G images undefTy)
    (hsrch : SearchKeepsSummaries G images pool fuel suggestions index codes aliases pc.checker) :
    StepChecked G images pc codes c node entry ms fresh answers ans st := by
  rcases checkedStep_ok h with hcopy | ⟨hc, effect, a0, a1, ha0, ha1, hacc, hans⟩
  · exact .inl hcopy
  · subst hans
    refine .inr ⟨hc, effect, a0, hacc, fun hsum => ?_⟩
    have hs0 : SummariesSound G images a0.summaries.toList := by
      rcases ha0 with rfl | ⟨adm, rfl⟩
      · exact hsum
      · exact hdir _ _ _ _ _ hsum
    refine ⟨hs0, ?_⟩
    rcases ha1 with rfl | ⟨k, own, adm, rfl⟩
    · exact hs0
    · exact hsrch _ _ _ _ _ hs0

omit [Instantiates ι] in
/-- **A step at a reassignment, its searches as oracles**: a step accepted
at `G` from answers whose summaries are checked is accepted at
`reassign G η` with a checker whose `select` is the same result there, the
answers reassigned; the evidence is the one the searches returned at `G`,
re-checked at `reassign G η`, so no invariance of the searches is used. -/
theorem stepChecked_reassign {G : NormalGraph ι} {η : MixedAssignment ι} {images : InstanceImageCheck G}
    {pc : PassChecker G images} {pc' : PassChecker (reassign G η) (images.reassign η)}
    (hpc : PassCheckerReassign G η images pc pc') {codes : CodeEntry ι → Bool} {c : PointClaim ι} {node : Node}
    {entry : SinglePass.State} {ms : List Nat} {fresh : Nat} {answers ans : Answered G} {st : Stepped ι}
    (h : StepChecked G images pc codes c node entry ms fresh answers ans st)
    (hsum : SummariesSound G images answers.summaries.toList) :
    StepChecked (reassign G η) (images.reassign η) pc' codes c node entry ms fresh (Answered.reassign answers η)
      (Answered.reassign ans η) st := by
  rcases h with ⟨x, hc, hr, hs, hf, hcp, hk, ho, rfl⟩ | ⟨hc, effect, a0, hacc, hss⟩
  · exact .inl ⟨x, hc, hr, hs, hf, hcp, hk, ho, rfl⟩
  · obtain ⟨hs0, hs1⟩ := hss hsum
    exact .inr ⟨hc, effect, Answered.reassign a0 η, stepAccepted_reassign G η images hpc hacc, fun _ =>
      ⟨Parametricity.summariesSound_reassign G η images hs0, Parametricity.summariesSound_reassign G η images hs1⟩⟩

end Oracle

end Verification.TolerantFrames
