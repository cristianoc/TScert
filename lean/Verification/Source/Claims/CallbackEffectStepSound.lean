import Verification.Source.Claims.CallbackEffectInference
import Verification.Programs.TolerantFramesFootprint
/-! The exact frame recorded for a step of a checked closure, at each exit.
The ordinary safety derivation and entry knowledge are the ones for this
visit. The argument-path facts relate the node to the closure entry. -/
namespace Verification.SourceClaimJson.CallbackEffectInference
open ControlFlow CertificateProducer GraphCode Footprints ProgramTyping PositiveGraphs PositiveRules
open CallEffects HeapObservations ExpressionEffects ProgramCertificates PositiveCertificates RequestJson

def StepExtends (result : Option Footprint) (prior : Footprint) (entry : Env) (initial before after : Heap) : Prop :=
  ∃ writes, result = some writes ∧ Footprints.Post (prior ++ writes).eraseDups entry initial after ∧
    Footprints.KeepsAt writes entry initial before after

private theorem prior_only {prior : Footprint} {entry : Env} {initial before : Heap}
    (history : Footprints.Post prior entry initial before) :
    Footprints.Post (prior ++ []).eraseDups entry initial before :=
  history.mono (cl := fun _ _ => none) (Footprint.le_of_subset fun _ h =>
    List.mem_eraseDups.mpr (List.mem_append_left _ h)) (by intro _ _ _ _ h; contradiction)

private theorem fieldWrite_step_extends {ι : Type} [DecidableEq ι] {G : NormalGraph ι}
    {node : Node} {pt : PointClaim ι} {facts : List ArgumentPathTracking.Fact} {q : SinglePass.StepCertificate}
    {prior : Footprint} {entry ρ : Env} {initial before after : Heap} {n k : Nat} {W : WorldT n} {t : Tm}
    {i : Nat} {key : PropKey} (exit : Completion)
    (scope : q.scope = true) (write : fieldWriteStep G pt.context node.expression = some (i,key))
    (env : EnvOk G pt.context ρ n W) (heap : HeapOk n W before)
    (safe : Safe (excOf G) (meaning G pt.type) n W before (instantiate 0 ρ node.expression))
    (history : Footprints.Post prior entry initial before)
    (factsOK : ArgumentPathTracking.Holds facts ρ entry initial)
    (budget : k < n) (run : Steps k before (instantiate 0 ρ node.expression) after t)
    (ends : match exit with | .normal => isVal t = true | .exceptional => ∃ v, Raises t v) :
    StepExtends ((step G node pt facts q).get exit) prior entry initial before after := by
  have actual := fieldWriteStep_sound write env heap safe
  cases exit with
  | normal =>
    have localPost := (returnsPost_of_safePost actual.post k after t budget run ends).1
    have ne : emptyType G pt.type = false := by
      cases hb : emptyType G pt.type with
      | false => rfl
      | true =>
        have no := noReturn_sound (R := fun _ _ => False) hb safe
        exact (returnsPost_of_safePost no k after t budget run ends).elim
    refine ⟨_, ?_, rebaseStep_post (slots := some) history localPost factsOK (by intro a b h; cases h; rfl) (Footprints.HeapOk.categories heap),
      rebaseStep_keeps (slots := some) localPost factsOK (by intro a b h; cases h; rfl) (Footprints.HeapOk.categories heap)⟩
    simp [step,scope,write,ne,Exits.get]
  | exceptional =>
    obtain ⟨v,raised⟩ := ends
    have same := raisesPost_of_safePostExc actual k after t v budget run raised
    subst after
    exact ⟨[], by simp [step,scope,write,Exits.get], prior_only history, Footprints.KeepsAt.same _ _ _ _⟩


private theorem selected_step_extends {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]
    {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {pt : PointClaim ι} {node : Node} {K : HeapKnowledge.Knowledge}
    {fresh : List Nat} {d : ProgramCertificates.Evidence ι} {eff : Effect} {facts : List ArgumentPathTracking.Fact}
    {prior : Footprint} {entry ρ : Env} {initial before after : Heap} {n k : Nat} {W : WorldT n} {t : Tm}
    {ε : HeapKnowledge.EntryState} (exit : Completion)
    (scope : checkScope pt.context.length node.expression = true)
    (nonwrite : fieldWriteStep G pt.context node.expression = none)
    (inspection : ExpressionEffects.check G pt.context node.expression = false)
    (inhabited : pt.context.any (emptyType G) = false)
    (live : exit = .normal → emptyType G pt.type = false)
    (grades : writeGrades G pt.context node.expression ++ initWriteGrades G pt.context K node.expression = [])
    (operands : selectedOperands d = true) (selected : selectedEffect d = some eff)
    (deriv : SinglePass.stepDerivChecked G images codes sums pt node K d = true)
    (codesOK : CodesSound G codes) (sumsOK : SummariesSound G images sums)
    (env : EnvOk G pt.context ρ n W) (know : HeapKnowledge.Holds K ε ρ before)
    (adm : WorldAdm W) (heap : HeapOk n W before) (refs : RefsOk W (instantiate 0 ρ node.expression))
    (history : Footprints.Post prior entry initial before)
    (factsOK : ArgumentPathTracking.Holds facts ρ entry initial)
    (budget : k < n) (run : Steps k before (instantiate 0 ρ node.expression) after t)
    (ends : match exit with | .normal => isVal t = true | .exceptional => ∃ v, Raises t v) :
    StepExtends ((step G node pt facts (SinglePass.stepCertificate G images codes sums fresh pt node K d)).get exit)
      prior entry initial before after := by
  have dc := deriv
  simp only [SinglePass.stepDerivChecked, Bool.and_eq_true, beq_iff_eq] at dc
  obtain ⟨⟨hterm,hctx⟩,tree⟩ := dc
  have env' := PromiseCalls.envOk_intRefines hctx env know.2.2.2.2.2
  have safe : SafePostExc (excOf G) (meaning G (claim d).type)
    (eff.callPost (receiverOf (instantiate 0 ρ node.expression)) (actualsOf (instantiate 0 ρ node.expression)) before)
    (eff.callExc (receiverOf (instantiate 0 ρ node.expression)) (actualsOf (instantiate 0 ρ node.expression)) before)
    n W before (instantiate 0 ρ node.expression) := by
    rw [← hterm] at refs ⊢
    rcases Bool.or_eq_true_iff.mp tree with checked | required
    · exact selected_sound_exc d checked operands selected codesOK sumsOK env' adm heap refs
    · obtain ⟨e,he,hs⟩ := PromiseCalls.requiresTree_sound_exc codesOK sumsOK d required
      rw [selected] at he
      cases he
      exact hs env' know adm heap refs
  let arity := (actualsOf (claim d).term).length
  have localPost : Footprints.Post ((eff.summary arity).get exit).frame
      (callEnv (receiverOf (instantiate 0 ρ node.expression)) (actualsOf (instantiate 0 ρ node.expression))) before after := by
    cases exit with
    | normal => exact Effect.callPost_within (returnsPost_of_safePost safe.post k after t budget run ends)
    | exceptional =>
      obtain ⟨v,hr⟩ := ends
      exact Effect.callExc_frame _ (raisesPost_of_safePostExc safe k after t v budget run hr)
  have rebased := rebaseStep_post history localPost factsOK
    (slots := PromiseCalls.actualSlot node.expression) (fun _ _ ha => PromiseCalls.actualSlot_sound ha ρ)
    (Footprints.HeapOk.categories heap)
  have keeps := rebaseStep_keeps (entry := entry) (initial := initial) localPost factsOK
    (slots := PromiseCalls.actualSlot node.expression) (fun _ _ ha => PromiseCalls.actualSlot_sound ha ρ)
    (Footprints.HeapOk.categories heap)
  refine ⟨_, ?_, rebased, keeps⟩
  cases exit <;> try specialize live rfl
  all_goals simp [step,SinglePass.stepCertificate,SinglePass.selectedSummaries,scope,nonwrite,inspection,
    inhabited,live,grades,operands,selected,deriv,arity,Exits.get,Thunk.get]


private theorem stepsLength {k before u after t} (run : Steps k before u after t) : before.length ≤ after.length := by
  induction run with
  | refl => exact Nat.le_refl _
  | next st _ ih => exact Nat.le_trans (step_length_le st) ih

private theorem both_post {Ξ T : Fam} {n : Nat} {W : WorldT n} {before after : Heap} {u t : Tm}
    {k : Nat} {R : Heap → Prop}
    (both : SafePostExc Ξ T (fun h _ => R h) R n W before u)
    (budget : k < n) (run : Steps k before u after t) (exit : Completion)
    (ends : match exit with | .normal => isVal t = true | .exceptional => ∃ v, Raises t v) : R after := by
  cases exit with
  | normal => exact returnsPost_of_safePost both.post k after t budget run ends
  | exceptional =>
    obtain ⟨v,hr⟩ := ends
    exact raisesPost_of_safePostExc both k after t v budget run hr

private theorem general_frame {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {node : Node}
    {pt : PointClaim ι} {facts : List ArgumentPathTracking.Fact} {q : SinglePass.StepCertificate}
    {prior frame : Footprint} {entry ρ : Env} {initial before after : Heap} (exit : Completion)
    (scope : q.scope = true) (nonwrite : fieldWriteStep G pt.context node.expression = none)
    (live : exit = .normal → emptyType G pt.type = false)
    (headFrame : ((((⟨q.normal,q.exceptional⟩ : Exits _).get exit).head?).map (·.frame)).getD Closed.top.fp = frame)
    (localPost : Footprints.Post frame
      (callEnv (receiverOf (instantiate 0 ρ node.expression)) (actualsOf (instantiate 0 ρ node.expression))) before after)
    (history : Footprints.Post prior entry initial before) (cats : HeapCategories before)
    (factsOK : ArgumentPathTracking.Holds facts ρ entry initial) :
    StepExtends ((step G node pt facts q).get exit) prior entry initial before after := by
  have rebased := rebaseStep_post history localPost factsOK
    (slots := PromiseCalls.actualSlot node.expression) (fun _ _ ha => PromiseCalls.actualSlot_sound ha ρ) cats
  have keeps := rebaseStep_keeps (entry := entry) (initial := initial) localPost factsOK
    (slots := PromiseCalls.actualSlot node.expression) (fun _ _ ha => PromiseCalls.actualSlot_sound ha ρ) cats
  refine ⟨_, ?_, rebased, keeps⟩
  cases exit <;> simp only [Exits.get] at headFrame <;> try specialize live rfl
  all_goals simp [step,scope,nonwrite,live,headFrame,Exits.get]

/-- The executable closure-step summary extends the known prefix on either
exit of every concrete expression evaluation below its safety budget. -/
theorem stepCertificate_extends {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]
    {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {pt : PointClaim ι} {node : Node} {K : HeapKnowledge.Knowledge}
    {fresh : List Nat} {d : ProgramCertificates.Evidence ι} {facts : List ArgumentPathTracking.Fact}
    {prior : Footprint} {entry ρ : Env} {initial before after : Heap} {n k : Nat} {W : WorldT n} {t : Tm}
    {ε : HeapKnowledge.EntryState} (exit : Completion)
    (codesOK : CodesSound G codes) (sumsOK : SummariesSound G images sums)
    (env : EnvOk G pt.context ρ n W) (know : HeapKnowledge.Holds K ε ρ before)
    (adm : WorldAdm W) (heap : HeapOk n W before)
    (safe : Safe (excOf G) (meaning G pt.type) n W before (instantiate 0 ρ node.expression))
    (history : Footprints.Post prior entry initial before) (factsOK : ArgumentPathTracking.Holds facts ρ entry initial)
    (budget : k < n) (run : Steps k before (instantiate 0 ρ node.expression) after t)
    (ends : match exit with | .normal => isVal t = true | .exceptional => ∃ v, Raises t v) :
    StepExtends ((step G node pt facts (SinglePass.stepCertificate G images codes sums fresh pt node K d)).get exit)
      prior entry initial before after := by
  let q := SinglePass.stepCertificate G images codes sums fresh pt node K d
  change StepExtends ((step G node pt facts q).get exit) prior entry initial before after
  have topPost (ρ : Env) : Footprints.Post Closed.top.fp ρ before after :=
    Closed.post_iff.mpr (Closed.holds_iff.mp (Closed.holds_top.mpr (stepsLength run)))
  cases hscope : q.scope with
  | false =>
    have full : Footprints.Post Closed.top.fp entry initial after :=
      Closed.post_iff.mpr (Closed.holds_iff.mp (Closed.holds_top.mpr (Nat.le_trans history.1 (stepsLength run))))
    exact ⟨Closed.top.fp, by cases exit <;> simp [step,hscope,Exits.get], full.mono (cl := fun _ _ => none)
      (Footprint.le_of_subset fun _ he => List.mem_eraseDups.mpr (List.mem_append_right _ he))
      (by intro _ _ _ _ miss; contradiction), Footprints.KeepsAt.closed (Footprints.HeapOk.categories heap) (topPost entry)⟩
  | true =>
    cases hw : fieldWriteStep G pt.context node.expression with
    | some p =>
      obtain ⟨i,key⟩ := p
      exact fieldWrite_step_extends exit hscope hw env heap safe history factsOK budget run ends
    | none =>
      have live : exit = .normal → emptyType G pt.type = false := by
        rintro rfl
        cases hb : emptyType G pt.type with
        | false => rfl
        | true => exact (returnsPost_of_safePost
            (noReturn_sound (R := fun _ _ => False) hb safe) k after t budget run ends).elim
      have inhabited : pt.context.any (emptyType G) = false := by
        cases hc : pt.context.any (emptyType G) with
        | false => rfl
        | true =>
          obtain ⟨A,hm,ha⟩ := List.any_eq_true.mp hc
          obtain ⟨i,hi⟩ := List.getElem?_of_mem hm
          exact (emptyType_sound ha (env.2 i A hi)).elim
      cases inspection : ExpressionEffects.check G pt.context node.expression with
      | true =>
        have inspected := sound_exc inspection hscope env adm heap safe
        have hp := both_post inspected budget run exit ends
        apply general_frame (frame := []) exit hscope hw live _
          (Footprints.Post.empty_iff.mpr (Closed.holds_empty.mp hp)) history (Footprints.HeapOk.categories heap) factsOK
        cases exit <;> simp [q,SinglePass.stepCertificate,inspection,Exits.get]
      | false =>
        cases grades : writeGrades G pt.context node.expression ++ initWriteGrades G pt.context K node.expression with
        | cons grade more =>
          have member : grade ∈ writeGrades G pt.context node.expression ++ initWriteGrades G pt.context K node.expression := by
            rw [grades]; simp
          have checked : TolerantFrames.passWrites G pt.context K grade node.expression = true := by
            simp only [TolerantFrames.passWrites,writeWithin_eq_grades,initWriteWithin_eq_grades,← List.any_append]
            exact List.any_eq_true.mpr ⟨grade,member,Closed.le_refl grade⟩
          have hp := both_post (TolerantFrames.passWrites_sound checked env heap know safe) budget run exit ends
          apply general_frame (frame := grade.fp) exit hscope hw live _
            (Closed.post_iff.mpr (Closed.holds_iff.mp hp)) history (Footprints.HeapOk.categories heap) factsOK
          cases exit <;> try specialize live rfl
          all_goals simp [q,SinglePass.stepCertificate,inspection,inhabited,live,grades,Exits.get]
        | nil =>
          by_cases sel : selectedOperands d = true ∧
              (selectedEffect d).isSome = true ∧ SinglePass.stepDerivChecked G images codes sums pt node K d = true
          · obtain ⟨ops,he,deriv⟩ := sel
            obtain ⟨eff,selected⟩ := Option.isSome_iff_exists.mp he
            exact selected_step_extends exit hscope hw inspection inhabited live grades ops selected deriv
              codesOK sumsOK env know adm heap safe.refs history factsOK budget run (by cases exit <;> exact ends)
          · apply general_frame (frame := Closed.top.fp) exit hscope hw live _ (topPost _)
              history (Footprints.HeapOk.categories heap) factsOK
            cases exit <;> try specialize live rfl
            all_goals
              cases ops : selectedOperands d <;> cases he : selectedEffect d <;>
                cases hd : SinglePass.stepDerivChecked G images codes sums pt node K d <;>
                first
                | solve | simp [q,SinglePass.stepCertificate,SinglePass.selectedSummaries,Thunk.get,Exits.get,
                    ops,he,hd,grades,inhabited,inspection,live]
                | exact (sel ⟨ops, by simp [he], hd⟩).elim

end Verification.SourceClaimJson.CallbackEffectInference
