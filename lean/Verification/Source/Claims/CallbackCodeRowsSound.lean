import Verification.Source.Claims.CallbackAcceptedWalk
import Verification.Source.Claims.PassUnitCodes

namespace Verification.SourceClaimJson.CallbackEffectInference
open ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore
open PositiveCertificates CertificateProducer ProgramCertificates TolerantFrames CallEffects Footprints

variable {τ ι : Type} [Labels ι] [StoreView τ ι]

private def closureCall (r : SourceRequest τ ι) (fuel : Nat) (known : List (ProgramCertificates.Evidence ι))
    (accepted : List (CodeEntry ι)) (answers : Answered (RequestJson.graph r.toRequest)) (q : CodeRequest ι) (code : Nat) :
    TolerantFrames.Target.RunCall (RequestJson.graph r.toRequest) (StoreView.images r.types) :=
  let rq := q.asRequest r.toRequest
  let hints := (r.codeHints[code]?).getD {}
  { pool := vocabulary (RequestJson.graph r.toRequest) r.searchLabels rq.claims rq.inputs, fuel, P := rq.program, claims := rq.claims,
    start := rq.start, inputs := rq.inputs, goal := q.entry.goal, assertions := hints.requirements,
    cuts := hints.cuts, candidates := hints.candidates, entryIndices := rq.entryIndices, suggestions := [],
    known, codes := GraphCode.admits accepted, aliases := r.aliases, passChecker := .ordinary, answers,
    reference := #[], debugNode := 1000000000, bound := codeBound q.entry, givenImplies := #[], givenArgs := #[],
    «ensures» := [], givenInputs := #[], entrySeparation := {}, observe := none, tracing := false,
    observeEntry := false, regional := none }

private def gradedResult {G : NormalGraph ι} {I : InstanceImageCheck G} (c : TolerantFrames.Target.RunCall G I) :=
  SinglePass.run G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions c.cuts c.candidates
    c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers c.reference c.debugNode
    c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation c.observe c.tracing
    c.observeEntry c.regional true

private theorem gradedAccepted {G : NormalGraph ι} {I : InstanceImageCheck G} {c : TolerantFrames.Target.RunCall G I}
    {counts next trace} (plain : c.framed = []) (passed : gradedResult c = (.accepted,counts,next,trace)) :
    c.Accepts next ∧ ∃ σ reach, gradedWalk c = .ok (σ,reach) ∧ counts.grades = σ.walk.visits := by
  unfold gradedResult SinglePass.run at passed
  rw [← gradedWalk] at passed
  cases walk : gradedWalk c with
  | error stop =>
    simp only [walk,Prod.mk.injEq] at passed
    exact (stop.outcome.outcome_ne_accepted passed.1).elim
  | ok p =>
    obtain ⟨σ,reach⟩ := p
    simp only [walk,Prod.mk.injEq] at passed
    obtain ⟨out,rfl,rfl,rfl⟩ := passed
    obtain ⟨_,_,_,_,_,_,ordinary⟩ := gradedWalk_origin plain walk
    refine ⟨⟨⟨{σ.unrecorded.counts with reached := reach, grades := σ.unrecorded.walk.visits},σ.trace,?_⟩,plain⟩,σ,reach,rfl,rfl⟩
    unfold TolerantFrames.Target.RunCall.result SinglePass.run
    unfold RunCall.walk at ordinary
    rw [ordinary]

    dsimp only
    rw [show σ.unrecorded.walk.outcome reach = σ.walk.outcome reach from rfl,out]
    rfl

/-- A computed closure row bounds executions from frames meeting its own
signature. The bound and the actual postcondition select the same exit. -/
def RowSound (G : NormalGraph ι) (row : CheckedCode ι) : Prop :=
  ∀ (s : IndexedHeap) (entry : Env), EnvOk G (codeFrame row.entry.arity row.entry.row row.entry.captures row.entry.spine)
    entry s.n s.W → RootsOk s.W entry →
    HeapKnowledge.IndexHolds ⟨entry,s.h⟩ (GraphCode.codeEntryIndices row.entry) entry s.h →
    ∀ {steps after state}, steps ≤ s.n →
      Execution (GraphCode.program row.entry.exprs row.entry.conts) steps s.h (.at row.entry.start entry) after state →
      ∀ exit : Completion, ∀ v : Val, state = (match exit with | .normal => .done v | .exceptional => .raised v) →
      ∃ bound, row.summary.get exit = some bound ∧ Footprints.Post bound entry s.h after

private def CheckedRow (G : NormalGraph ι) (row : CheckedCode ι) : Prop :=
  RowSound G row ∧ ∀ η, row.entry.Spec (reassign G η)

private theorem prefixLength {P k h s h' s'} (r : Execution P k h s h' s') : h.length ≤ h'.length := by
  induction r with
  | refl => exact Nat.le_refl _
  | next tr _ ih =>
    apply Nat.le_trans _ ih
    cases tr <;> first | exact Nat.le_refl _ | exact step_length_le (by assumption)

private theorem oneRow {r : SourceRequest τ ι} {fuel known accepted answers q code counts next trace summary}
    (cond : codeConditions q.entry = true)
    (passed : gradedResult (closureCall r fuel known accepted answers q code) = (.accepted,counts,next,trace))
    (hsums : SummariesSound (RequestJson.graph r.toRequest) (StoreView.images r.types) next.summaries.toList)
    (codes : CodesSound (RequestJson.graph r.toRequest) (GraphCode.admits accepted))
    (inferred : if q.async then summary = ⟨some Closed.top.fp,some Closed.top.fp⟩ else
      inferChecked (RequestJson.graph r.toRequest) q counts.grades = .ok summary) :
    CheckedRow (RequestJson.graph r.toRequest) ⟨q.entry,summary⟩ ∧
      CodesSound (RequestJson.graph r.toRequest) (GraphCode.admits (accepted ++ [q.entry])) := by
  let c := closureCall r fuel known accepted answers q code
  obtain ⟨ha,σ,reach,hwalk,hrecords⟩ := gradedAccepted (c := c) rfl passed
  have hp : RunPremises _ _ c next (fun _ => True) :=
    ⟨ha.1,.ordinary,codes,hsums,fun _ _ _ h => by cases h⟩
  have guarantee := run_sound_single_pass _ _ c next _ ha hp.2.1 hp.2.2.1 hsums hp.2.2.2.2
  have spec := PassUnit.codeSpec_of_guarantee cond guarantee
  refine ⟨⟨?_,spec⟩,PassUnit.codesSound_snoc codes spec⟩
  · intro s entry he roots indices steps after state budget run ex v done
    cases async : q.async with
    | true =>
      simp only [async,ite_true] at inferred
      subst summary
      refine ⟨Closed.top.fp,by cases ex <;> rfl,?_⟩
      exact Closed.post_iff.mpr (Closed.holds_iff.mp (Closed.holds_top.mpr (prefixLength run)))
    | false =>
      simp only [async,Bool.false_eq_true,ite_false] at inferred
      rw [hrecords] at inferred
      exact inferChecked_execution_of_accepted hp trivial rfl hwalk rfl rfl rfl he roots
        (HeapSeparation.empty_holds _) indices budget (Nat.le_refl _) inferred run ex v done
private theorem inferCodeRows_sound (r : SourceRequest τ ι) (fuel known) :
    ∀ rest accepted table answers rows final,
    inferCodeRows r fuel known accepted table answers rest = .ok (rows,final) →
    (∀ x ∈ answers.summaries.toList, x ∈ final.summaries.toList) ∧
    SummariesSound (RequestJson.graph r.toRequest) (StoreView.images r.types) final.summaries.toList ∧
    PassUnit.CodesAccepted (RequestJson.graph r.toRequest) (StoreView.images r.types) r accepted rest answers final ∧
    (CodesSound (RequestJson.graph r.toRequest) (GraphCode.admits accepted) →
      (∀ row ∈ table, CheckedRow (RequestJson.graph r.toRequest) row) →
      ∀ row ∈ rows, CheckedRow (RequestJson.graph r.toRequest) row) := by
  intro rest
  induction rest with
  | nil =>
    intro accepted table answers rows final h
    simp only [inferCodeRows] at h
    split at h
    · rename_i hsum
      cases h
      refine ⟨fun _ h => h,?_,rfl, fun _ h => h⟩
      exact checkReadSummaries_sound (Bool.and_eq_true_iff.mp hsum).2
    · contradiction
  | cons head rest ih =>
    obtain ⟨q,code⟩ := head
    intro accepted table answers rows final h
    simp only [inferCodeRows] at h
    split at h
    · contradiction
    rename_i valid
    let c := closureCall r fuel known accepted answers q code
    generalize hr : gradedResult c = result
    obtain ⟨out,counts,next,trace⟩ := result
    have equation := hr
    dsimp only [c,gradedResult,closureCall] at equation
    rw [equation] at h
    dsimp only at h
    cases out <;> try contradiction
    have cond : codeConditions q.entry = true := by simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr valid)).1
    have hk : ∀ x ∈ answers.summaries.toList, x ∈ next.summaries.toList := by
      obtain ⟨acc,_⟩ := gradedAccepted (c := c) rfl hr
      obtain ⟨_,_,pass⟩ := acc.1
      intro x hx
      have := runKeepsSummaries _ _ c x hx
      rw [pass] at this
      exact this
    have finish (summary) (inf : if q.async then summary = ⟨some Closed.top.fp,some Closed.top.fp⟩ else
        inferChecked (RequestJson.graph r.toRequest) q counts.grades = .ok summary)
        (rec : inferCodeRows r fuel known (accepted ++ [q.entry]) (table.push ⟨q.entry,summary⟩) next rest = .ok (rows,final)) :
    (∀ x ∈ answers.summaries.toList, x ∈ final.summaries.toList) ∧
    SummariesSound (RequestJson.graph r.toRequest) (StoreView.images r.types) final.summaries.toList ∧
    PassUnit.CodesAccepted (RequestJson.graph r.toRequest) (StoreView.images r.types) r accepted ((q,code)::rest) answers final ∧
    (CodesSound (RequestJson.graph r.toRequest) (GraphCode.admits accepted) →
      (∀ row ∈ table, CheckedRow (RequestJson.graph r.toRequest) row) →
      ∀ row ∈ rows, CheckedRow (RequestJson.graph r.toRequest) row) := by
      obtain ⟨sub,finalOK,codeRuns,rowsOK⟩ := ih _ _ _ _ _ rec
      have asyncOK : asyncAdmits q.async q.entry.row.effect = true := by
        simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr valid)).2
      refine ⟨fun x hx => sub x (hk x hx),finalOK,⟨next,?_,codeRuns⟩,?_⟩
      · exact ⟨cond,asyncOK,c,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,(gradedAccepted rfl hr).1⟩
      · intro codes previous
        obtain ⟨rowOK,codes'⟩ := oneRow cond hr (fun x hx => finalOK x (sub x hx)) codes inf
        apply rowsOK codes'
        intro row hm
        rcases Array.mem_push.mp hm with member | rfl
        · exact previous row member
        · exact rowOK
    cases async : q.async with
    | true =>
      simp only [async,ite_true,pure_bind] at h
      apply finish _ _ h
      simp [async]
    | false =>
      simp only [async,Bool.false_eq_true,ite_false] at h
      cases hc : inferChecked (RequestJson.graph r.toRequest) q counts.grades with
      | error err => rw [hc] at h; contradiction
      | ok summary =>
        rw [hc] at h
        apply finish summary _ h
        simpa [async] using hc

/-- Every row produced by the actual source request loop meets both inferred
exit bounds, including rows that call closures accepted earlier in the loop. -/
private theorem inferCodes_checked {r : SourceRequest τ ι} {fuel rows known final}
    (inferred : inferCodes r fuel = .ok (rows,known,final)) :
    (∀ row ∈ rows, CheckedRow (RequestJson.graph r.toRequest) row) ∧
    ∃ initial, PassUnit.CodesAccepted (RequestJson.graph r.toRequest) (StoreView.images r.types) r [] r.codes.zipIdx initial final ∧
      SummariesSound (RequestJson.graph r.toRequest) (StoreView.images r.types) final.summaries.toList := by
  unfold inferCodes at inferred
  split at inferred
  · contradiction
  dsimp only at inferred
  split at inferred
  · rename_i result produced
    obtain ⟨first,answers⟩ := result
    simp only [pure_bind] at inferred
    generalize hc : inferCodeRows r fuel _ [] #[] _ r.codes.zipIdx = checked at inferred
    cases checked with
    | error err => contradiction
    | ok pair =>
      obtain ⟨rows',final'⟩ := pair
      cases inferred
      obtain ⟨_,hs,hr,hrows⟩ := inferCodeRows_sound _ _ _ _ _ _ _ _ _ hc
      exact ⟨hrows (by intro c claimed; simp [GraphCode.admits] at claimed) (by simp),_,hr,hs⟩
  · contradiction

theorem inferCodes_rows_sound {r : SourceRequest τ ι} {fuel rows known final}
    (inferred : inferCodes r fuel = .ok (rows,known,final)) :
    ∀ row ∈ rows, RowSound (RequestJson.graph r.toRequest) row := fun row h => ((inferCodes_checked inferred).1 row h).1

theorem inferCodes_table_sound {r : SourceRequest τ ι} {fuel rows known final}
    (inferred : inferCodes r fuel = .ok (rows,known,final)) :
    CodesSound (RequestJson.graph r.toRequest) (GraphCode.admits (rows.toList.map (·.entry))) := by
  intro code hit
  obtain ⟨row,hm,rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp hit)
  exact ((inferCodes_checked inferred).1 row (by simpa using hm)).2

/-- The same accepted code runs establish every written closure assertion. -/
theorem inferCodes_assertions {r : SourceRequest τ ι} {fuel rows known final}
    (inferred : inferCodes r fuel = .ok (rows,known,final)) : PassUnit.CodeAssertionsClause r := by
  obtain ⟨initial,checked,sums⟩ := (inferCodes_checked inferred).2
  have codes := PassUnit.codesAccepted_guarantees TolerantFrames.run_sound_single_pass
    TolerantFrames.runKeepsSummaries sums checked (fun _ h => h) (by intro e h; simp [GraphCode.admits] at h)
  intro ci q found η n W h ρ entry refs l k stated j h' ρ' budget reached
  have atCode := codes (q,ci) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  exact atCode.asserted η trivial n W h ρ entry (program_source_refsOk atCode.source W) refs l k stated j h' ρ' budget reached

end Verification.SourceClaimJson.CallbackEffectInference
