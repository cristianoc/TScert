import Verification.Programs.TolerantFramesExitChecks
import Verification.Programs.TolerantFramesDriverExits

/-! # Checks exposed by a successful exit type computation -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Checks
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- The yields an exit reads are cached or checked at the step's final answers. -/
@[nospecialize] def ExitYieldSource (env : WalkEnv ι G I) (l : Nat) (en : Entered ι) (sd : StepDone ι G)
    (cached : Option (List (PromiseCalls.Yield ι))) (ys : List (PromiseCalls.Yield ι)) : Prop :=
  ys = cached.getD [] ∨ ∃ raw, ys = checkYsAt G I env.codes sd.answers env.claimed[l]! env.nodes[l]! sd.st
    (slotImplOf en.entry.names en.implies) raw

/-- The initial exits' yields have a checked source. -/
theorem exitsYields_source (env : WalkEnv ι G I) (l : Nat) (en : Entered ι) (sd : StepDone ι G) :
    ExitYieldSource env l en sd sd.yields ((exitsYields G I env l en sd).1.getD []) := by
  unfold exitsYields
  dsimp only
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

/-- A successful type check exposes evidence at an exit context and the
checked source of any yields its refinement reads. -/
theorem exitTypes_checked {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {outAll : Thunk HeapKnowledge.Knowledge} {t : Target} {tc : PointClaim ι}
    {Γ : List (Ty ι)} {names : List Nat} {edgeStore : Store} {pushed isHandler : Bool}
    {observed : Option BranchRefinement.Observation} {first : Bool} {acc acc' : ExitsDone ι G}
    {et : SinglePass.ExitTyped ι}
    (h : exitTypes G I env l en sd outAll t tc Γ names edgeStore pushed isHandler observed first
      (differing Γ tc.context t.mapping) acc = .ok (acc', et)) :
    ∃ ys, ExitYieldSource env l en sd acc.yields ys ∧ ys = acc'.yields.getD [] ∧
      ExitTyped G I Γ tc.context t observed
        (KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G Γ)
          (materialize { names, store := edgeStore }
            (if pushed then (env.claimed[l]!).context.length + 1 else (env.claimed[l]!).context.length)
            (0 :: (differing Γ tc.context t.mapping).map (·.2)) false).1)
        (refinedContext G env.claimed[l]! (env.nodes[l]!).continuation (yieldsAtSlots en.entry.names ys)
          outAll.get first) outAll.get := by
  unfold exitTypes at h
  extract_lets node c width entry at h
  split at h
  rename_i ok a hd
  split at h
  · rename_i hok
    cases h
    refine ⟨acc.yields.getD [], .inl rfl, rfl, .inl (subtypesPass_of (observed := observed) (answers := acc.answers) ?_)⟩
    exact (congrArg Prod.fst hd).trans hok
  · split at h
    rename_i k pairs lookup hk
    extract_lets ko at h
    split at h
    rename_i found a1 hf
    extract_lets answers at h
    split at h
    · cases h
    · split at h
      · rename_i hfound
        cases h
        refine ⟨acc.yields.getD [], .inl rfl, rfl, .inr (.inl ?_)⟩
        have hf' : (checkedEdge G I env.claimed tc.context Γ t observed ko a).1 = true :=
          (congrArg Prod.fst hf).trans hfound
        have hh := edgeFound_of_checked hf'
        dsimp only [ko] at hh
        have hko := congrArg (KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G Γ)) (congrArg Prod.fst hk)
        change EdgeFound G I tc.context Γ t observed _
        rw [hko]
        exact hh
      · split at h
        rename_i ys a2 hys
        have hsrc : ExitYieldSource env l en sd acc.yields ys := by
          cases hcache : acc.yields with
          | some xs =>
            simp only [hcache] at hys
            exact .inl ((congrArg Prod.fst hys).symm)
          | none =>
            simp only [hcache] at hys
            split at hys
            rename_i raw ar hraw
            exact .inr ⟨raw, (congrArg Prod.fst hys).symm⟩
        extract_lets Γr at h
        split at h
        rename_i foundR a3 hr
        extract_lets answersR at h
        split at h
        rename_i foundM a4 typ hmixed
        split at h
        · cases h
        · rename_i hfinal
          have htrue : foundM = true := by
            cases foundM with
            | false => exact (hfinal rfl).elim
            | true => rfl
          cases h
          refine ⟨ys, hsrc, rfl, .inr (.inr ?_)⟩
          by_cases hfr : foundR = true
          · exact .inl (edgeFound_of_checked ((congrArg Prod.fst hr).trans hfr))
          · rw [if_neg hfr] at hmixed
            split at hmixed
            rename_i Γm am hmix
            split at hmixed
            · split at hmixed
              rename_i fm am2 hm
              have hfm : fm = true := (congrArg Prod.fst hmixed).trans htrue
              refine .inr ⟨Γm, ?_, edgeFound_of_checked ((congrArg Prod.fst hm).trans hfm)⟩
              have hh := mixedOf_mixedContext G I Γ Γr tc.context t.mapping answersR
              rw [hmix] at hh
              exact hh
            · exact (hfr ((congrArg Prod.fst hmixed).trans htrue)).elim

/-- Every list `checkYsAt` returns is judged from the entry implications
and the sound summary table it reads. -/
theorem checkYsAt_judged (env : WalkEnv ι G I) (l : Nat) (en : Entered ι) (sd : StepDone ι G)
    (raw : List (PromiseCalls.Yield ι)) (start : List Nat) (ρ0 : Env) (m : Nat)
    (hcodes : CodesSound G env.codes) (hsums : SummariesSound G I sd.answers.summaries.toList) :
    YieldsJudged G (env.claimed[l]!).type (env.claimed[l]!).context (env.nodes[l]!).expression
      en.entry en.implies start ρ0 m sd.st.stepK
      (checkYsAt G I env.codes sd.answers env.claimed[l]! env.nodes[l]! sd.st
        (slotImplOf en.entry.names en.implies) raw) :=
  yieldsJudged_of_checked (fun _ _ hS => slotImplOf_entry (fun _ h => h) hS) hcodes hsums

/-- The computed exit yields are judged whenever the cached ones are. -/
theorem ExitYieldSource.judged {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {cached : Option (List (PromiseCalls.Yield ι))} {ys : List (PromiseCalls.Yield ι)}
    (h : ExitYieldSource env l en sd cached ys) (start : List Nat) (ρ0 : Env) (m : Nat)
    (hcodes : CodesSound G env.codes) (hsums : SummariesSound G I sd.answers.summaries.toList)
    (hcache : YieldsJudged G (env.claimed[l]!).type (env.claimed[l]!).context (env.nodes[l]!).expression
      en.entry en.implies start ρ0 m sd.st.stepK (cached.getD [])) :
    YieldsJudged G (env.claimed[l]!).type (env.claimed[l]!).context (env.nodes[l]!).expression
      en.entry en.implies start ρ0 m sd.st.stepK ys := by
  rcases h with rfl | ⟨raw, rfl⟩
  · exact hcache
  · exact checkYsAt_judged env l en sd raw start ρ0 m hcodes hsums

/-- A successful assertion check entails the target's written facts at
the context and edge facts the pass reads. -/
theorem assertionExit_checked {env : WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γe : Thunk (List (Ty ι))} {names : List Nat} {edgeStore : Store} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {acc acc' : ExitsDone ι G}
    (h : assertionExit G env l t tc Γe names edgeStore pushed observed false acc = .ok acc')
    {req : HeapKnowledge.Knowledge} (hr : env.stated[t.label]! = some req) :
    KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context)
      (assertionSource G Γe.get req
        (materialize { names, store := edgeStore }
          (if pushed then (env.claimed[l]!).context.length + 1 else (env.claimed[l]!).context.length)
          (((atomsOf req).flatMap Atom.names).map (PointClaims.slot t.mapping)) false).1 t.mapping observed)
      req t.mapping = true := by
  unfold assertionExit at h
  rw [hr] at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals simp_all (config := { zetaDelta := true }) [assertionSource]

end Checks
end Verification.TolerantFrames
