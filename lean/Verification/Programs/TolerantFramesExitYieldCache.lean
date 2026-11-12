import Verification.Programs.TolerantFramesExitTypeChecks
import Verification.Programs.TolerantFramesExitRecords

/-! # Checked yields throughout the exit fold

Every yield cache in a successful exit fold has a checked source at the
step's final answers. Each indexed exit retains that source, including
when an earlier exit populates the cache.
-/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Cache
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- Checked yield sources compose through the cache. -/
theorem ExitYieldSource.trans {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {a b : Option (List (PromiseCalls.Yield ι))} {ys : List (PromiseCalls.Yield ι)}
    (hab : ExitYieldSource env l en sd a (b.getD []))
    (hby : ExitYieldSource env l en sd b ys) : ExitYieldSource env l en sd a ys := by
  rcases hby with rfl | h
  · exact hab
  · exact .inr h

/-- Type checking either keeps the cache or fills it with checked yields. -/
theorem exitTypes_yields_source {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {out : Thunk HeapKnowledge.Knowledge} {t : Target} {tc : PointClaim ι} {Γ : List (Ty ι)}
    {names : List Nat} {store : Store} {pushed handler : Bool}
    {observed : Option BranchRefinement.Observation} {first : Bool} {diff : List (Nat × Nat)}
    {a b : ExitsDone ι G} {et : SinglePass.ExitTyped ι}
    (h : exitTypes G I env l en sd out t tc Γ names store pushed handler observed first diff a = .ok (b, et)) :
    ExitYieldSource env l en sd a.yields (b.yields.getD []) := by
  unfold exitTypes at h
  extract_lets node c width entry at h
  split at h
  split at h
  · cases h; exact .inl rfl
  · split at h
    extract_lets ko at h
    split at h
    extract_lets answers at h
    split at h
    · cases h
    · split at h
      · cases h; exact .inl rfl
      · split at h
        rename_i ys a2 hys
        have hsrc : ExitYieldSource env l en sd a.yields ys := by
          cases hcache : a.yields with
          | some xs =>
            simp only [hcache] at hys
            exact .inl ((congrArg Prod.fst hys).symm)
          | none =>
            simp only [hcache] at hys
            split at hys
            rename_i raw ar hraw
            exact .inr ⟨raw, (congrArg Prod.fst hys).symm⟩
        repeat' (first | split at h | extract_lets at h)
        all_goals cases h <;> exact hsrc

/-- A head check preserves the yield cache. -/
theorem headExit_yields {env : WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γ : List (Ty ι)} {names : List Nat} {store : Store} {pushed vacuous : Bool}
    {carried : List (PromiseCalls.Implication ι)} {a b : ExitsDone ι G}
    (h : headExit G I env l t tc Γ names store pushed vacuous carried a = .ok b) : b.yields = a.yields := by
  unfold headExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- An assertion check preserves the yield cache. -/
theorem assertionExit_yields {env : WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γe : Thunk (List (Ty ι))} {names : List Nat} {store : Store} {pushed vacuous : Bool}
    {observed : Option BranchRefinement.Observation} {a b : ExitsDone ι G}
    (h : assertionExit G env l t tc Γe names store pushed observed vacuous a = .ok b) : b.yields = a.yields := by
  unfold assertionExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- Every successful exit preserves the checked source of its cache. -/
theorem exitStep_yields_source {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    {a b : ExitsDone ι G} {e : Exit × Nat}
    (h : exitStep G I env l en sd ys out a e = .ok b) :
    ExitYieldSource env l en sd a.yields (b.yields.getD []) := by
  unfold exitStep at h
  extract_lets ex first node c width entry st t pushed observed handler pushedNames tr a0 Γ names store unsatΓ vacuous Γe read Γr at h
  split at h
  · cases h
  split at h
  · cases h
  extract_lets diff u a2 typed at h
  generalize ht : typed = T at h
  split at h
  · cases h
  rename_i a1 et
  simp only [typed] at ht
  have hp : a2.yields = a.yields := by
    dsimp only [a2, a0]
    split <;> split <;> rfl
  have hp1 : ExitYieldSource env l en sd a.yields (a1.yields.getD []) := by
    split at ht
    · cases ht; exact .inl (congrArg (fun x => x.getD []) hp)
    · rw [← hp]; exact exitTypes_yields_source ht
  extract_lets freshImpl record at h
  split at h
  · simp only [Except.map] at h
    split at h
    · cases h
    · rename_i a3 hh
      cases h
      change ExitYieldSource env l en sd a.yields (a3.yields.getD [])
      rw [headExit_yields hh]
      exact hp1
  · split at h
    · cases h
    rename_i a3 ha
    split at h
    cases h
    change ExitYieldSource env l en sd a.yields (a3.yields.getD [])
    rw [assertionExit_yields ha]
    exact hp1

/-- The final cache of a successful fold has a source in its initial cache. -/
theorem exitsFold_yields_source {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (Exit × Nat)) (a b : ExitsDone ι G),
      es.foldlM (exitStep G I env l en sd ys out) a = .ok b →
      ExitYieldSource env l en sd a.yields (b.yields.getD [])
  | [], _, _, h => by cases h; exact .inl rfl
  | e :: es, a, b, h => by
    rw [List.foldlM_cons] at h
    cases ha : exitStep G I env l en sd ys out a e with
    | error stop => rw [ha] at h; cases h
    | ok a' =>
      rw [ha] at h
      exact (exitStep_yields_source ha).trans (exitsFold_yields_source es a' b h)

/-- Each record has an execution witness whose input and output caches
have checked sources in the fold's initial cache. -/
theorem exitsFold_records_yields {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (Exit × Nat)) (a b : ExitsDone ι G),
      es.foldlM (exitStep G I env l en sd ys out) a = .ok b →
      ∀ e ∈ es, ∃ r ∈ b.exits.toList, r.index = e.2 ∧ r.target = e.1.target ∧ ∃ a' b',
        exitStep G I env l en sd ys out a' e = .ok b' ∧ b'.exits = a'.exits.push r ∧
        ExitYieldSource env l en sd a.yields (a'.yields.getD []) ∧
        ExitYieldSource env l en sd a.yields (b'.yields.getD [])
  | [], _, _, _, _, he => by cases he
  | e :: es, a, b, h, e', he => by
    rw [List.foldlM_cons] at h
    cases ha : exitStep G I env l en sd ys out a e with
    | error stop => rw [ha] at h; cases h
    | ok a' =>
      rw [ha] at h
      rcases List.mem_cons.mp he with rfl | he
      · obtain ⟨r, hr, hi, ht, -⟩ := exitStep_record ha
        obtain ⟨rs, hrs⟩ := exitsFold_records_prefix es a' b h
        refine ⟨r, ?_, hi, ht, a, a', ha, hr, .inl rfl, exitStep_yields_source ha⟩
        rw [hrs, hr, Array.toList_push]
        simp
      · obtain ⟨r, hr, hi, ht, x, y, hxy, hy, hxsrc, hysrc⟩ := exitsFold_records_yields es a' b h e' he
        exact ⟨r, hr, hi, ht, x, y, hxy, hy,
          (exitStep_yields_source ha).trans hxsrc, (exitStep_yields_source ha).trans hysrc⟩

/-- Every indexed exit has a record and checked cache provenance from the
step's yields, including caches populated by earlier exits. -/
theorem visitExits_records_yields {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G}
    (h : visitExits G I env σ l en sd = .ok ex) :
    ∀ e ∈ (Exit.ofNode env.nodes[l]!).zipIdx, ∃ r ∈ ex.exits.toList,
      r.index = e.2 ∧ r.target = e.1.target ∧ ∃ a b,
        exitStep G I env l en sd
          (yieldsAtSlots en.entry.names ((exitsYields G I env l en sd).1.getD []))
          (Thunk.mk fun _ => outAllOf G env.claimed[l]! sd.st.stepOut) a e = .ok b ∧
        b.exits = a.exits.push r ∧
        ExitYieldSource env l en sd sd.yields (a.yields.getD []) ∧
        ExitYieldSource env l en sd sd.yields (b.yields.getD []) := by
  unfold visitExits at h
  extract_lets node c at h
  split at h
  rename_i ys answers heq
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · have hsrc := exitsYields_source env l en sd
    rw [heq] at hsrc
    intro e he
    obtain ⟨r, hr, hi, ht, a, b, hb, hrec, ha, hy⟩ := exitsFold_records_yields _ _ _ h e he
    refine ⟨r, hr, hi, ht, a, b, ?_, hrec, hsrc.trans ha, hsrc.trans hy⟩
    rw [heq]
    exact hb

/-- A successful type check marked `refined` stores the yields it used
in its output cache. -/
theorem exitTypes_refined_yields {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {out : Thunk HeapKnowledge.Knowledge} {t : Target} {tc : PointClaim ι} {Γ Γr : List (Ty ι)}
    {names : List Nat} {store : Store} {pushed handler : Bool}
    {observed : Option BranchRefinement.Observation} {first : Bool} {diff : List (Nat × Nat)}
    {a b : ExitsDone ι G} {kr : HeapKnowledge.Knowledge} {ys : List (PromiseCalls.Yield ι)}
    (h : exitTypes G I env l en sd out t tc Γ names store pushed handler observed first diff a =
      .ok (b, .refined Γr kr ys)) : b.yields = some ys := by
  unfold exitTypes at h
  extract_lets node c width entry at h
  split at h
  split at h
  · cases h
  · split at h
    extract_lets ko at h
    split at h
    extract_lets answers at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        extract_lets Γr at h
        split at h
        extract_lets answersR at h
        split at h
        rename_i foundM a4 typ hmixed
        split at h
        · cases h
        · cases h
          split at hmixed
          · simp only [Prod.mk.injEq, SinglePass.ExitTyped.refined.injEq] at hmixed
            exact congrArg some hmixed.2.2.2.2
          · repeat' (first | split at hmixed | extract_lets at hmixed)
            all_goals cases hmixed

/-- The yields in a refined exit record are the cache at that exit's
successful return, including head and assertion processing. -/
theorem exitStep_refined_yields {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ysAll : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    {a b : ExitsDone ι G} {e : Exit × Nat} {r : ExitRecord ι}
    (h : exitStep G I env l en sd ysAll out a e = .ok b)
    (hr : b.exits = a.exits.push r) {Γr : List (Ty ι)} {kr : HeapKnowledge.Knowledge}
    {ys : List (PromiseCalls.Yield ι)} (htyped : r.typed = .refined Γr kr ys) :
    b.yields = some ys := by
  unfold exitStep at h
  extract_lets ex first node c width entry st t pushed observed handler pushedNames tr a0 Γ names store unsatΓ vacuous Γe read recordedΓ at h
  split at h
  · cases h
  split at h
  · cases h
  extract_lets diff u a2 typed at h
  generalize ht : typed = T at h
  split at h
  · cases h
  rename_i a1 et
  simp only [typed] at ht
  have hp : a2.exits = a.exits := by
    dsimp only [a2, a0]
    split <;> split <;> rfl
  have hp1 : a1.exits = a.exits := by
    split at ht
    · cases ht; exact hp
    · exact (exitTypes_exits ht).trans hp
  have hy : et = .refined Γr kr ys → a1.yields = some ys := by
    intro het
    subst et
    split at ht
    · cases ht
    · exact exitTypes_refined_yields ht
  extract_lets freshImpl record at h
  split at h
  · simp only [Except.map] at h
    split at h
    · cases h
    · rename_i a3 hh
      cases h
      change a3.exits.push _ = a.exits.push r at hr
      rw [headExit_exits hh, hp1] at hr
      have hlist := congrArg Array.toList hr
      simp only [Array.toList_push] at hlist
      have hetr := congrArg ExitRecord.typed (List.cons.inj (List.append_cancel_left hlist)).1
      change et = r.typed at hetr
      change a3.yields = some ys
      rw [headExit_yields hh]
      exact hy (hetr.trans htyped)
  · split at h
    · cases h
    rename_i a3 ha
    split at h
    cases h
    change a3.exits.push _ = a.exits.push r at hr
    rw [assertionExit_exits ha, hp1] at hr
    have hlist := congrArg Array.toList hr
    simp only [Array.toList_push] at hlist
    have hetr := congrArg ExitRecord.typed (List.cons.inj (List.append_cancel_left hlist)).1
    change et = r.typed at hetr
    change a3.yields = some ys
    rw [assertionExit_yields ha]
    exact hy (hetr.trans htyped)

/-- Every indexed exit owns a record whose refined yields are judged.
The premise concerns the step cache and the summaries that `checkYsAt`
reads; no equality with the kept yields is required. -/
theorem visitExits_refined_judged {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G}
    (h : visitExits G I env σ l en sd = .ok ex) (start : List Nat) (ρ0 : Env) (m : Nat)
    (hcodes : CodesSound G env.codes) (hsums : SummariesSound G I sd.answers.summaries.toList)
    (hcache : YieldsJudged G (env.claimed[l]!).type (env.claimed[l]!).context (env.nodes[l]!).expression
      en.entry en.implies start ρ0 m sd.st.stepK (sd.yields.getD [])) :
    ∀ e ∈ (Exit.ofNode env.nodes[l]!).zipIdx, ∃ r ∈ ex.exits.toList,
      r.index = e.2 ∧ r.target = e.1.target ∧
      ∀ Γr kr ys, r.typed = .refined Γr kr ys →
        YieldsJudged G (env.claimed[l]!).type (env.claimed[l]!).context (env.nodes[l]!).expression
          en.entry en.implies start ρ0 m sd.st.stepK ys := by
  intro e he
  obtain ⟨r, hr, hi, ht, a, b, hb, hrec, -, hsrc⟩ := visitExits_records_yields h e he
  refine ⟨r, hr, hi, ht, fun Γr kr ys hty => ?_⟩
  have hy := exitStep_refined_yields hb hrec hty
  have hj := hsrc.judged start ρ0 m hcodes hsums hcache
  simpa only [hy, Option.getD_some] using hj

end Cache
end Verification.TolerantFrames
