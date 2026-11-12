import Verification.Programs.TolerantFramesExitWidths

/-! # Exit records retain each successful indexed check -/
namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore

section Records
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- Type checking leaves the earlier exit records intact. -/
theorem exitTypes_exits {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {out : Thunk HeapKnowledge.Knowledge} {t : Target} {tc : PointClaim ι}
    {Γ : List (ProgramTyping.Ty ι)} {names : List Nat} {store : SinglePass.Store} {pushed handler : Bool}
    {observed : Option BranchRefinement.Observation} {first : Bool} {diff : List (Nat × Nat)}
    {a b : SinglePass.ExitsDone ι G} {et : SinglePass.ExitTyped ι}
    (h : SinglePass.exitTypes G I env l en sd out t tc Γ names store pushed handler observed first diff a = .ok (b, et)) :
    b.exits = a.exits := by
  unfold SinglePass.exitTypes at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- The head check leaves the earlier exit records intact. -/
theorem headExit_exits {env : SinglePass.WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γ : List (ProgramTyping.Ty ι)} {names : List Nat} {store : SinglePass.Store} {pushed vacuous : Bool}
    {carried : List (PromiseCalls.Implication ι)} {a b : SinglePass.ExitsDone ι G}
    (h : SinglePass.headExit G I env l t tc Γ names store pushed vacuous carried a = .ok b) :
    b.exits = a.exits := by
  unfold SinglePass.headExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- The assertion check leaves the earlier exit records intact. -/
theorem assertionExit_exits {env : SinglePass.WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γe : Thunk (List (ProgramTyping.Ty ι))} {names : List Nat} {store : SinglePass.Store} {pushed vacuous : Bool}
    {observed : Option BranchRefinement.Observation} {a b : SinglePass.ExitsDone ι G}
    (h : SinglePass.assertionExit G env l t tc Γe names store pushed observed vacuous a = .ok b) :
    b.exits = a.exits := by
  unfold SinglePass.assertionExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- A successful exit appends exactly one record with its index, target,
source names, head flag and checked mapping width. -/
theorem exitStep_record {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    {a b : SinglePass.ExitsDone ι G} {e : SinglePass.Exit × Nat}
    (h : SinglePass.exitStep G I env l en sd ys out a e = .ok b) :
    ∃ r : SinglePass.ExitRecord ι, b.exits = a.exits.push r ∧ r.index = e.2 ∧ r.target = e.1.target ∧
      r.names = exitNames en sd e.1 ∧ r.head = env.isHead[e.1.target.label]! ∧
      ∃ tc, env.claimed[r.target.label]? = some tc ∧
        SinglePass.mappingWidthOk r.target.mapping r.names.length tc.context.length = true := by
  have hw := exitStep_mappingWidth h
  unfold SinglePass.exitStep at h
  extract_lets ex first node c width entry st t pushed observed handler pushedNames tr a0 Γ names store unsatΓ vacuous Γe read Γr at h
  split at h
  · cases h
  rename_i tc htc
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
  extract_lets freshImpl record at h
  split at h
  · rename_i hh
    simp only [Except.map] at h
    split at h
    · cases h
    · rename_i a3 hhead
      cases h
      refine ⟨{ record with head := true }, ?_, rfl, rfl, rfl, hh.symm, ?_⟩
      · rw [headExit_exits hhead, hp1]
      · exact hw
  · rename_i hh
    split at h
    · cases h
    rename_i a3 ha
    split at h
    rename_i target carried hcar
    cases h
    refine ⟨{ record with Γe := Γr, carried := some (target, carried) }, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · change a3.exits.push _ = a.exits.push _
      rw [assertionExit_exits ha, hp1]
    · exact (Bool.eq_false_iff.mpr hh).symm
    · exact hw

/-- Every earlier exit record persists through a successful fold. -/
theorem exitsFold_records_prefix {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (SinglePass.Exit × Nat)) (a b : SinglePass.ExitsDone ι G),
      es.foldlM (SinglePass.exitStep G I env l en sd ys out) a = .ok b →
      ∃ rs, b.exits.toList = a.exits.toList ++ rs
  | [], _, _, h => by cases h; exact ⟨[], (List.append_nil _).symm⟩
  | e :: es, a, b, h => by
    rw [List.foldlM_cons] at h
    cases ha : SinglePass.exitStep G I env l en sd ys out a e with
    | error stop => rw [ha] at h; cases h
    | ok a' =>
      rw [ha] at h
      obtain ⟨r, hr, -⟩ := exitStep_record ha
      obtain ⟨rs, hrs⟩ := exitsFold_records_prefix es a' b h
      exact ⟨r :: rs, by rw [hrs, hr, Array.toList_push, List.append_assoc]; rfl⟩

/-- The final array contains the record appended by every indexed exit. -/
theorem exitsFold_records_checked {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (SinglePass.Exit × Nat)) (a b : SinglePass.ExitsDone ι G),
      es.foldlM (SinglePass.exitStep G I env l en sd ys out) a = .ok b →
      ∀ e ∈ es, ∃ r ∈ b.exits.toList, r.index = e.2 ∧ r.target = e.1.target ∧ ∃ a' b',
        SinglePass.exitStep G I env l en sd ys out a' e = .ok b' ∧ b'.exits = a'.exits.push r
  | [], _, _, _, _, he => by cases he
  | e :: es, a, b, h, e', he => by
    rw [List.foldlM_cons] at h
    cases ha : SinglePass.exitStep G I env l en sd ys out a e with
    | error stop => rw [ha] at h; cases h
    | ok a' =>
      rw [ha] at h
      rcases List.mem_cons.mp he with rfl | he
      · obtain ⟨r, hr, hi, ht, -⟩ := exitStep_record ha
        obtain ⟨rs, hrs⟩ := exitsFold_records_prefix es a' b h
        refine ⟨r, ?_, hi, ht, a, a', ha, hr⟩
        rw [hrs, hr, Array.toList_push]
        simp
      · exact exitsFold_records_checked es a' b h e' he

/-- A successful exit visit retains every indexed exit's own record. -/
theorem visitExits_records {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G} {ex : SinglePass.ExitsDone ι G}
    (h : SinglePass.visitExits G I env σ l en sd = .ok ex) : ExitRecordsChecked G I env l en sd ex := by
  unfold SinglePass.visitExits at h
  extract_lets node c at h
  split at h
  rename_i ys answers heq
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · intro e he
    obtain ⟨r, hr, hi, ht, a, b, hb, hext⟩ := exitsFold_records_checked _ _ _ h e he
    refine ⟨r, hr, hi, ht, a, b, ?_, hext⟩
    rw [heq]
    exact hb

end Records
end Verification.TolerantFrames
