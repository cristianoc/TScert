import Verification.Programs.TolerantFramesDriverExits

/-! # The meaning of the exit satisfiability cache

A true cache entry states that the target context is empty. The answer
computed by `exitStep` has that property for every list of differing slots.
-/
namespace Verification.TolerantFrames
open Verification SinglePass ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore ProgramTyping

section Cache
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

omit [Labels ι] in
/-- An unfilled cache, as allocated by setup, satisfies the invariant. -/
theorem cachedVacuity_empty (claimed : Array (PointClaim ι)) (n : Nat) :
    CachedVacuity G claimed (Array.replicate n none) := by
  intro l hl
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at hl
  by_cases hlt : l < (Array.replicate n (none : Option Bool)).size
  · rw [Array.getElem?_eq_getElem hlt] at hl
    simp at hl
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hl
    cases hl

omit [Labels ι] in
/-- A true answer computed for a target has an empty-context witness. -/
theorem exitUnsatAnswer_sound (Γ : List (Ty ι)) (unsatΓ : Bool) (diff : List (Nat × Nat))
    (h : (if unsatΓ then ControlFlow.unsatisfiable G Γ
      else diff.any fun p => (Γ[p.1]?).any fun B => ControlFlow.unsatisfiable G [B]) = true) :
    HereEmpty G Γ := by
  split at h
  · exact .inl h
  · obtain ⟨p, _, hp⟩ := List.any_eq_true.mp h
    obtain ⟨B, hB, hu⟩ := option_any_some hp
    exact .inr ⟨p.1, B, hB, hu⟩

/-- A successful entry exposes exactly the cached unsatisfiability answer it uses. -/
theorem visitEntry_here {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} (h : SinglePass.visitEntry G I env σ l = .ok en) :
    en.here = (σ.unsat[l]!).getD (ControlFlow.unsatisfiable G (env.claimed[l]!).context) := by
  unfold SinglePass.visitEntry at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals simp_all only [Option.getD_some, Option.getD_none] <;> rfl

/-- The entry's `here` flag is sound under the cache invariant. -/
theorem visitEntry_hereEmpty {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat} {en : Entered ι}
    (hc : CachedVacuity G env.claimed σ.unsat) (h : visitEntry G I env σ l = .ok en)
    (hh : en.here = true) : HereEmpty G (env.claimed[l]!).context := by
  rw [visitEntry_here h] at hh
  cases hu : σ.unsat[l]! with
  | none => exact .inl (by simpa only [hu, Option.getD_none] using hh)
  | some b =>
    have hb : b = true := by simpa only [hu, Option.getD_some] using hh
    exact hc l (hb ▸ hu)

omit [Labels ι] in
/-- Replacing one cache entry by a sound answer preserves the invariant. -/
theorem CachedVacuity.set {claimed : Array (PointClaim ι)} {cache : Array (Option Bool)}
    (hc : CachedVacuity G claimed cache) (t : Nat) (b : Bool)
    (hb : b = true → HereEmpty G (claimed[t]!).context) :
    CachedVacuity G claimed (cache.set! t (some b)) := by
  intro l hl
  by_cases hlt : l = t
  · subst l
    by_cases ht : t < cache.size
    · simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD,
        Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt ht, Option.getD_some] at hl
      exact hb (Option.some.inj hl)
    · have heq : cache.set! t (some b) = cache := by
        simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, ht]
      exact hc t (heq ▸ hl)
  · have heq : (cache.set! t (some b))[l]! = cache[l]! := by
      simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_ne (Ne.symm hlt)]
    exact hc l (heq ▸ hl)

/-- Type checking an exit preserves the satisfiability cache. -/
theorem exitTypes_unsat {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {outAll : Thunk HeapKnowledge.Knowledge} {t : Target} {tc : PointClaim ι} {Γ : List (Ty ι)}
    {names : List Nat} {edgeStore : Store} {pushed isHandler : Bool}
    {observed : Option BranchRefinement.Observation} {first : Bool} {diff : List (Nat × Nat)}
    {acc acc' : ExitsDone ι G}
    (h : exitTypes G I env l en sd outAll t tc Γ names edgeStore pushed isHandler observed first diff acc = .ok acc') :
    acc'.unsat = acc.unsat := by
  unfold exitTypes at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- A head check preserves the satisfiability cache. -/
theorem headExit_unsat {env : WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι} {Γ : List (Ty ι)}
    {names : List Nat} {edgeStore : Store} {pushed vacuous : Bool} {carried : List (PromiseCalls.Implication ι)}
    {acc acc' : ExitsDone ι G}
    (h : headExit G I env l t tc Γ names edgeStore pushed vacuous carried acc = .ok acc') :
    acc'.unsat = acc.unsat := by
  unfold headExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- An assertion check preserves the satisfiability cache. -/
theorem assertionExit_unsat {env : WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γe : Thunk (List (Ty ι))} {names : List Nat} {edgeStore : Store} {pushed vacuous : Bool}
    {observed : Option BranchRefinement.Observation} {acc acc' : ExitsDone ι G}
    (h : assertionExit G env l t tc Γe names edgeStore pushed observed vacuous acc = .ok acc') :
    acc'.unsat = acc.unsat := by
  unfold assertionExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- Each successful exit preserves the meaning of cached vacuity. -/
theorem exitStep_cachedVacuity {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ysAll : List (PromiseCalls.Yield ι)} {outAll : Thunk HeapKnowledge.Knowledge}
    {acc acc' : ExitsDone ι G} {exi : Exit × Nat}
    (hc : CachedVacuity G env.claimed acc.unsat)
    (h : exitStep G I env l en sd ysAll outAll acc exi = .ok acc') :
    CachedVacuity G env.claimed acc'.unsat := by
  unfold exitStep at h
  extract_lets ex first node c width entry st t pushed observed isHandler pushedNames tr acc0 Γ names store unsatΓ vacuous Γe at h
  split at h
  · cases h
  rename_i tc htc
  extract_lets diff u acc2 typed at h
  generalize ht : typed = T at h
  split at h
  · cases h
  rename_i acc1
  simp only [typed] at ht
  have hp : CachedVacuity G env.claimed acc2.unsat := by
    have h0 : CachedVacuity G env.claimed acc0.unsat := by
      dsimp only [acc0]
      split <;> exact hc
    have hclaim : env.claimed[t.label]! = tc := by
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, htc, Option.getD_some]
    dsimp only [acc2]
    split
    · apply h0.set t.label u
      intro hu
      rw [hclaim]
      exact exitUnsatAnswer_sound tc.context unsatΓ diff hu
    · exact h0
  have hc1 : CachedVacuity G env.claimed acc1.unsat := by
    split at ht
    · cases ht; exact hp
    · rw [exitTypes_unsat ht]; exact hp
  extract_lets freshImpl at h
  split at h
  · rw [headExit_unsat h]; exact hc1
  · split at h
    · cases h
    rename_i acc3 hA
    split at h
    cases h
    change CachedVacuity G env.claimed acc3.unsat
    rw [assertionExit_unsat hA]
    exact hc1

/-- The exits' fold preserves the cache invariant. -/
theorem exitsFold_cachedVacuity {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {ysAll : List (PromiseCalls.Yield ι)} {outAll : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (Exit × Nat)) (acc r : ExitsDone ι G),
      es.foldlM (exitStep G I env l en sd ysAll outAll) acc = .ok r →
      CachedVacuity G env.claimed acc.unsat → CachedVacuity G env.claimed r.unsat
  | [], _, _, h, hc => by cases h; exact hc
  | e :: es, acc, r, h, hc => by
    rw [List.foldlM_cons] at h
    cases ha : exitStep G I env l en sd ysAll outAll acc e with
    | error stop => rw [ha] at h; cases h
    | ok a =>
      rw [ha] at h
      exact exitsFold_cachedVacuity es a r h (exitStep_cachedVacuity hc ha)

/-- A successful exit visit preserves the cache invariant. -/
theorem visitExits_cachedVacuity {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G}
    (h : visitExits G I env σ l en sd = .ok ex) (hc : CachedVacuity G env.claimed σ.unsat) :
    CachedVacuity G env.claimed ex.unsat := by
  unfold visitExits at h
  extract_lets node c at h
  split at h
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · exact exitsFold_cachedVacuity _ _ _ h hc

end Cache
end Verification.TolerantFrames
