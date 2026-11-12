import Verification.Programs.TolerantFramesDriverNames

/-! # The entry recorded by a visit -/
namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore ProgramTyping

section Entry
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- The visited label contains exactly the visit's record. -/
theorem visitResult_record {σ : SinglePass.WalkState ι G} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ex : SinglePass.ExitsDone ι G} (hl : l < σ.walk.labels.size) :
    (visitResult σ l en sd ex).walk.labels[l]? = some (SinglePass.LabelWalk.ofVisit σ.fresh en sd (ex.regional.map (·.state))) := by
  simp only [visitResult, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hl]

/-- A walk agreeing with the visit's label has its entry, implications and visited flag. -/
theorem ofPass_visitRecord {w : SinglePass.Walk ι} {heads : Nat → Bool} {l fresh : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G} {region : Option SinglePass.RegionState}
    (h : w.labels[l]? = some (SinglePass.LabelWalk.ofVisit fresh en sd region)) :
    (ofPass w heads).entry l = en.entry ∧ (ofPass w heads).implies l = en.implies ∧
      (ofPass w heads).visited l := by
  simp [ofPass, h, SinglePass.LabelWalk.ofVisit]

/-- At the start the recorded entry is the head entry justified by setup. -/
theorem visitStart_entered {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    {σ : SinglePass.WalkState ι G} {l : Nat} {rest : List Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ex : SinglePass.ExitsDone ι G}
    (hP : VisitParts c env σ l rest en sd ex) (hl : l = c.start)
    {w : SinglePass.Walk ι}
    {region : Option SinglePass.RegionState}
    (hrec : w.labels[l]? = some (SinglePass.LabelWalk.ofVisit σ.fresh en sd region)) :
    StartEntered c (ofPass w (envHead env)) (passCtx c) (passStated c) := by
  subst l
  obtain ⟨he, hi, hv⟩ := ofPass_visitRecord (heads := envHead env) hrec
  obtain ⟨supplied, href, hg⟩ := hP.facts.startGiven
  obtain ⟨-, -, hentry, himp⟩ := visitEntry_merge hP.entry
  have hctx : (env.claimed[c.start]!).context = c.inputs :=
    (hP.facts.context hP.facts.start.1).trans hP.facts.startContext
  refine ⟨supplied, _, _, _, σ.fresh, env.startEntered, href, hv, ?_, ?_, ?_, hP.facts.startContext⟩
  · intro _
    by_cases h0 : c.inputs.length = 0
    · omega
    · have := hP.inv.startFresh (c.inputs.length - 1) (List.mem_range.mpr (by omega))
      omega
  · rw [he, hentry, withStated_eq, hP.facts.startHead]
    simp only [ite_true]
    unfold SinglePass.entryStart
    rw [hg]
    simp only [hP.facts.startLabel, beq_self_eq_true, Bool.true_and, hctx,
      hP.facts.startNames, hP.facts.argName]
  · rw [hi, himp]
    unfold SinglePass.entryStart
    rw [hg]
    simp only [hP.facts.startLabel, beq_self_eq_true, Bool.true_and, hctx,
      hP.facts.startNames, hP.facts.argName]

/-- Zipping lists of equal length preserves the first list. -/
theorem zip_map_fst_eq {α β : Type} (xs : List α) (ys : List β) (h : xs.length = ys.length) :
    (xs.zip ys).map Prod.fst = xs := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp only [List.length_cons, Nat.add_right_cancel_iff] at h
                   simp [ih ys h]

/-- At a non-head the entry uses its single predecessor or its merge. -/
theorem entryStart_incoming {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    (hg : env.given[l]! = none)
    (hlen : (σ.walk.incoming[l]!).length = (σ.walk.incomingImpl[l]!).length) :
    (∀ e, (σ.walk.incoming[l]!).zip σ.walk.incomingImpl[l]! = [e] →
      (SinglePass.entryStart G env σ l).base = e.1 ∧ (SinglePass.entryStart G env σ l).implies = e.2) ∧
    (2 ≤ ((σ.walk.incoming[l]!).zip σ.walk.incomingImpl[l]!).length →
      (SinglePass.entryStart G env σ l).base =
        (SinglePass.mergeState G (env.claimed[l]!).context σ.walk.incoming[l]! σ.walk.incomingEdges[l]! σ.fresh).state ∧
      (SinglePass.entryStart G env σ l).implies =
        (SinglePass.mergeState G (env.claimed[l]!).context σ.walk.incoming[l]! σ.walk.incomingEdges[l]! σ.fresh).implies ∧
      (SinglePass.entryStart G env σ l).merge = some ((env.claimed[l]!).context, σ.fresh)) := by
  unfold SinglePass.entryStart
  rw [hg]
  cases hs : σ.walk.incoming[l]! with
  | nil => simp
  | cons q qs =>
    cases qs with
    | nil =>
      rw [hs] at hlen
      cases hi : σ.walk.incomingImpl[l]! with
      | nil => simp [hi] at hlen
      | cons xs xss =>
        have ht : xss = [] := by simpa [hi] using hlen.symm
        subst xss
        simp
    | cons q' qs =>
      refine ⟨fun e he => ?_, fun _ => ⟨rfl, rfl, rfl⟩⟩
      have := congrArg List.length he
      simp only [List.length_zip, List.length_cons, List.length_nil] at this
      rw [hs] at hlen
      simp only [List.length_cons] at hlen
      omega

/-- The settled non-head entry is the written assertion over its single
incoming state or its recorded merge. -/
theorem visitEntry_settled {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    {σ : SinglePass.WalkState ι G} {l : Nat} {rest : List Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ex : SinglePass.ExitsDone ι G}
    (hP : VisitParts c env σ l rest en sd ex) (hself : envHead env l = false → l ∉ exitsOf env l)
    (hg : envHead env l = false) :
    let σ' := visitResult { σ with queue := rest } l en sd ex
    ∃ b, (ofPass σ'.walk (envHead env)).entry l = withWritten (passStated c l) b ∧
      (∀ e, (ofPass σ'.walk (envHead env)).incoming l = [e] →
        b = e.1 ∧ (ofPass σ'.walk (envHead env)).implies l = e.2) ∧
      (2 ≤ ((ofPass σ'.walk (envHead env)).incoming l).length →
        b = (SinglePass.mergeState G (passCtx c l) (((ofPass σ'.walk (envHead env)).incoming l).map (·.1))
          (passEdgesIn σ'.walk l) (passFresh σ'.walk l)).state ∧
        (ofPass σ'.walk (envHead env)).implies l = (SinglePass.mergeState G (passCtx c l)
          (((ofPass σ'.walk (envHead env)).incoming l).map (·.1))
          (passEdgesIn σ'.walk l) (passFresh σ'.walk l)).implies) := by
  have hl := (hP.inv.queue l (by rw [hP.queue]; exact List.mem_cons_self ..)).1
  have hlabel := visitResult_record (σ := { σ with queue := rest }) (en := en) (sd := sd) (ex := ex)
    (hP.inv.size ▸ hl)
  obtain ⟨he, hi, -⟩ := ofPass_visitRecord (heads := envHead env) hlabel
  obtain ⟨acc, a1, a2, a3, -, -, -, hf⟩ := visitExits_fold hP.exits
  obtain ⟨f1, f2, f3⟩ := hf.frame l (by rw [exitLabels_ofNode]; exact hself hg)
  rw [a1] at f1
  rw [a2] at f2
  rw [a3] at f3
  have hin : (ofPass (visitResult { σ with queue := rest } l en sd ex).walk (envHead env)).incoming l =
      (σ.walk.incoming[l]!).zip σ.walk.incomingImpl[l]! := by
    simp only [ofPass, hg, Bool.false_eq_true, ↓reduceIte, visitResult, f1, f2,
      Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    rfl
  have hlen : (σ.walk.incoming[l]!).length = (σ.walk.incomingImpl[l]!).length := by
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    exact hP.inv.inLen l
  have hs := entryStart_incoming (σ := { σ with queue := rest })
    (hP.facts.given l (by rwa [← envHead_eq])) hlen
  obtain ⟨hm, -, hen, himp⟩ := visitEntry_merge hP.entry
  refine ⟨(SinglePass.entryStart G env { σ with queue := rest } l).base, ?_, ?_, ?_⟩
  · rw [he, hen, withStated_eq, ← envHead_eq, hg, hP.facts.stated]
    rfl
  · intro e heq
    rw [hin] at heq
    rw [hi, himp]
    exact hs.1 e heq
  · intro h2
    rw [hin] at h2
    obtain ⟨hb, hi', hm'⟩ := hs.2 h2
    have hfr : passFresh (visitResult { σ with queue := rest } l en sd ex).walk l = σ.fresh := by
      simp only [passFresh, hlabel, SinglePass.LabelWalk.ofVisit, hm, hm']
      rfl
    rw [hin, zip_map_fst_eq _ _ hlen, hi, himp, hfr]
    have hedges : passEdgesIn (visitResult { σ with queue := rest } l en sd ex).walk l =
        σ.walk.incomingEdges[l]! := by
      simp only [passEdgesIn, visitResult, f3, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      rfl
    rw [hedges, ← hP.facts.context hl]
    exact ⟨hb, hi'⟩

end Entry
end Verification.TolerantFrames
