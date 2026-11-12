import Verification.Programs.TolerantFramesDriverEntry

/-! # Every accepted exit mapping has the target's width -/
namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore

section Widths
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- A successful exit passes the mapping check against its target claim. -/
theorem exitStep_mappingWidth {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    {a b : SinglePass.ExitsDone ι G} {e : SinglePass.Exit × Nat}
    (h : SinglePass.exitStep G I env l en sd ys out a e = .ok b) :
    ∃ tc, env.claimed[e.1.target.label]? = some tc ∧
      SinglePass.mappingWidthOk e.1.target.mapping (exitNames en sd e.1).length tc.context.length = true := by
  unfold SinglePass.exitStep at h
  extract_lets at h
  split at h
  · cases h
  rename_i tc htc
  split at h
  · cases h
  rename_i hw
  exact ⟨tc, htc, by simpa (config := { zetaDelta := true }) only [exitNames, Bool.not_eq_true', Bool.not_eq_false] using hw⟩

/-- Every member of a successful exit fold passes its mapping check. -/
theorem exitsFold_mappingWidth {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (SinglePass.Exit × Nat)) (a b : SinglePass.ExitsDone ι G),
      es.foldlM (SinglePass.exitStep G I env l en sd ys out) a = .ok b →
      ∀ e ∈ es, ∃ tc, env.claimed[e.1.target.label]? = some tc ∧
        SinglePass.mappingWidthOk e.1.target.mapping (exitNames en sd e.1).length tc.context.length = true
  | [], _, _, _, _, he => by cases he
  | e :: es, a, b, h, e', he => by
    rw [List.foldlM_cons] at h
    cases ha : SinglePass.exitStep G I env l en sd ys out a e with
    | error stop => rw [ha] at h; cases h
    | ok a' =>
      rw [ha] at h
      rcases List.mem_cons.mp he with rfl | he
      · exact exitStep_mappingWidth ha
      · exact exitsFold_mappingWidth es a' b h e' he

/-- The driver's checked mapping supplies `ExitsWidth`. -/
theorem exitsWidth : ExitsWidth ι := by
  intro G I c env σ l rest en sd ex hp e he
  have h := hp.exits
  unfold SinglePass.visitExits at h
  extract_lets node cl at h
  split at h
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · have hm : e ∈ ((SinglePass.Exit.ofNode env.nodes[l]!).zipIdx.map (·.1)) := by
      simpa only [List.zipIdx_map_fst] using he
    obtain ⟨ei, hei, rfl⟩ := List.mem_map.mp hm
    obtain ⟨tc, htc, hw⟩ := exitsFold_mappingWidth _ _ _ h ei hei
    have hctx : passCtx c ei.1.target.label = tc.context := by
      unfold passCtx
      rw [hp.facts.claims, List.getElem?_toArray] at htc
      rw [htc]
      rfl
    rw [hctx]
    cases ht : ei.1.target.mapping with
    | none => simpa [SinglePass.mappingWidthOk, ht] using hw
    | some slots => simpa [SinglePass.mappingWidthOk, ht, List.all_eq_true] using hw

end Widths
end Verification.TolerantFrames
