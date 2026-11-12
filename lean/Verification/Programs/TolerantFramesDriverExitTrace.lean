import Verification.Programs.TolerantFramesDriverExitGrowth

/-! # Successful checks for each exit in a visit -/
namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore

section Trace
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- Every successful exit fold extends its initial arrays. -/
theorem exitsFold_extends {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ysAll : List (PromiseCalls.Yield ι)} {outAll : Thunk HeapKnowledge.Knowledge}
    {es : List (SinglePass.Exit × Nat)} {acc r : SinglePass.ExitsDone ι G}
    (h : es.foldlM (SinglePass.exitStep G I env l en sd ysAll outAll) acc = .ok r)
    (hs : acc.incoming.size = acc.incomingImpl.size) : WalkExtends (exitsWalk acc) (exitsWalk r) := by
  have hf := exitsFold_of es acc r h
  refine ⟨fun t => ?_, exitsFold_mergeGrowth es acc r h, ?_⟩
  · obtain ⟨ns, nis, h1, h2, h3, -⟩ := hf.pushes t
    exact ⟨ns, nis, h1, h2, h3 hs⟩
  · obtain ⟨ns, hn, -⟩ := hf.edges
    exact ⟨ns, hn⟩

/-- Each indexed exit has a successful check at these entry and step values;
its resulting arrays persist in the fold's final arrays. -/
theorem exitsFold_checked {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ysAll : List (PromiseCalls.Yield ι)} {outAll : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (SinglePass.Exit × Nat)) (acc r : SinglePass.ExitsDone ι G),
      es.foldlM (SinglePass.exitStep G I env l en sd ysAll outAll) acc = .ok r →
      acc.incoming.size = acc.incomingImpl.size →
      ∀ e ∈ es, ∃ a b, SinglePass.exitStep G I env l en sd ysAll outAll a e = .ok b ∧
        WalkExtends (exitsWalk b) (exitsWalk r)
  | [], _, _, _, _, _, he => by cases he
  | e :: es, acc, r, h, hs, e', he => by
    rw [List.foldlM_cons] at h
    cases ha : SinglePass.exitStep G I env l en sd ysAll outAll acc e with
    | error stop => rw [ha] at h; cases h
    | ok a =>
      rw [ha] at h
      have hf : ExitsFold env l en sd [e.1] acc a :=
        exitsFold_of (ysAll := ysAll) (outAll := outAll) [e] acc a (by simp only [List.foldlM_cons, List.foldlM_nil, ha]; rfl)
      have hsa : a.incoming.size = a.incomingImpl.size := by rw [hf.sizes.1, hf.sizes.2, hs]
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨acc, a, ha, exitsFold_extends h hsa⟩
      · exact exitsFold_checked es a r h hsa e' he

/-- A visit checks each exit (including its handler), retaining the precise
index used to distinguish the first branch. Its arrays persist in any later
walk extending the visit's output. -/
theorem visitExits_checked {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G} {ex : SinglePass.ExitsDone ι G}
    (h : SinglePass.visitExits G I env σ l en sd = .ok ex)
    (hs : σ.walk.incoming.size = σ.walk.incomingImpl.size)
    {w : SinglePass.Walk ι} (hw : WalkExtends (exitsWalk ex) w) :
    ∀ e ∈ (SinglePass.Exit.ofNode env.nodes[l]!).zipIdx, ∃ a b,
      SinglePass.exitStep G I env l en sd
        (SinglePass.yieldsAtSlots en.entry.names ((SinglePass.exitsYields G I env l en sd).1.getD []))
        (Thunk.mk fun _ => SinglePass.outAllOf G env.claimed[l]! sd.st.stepOut) a e = .ok b ∧
      WalkExtends (exitsWalk b) w := by
  unfold SinglePass.visitExits at h
  extract_lets node c at h
  split at h
  rename_i yields answers heq
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · intro e he
    obtain ⟨a, b, hb, hg⟩ := exitsFold_checked _ _ _ h hs e he
    refine ⟨a, b, ?_, hg.trans hw⟩
    rw [heq]
    exact hb

end Trace
end Verification.TolerantFrames
