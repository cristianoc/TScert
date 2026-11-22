import Verification.Programs.TolerantFramesGuaranteeTarget

/-! Every path to an asserted label is unchanged if nodes whose outgoing
edges cannot reach any assertion are replaced by returns. This lets the
ordinary pass certify assertions without typing an unrelated invocation. -/
namespace Verification.ControlFlow.AssertionSlice

open CertificateProducer TolerantFrames.Target

def returnsTo (live : Nat → Bool) (k : Continuation) (handler : Option ControlFlow.Target) : Bool :=
  (successors k).any (fun t => live t.label) || handler.any (fun t => live t.label)

/-- Backwards closure from the asserted labels. The independent check below
validates the proposed set, so its precision only affects search. -/
def labels (P : Program) (asserted : List Nat) : List Nat := Id.run do
  let mut found := asserted.eraseDups
  for _ in List.range P.length do
    let more := P.zipIdx.filterMap fun (node,l) =>
      if !found.contains l && returnsTo found.contains node.continuation node.handler then some l else none
    if more.isEmpty then break
    found := more ++ found
  return found

def closed (P : Program) (live : Nat → Bool) : Bool :=
  P.zipIdx.all fun (node,l) => !returnsTo live node.continuation node.handler || live l

def project (P : Program) (live : Nat → Bool) (result : Tm) : Program :=
  P.map fun node => if returnsTo live node.continuation node.handler then node else ⟨result,.ret,none⟩

private def needed (live : Nat → Bool) : State → Bool
  | .at l _ => live l
  | .eval _ _ k x => returnsTo live k x
  | .done _ | .raised _ => false

private theorem edge {P live result h a h' b} (hc : closed P live = true)
    (s : Transition P h a h' b) (dst : needed live b = true) :
    needed live a = true ∧ Transition (project P live result) h a h' b := by
  cases s with
  | enter atNode =>
    have member := List.mk_mem_zipIdx_iff_getElem?.mpr atNode
    have checked := List.all_eq_true.mp hc _ member
    simp only [needed] at dst ⊢
    refine ⟨?_,.enter (by simp [project,List.getElem?_map,atNode,dst])⟩
    simpa [dst] using checked
  | expr s => exact ⟨dst,.expr s⟩
  | ret _ | raise _ => contradiction
  | bind hv => exact ⟨by simp_all [needed,returnsTo,successors],.bind hv⟩
  | effect hv => exact ⟨by simp_all [needed,returnsTo,successors],.effect hv⟩
  | yes => exact ⟨by simp_all [needed,returnsTo,successors],.yes⟩
  | no => exact ⟨by simp_all [needed,returnsTo,successors],.no⟩
  | yesBind => exact ⟨by simp_all [needed,returnsTo,successors],.yesBind⟩
  | noBind => exact ⟨by simp_all [needed,returnsTo,successors],.noBind⟩
  | tagBind hv =>
    simp only [needed] at dst
    split at dst <;> exact ⟨by simp_all [needed,returnsTo,successors],.tagBind hv⟩
  | handle thrown => exact ⟨by simp_all [needed,returnsTo],.handle thrown⟩

theorem reaches {P live result j h a h' l ρ} (hc : closed P live = true)
    (run : ReachesIn P j h a h' (.at l ρ)) (hit : live l = true) :
    ReachesIn (project P live result) j h a h' (.at l ρ) := by
  have transport {j h a h' b} (r : ReachesIn P j h a h' b) (mem : needed live b = true) :
      needed live a = true ∧ ReachesIn (project P live result) j h a h' b := by
    induction r with
    | refl => exact ⟨mem,.refl⟩
    | step s _ ih =>
      obtain ⟨inNext,tail⟩ := ih mem
      obtain ⟨inStart,first⟩ := edge hc s inNext
      exact ⟨inStart,.step first tail⟩
  exact (transport run hit).2

end Verification.ControlFlow.AssertionSlice
