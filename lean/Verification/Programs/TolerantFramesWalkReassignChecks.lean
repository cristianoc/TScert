import Verification.Programs.TolerantFramesWalkReassign
import Verification.Programs.Parametricity

/-! # Tolerant frames: the pass's checks at a reassignment

The pass runs at `G`; `run_guarantee` asks for its walk predicates at
`reassign G η`. The proved checker's route (`Parametricity.accept_reassign`)
is followed for the pass's functions: each is the same function at the
reassigned graph with the reassigned image check, where its answers are
carried by `Answered.reassign`. Proved here: the footprint check, the
subtype search and its instance proposals, the answered subtype request,
the return check, an edge's store and the unit's entry check. -/
namespace Verification.TolerantFrames
open Verification PositiveGraphs PositiveRules PositiveCertificates ProgramTyping ProgramCertificates SinglePass CertificateProducer

section Checks
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (η : MixedAssignment ι)
  (images : InstanceImageCheck G)

omit [Hashable ι] [Instantiates ι] in
theorem footprintCheck_reassign (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (Φ : Footprints.Closed)
    (F : List Nat) (c : PointClaim ι) (node : ControlFlow.Node) (stepK : HeapKnowledge.Knowledge)
    (deriv : ProgramCertificates.Evidence ι) (liveHandler exc ret outFresh : Bool) :
    footprintCheck (reassign G η) (images.reassign η) codes sums Φ F c node stepK deriv liveHandler exc ret outFresh =
      footprintCheck G images codes sums Φ F c node stepK deriv liveHandler exc ret outFresh := by
  simp only [footprintCheck, Parametricity.checkTree_reassign, Parametricity.requiresTree_reassign]
  rfl

omit [Hashable ι] [Instantiates ι] in
theorem searching_reassign : (images.reassign η).searching = images.searching.reassign η := rfl

theorem unifiedInstance_reassign (sub : Option (Renaming G)) (s : SchemeRow ι) (L : PositiveRules.Ops ι)
    (M : List (CallEffects.RestArrow (List ι))) :
    unifiedInstance (reassign G η) (sub.map (·.reassign η)) s L M = unifiedInstance G sub s L M := by
  cases sub <;> rfl

omit [Hashable ι] [Instantiates ι] in
theorem searchReads_reassign (S : List ι) : searchReads (reassign G η) S = searchReads G S := rfl

omit [Hashable ι] [Instantiates ι] in
theorem searchFree_reassign (D : List ι) : searchFree (reassign G η) D = searchFree G D := by
  unfold searchFree
  rw [freeMapOf_reassign]

omit [Hashable ι] in
theorem matchRow_reassign (bs : List ι) (V : FreeMap ι) (fuel : Nat) :
    matchRow (reassign G η) bs V fuel = matchRow G bs V fuel := by
  induction fuel with
  | zero => funext st κ S T; rfl
  | succ n ih =>
    funext st κ S T
    rw [matchRow.eq_def, matchRow.eq_def]
    dsimp only
    rw [ih]
    rfl

omit [Hashable ι] in
theorem matchSig_reassign (bs : List ι) (V : FreeMap ι) (fuel : Nat) :
    matchSig (reassign G η) bs V fuel = matchSig G bs V fuel := by
  funext st κ p q
  unfold matchSig
  rw [matchRow_reassign]
  rfl

omit [Hashable ι] in
theorem matchRest_reassign (bs : List ι) (V : FreeMap ι) (fuel : Nat) :
    matchRest (reassign G η) bs V fuel = matchRest G bs V fuel := by
  funext st κ p q
  unfold matchRest
  rw [matchRow_reassign]
  rfl

theorem matchedInstance_reassign (fuel : Nat) (s : SchemeRow ι) (L : PositiveRules.Ops ι)
    (M : List (CallEffects.RestArrow (List ι))) :
    matchedInstance (reassign G η) fuel s L M = matchedInstance G fuel s L M := by
  unfold matchedInstance
  simp only [searchReads_reassign, searchFree_reassign, matchSig_reassign, matchRest_reassign]
  rfl

theorem instantiationUsing_reassign (fuel : Nat) :
    instantiationUsing (reassign G η) (images.reassign η) fuel = instantiationUsing G images fuel := by
  funext A B
  unfold instantiationUsing instanceProposals
  show (match A, PositiveCertificates.instanceTarget G B with
    | [i], some (L, M, _) => match G.schemes i with
      | some s => ((unifiedInstance (reassign G η) (images.sub.map fun (r : Renaming G) => r.reassign η) s L M).toList.map
          fun c => Thunk.pure (some c)) ++ [Thunk.mk fun _ => matchedInstance (reassign G η) fuel s L M]
      | none => []
    | _, _ => []) = _
  simp only [unifiedInstance_reassign, matchedInstance_reassign]
  rfl

theorem instanceCandidates_reassign (sub : Option (Renaming G)) (fuel : Nat) (s : SchemeRow ι)
    (L : PositiveRules.Ops ι) (M : List (CallEffects.RestArrow (List ι))) :
    instanceCandidates (reassign G η) (sub.map fun (r : Renaming G) => r.reassign η) fuel s L M =
      instanceCandidates G sub fuel s L M := by
  unfold instanceCandidates
  rw [unifiedInstance_reassign, matchedInstance_reassign]

theorem rowInstances_reassign (fuel : Nat) :
    rowInstances (reassign G η) (images.reassign η) fuel = rowInstances G images fuel := by
  funext table
  unfold rowInstances
  simp only [InstanceImageCheck.reassign]
  cases hs : images.sub with
  | none =>
    have h := instanceCandidates_reassign G η none fuel
    simp only [Option.map_none] at h
    simp only [Option.map_none, h]
    rfl
  | some r =>
    have h := instanceCandidates_reassign G η (some r) fuel
    simp only [Option.map_some] at h
    simp only [Option.map_some, h]
    rfl

theorem subtypeSearch_reassign (A B : Ty ι) :
    subtypeSearch (reassign G η) (images.reassign η) A B = subtypeSearch G images A B := by
  unfold subtypeSearch comparisonUsing
  rw [searching_reassign, instantiationUsing_reassign, rowInstances_reassign, Parametricity.compareUsing_reassign]
  rfl

/-- **A subtype request at a reassigned graph**: the same result, the
answers reassigned (`Answered.reassign`). -/
theorem subtypeUsing_reassign (A B : Ty ι) (s : Answered G) :
    subtypeUsing (reassign G η) (images.reassign η) A B (Answered.reassign s η) =
      ((subtypeUsing G images A B s).1, Answered.reassign (subtypeUsing G images A B s).2 η) := by
  unfold subtypeUsing
  simp only [Answered.reassign, subtypeSearch_reassign]
  split <;> rename_i h
  · rfl
  · split <;> rfl

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- A left fold commuting with a map of its state. -/
theorem foldl_map_state {α β γ : Type} (g : β → γ) (f : β → α → β) (f' : γ → α → γ)
    (h : ∀ b a, f' (g b) a = g (f b a)) (l : List α) (b : β) : l.foldl f' (g b) = g (l.foldl f b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp only [List.foldl, h, ih]

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
theorem emptyType_reassign : ExpressionEffects.emptyType (reassign G η) = ExpressionEffects.emptyType G := rfl

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
theorem typeSets_reassign : HeapKnowledge.typeSets (reassign G η) = HeapKnowledge.typeSets G := rfl

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
theorem onlyBoolean_reassign : BranchRefinement.onlyBoolean (reassign G η) = BranchRefinement.onlyBoolean G := rfl

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
theorem onlyUndef_reassign : PromiseCalls.onlyUndef (reassign G η) = PromiseCalls.onlyUndef G := rfl

omit [Hashable ι] [Instantiates ι] in
theorem impossible_reassign : BranchRefinement.impossible (reassign G η) = BranchRefinement.impossible G := rfl

theorem returnCheck_reassign (goal : ControlFlow.Goal ι) (ensures : List HeapKnowledge.IndexFact) (c : PointClaim ι)
    (l : Nat) (entry : SinglePass.State) (store : Store) (result start : Nat) (startNames : List Nat)
    (argName : Option Nat) (yields : List (PromiseCalls.Yield ι)) (debugNode : Nat) (answers : Answered G) :
    returnCheck (reassign G η) (images.reassign η) goal ensures c l entry store result start startNames argName yields
        debugNode (Answered.reassign answers η) =
      let r := returnCheck G images goal ensures c l entry store result start startNames argName yields debugNode answers
      (r.1, Answered.reassign r.2.1 η, r.2.2) := by
  unfold returnCheck
  rw [emptyType_reassign, typeSets_reassign, onlyBoolean_reassign, onlyUndef_reassign,
    impossible_reassign, Parametricity.refineBy_reassign]
  dsimp only
  split
  · rename_i h
    rw [h]
  · rename_i hne
    have key : ∀ (b : Bool) (a : Answered G),
        (fun (p : Bool × Answered G) => (p.1, Answered.reassign p.2 η)) (b, a) = (b, Answered.reassign a η) :=
      fun _ _ => rfl
    cases goal with
    | plain R =>
      dsimp only
      all_goals split <;> first | rfl | (rename_i h; exact absurd h (hne _ _))
    | guards T _ =>
      dsimp only
      rw [← key, foldl_map_state (fun (p : Bool × Answered G) => (p.1, Answered.reassign p.2 η))]
      · intro ⟨b, a⟩ p
        dsimp only
        split
        · rfl
        · split
          · simp only [subtypeUsing_reassign]
          · rfl
    | asserts T _ =>
      dsimp only
      rw [← key, foldl_map_state (fun (p : Bool × Answered G) => (p.1, Answered.reassign p.2 η))]
      · intro ⟨b, a⟩ p
        dsimp only
        split
        · rfl
        · split
          · simp only [subtypeUsing_reassign]
          · rfl

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- An edge's store reads the graph through its rows only. -/
theorem edgeStoreOf_reassign (Γ : List (Ty ι)) (entryStore store : Store) (names pushedNames : List Nat)
    (width : Nat) (pushed isHandler : Bool) (observed : Option BranchRefinement.Observation) (promote : Option Bool) :
    edgeStoreOf (reassign G η) Γ entryStore store names pushedNames width pushed isHandler observed promote =
      edgeStoreOf G Γ entryStore store names pushedNames width pushed isHandler observed promote := rfl

omit [Hashable ι] [Instantiates ι] in
/-- The unit's entry check at a reassigned graph. -/
theorem entryRefusal_reassign (inputs : List (Ty ι)) (claims : List (PointClaim ι)) (start : Nat)
    (goal : ControlFlow.Goal ι) (written : Option HeapKnowledge.Knowledge) (supplied : List HeapKnowledge.IndexAtom)
    (givenImplies : List (PromiseCalls.Implication ι)) (givenArgs : List Nat) (givenInputs : List (Nat × Nat))
    (entryIndices : List HeapKnowledge.IndexAtom) (entrySeparation : HeapSeparation.Separation) :
    entryRefusal (reassign G η) inputs claims start goal written supplied givenImplies givenArgs givenInputs entryIndices
        entrySeparation =
      entryRefusal G inputs claims start goal written supplied givenImplies givenArgs givenInputs entryIndices
        entrySeparation := rfl

end Checks
end Verification.TolerantFrames
