import Verification.Programs.CertificateProducer

/-! # Graph evidence is parametric in the assignment

A graph's parameter rows mean what its assignment `env` gives them, and a
graph's `meaning` reads them there. No check reads `env`: every checker reads a
graph through its rows, schemes, parameter kinds and meets. This file proves
it for the whole graph checker, `CertificateProducer.acceptUsing`, with any
proved instance image checker: acceptance of a graph is acceptance of every
reassignment of it by the same checker (`accept_reassign`). The
safety theorem for accepted evidence then holds at every assignment
(`accepted_at`), so a body checked once with its type parameters as opaque
parameter rows is safe at every instantiation of them.

Most checkers are definitionally independent of `env`; the lemmas below are
for the ones whose unfolding the kernel does not do on its own: the recursive
checkers, the inductive subtyping judgment, and the checkers built on them. -/
namespace Verification.Parametricity
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ProgramCertificates
  PositiveCertificates PointClaims BranchRefinement HeapExpressionRules ControlFlow

variable {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)

omit [DecidableEq ι] in

omit [DecidableEq ι] in

theorem expand_reassign (F : List ι) : expand (reassign G η) F = expand G F := rfl

/-- Fixing the assignment erases an earlier reassignment of image metadata. -/
theorem images_reassign_fixed (images : InstanceImageCheck G) :
    (images.reassign η).reassign (ParameterAssignment.empty .mixed) =
      images.reassign (ParameterAssignment.empty .mixed) := by
  cases hs : images.sub <;>
    simp only [InstanceImageCheck.reassign, hs, Option.map_none, Option.map_some] <;> rfl

/-- Reassigning parameter meanings preserves execution policy. -/
theorem budget_reassign (images : InstanceImageCheck G) :
    (images.reassign η).budget = images.budget := rfl

/-- Reassigning parameter meanings preserves the proved inclusions. -/
theorem known_reassign (images : InstanceImageCheck G) :
    (images.reassign η).known = images.known := rfl

/-! Every checker below takes a proved instance image checker. Its check is
the same function at every reassignment (`InstanceImageCheck.reassign`). -/
variable (images : InstanceImageCheck G)

theorem proposal_reassign (S T : List ι) (p : SubtypeChoices ι) :
    p.proposal (reassign G η) S T = p.proposal G S T := rfl

theorem compareUsingCore_reassign (instantiation : List ι → List ι → Proposals ι)
    (members : Table ι → List (KnownInstance ι)) (depth : Nat) (path : Table ι) (S T : List ι) :
    compareUsingCore (reassign G η) (images.reassign η) instantiation members depth path S T =
      compareUsingCore G images instantiation members depth path S T := by
  unfold compareUsingCore
  dsimp only
  rw [images_reassign_fixed]
  rfl

theorem compareUsing_reassign (S T : List ι) (instantiation : List ι → List ι → Proposals ι)
    (members : Table ι → List (KnownInstance ι)) :
    compareUsing (reassign G η) (images.reassign η) S T instantiation members =
      compareUsing G images S T instantiation members := by
  simp only [compareUsing, budget_reassign, known_reassign, compareUsingCore_reassign]

theorem check_reassign (S T : List ι) (p : SubtypeChoices ι) :
    PositiveCertificates.checkUsing (reassign G η) (images.reassign η) S T p =
      PositiveCertificates.checkUsing G images S T p := by
  simp only [PositiveCertificates.checkUsing, proposal_reassign, compareUsing_reassign]

/-- The subtype checker as a function of its graph. -/
theorem check_fun_reassign :
    PositiveCertificates.checkUsing (reassign G η) (images.reassign η) =
      PositiveCertificates.checkUsing G images := by
  funext S T p; exact check_reassign G η images S T p

theorem checkEdge_reassign (Γ Δ : List (List ι)) (ps : EdgeEvidence ι) :
    checkEdgeUsing (reassign G η) (images.reassign η) Γ Δ ps = checkEdgeUsing G images Γ Δ ps := by
  induction ps generalizing Γ Δ with
  | nil => cases Γ <;> cases Δ <;> rfl
  | cons p ps ih =>
    cases Γ <;> cases Δ <;>
      rw [checkEdgeUsing_eq (reassign G η) (images.reassign η), checkEdgeUsing_eq G images] <;>
      simp only [check_reassign, ih]

theorem checkMapped_reassign (Γ Δ : List (List ι)) (m : Mapping) (ps : EdgeEvidence ι) :
    checkMappedUsing (reassign G η) (images.reassign η) Γ Δ m ps =
      checkMappedUsing G images Γ Δ m ps := by
  cases m <;> simp only [checkMappedUsing_eq, checkEdge_reassign, check_fun_reassign]

theorem allocBuiltins_reassign (parts : List (PropKey × List ι)) :
    allocBuiltins (reassign G η) parts = allocBuiltins G parts := by
  unfold allocBuiltins
  simp only [builtinsFree_reassign]
  rfl

theorem allocBuiltinsUsing_reassign (parts : List (PropKey × List ι)) :
    allocBuiltinsUsing (images.reassign η) parts = allocBuiltinsUsing images parts := by
  unfold allocBuiltinsUsing
  rfl

theorem builtinArrayLabel_reassign :
    BranchRefinement.builtinArrayLabel (reassign G η) = BranchRefinement.builtinArrayLabel G := by
  funext L
  unfold BranchRefinement.builtinArrayLabel
  simp only [builtinsFree_reassign]
  rfl

theorem arraySlice_reassign (A B : List ι) :
    BranchRefinement.arraySlice (reassign G η) A B = BranchRefinement.arraySlice G A B := by
  unfold BranchRefinement.arraySlice
  simp only [builtinArrayLabel_reassign]
  rfl

theorem checkObservedSub_reassign (A B : List ι) (o : Observation) (p : SubtypeChoices ι) :
    checkObservedSubUsing (reassign G η) (images.reassign η) A B o p =
      checkObservedSubUsing G images A B o p := by
  cases o <;> simp only [checkObservedSubUsing_eq, check_reassign, arraySlice_reassign] <;> rfl

theorem fieldRefinements_reassign (o : Observation) (fields : List (Nat × PropKey)) (A B : List ι)
    (j : Nat) (p : SubtypeChoices ι) :
    fieldRefinements o fields A B j (reassign G η) (images.reassign η) p =
      fieldRefinements o fields A B j G images p := by
  cases o <;> simp only [fieldRefinements_eq, check_fun_reassign] <;> rfl

theorem optionalRefinements_reassign (o : Observation) (optionals : List (Nat × PropKey)) (A B : List ι)
    (j : Nat) :
    optionalRefinements o optionals A B j (reassign G η) = optionalRefinements o optionals A B j G := rfl

theorem presentRefinements_reassign (o : Observation) (optionals : List (Nat × PropKey)) (A B : List ι)
    (j : Nat) (p : SubtypeChoices ι) :
    presentRefinements o optionals A B j (reassign G η) (images.reassign η) p =
      presentRefinements o optionals A B j G images p := by
  cases o <;> simp only [presentRefinements_eq, check_fun_reassign] <;> rfl

theorem cellRefinements_reassign (cells : HeapFacts.Facts) (A B : List ι) (j : Nat) (p : SubtypeChoices ι) :
    cellRefinements cells A B j (reassign G η) (images.reassign η) p =
      cellRefinements cells A B j G images p := by
  simp only [cellRefinements_eq, check_fun_reassign]
  rfl

theorem checkObserved_reassign (Γ Δ : List (List ι)) (tested : Nat) (o : Observation)
    (m : Mapping) (ps : EdgeEvidence ι) (fields optionals : List (Nat × PropKey)) (cells : HeapFacts.Facts) :
    checkObservedUsing (reassign G η) (images.reassign η) Γ Δ tested o m ps fields optionals cells =
      checkObservedUsing G images Γ Δ tested o m ps fields optionals cells := by
  simp only [checkObservedUsing_eq, checkObservedSub_reassign, check_fun_reassign,
    fieldRefinements_reassign, optionalRefinements_reassign, presentRefinements_reassign, cellRefinements_reassign]
  rfl

theorem CallProofs_reassign (q : CallEffects.Arrow (List ι)) (c : CallEffects.MethodArrow (List ι))
    (ps : List (SubtypeChoices ι) × SubtypeChoices ι) :
    CallProofsUsing (reassign G η) (images.reassign η) q c ps = CallProofsUsing G images q c ps := by
  simp only [CallProofsUsing, check_reassign]

theorem RestProofs_reassign (q : CallEffects.RestArrow (List ι)) (c : CallEffects.MethodRestArrow (List ι))
    (ps : List (SubtypeChoices ι) × SubtypeChoices ι × SubtypeChoices ι) :
    RestProofsUsing (reassign G η) (images.reassign η) q c ps = RestProofsUsing G images q c ps := by
  simp only [RestProofsUsing, check_reassign]

/-- A generic closure's capture check reads the graph's rows only. -/
theorem capturesFree_reassign (s : SchemeRow ι) (Cs : List (List ι)) :
    capturesFree (reassign G η) s Cs = capturesFree G s Cs := by
  simp only [capturesFree, captureDomain, captureFree, readsFrom_reassign, freeMapOf_reassign]
  rfl

theorem graphCodesChecked_reassign (A : List ι) (codes : CodeEntry ι → Bool) (kind : Invoke) (arity : Nat)
    (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (List ι)) :
    graphCodesChecked (reassign G η) A codes kind arity E K start Cs =
      graphCodesChecked G A codes kind arity E K start Cs := by
  unfold graphCodesChecked
  simp only [capturesFree_reassign]
  rfl

theorem Local_reassign (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι))
    (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) :
    LocalUsing (reassign G η) (images.reassign η) j r ps codes (sums := sums) =
      LocalUsing G images j r ps codes (sums := sums) := by
  unfold LocalUsing MemberProofsUsing
  simp (config := { iota := false }) only [check_fun_reassign, CallProofs_reassign, RestProofs_reassign, graphCodesChecked_reassign,
    allocBuiltinsUsing_reassign]
  rfl

theorem LocalRequires_reassign (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι))
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (allow : Bool) :
    LocalUsing (reassign G η) (images.reassign η) j r ps codes (sums := sums) (allowRequires := allow) =
      LocalUsing G images j r ps codes (sums := sums) (allowRequires := allow) := by
  unfold LocalUsing MemberProofsUsing
  simp (config := { iota := false }) only [check_fun_reassign, CallProofs_reassign, RestProofs_reassign, graphCodesChecked_reassign,
    allocBuiltinsUsing_reassign]
  rfl

/-- A body's explicit subsumption procedure is held fixed while its
semantic assignment changes. Its soundness is supplied at that assignment. -/
theorem LocalWith_reassign (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι))
    (codes : CodeEntry ι → Bool)
    (subtype : Ty ι → Ty ι → SubtypeChoices ι → Bool) (sums : List (ReadSummary ι)) :
    LocalUsing (reassign G η) (images.reassign η) j r ps codes subtype sums =
      LocalUsing G images j r ps codes subtype sums := by
  unfold LocalUsing MemberProofsUsing
  simp (config := { iota := false }) only [check_fun_reassign, CallProofs_reassign, RestProofs_reassign,
    graphCodesChecked_reassign, allocBuiltinsUsing_reassign]
  rfl

theorem checkTreeWith_reassign
    (subtype : Ty ι → Ty ι → SubtypeChoices ι → Bool)
    (e : ProgramCertificates.Evidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    checkTreeWith (reassign G η) (images.reassign η) subtype e codes sums =
      checkTreeWith G images subtype e codes sums := by
  match e with
  | .node j r ps =>
    rw [checkTreeWith, checkTreeWith]
    simp only [LocalWith_reassign]
    congr 1
    congr 1
    funext x
    exact checkTreeWith_reassign subtype x.val codes sums
termination_by sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem x.property
  simp only [ProgramCertificates.Evidence.node.sizeOf_spec]
  omega

theorem checkTree_reassign (e : ProgramCertificates.Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) :
    checkTreeUsing (reassign G η) (images.reassign η) e codes sums = checkTreeUsing G images e codes sums := by
  match e with
  | .node j r ps =>
    rw [checkTreeUsing_eq, checkTreeUsing_eq]
    simp only [Local_reassign]
    congr 1
    congr 1
    funext x
    exact checkTree_reassign x.val codes sums
termination_by sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem x.property
  simp only [ProgramCertificates.Evidence.node.sizeOf_spec]
  omega

/-- A read summary's check reads the graph through its rows and the image
check through its comparison only: it is the same check at every
reassignment (`readSummary_reassign`). -/
theorem checkReadSummary_reassign (s : ReadSummary ι) :
    checkReadSummary (reassign G η) (images.reassign η) s = checkReadSummary G images s := by
  simp only [checkReadSummary_eq, check_reassign]
  rfl

/-- **Summaries transport.** A table checked at the graph is sound at every
reassignment of its parameter rows, with the reassigned image check. -/
theorem summariesSound_reassign {sums : List (ReadSummary ι)} (h : SummariesSound G images sums) :
    SummariesSound (reassign G η) (images.reassign η) sums := fun s hs =>
  (checkReadSummary_reassign G η images s).trans (h s hs)

theorem checkStep_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) :
    checkStepUsing (reassign G η) (images.reassign η) j k e codes sums = checkStepUsing G images j k e codes sums := by
  cases e <;> simp only [checkStepUsing_eq, checkTree_reassign, checkObservedSub_reassign, check_reassign] <;> rfl

theorem carries_reassign (Γ : List (List ι)) (facts : HeapKnowledge.Knowledge) (xs : List (PromiseCalls.Implication ι))
    (sources : List Nat) (t : Target) (c : NodeEvidence ι) :
    carries (reassign G η) Γ facts xs sources t c = carries G Γ facts xs sources t c := rfl

omit [DecidableEq ι] in
theorem unsatisfiable_reassign (Γ : List (List ι)) :
    unsatisfiable (reassign G η) Γ = unsatisfiable G Γ := rfl

omit [DecidableEq ι] in
theorem fieldSets_reassign : ∀ (Els : List (List ι)),
    HeapExpressionRules.fieldSets (reassign G η) Els = HeapExpressionRules.fieldSets G Els
  | [] => rfl
  | El :: rest => by
    simp only [HeapExpressionRules.fieldSets, fieldSets_reassign rest]
    rfl

theorem withTypedCells_reassign (Γ : List (List ι)) (k : HeapKnowledge.Knowledge) (m : Mapping)
    (facts : HeapKnowledge.Knowledge) :
    withTypedCells (reassign G η) Γ k m facts = withTypedCells G Γ k m facts := by
  simp only [withTypedCells, HeapExpressionRules.typedCells, HeapExpressionRules.typedFieldSet, expand_reassign,
    fieldSets_reassign]

theorem checkTarget_reassign (P : Program) (C : ControlFlow.Certificate ι) (Γ : List (List ι)) (t : Target)
    (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge) (xs : List (PromiseCalls.Implication ι))
    (sources : List Nat) :
    checkTargetUsing (reassign G η) (images.reassign η) P C Γ t p facts xs sources =
      checkTargetUsing G images P C Γ t p facts xs sources := by
  simp only [checkTargetUsing_eq, checkMapped_reassign, carries_reassign, unsatisfiable_reassign,
    withTypedCells_reassign]
  rfl

theorem checkBranchTarget_reassign (P : Program) (C : ControlFlow.Certificate ι) (Γ : List (List ι))
    (o : Observation) (t : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge)
    (xs : List (PromiseCalls.Implication ι)) (sources : List Nat) :
    checkBranchTargetUsing (reassign G η) (images.reassign η) P C Γ o t p facts xs sources =
      checkBranchTargetUsing G images P C Γ o t p facts xs sources := by
  simp only [checkBranchTargetUsing_eq, checkObserved_reassign, carries_reassign, unsatisfiable_reassign,
    withTypedCells_reassign]
  rfl

theorem fieldYield_reassign (Γ : List (List ι)) (links : HeapLinks.Links) (y : PromiseCalls.Yield ι)
    (i : Nat) (tag : Tag) (q : Bool) :
    PromiseCalls.fieldYield (reassign G η) (images.reassign η) Γ links y i tag q =
      PromiseCalls.fieldYield G images Γ links y i tag q := by
  unfold PromiseCalls.fieldYield
  simp only [check_fun_reassign]
  rfl

theorem memberYield_reassign (Γ : List (List ι)) (links : HeapLinks.Links) (y : PromiseCalls.Yield ι)
    (ts : List Tag) (i : Nat) :
    PromiseCalls.memberYield (reassign G η) (images.reassign η) Γ links y ts i =
      PromiseCalls.memberYield G images Γ links y ts i := by
  unfold PromiseCalls.memberYield
  simp only [check_fun_reassign]
  rfl

theorem memberFollows_reassign (Γ : List (List ι)) (links : HeapLinks.Links) (t : Tm) (y : PromiseCalls.Yield ι) :
    PromiseCalls.memberFollows (reassign G η) (images.reassign η) Γ links t y =
      PromiseCalls.memberFollows G images Γ links t y := by
  unfold PromiseCalls.memberFollows
  simp only [memberYield_reassign]

theorem yieldFollows_reassign (Γ : List (List ι)) (xs : List (PromiseCalls.Implication ι))
    (links : HeapLinks.Links) (t : Tm) :
    PromiseCalls.yieldFollows (reassign G η) (images.reassign η) Γ xs links t =
      PromiseCalls.yieldFollows G images Γ xs links t := by
  funext y
  unfold PromiseCalls.yieldFollows PromiseCalls.yieldFollows.observed
  simp only [checkObservedSub_reassign, fieldYield_reassign, memberFollows_reassign]

theorem promiseOf_reassign (e : ProgramCertificates.Evidence ι) :
    PromiseCalls.promiseOf (reassign G η) e = PromiseCalls.promiseOf G e := rfl

theorem checkYields_reassign (c : NodeEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    checkYields (reassign G η) (images.reassign η) c codes sums = checkYields G images c codes sums := by
  unfold checkYields
  rw [promiseOf_reassign, yieldFollows_reassign]
  simp only [checkTree_reassign]
  rfl

theorem refineBy_reassign : PromiseCalls.refineBy (reassign G η) = PromiseCalls.refineBy G := rfl

theorem checkReturn_reassign (goal : ControlFlow.Goal ι) (c : NodeEvidence ι) :
    (checkReturnResult (reassign G η) (images.reassign η) goal c).accepted =
      (checkReturnResult G images goal c).accepted := by
  have within : ∀ facts T, (checkReturnResult.argumentWithin (reassign G η) (images.reassign η) c facts T).accepted =
      (checkReturnResult.argumentWithin G images c facts T).accepted := by
    intro facts T
    unfold checkReturnResult.argumentWithin
    rw [refineBy_reassign]
    split
    · split
      · split
        · simp only [ProgramCertificates.checkSubtypeUsing_accepted, check_reassign]
        · rfl
      · rfl
    · rfl
  cases goal <;> simp only [checkReturnResult, CheckResult.accepted_bind, CheckResult.accepted_orElse,
    CheckResult.accepted_ofBool, within] <;> rfl

theorem checkHandler_reassign (P : Program) (C : ControlFlow.Certificate ι) (node : Node) (c : NodeEvidence ι) :
    checkHandlerUsing (reassign G η) (images.reassign η) P C node c =
      checkHandlerUsing G images P C node c := by
  simp only [checkHandlerUsing_eq, checkTarget_reassign]
  rfl

omit [DecidableEq ι] in
theorem withStable_reassign :
    HeapExpressionRules.withStable (reassign G η) = HeapExpressionRules.withStable G := rfl

theorem checkStepResult_value_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (checkStepResult (reassign G η) (images.reassign η) j k e codes sums).value =
      (checkStepResult G images j k e codes sums).value :=
  checkStep_reassign G η images j k e codes sums

/-- Descriptor evidence may vary with the assignment while the executable
body comparison stays fixed. -/
theorem checkBodyStep_reassign (body : BodySubtyping G)
    (body' : BodySubtyping (reassign G η)) (same : body'.check = body.check)
    (ord : ∀ {A B p}, checkUsing G images A B p = true → body.check A B p = true)
    (ord' : ∀ {A B p}, checkUsing (reassign G η) (images.reassign η) A B p = true → body'.check A B p = true)
    (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    ((Checker.withSubtyping (reassign G η) (images.reassign η) body' ord').run j k e codes sums).value =
      ((Checker.withSubtyping G images body ord).run j k e codes sums).value := by
  simp only [Checker.withSubtyping, Checker.keepingStable, CheckResult.map, withStable_reassign]
  congr 1
  cases e <;> simp only [Checker.subtypingSteps, CheckResult.value_bind_const,
    CheckResult.accepted_ofBool, same, checkTreeWith_reassign,
    checkStepResult_value_reassign] <;> rfl

theorem checkBodyNode_reassign (body : BodySubtyping G)
    (body' : BodySubtyping (reassign G η)) (same : body'.check = body.check)
    (ord : ∀ {A B p}, checkUsing G images A B p = true → body.check A B p = true)
    (ord' : ∀ {A B p}, checkUsing (reassign G η) (images.reassign η) A B p = true → body'.check A B p = true)
    (Rty : ControlFlow.Goal ι) (P : Program) (C : ControlFlow.Certificate ι) (node : Node)
    (c : NodeEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    checkNodeUsing (reassign G η) (images.reassign η) Rty P C node c codes
      (Checker.withSubtyping (reassign G η) (images.reassign η) body' ord') sums =
    checkNodeUsing G images Rty P C node c codes (Checker.withSubtyping G images body ord) sums := by
  simp only [checkNodeUsing_eq, checkBodyStep_reassign G η images body body' same ord ord',
    checkHandler_reassign, checkTarget_reassign, checkBranchTarget_reassign, checkYields_reassign,
    checkReturn_reassign]
  rfl

theorem checkBodyGraph_reassign (body : BodySubtyping G)
    (body' : BodySubtyping (reassign G η)) (same : body'.check = body.check)
    (ord : ∀ {A B p}, checkUsing G images A B p = true → body.check A B p = true)
    (ord' : ∀ {A B p}, checkUsing (reassign G η) (images.reassign η) A B p = true → body'.check A B p = true)
    (Rty : ControlFlow.Goal ι) (P : Program) (C : ControlFlow.Certificate ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    checkGraphUsing (reassign G η) (images.reassign η) Rty P C codes
      (Checker.withSubtyping (reassign G η) (images.reassign η) body' ord') sums =
    checkGraphUsing G images Rty P C codes (Checker.withSubtyping G images body ord) sums := by
  simp only [checkGraphUsing_eq, checkBodyNode_reassign G η images body body' same ord ord']

theorem checkBodyEntry_reassign (body : BodySubtyping G)
    (body' : BodySubtyping (reassign G η)) (same : body'.check = body.check)
    (ord : ∀ {A B p}, checkUsing G images A B p = true → body.check A B p = true)
    (ord' : ∀ {A B p}, checkUsing (reassign G η) (images.reassign η) A B p = true → body'.check A B p = true)
    (Rty : ControlFlow.Goal ι) (P : Program) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (List ι)) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    checkEntryUsing (reassign G η) (images.reassign η) Rty P C start inputs codes
      (Checker.withSubtyping (reassign G η) (images.reassign η) body' ord') sums =
    checkEntryUsing G images Rty P C start inputs codes (Checker.withSubtyping G images body ord) sums := by
  simp only [checkEntryUsing_eq, checkBodyGraph_reassign G η images body body' same ord ord']

theorem keepsCall_reassign (j : Sequent ι) (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    PromiseCalls.keepsCall (reassign G η) (images.reassign η) j e codes sums =
      PromiseCalls.keepsCall G images j e codes sums := by
  unfold PromiseCalls.keepsCall
  split
  · rename_i p
    rw [promiseOf_reassign]
    congr 1
    exact checkTree_reassign G η images p codes sums
  · rfl

theorem keepingCalls_value_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    ((Checker.steps (reassign G η) (images.reassign η)).keepingCalls.run j k e codes sums).value =
      ((Checker.steps G images).keepingCalls.run j k e codes sums).value := by
  simp only [Checker.keepingCalls, keepsCall_reassign]
  split
  · rfl
  · exact checkStepResult_value_reassign G η images j k e codes sums

theorem freshCall_reassign (j : Sequent ι) (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    PromiseCalls.freshCall (reassign G η) (images.reassign η) j e codes sums =
      PromiseCalls.freshCall G images j e codes sums := by
  unfold PromiseCalls.freshCall
  split
  · rename_i p
    rw [checkTree_reassign G η images p codes sums]
  · rfl

theorem ownCallChecked_reassign (j : Sequent ι) (e : StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) :
    PromiseCalls.ownCallChecked (reassign G η) (images.reassign η) j e codes sums =
      PromiseCalls.ownCallChecked G images j e codes sums := by
  unfold PromiseCalls.ownCallChecked
  split
  · rename_i p
    rw [checkTree_reassign G η images p codes sums]
  · rfl

theorem ownCall_reassign (j : Sequent ι) (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    PromiseCalls.ownCall (reassign G η) (images.reassign η) j e codes sums =
      PromiseCalls.ownCall G images j e codes sums := by
  simp only [PromiseCalls.ownCall, ownCallChecked_reassign]

theorem keepingOwnCalls_value_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    ((Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.run j k e codes sums).value =
      ((Checker.steps G images).keepingCalls.keepingOwnCalls.run j k e codes sums).value := by
  simp only [Checker.keepingOwnCalls, ownCall_reassign]
  split
  · rfl
  · exact keepingCalls_value_reassign G η images j k e codes sums

theorem allocatingCalls_value_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    ((Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.run j k e codes sums).value =
      ((Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.run j k e codes sums).value := by
  simp only [Checker.allocatingCalls, freshCall_reassign]
  split
  · rfl
  · exact keepingOwnCalls_value_reassign G η images j k e codes sums

theorem elementsCall_reassign (j : Sequent ι) (e : StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) :
    PromiseCalls.elementsCall (reassign G η) (images.reassign η) j e codes sums =
      PromiseCalls.elementsCall G images j e codes sums := by
  unfold PromiseCalls.elementsCall
  split
  · rename_i p _
    rw [checkTree_reassign G η images p codes sums]
    rfl
  · rfl

theorem requiresApp_reassign (k : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (p : ProgramCertificates.Evidence ι) :
    PromiseCalls.requiresApp (reassign G η) (images.reassign η) k codes sums p =
      PromiseCalls.requiresApp G images k codes sums p := by
  unfold PromiseCalls.requiresApp
  split
  · simp only [LocalRequires_reassign, checkTree_reassign]
  · rfl

theorem requiresTree_reassign (k : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (p : ProgramCertificates.Evidence ι) :
    PromiseCalls.requiresTree (reassign G η) (images.reassign η) k codes sums p =
      PromiseCalls.requiresTree G images k codes sums p := by
  unfold PromiseCalls.requiresTree
  split
  · simp only [Local_reassign, requiresApp_reassign]
  · exact requiresApp_reassign G η images k codes sums _

theorem requiresCall_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    PromiseCalls.requiresCall (reassign G η) (images.reassign η) j k e codes sums =
      PromiseCalls.requiresCall G images j k e codes sums := by
  unfold PromiseCalls.requiresCall
  split
  · rename_i p
    rw [requiresTree_reassign]
  · rfl

theorem requiringCalls_value_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    ((Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.run
        j k e codes sums).value =
      ((Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.run j k e codes sums).value := by
  simp only [Checker.requiringCalls, requiresCall_reassign]
  split
  · rfl
  · exact allocatingCalls_value_reassign G η images j k e codes sums

theorem elementCalls_value_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    ((Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.run
        j k e codes sums).value =
      ((Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.run
        j k e codes sums).value := by
  simp only [Checker.elementCalls, elementsCall_reassign]
  split
  · rfl
  · exact requiringCalls_value_reassign G η images j k e codes sums

theorem negatingSlots_value_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    ((Checker.steps (reassign G η) (images.reassign η)).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.negatingSlots.run
        j k e codes sums).value =
      ((Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.negatingSlots.run
        j k e codes sums).value := by
  simp only [Checker.negatingSlots]
  split
  · simp only [CheckResult.map]
    rw [elementCalls_value_reassign]
  · exact elementCalls_value_reassign G η images j k e codes sums

theorem checkNode_reassign (Rty : ControlFlow.Goal ι) (P : Program) (C : ControlFlow.Certificate ι) (node : Node)
    (c : NodeEvidence ι) (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) :
    checkNodeUsing (sums := sums) (reassign G η) (images.reassign η) Rty P C node c codes =
      checkNodeUsing (sums := sums) G images Rty P C node c codes := by
  simp only [checkNodeUsing_eq, Checker.ordinary, Checker.keepingStable, CheckResult.map,
    withStable_reassign, checkHandler_reassign, negatingSlots_value_reassign, checkTarget_reassign,
    checkBranchTarget_reassign, checkYields_reassign, checkReturn_reassign]
  rfl

theorem checkGraph_reassign (Rty : ControlFlow.Goal ι) (P : Program) (C : ControlFlow.Certificate ι)
    (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) :
    checkGraphUsing (sums := sums) (reassign G η) (images.reassign η) Rty P C codes =
      checkGraphUsing (sums := sums) G images Rty P C codes := by
  simp only [checkGraphUsing_eq, checkNode_reassign]

theorem checkEntry_reassign (Rty : ControlFlow.Goal ι) (P : Program) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (List ι)) (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) :
    checkEntryUsing (sums := sums) (reassign G η) (images.reassign η) Rty P C start inputs codes =
      checkEntryUsing (sums := sums) G images Rty P C start inputs codes := by
  simp only [checkEntryUsing_eq, checkGraph_reassign]

/-- **Acceptance reads no assignment.** A graph's evidence is accepted exactly
when it is accepted for every reassignment of the graph's parameter rows, by
the same image checker. -/
theorem accept_reassign (R : ControlFlow.Goal ι) (P : Program) (claims : List (CertificateProducer.PointClaim ι))
    (C : ControlFlow.Certificate ι) (start : Nat) (inputs : List (List ι))
    (codes : CodeEntry ι → Bool := fun _ => false) (sums : List (ReadSummary ι) := []) :
    CertificateProducer.acceptUsing (sums := sums) (reassign G η) (images.reassign η) R P claims C start inputs codes =
      CertificateProducer.acceptUsing (sums := sums) G images R P claims C start inputs codes := by
  simp only [CertificateProducer.acceptUsing_eq, checkEntry_reassign]

/-- **Parametricity.** Accepted evidence is safe at every assignment of the
graph's parameter rows: every input environment meeting the inputs read at
`η` runs safely to a result of the result type read at `η`. -/
theorem accepted_at {G : NormalGraph ι} {images : InstanceImageCheck G} {R : ControlFlow.Goal ι} {P claims C start inputs}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : CertificateProducer.acceptUsing (sums := sums) G images R P claims C start inputs codes = true)
    (η : MixedAssignment ι) (n W h ρ)
    (he : EnvOk (reassign G η) inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hcodes : CodesSound (reassign G η) codes := by exact Verification.ProgramCertificates.codesSound_none _)
    (hsums : SummariesSound G images sums := by exact Verification.ProgramCertificates.summariesSound_none _ _) :
    SafeGraph (excOf (reassign G η)) P (ControlFlow.GoalHolds (reassign G η) R (R.argument ρ)) n W h (.at start ρ) := by
  have hc' := (accept_reassign G η images R P claims C start inputs codes sums).trans hc
  simp only [CertificateProducer.acceptUsing_eq, Bool.and_eq_true] at hc'
  exact ControlFlow.accepted_inputs_safe hc'.2 n W h ρ he hw hh hcodes (summariesSound_reassign G η images hsums)

end Verification.Parametricity
