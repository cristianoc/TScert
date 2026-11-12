import Verification.Programs.TolerantFramesExitTypeChecks

/-! # Checks on exits into given heads

The implication search retains a witness for each required implication.
A successful nonvacuous head check establishes its input slots, argument
slots and heap query at the context it reads.
-/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules LabelStore

section Checks
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- A successful implication lookup retains a carried implication with
an equal type or an accepted subtype answer. -/
theorem impliesHeld_checked {x : PromiseCalls.Implication ι} {held : List (PromiseCalls.Implication ι)}
    {answers : Answered G} (h : (impliesHeld G I x held answers).1 = true) :
    ∃ y ∈ held, y.type = x.type ∨ ∃ a, ((subtypeUsing G I y.type x.type a).1).value.isSome = true := by
  have hi : ∀ acc : Bool × Answered G, acc = (false, answers) →
      acc.1 = true → ∃ y ∈ held, y.type = x.type ∨
        ∃ a, ((subtypeUsing G I y.type x.type a).1).value.isSome = true := by
    intro acc ha ht
    cases ha
    cases ht
  unfold impliesHeld at h
  let step := fun (acc : Bool × Answered G) (y : PromiseCalls.Implication ι) =>
    if acc.1 then acc else if same y.type x.type then (true, acc.2) else
      let (res, a') := subtypeUsing G I y.type x.type acc.2
      (res.value.isSome, keepSummaries acc.2 a')
  have hf := foldl_inv (fun acc : Bool × Answered G => acc.1 = true →
      ∃ y ∈ held, y.type = x.type ∨ ∃ a, ((subtypeUsing G I y.type x.type a).1).value.isSome = true)
    step held (false, answers) (hi _ rfl) (by
      intro y hy acc hac
      dsimp only [step]
      split
      · exact hac
      · split
        · rename_i hs
          exact fun _ => ⟨y, hy, .inl (by simpa only [same_eq_beq, beq_iff_eq] using hs)⟩
        · intro ht
          exact ⟨y, hy, .inr ⟨acc.2, ht⟩⟩)
  exact hf h

/-- Every implication a head requests has a matching carried implication
at its mapped slots, with equal type or an accepted subtype answer. -/
theorem headImplies_checked {env : WalkEnv ι G I} {t : Target} {names : List Nat}
    {carried : List (PromiseCalls.Implication ι)} {answers : Answered G}
    (h : (headImplies G I env t names carried answers).1 = true) :
    ∀ x ∈ (env.givenImplies[t.label]?).getD [], ∃ y ∈ carried,
      names[PointClaims.slot t.mapping x.test]? = some y.test ∧
      names[PointClaims.slot t.mapping x.target]? = some y.target ∧
      (y.type = x.type ∨ ∃ a, ((subtypeUsing G I y.type x.type a).1).value.isSome = true) := by
  let xs := (env.givenImplies[t.label]?).getD []
  let step := fun (acc : Bool × Answered G) (x : PromiseCalls.Implication ι) =>
    if !acc.1 then acc else
      impliesHeld G I x (carried.filter fun y =>
        some y.test == names[PointClaims.slot t.mapping x.test]? &&
        some y.target == names[PointClaims.slot t.mapping x.target]?) acc.2
  have hf : ∀ (rest : List (PromiseCalls.Implication ι)) (a : Bool × Answered G),
      (rest.foldl step a).1 = true → a.1 = true ∧
        ∀ x ∈ rest, ∃ y ∈ carried,
          names[PointClaims.slot t.mapping x.test]? = some y.test ∧
          names[PointClaims.slot t.mapping x.target]? = some y.target ∧
          (y.type = x.type ∨ ∃ b, ((subtypeUsing G I y.type x.type b).1).value.isSome = true) := by
    intro rest
    induction rest with
    | nil => intro a ha; exact ⟨ha, by simp⟩
    | cons x rest ih =>
      intro a ha
      obtain ⟨hs, hr⟩ := ih (step a x) ha
      have ha' : a.1 = true := by
        cases hh : a.1 with
        | true => rfl
        | false => simp only [step, hh, Bool.not_false, if_true] at hs; cases hs
      refine ⟨ha', ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simp only [step, ha', Bool.not_true, Bool.false_eq_true, if_false] at hs
        obtain ⟨y, hy, hty⟩ := impliesHeld_checked hs
        obtain ⟨hy, hn⟩ := List.mem_filter.mp hy
        simp only [Bool.and_eq_true, beq_iff_eq] at hn
        exact ⟨y, hy, hn.1.symm, hn.2.symm, hty⟩
      · exact hr z hz
  exact (hf xs (true, answers) h).2

/-- A successful nonvacuous head exit checks the head's required
implications, input and argument slots, and heap facts. -/
theorem headExit_checked {env : WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γ : List (Ty ι)} {names : List Nat} {store : Store} {pushed : Bool}
    {carried : List (PromiseCalls.Implication ι)} {a b : ExitsDone ι G}
    (h : headExit G I env l t tc Γ names store pushed false carried a = .ok b) :
    (∀ x ∈ (env.givenImplies[t.label]?).getD [], ∃ y ∈ carried,
      names[PointClaims.slot t.mapping x.test]? = some y.test ∧
      names[PointClaims.slot t.mapping x.target]? = some y.target ∧
      (y.type = x.type ∨ ∃ ans, ((subtypeUsing G I y.type x.type ans).1).value.isSome = true)) ∧
    (∀ p ∈ (env.givenInputs[t.label]?).getD [], names[PointClaims.slot t.mapping p.1]? = env.startNames[p.2]?) ∧
    (∀ j ∈ (env.givenArgs[t.label]?).getD [], names[PointClaims.slot t.mapping j]? = env.argName) ∧
    ∃ req, env.given[t.label]! = some req ∧
      KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context)
        (HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req t.mapping
          (materialize { names, store }
            (if pushed then (env.claimed[l]!).context.length + 1 else (env.claimed[l]!).context.length)
            (((atomsOf req).flatMap Atom.names).map (PointClaims.slot t.mapping)) true).1)) req t.mapping = true := by
  unfold headExit at h
  simp only [Bool.false_eq_true, if_false, Bool.not_false, Bool.true_and] at h
  split at h
  · cases h
  rename_i hi
  split at h
  · cases h
  rename_i hin
  split at h
  · cases h
  rename_i hargs
  split at h
  · cases h
  rename_i req hreq
  have hq : KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context)
      (HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req t.mapping
        (materialize { names, store }
          (if pushed then (env.claimed[l]!).context.length + 1 else (env.claimed[l]!).context.length)
          (((atomsOf req).flatMap Atom.names).map (PointClaims.slot t.mapping)) true).1)) req t.mapping = true := by
    apply Classical.byContradiction
    intro hn
    have hf := Bool.eq_false_iff.mpr hn
    simp only [timedKind, hf, Bool.not_false, if_true] at h
    cases h
  have hi' : (headImplies G I env t names carried a.answers).1 = true := by simpa using hi
  refine ⟨headImplies_checked hi', ?_, ?_, req, hreq, ?_⟩
  · intro p hp
    have hn : ((env.givenInputs[t.label]?).getD []).any
        (fun p => names[PointClaims.slot t.mapping p.1]? != env.startNames[p.2]?) = false :=
      Bool.eq_false_iff.mpr hin
    have hh := List.any_eq_false.mp hn p hp
    simpa using hh
  · intro j hj
    have hn : ((env.givenArgs[t.label]?).getD []).any
        (fun j => names[PointClaims.slot t.mapping j]? != env.argName) = false :=
      Bool.eq_false_iff.mpr hargs
    have hh := List.any_eq_false.mp hn j hj
    simpa using hh
  · exact hq

end Checks
end Verification.TolerantFrames
