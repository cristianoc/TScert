import Verification.Programs.TolerantFramesWrites

/-! # Tolerant frames: the pass's selected output under its own tree check

The pass takes a step's output from `Checker.select` (`SinglePass.lean` 1260
for a direct call, 1335 for every writing step) or from the search, whose
output is `select`'s (`CertificateProducer.expressionEffectUsing`, its last
loop). `Checker.steps`' `select` skips the derivation's tree check
(`tree := false`), and the pass checks the tree once (lines 1271–1282): by
`checkTreeUsing … codes` or by `PromiseCalls.requiresTree`, both at the
step's knowledge (`passTreeOk`). This module states what that pair gives:

- `Checker.passSteps`: the base checker whose `run` is `Checker.steps`'
  `select` where `passTreeOk` holds; its soundness (`passSteps_sound`) covers
  the tree accepted by `requiresTree` alone (an `ordinary` step: the call's
  type; any other kind: impossible, `requiresTree` roots at a call) and
  `typedRead`'s optional-field branch with codes;
- `Checker.passOrdinary`: the layers of `Checker.ordinary` over that base
  (`ordinaryOver`); where `passTreeOk` holds, `Checker.ordinary`'s `select`
  is `passOrdinary`'s `run`, exactly (`ordinary_select_eq`), so every
  theorem stated for a checker's `run` holds of the pass's selected output
  (`ordinary_select_sound`);
- the preserving steps at the selected output (`passPreserving_keeps_select`,
  `pass_preserving_frame_select`); `withSubtyping`'s `select` is its `run`
  (`withSubtyping_select`).

Where `run` itself rejects what the pass accepts: `typedRead`'s optional-field
branch checks its tree with no codes (`optional_run_rejects`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom)

section Select
variable {ι : Type} [DecidableEq ι]
open ProgramTyping PositiveCertificates ProgramCertificates PositiveGraphs PositiveRules HeapExpressionRules

/-! ## The pass's tree check -/

/-- The derivation the pass checks (`SinglePass.lean` 1271–1273): a sliced
read's proof at the location's contract, else the step's proof. -/
def passTree : StepEvidence ι → Option (ProgramCertificates.Evidence ι)
  | .slicedRead _ _ _ e _ => some e
  | e => e.proof?

/-- The pass's tree check (`SinglePass.lean` 1276–1282, `selectChecks`
false): the derivation accepted by `checkTreeUsing` with the codes, or by
`requiresTree` at the step's knowledge. -/
def passTreeOk (G : NormalGraph ι) (images : InstanceImageCheck G) (k : HeapKnowledge.Knowledge)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (e : StepEvidence ι) : Bool :=
  match passTree e with
  | some p => checkTreeUsing G images p codes sums || PromiseCalls.requiresTree G images k codes sums p
  | none => true

/-- A tree `checkTreeUsing` accepts passes the check at every knowledge: the
whole-facts `select` (line 1335) at a tree the narrow check (line 1276)
accepted by `checkTreeUsing`. -/
theorem passTreeOk_of_tree {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {e : StepEvidence ι}
    (ht : ∀ p, passTree e = some p → checkTreeUsing G images p codes sums = true) (k : HeapKnowledge.Knowledge) :
    passTreeOk G images k codes sums e = true := by
  unfold passTreeOk
  split
  · rename_i p hp; simp [ht p hp]
  · rfl

/-- A term of a call or a construction. -/
def callTerm : Tm → Bool
  | .invoke .. | .construct .. => true
  | _ => false

/-- **`requiresApp` roots at a call**: its rule is `.app` or `.construct`,
whose local check fixes the claimed term's shape. -/
theorem requiresApp_term {G : NormalGraph ι} {images : InstanceImageCheck G} {k : HeapKnowledge.Knowledge}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {p : ProgramCertificates.Evidence ι}
    (hc : PromiseCalls.requiresApp G images k codes sums p = true) : callTerm (claim p).term = true := by
  obtain ⟨j, r, ps⟩ := p
  cases r <;> simp only [PromiseCalls.requiresApp, Bool.false_eq_true] at hc
  all_goals
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨-, hl⟩, -⟩, -⟩ := hc
    simp only [LocalUsing] at hl
    simp only [claim]
    split at hl
    · rename_i hj _; rw [hj]; rfl
    · exact hl.elim

/-- **`requiresTree` roots at a call**, possibly under one subsumption, which
keeps the term. -/
theorem requiresTree_term {G : NormalGraph ι} {images : InstanceImageCheck G} {k : HeapKnowledge.Knowledge}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {p : ProgramCertificates.Evidence ι}
    (hc : PromiseCalls.requiresTree G images k codes sums p = true) : callTerm (claim p).term = true := by
  unfold PromiseCalls.requiresTree at hc
  split at hc
  · rename_i j c q
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hl, ha⟩ := hc
    obtain ⟨-, hterm, -⟩ := hl
    have := requiresApp_term ha
    simp only [claim] at this ⊢
    rw [← hterm]; exact this
  · exact requiresApp_term hc

/-! ## `select` against `run` at the base -/

theorem checkedOutput_value_tree (G : NormalGraph ι) (images : InstanceImageCheck G)
    (e : ProgramCertificates.Evidence ι) (m : Bool) (out : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (b : Bool) :
    (checkedOutput G images e m out codes sums b).value =
      if m && (treeChecked G images e codes sums b).accepted then some out else none := by
  rw [checkedOutput, CheckResult.value_bind_const, CheckResult.accepted_ofBool, CheckResult.value_map_const]
  cases m <;> simp

theorem treeChecked_false (G : NormalGraph ι) (images : InstanceImageCheck G)
    (e : ProgramCertificates.Evidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    (treeChecked G images e codes sums false).accepted = true := rfl

theorem treeChecked_accepted {G : NormalGraph ι} {images : InstanceImageCheck G}
    {e : ProgramCertificates.Evidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (ht : checkTreeUsing G images e codes sums = true) (b : Bool) :
    (treeChecked G images e codes sums b).accepted = true := by
  cases b
  · rfl
  · exact ht

/-- **Where the pass's tree is accepted by `checkTreeUsing`, `select` is
`run`** at the base, for every kind but `typedRead` (whose optional-field
branch `run` checks with no codes). -/
theorem select_value_eq {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hnt : ∀ i q, e ≠ .typedRead i q)
    (ht : ∀ p, passTree e = some p → checkTreeUsing G images p codes sums = true) :
    (checkStepResult G images j k e codes sums (tree := false)).value =
      (checkStepResult G images j k e codes sums).value := by
  cases e with
  | typedRead i q => exact absurd rfl (hnt i q)
  | ordinary p | pure p | reading p | created p =>
    have h := ht p rfl
    simp only [checkStepResult, checkedOutput_value_tree, CheckResult.value_bind_const, treeChecked_accepted h]
  | allocated p =>
    have h := ht p rfl
    simp only [checkStepResult]
    rcases allocationSlots j.term with _ | s₁ <;> rcases mergeSlots j.term with _ | ⟨d, a, b⟩ <;>
      rcases storeSlots j.term with _ | s₃ <;>
      simp only [checkedOutput_value_tree, treeChecked_accepted h]
  | written i v R p =>
    have h := ht p rfl
    simp only [checkStepResult]
    rcases writeSlots j.term with _ | ⟨f, i', v'⟩ <;> simp only [checkedOutput_value_tree, treeChecked_accepted h]
  | slicedRead tag q i p sub =>
    have h := ht p rfl
    simp only [checkStepResult]
    rcases readSlot j.term with _ | ⟨f, i'⟩ <;> simp only [CheckResult.value_bind_const, treeChecked_accepted h]
  | _ => rfl

/-- The tree the pass checks is claimed at the step's term. -/
theorem select_claim_term {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {p : ProgramCertificates.Evidence ι}
    (hc : (checkStepResult G images j k e codes sums (tree := false)).value = some out)
    (hp : passTree e = some p) : (claim p).term = j.term := by
  cases e <;> simp only [passTree, StepEvidence.proof?, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    simp only [checkStepResult, checkedOutput_value_tree, CheckResult.value_bind_const, treeChecked_false,
      Bool.and_true, CheckResult.accepted_ofBool] at hc
  all_goals (repeat' split at hc)
  all_goals try simp only [CheckResult.value_orElse, checkedOutput_value_tree, CheckResult.value_bind_const,
    treeChecked_false, Bool.and_true, CheckResult.accepted_ofBool] at hc
  all_goals (repeat' split at hc)
  all_goals simp_all

/-- **No kind but `ordinary` accepts a call's term.** -/
theorem select_call_none {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hcall : callTerm j.term = true) (hno : ∀ q, e ≠ .ordinary q) :
    (checkStepResult G images j k e codes sums (tree := false)).value = none := by
  obtain ⟨Γ, t, T⟩ := j
  cases t <;> simp only [callTerm, Bool.false_eq_true] at hcall
  all_goals
    cases e
    all_goals first
      | exact absurd rfl (hno _)
      | simp [checkStepResult, checkedOutput_value_tree, readSlot, writeSlots, allocationSlots, mergeSlots,
          storeSlots, Purity.pureTerm, Purity.inspectTerm, isVal, CheckResult.value_bind_const,
          CheckResult.fromOption, CheckResult.value_failure]

/-- **What `select` at the base and the pass's tree check give**: `run`'s
acceptance with the same output; or an `ordinary` step whose tree only
`requiresTree` accepts, output `ordinaryOutput`; or `typedRead`'s
optional-field branch with its tree accepted with the codes. -/
theorem passSteps_value {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hok : passTreeOk G images k codes sums e = true)
    (hc : (checkStepResult G images j k e codes sums (tree := false)).value = some out) :
    checkStepUsing G images j k e codes sums = some out ∨
    (∃ p, e = .ordinary p ∧ claim p = j ∧ out = ordinaryOutput k ∧
      PromiseCalls.requiresTree G images k codes sums p = true) ∨
    (∃ i p fld Ref, e = .typedRead i p ∧ claim p = j ∧ j.term = .readAt fld (.var i) ∧ j.context[i]? = some Ref ∧
      optionalOperand (expand G Ref) fld = true ∧ checkTreeUsing G images p codes sums = true ∧
      out = readFrame k i fld true) := by
  cases hpt : passTree e with
  | none =>
    left
    cases e <;> simp only [passTree, StepEvidence.proof?, reduceCtorEq] at hpt <;> exact hc
  | some p =>
    have hok' : (checkTreeUsing G images p codes sums || PromiseCalls.requiresTree G images k codes sums p) = true := by
      simpa [passTreeOk, hpt] using hok
    by_cases ht : checkTreeUsing G images p codes sums = true
    · by_cases hty : ∃ i q, e = .typedRead i q
      · obtain ⟨i, q, rfl⟩ := hty
        simp only [passTree, StepEvidence.proof?, Option.some.injEq] at hpt
        subst hpt
        simp only [checkStepResult] at hc
        split at hc
        · rename_i fld i' hslot
          simp only [CheckResult.value_orElse, checkedOutput_value_tree, treeChecked_false, Bool.and_true] at hc
          split at hc
          · rename_i hm
            left
            simp only [Option.orElse, Option.some.injEq] at hc
            subst hc
            simp only [checkStepUsing, checkStepResult, hslot, CheckResult.value_orElse, checkedOutput_value_tree,
              treeChecked_accepted ht, Bool.and_true, hm, if_true, Option.orElse]
          · right; right
            simp only [Option.orElse] at hc
            split at hc
            · rename_i hm2
              simp only [decide_eq_true_eq] at hm2
              obtain ⟨hj, rfl, hany⟩ := hm2
              cases hi : j.context[i']? with
              | none => simp [hi] at hany
              | some Ref =>
                simp only [hi, Option.any_some] at hany
                cases hc
                exact ⟨i', q, fld, Ref, rfl, hj, readSlot_eq hslot, hi, hany, ht, rfl⟩
            · cases hc
        · cases hc
      · left
        have hnt : ∀ i q, e ≠ .typedRead i q := fun i q h => hty ⟨i, q, h⟩
        rw [checkStepUsing, ← select_value_eq hnt (fun p' hp' => by rw [hpt] at hp'; cases hp'; exact ht)]
        exact hc
    · have hreq : PromiseCalls.requiresTree G images k codes sums p = true := by simpa [ht] using hok'
      have hcall := requiresTree_term hreq
      rw [select_claim_term hc hpt] at hcall
      by_cases hord : ∃ q, e = .ordinary q
      · obtain ⟨q, rfl⟩ := hord
        simp only [passTree, StepEvidence.proof?, Option.some.injEq] at hpt
        subst hpt
        right; left
        simp only [checkStepResult, checkedOutput_value_tree, treeChecked_false, Bool.and_true] at hc
        split at hc
        · rename_i hm
          simp only [decide_eq_true_eq] at hm
          cases hc
          exact ⟨q, rfl, hm.1, rfl, hreq⟩
        · cases hc
      · rw [select_call_none hcall (fun q h => hord ⟨q, h⟩)] at hc
        cases hc

/-- **The base's selected output under the pass's tree check is sound**: the
consequence `Checker.sound` states for `run`. -/
theorem passSteps_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hok : passTreeOk G images k codes sums e = true)
    (hc : (checkStepResult G images j k e codes sums (tree := false)).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type) (fun h' v => HeapKnowledge.Holds out (push v ρ) h') n W h
      (instantiate 0 ρ j.term) := by
  rcases passSteps_value hok hc with hu | ⟨p, rfl, hj, rfl, hreq⟩ | ⟨i, p, fld, Ref, rfl, hj, ht, hi, hopt, htree, rfl⟩
  · exact checkStep_sound hu hcodes hsums he hk hw hh
  · obtain ⟨eff, -, hs⟩ := PromiseCalls.requiresTree_sound hcodes hsums p hreq
    subst hj
    apply of_value_property _ (erase (hs he hk hw hh))
    intro _ _ heap v _
    exact ⟨HeapFacts.holds_nil _ _, (HeapKnowledge.shift_holds (v := v) hk).2.1,
      HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := v) hk).2.2.1,
      (HeapKnowledge.shift_holds (v := v) hk).2.2.2.1, HeapKnowledge.elemsHolds_nil _ _,
      HeapKnowledge.envIndices_holds (HeapKnowledge.shift_holds (v := v) hk).2.2.2.2.2 _⟩
  · have typed := checkTreeUsing_sound p htree hcodes hsums
    rw [hj, ht] at typed
    rw [ht]
    simpa [instantiate] using optionalRead_sound typed hi hopt he hk hw hh

/-! ## The checker the pass's selection runs -/

/-- The base checker whose `run` is `Checker.steps`' `select` where the
pass's tree check holds. -/
@[nospecialize] def passSteps (G : NormalGraph ι) (images : InstanceImageCheck G) : Checker G images where
  run := fun j k e codes sums =>
    if passTreeOk G images k codes sums e then checkStepResult G images j k e codes sums (tree := false) else failure
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    split at hc
    · exact passSteps_sound ‹_› hc hcodes hsums he hk hw hh
    · cases hc

/-- The layers of `Checker.ordinary` over a base checker. -/
@[nospecialize] def ordinaryOver {G : NormalGraph ι} {images : InstanceImageCheck G} (base : Checker G images) :
    Checker G images :=
  base.keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls
    |>.negatingSlots.indexing.boundedWrites.keepingStable

theorem ordinary_eq_over (G : NormalGraph ι) (images : InstanceImageCheck G) :
    Checker.ordinary G images = ordinaryOver (Checker.steps G images) := rfl

/-- `Checker.ordinary`'s layers over `passSteps`. -/
@[nospecialize] def passOrdinary (G : NormalGraph ι) (images : InstanceImageCheck G) : Checker G images :=
  ordinaryOver (passSteps G images)

/-- **Under the pass's tree check, `Checker.ordinary`'s `select` is
`passOrdinary`'s `run`**: every layer reads its base at the same step. -/
theorem ordinary_select_eq {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hok : passTreeOk G images k codes sums e = true) :
    (Checker.ordinary G images).select j k e codes sums = (passOrdinary G images).run j k e codes sums := by
  simp only [Checker.ordinary, passOrdinary, ordinaryOver, Checker.keepingStable, Checker.boundedWrites,
    Checker.indexing, Checker.emptyArrays, Checker.negatingSlots, Checker.ensuringCalls, Checker.elementCalls,
    Checker.requiringCalls, Checker.allocatingCalls, Checker.keepingOwnCalls, Checker.keepingCalls,
    Checker.steps, passSteps, hok, if_true]

/-- **The pass's selected output is `passOrdinary`'s `run`**: the premise
every step theorem of this development takes of a checker's `run`. -/
theorem select_run {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hok : passTreeOk G images k codes sums e = true)
    (hsel : ((Checker.ordinary G images).select j k e codes sums).value = some out) :
    ((passOrdinary G images).run j k e codes sums).value = some out := by
  rw [← ordinary_select_eq hok]; exact hsel

/-- **The pass's selected output is sound**: from the Boolean conditions the
pass evaluates (`select` at line 1260 or 1335, the tree check at 1276–1282),
the conclusion `Checker.sound` states for `run`. -/
theorem ordinary_select_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hok : passTreeOk G images k codes sums e = true)
    (hsel : ((Checker.ordinary G images).select j k e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type) (fun h' v => HeapKnowledge.Holds out (push v ρ) h') n W h
      (instantiate 0 ρ j.term) :=
  (passOrdinary G images).sound (select_run hok hsel) hcodes hsums he hk hw hh

/-- **A qualified body's `select` is its `run`** (`selectChecks`, line 1276). -/
theorem withSubtyping_select {G : NormalGraph ι} {images : InstanceImageCheck G} (subtyping : BodySubtyping G)
    (ord : ∀ {A B p}, PositiveCertificates.checkUsing G images A B p = true → subtyping.check A B p = true) :
    (Checker.withSubtyping G images subtyping ord).select = (Checker.withSubtyping G images subtyping ord).run := rfl

/-! ## The preserving steps at the selected output -/

/-- **The layers over any base accept a preserving kind only where the base
or `elementsCall` does** (`ordinary_run_base`, for any base). -/
theorem ordinaryOver_run_base {G : NormalGraph ι} {images : InstanceImageCheck G} (base : Checker G images)
    {j : Sequent ι} {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hp : kindPreserving e = true) (hr : ((ordinaryOver base).run j k e codes sums).value = some out) :
    (∃ out₀, (base.run j k e codes sums).value = some out₀) ∨
      (PromiseCalls.elementsCall G images j e codes sums).isSome := by
  have hb : ∀ out,
      (base.keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls.run
        j k e codes sums).value = some out →
      (∃ out₀, (base.run j k e codes sums).value = some out₀) ∨
        (PromiseCalls.elementsCall G images j e codes sums).isSome := by
    intro out hr
    have h1 : PromiseCalls.ensuresCall G images j k e codes sums = none := by
      cases e <;> first | rfl | cases hp
    have h2 : PromiseCalls.requiresCall G images j k e codes sums = false := by
      cases e <;> first | rfl | cases hp
    have h3 : PromiseCalls.freshCall G images j e codes sums = false := by
      cases e <;> first | rfl | cases hp
    have h4 : PromiseCalls.ownCall G images j e codes sums = none := by
      cases e <;> first | rfl | cases hp
    have h5 : PromiseCalls.keepsCall G images j e codes sums = false := by
      cases e <;> first | rfl | cases hp
    simp only [Checker.ensuringCalls, Checker.elementCalls, Checker.requiringCalls, Checker.allocatingCalls,
      Checker.keepingOwnCalls, Checker.keepingCalls, h1, h2, h3, h4, h5] at hr
    cases hel : PromiseCalls.elementsCall G images j e codes sums with
    | some _ => exact .inr rfl
    | none =>
      simp only [hel, Bool.false_eq_true, if_false] at hr
      exact .inl ⟨out, hr⟩
  simp only [ordinaryOver, Checker.keepingStable, Checker.boundedWrites, Checker.indexing,
    Checker.emptyArrays, Checker.negatingSlots, CheckResult.map, Option.map_eq_some_iff] at hr
  obtain ⟨o₁, hr, -⟩ := hr
  have hnb : ∀ a i v p, e ≠ .boundedWrite a i v p := fun _ _ _ _ he => by subst he; cases hp
  split at hr
  · rename_i a i v p; exact absurd rfl (hnb a i v p)
  · obtain ⟨o₂, hr, -⟩ := Option.map_eq_some_iff.mp hr
    obtain ⟨o₃, hr, -⟩ := Option.map_eq_some_iff.mp hr
    obtain ⟨o₄, hr, -⟩ := Option.map_eq_some_iff.mp hr
    split at hr
    · obtain ⟨o₅, hr, -⟩ := Option.map_eq_some_iff.mp hr
      exact hb o₅ hr
    · exact hb o₄ hr

/-- **A preserving kind the base accepts under the pass's tree check keeps
the heap**: `run`'s acceptance (`base_keeps`), or the optional-field read, an
inspection. -/
theorem passSteps_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : ((passSteps G images).run j k e codes sums).value = some out) (hp : kindPreserving e = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) : KeepsPost G j ρ n W h := by
  have hs := erase ((passSteps G images).sound hc hcodes hsums he hk hw hh)
  simp only [passSteps] at hc
  split at hc
  · rename_i hok
    rcases passSteps_value hok hc with hu | ⟨p, rfl, -⟩ | ⟨i, p, fld, Ref, rfl, -, ht, hi, -⟩
    · exact base_keeps hu hp hcodes hsums he hk hw hh
    · cases hp
    · refine inspection_keeps hs ?_ hw hh
      rw [ht]
      simpa [instantiate, Purity.inspectTerm] using
        slot_inspect he (List.getElem?_eq_some_iff.mp hi).1
  · cases hc

/-- **Every step the pass classifies preserving keeps the heap**, at the
pass's selected output under its tree check. -/
theorem passPreserving_keeps_select {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {kE out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hpres : passPreserving G images j kE e codes sums = true)
    (hok : passTreeOk G images kE codes sums e = true)
    (hsel : ((Checker.ordinary G images).select j kE e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) : KeepsPost G j ρ n W h := by
  simp only [passPreserving, Bool.or_eq_true] at hpres
  rcases hpres with hc | hp
  · exact callKeepsHeap_keeps hc hcodes hsums he hk hw hh
  · rcases ordinaryOver_run_base (passSteps G images) hp (select_run hok hsel) with ⟨o, hb⟩ | hel
    · exact passSteps_keeps hb hp hcodes hsums he hk hw hh
    · obtain ⟨⟨x, R⟩, hel⟩ := Option.isSome_iff_exists.mp hel
      exact elementsCall_keeps hel hcodes hsums he hw hh

/-- **The pass's preserving steps, both exits, at its selected output**:
`pass_preserving_frame` with `hr` discharged by the pass's own conditions. -/
theorem pass_preserving_frame_select {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {kE out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hpres : passPreserving G images j kE e codes sums = true)
    (hok : passTreeOk G images kE codes sums e = true)
    (hsel : ((Checker.ordinary G images).select j kE e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ η : Env} {r m : Nat} {s : IndexedHeap} {S : List Atom}
    (he : EnvOk G j.context ρ s.n s.W) (hkE : HeapKnowledge.Holds kE ρ s.h)
    (hS : Named S η ρ m s) (hfr : ∀ a ∈ S, r ∉ a.names)
    {k : Nat} {h' : Heap} {t' : Tm} (hst : Steps k s.h (instantiate 0 ρ j.term) h' t') (hk : k < s.n) :
    (isVal t' = true → ∃ s' : IndexedHeap, Action Footprints.Closed.empty.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ meaning G j.type s'.n s'.W t' ∧
        HeapKnowledge.Holds out (push t' ρ) h' ∧ Named S (Env.set η r t') ρ m s') ∧
      (∀ x, Raises t' x → ∃ s' : IndexedHeap, Action Footprints.Closed.top.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ Scoped 0 x ∧ excOf G s'.n s'.W x ∧ Named (S.filter (·.heapFree)) η ρ m s') :=
  preserving_step_frame (passOrdinary G images) (select_run hok hsel) hcodes hsums he hkE
    (passPreserving_keeps_select hpres hok hsel hcodes hsums he hkE s.adm s.ok) hS hfr hst hk

/-- **A step the pass frames, at its selected output**: `preserving_judgment`
with `hr` discharged by the pass's own conditions. -/
theorem preserving_judgment_select {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {kE out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hpres : passPreserving G images j kE e codes sums = true)
    (hok : passTreeOk G images kE codes sums e = true)
    (hsel : ((Checker.ordinary G images).select j kE e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G j.type)
      (fun h' v => Footprints.Closed.empty.Holds h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => Footprints.Closed.top.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) := by
  have hboth := cross_upto n (fun _ _ _ _ _ _ _ _ hb _ => hb) W W h _ hh hh
    (passPreserving_keeps_select hpres hok hsel hcodes hsums he hk hw hh)
    (ordinary_select_sound hok hsel hcodes hsums he hk hw hh)
  exact SafePostExc.weaken (fun _ _ hq => ⟨hq.2.1.1, hq.2.2⟩)
    (fun _ hq => ⟨Footprints.Closed.holds_top.mpr hq, trivial⟩) (safePost_grow h.length (Nat.le_refl _) hboth)

end Select

end Verification.TolerantFrames
