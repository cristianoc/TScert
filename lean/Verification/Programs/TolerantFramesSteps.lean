import Verification.Programs.TolerantFramesNamed

/-! # Tolerant frames: the pass's preserving steps through their checked rules

The pass applies a step's output with the frame of the facts it was not handed
(`applyDelta … true`, `SinglePass.lean` 1315–1318) when the step is
**preserving**: a call the pass's own predicates find keeping the heap
(`callKeepsHeap`, lines 1289–1296), or a step of any kind other than
`ordinary`, `written` and `boundedWrite` (`kindPreserving`, lines 1307–1309).
This module connects that classification to the frame (`preserving_normal`,
`preserving_throw`) through the checked rule:

- each preserving kind's base rule (`HeapExpressionRules.checkStepUsing`)
  fixes the term's shape, an inspection or a graph closure's creation, so its
  normal exit only extends the heap (`base_keeps`);
- the call predicates keep the heap by their selected signature
  (`elementsCall_keeps`, `requiresCall_keeps`, `callKeepsHeap_keeps`);
- the production checker `Checker.ordinary` accepts a preserving kind only
  where its base rule or `elementsCall` does (`ordinary_run_base`), so every
  step the pass classifies preserving keeps the heap (`passPreserving_keeps`);
- with the output the checker's `run` gives, both exits of the step: the
  action, the residual budget, the type, the rule's output, and the store's
  facts at the name valuation (`preserving_step_frame`, and at
  `Checker.ordinary`, `pass_preserving_frame`).

What is assumed: the output the pass applies is `run`'s (`hrun`); the pass
takes it from `Checker.select` or the search. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom)

section Steps
variable {ι : Type} [DecidableEq ι]
open ProgramTyping PositiveCertificates ProgramCertificates PositiveGraphs PositiveRules HeapExpressionRules

/-! ## The pass's classification -/

/-- The step kinds the pass frames whatever their rule (`SinglePass.lean`
lines 1307–1309): every kind but `ordinary`, `written` and `boundedWrite`. -/
def kindPreserving : StepEvidence ι → Bool
  | .ordinary _ | .written .. | .boundedWrite .. => false
  | _ => true

/-- The calls the pass frames (`SinglePass.lean` lines 1289–1296): one
promising its receiver's elements, one at a precondition whose selected
signature keeps the heap, one allocating its result, else one keeping the heap
that changes no receiver's own locations. -/
def callKeepsHeap (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι) (kE : HeapKnowledge.Knowledge)
    (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) : Bool :=
  match e with
  | .ordinary p =>
    (PromiseCalls.elementsCall G images j e codes sums).isSome ||
    (if PromiseCalls.requiresCall G images j kE e codes sums then
      (ExpressionEffects.selectedEffect p).any PromiseCalls.keepsHeap
    else PromiseCalls.freshCall G images j e codes sums ||
      ((PromiseCalls.ownCall G images j e codes sums).isNone && PromiseCalls.keepsCall G images j e codes sums))
  | _ => false

/-- The pass's `preserving` (line 1307). -/
def passPreserving (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι) (kE : HeapKnowledge.Knowledge)
    (e : StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) : Bool :=
  callKeepsHeap G images j kE e codes sums || kindPreserving e

/-- The step's normal exit is within `{values: keep, stores: keep}` from `h`. -/
def KeepsPost (G : NormalGraph ι) (j : Sequent ι) (ρ : Env) (n : Nat) (W : WorldT n) (h : Heap) : Prop :=
  SafePost (excOf G) (meaning G j.type) (fun h' _ => Footprints.Closed.empty.Holds h h' ∧ True) n W h
    (instantiate 0 ρ j.term)

/-! ## Term shapes -/

/-- A pure term is an inspection. -/
theorem pure_inspect : ∀ {t : Tm}, Purity.pureTerm t = true → Purity.inspectTerm t = true := by
  intro t
  induction t using Tm.induct with
  | var => intro; rfl
  | _ =>
    intro hp
    first
      | (simp only [Purity.pureTerm, Purity.inspectTerm, Bool.and_eq_true] at hp ⊢; simp_all; done)
      | exact Purity.inspect_value (by simpa [Purity.pureTerm] using hp)

omit [DecidableEq ι] in
/-- A slot of the context holds a value, an inspection. -/
theorem slot_inspect {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat} {W : WorldT n} {i : Nat}
    (he : EnvOk G Γ ρ n W) (hi : i < Γ.length) : Purity.inspectTerm (ρ i) = true :=
  Purity.inspect_value (meaning_value (he.2 i Γ[i] (List.getElem?_eq_getElem hi))).1

theorem slot_lt_of_any {Γ : List α} {i : Nat} {p : α → Bool} (h : (Γ[i]?).any p = true) : i < Γ.length := by
  cases hg : Γ[i]? with
  | none => rw [hg] at h; cases h
  | some _ => exact (List.getElem?_eq_some_iff.mp hg).1

/-- **Creating a graph closure only extends the heap**: one step allocating
its two frames, to a value. -/
theorem created_keeps {Ξ T : Fam} {n : Nat} {W : WorldT n} {h : Heap} {ρ : Env} {arity E K start caps kind rest}
    (hs : Safe Ξ T n W h (instantiate 0 ρ (.makeFn (.graph arity E K start caps kind rest) .nul))) :
    SafePost Ξ T (fun h' _ => Footprints.Closed.empty.Holds h h' ∧ True) n W h
      (instantiate 0 ρ (.makeFn (.graph arity E K start caps kind rest) .nul)) := by
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hv, _⟩ | ⟨_, hr, _⟩) | ⟨U, h', t', hx, hu, step, hh', hs'⟩
    · simp [instantiate, isVal] at hv
    · simp only [instantiate, instantiateArgs_eq_map, List.map] at hr
      cases hr with | makeArg hg _ hr => obtain ⟨rfl, rfl⟩ := singleton_get hg; cases hr
    · simp only [instantiate, instantiateArgs_eq_map, List.map] at step hs' ⊢
      obtain ⟨rfl, rfl⟩ := makeFn_step_inv rfl step
      exact Or.inr ⟨U, _, _, hx, hu, step, hh',
        refine_value rfl ⟨Footprints.Closed.holds_empty.mpr ⟨[.nul, .nul], by simp⟩, trivial⟩ hs'⟩

/-- **The base rule of a preserving kind fixes the term's shape**: the
instantiated term is an inspection, or the term creates a graph closure. -/
theorem base_shape {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι} {k out : HeapKnowledge.Knowledge}
    {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : checkStepUsing G images j k e codes sums = some out) (hp : kindPreserving e = true)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h) :
    Purity.inspectTerm (instantiate 0 ρ j.term) = true ∨
      ∃ arity E K start caps kind rest, j.term = .makeFn (.graph arity E K start caps kind rest) .nul := by
  have read : ∀ fld i, j.term = .readAt fld (.var i) → Purity.inspectTerm (ρ i) = true →
      Purity.inspectTerm (instantiate 0 ρ j.term) = true := fun fld i ht hi => by
    rw [ht]; simpa [instantiate, Purity.inspectTerm] using hi
  rw [checkStepUsing_eq] at hc
  cases e with
  | ordinary => cases hp
  | written => cases hp
  | boundedWrite => cases hp
  | pure e =>
    simp only at hc
    split at hc
    · rename_i hq
      exact .inl (inspect_instantiate (d := 0) (pure_inspect hq.2.2.2) (by simpa using hq.2.1) he)
    · cases hc
  | reading e =>
    simp only at hc
    split at hc
    · rename_i hq
      exact .inl (inspect_instantiate (d := 0) hq.2.2.2 (by simpa using hq.2.1) he)
    · cases hc
  | created e =>
    simp only at hc
    split at hc
    · split at hc
      · rename_i heq; exact .inr ⟨_, _, _, _, _, _, _, heq⟩
      · cases hc
    · cases hc
  | typedRead i e =>
    simp only at hc
    split at hc
    · rename_i fld i' hr
      have ht := readSlot_eq hr
      split at hc
      · rename_i hq
        obtain ⟨-, -, rfl, hany⟩ := hq
        exact .inl (read fld i' ht (slot_inspect he (slot_lt_of_any hany)))
      · split at hc
        · rename_i hq
          obtain ⟨-, -, rfl, hany⟩ := hq
          exact .inl (read fld i' ht (slot_inspect he (slot_lt_of_any hany)))
        · cases hc
    · cases hc
  | observedRead i R =>
    simp only at hc
    split at hc
    · rename_i fld i' hr
      split at hc
      · rename_i hq
        obtain ⟨rfl, hi, -⟩ := hq
        exact .inl (read fld i' (readSlot_eq hr) (slot_inspect he hi))
      · cases hc
    · cases hc
  | slicedRead tag q i e p =>
    simp only at hc
    split at hc
    · rename_i fld i' hr
      split at hc
      · rename_i hq
        obtain ⟨-, -, -, rfl, hany, -⟩ := hq
        exact .inl (read fld i' (readSlot_eq hr) (slot_inspect he (slot_lt_of_any hany)))
      · cases hc
    · cases hc
  | knownValue i R =>
    simp only at hc
    split at hc
    · rename_i hq
      obtain ⟨ht, hi, -⟩ := hq
      exact .inl (by rw [ht]; simpa [instantiate] using slot_inspect he hi)
    · cases hc
  | linkedRead i y p =>
    simp only at hc
    split at hc
    · rename_i fld i' B hr hB
      split at hc
      · rename_i hq
        obtain ⟨rfl, hl, -⟩ := hq
        obtain ⟨g, hg, hm⟩ := List.any_eq_true.mp hl
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_iff_mem] at hm
        obtain ⟨⟨⟨hal, -⟩, ha⟩, -⟩ := hm
        have hcell : ρ g.cell = ρ i' := HeapLinks.aliases_eq hk.2.2.1 hal
        have hgl := hk.2.2.1 g hg
        simp only [ha, Bool.false_eq_true, if_false] at hgl
        have hobj : ∃ flds c oid, ρ i' = .objAt flds c oid := by
          split at hgl
          · obtain ⟨flds, c, oid, ho, -⟩ := hgl; exact ⟨flds, c, oid, hcell ▸ ho⟩
          · obtain ⟨flds, c, oid, -, ho, -⟩ := hgl; exact ⟨flds, c, oid, hcell ▸ ho⟩
        obtain ⟨flds, c, oid, ho⟩ := hobj
        exact .inl (read fld i' (readSlot_eq hr) (by rw [ho]; rfl))
      · cases hc
    · cases hc
  | allocated e =>
    simp only at hc
    split at hc
    · rename_i slots hs
      split at hc
      · rename_i hq
        obtain ⟨code, ht⟩ := allocationSlots_eq hs
        refine .inl (inspect_instantiate (d := 0) ?_ (by simpa using hq.2.1) he)
        rw [ht]; simp [Purity.inspectTerm, Purity.operandTerm]
      · cases hc
    · split at hc
      · rename_i d a b hm
        split at hc
        · rename_i hq
          obtain ⟨-, -, ha, hb⟩ := hq
          rcases mergeSlots_eq hm with ht | ht <;> rw [ht] <;>
            simp [instantiate, Purity.inspectTerm, slot_inspect he ha, slot_inspect he hb]
        · cases hc
      · split at hc
        · rename_i slots hs
          split at hc
          · rename_i hq
            obtain ⟨-, -, hin⟩ := hq
            refine .inl ?_
            rw [storeSlots_eq hs]
            simp only [instantiate, instantiateArgs_eq_map, Purity.inspectTerm, List.map_map, List.all_eq_true,
              List.mem_map]
            rintro _ ⟨i, hi, rfl⟩
            have hv := (meaning_value (he.2 i _ (List.getElem?_eq_getElem (hin i hi)))).1
            simp only [Function.comp, instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero]
            cases hr : ρ i <;> simp_all [Purity.initTerm, Purity.operandTerm, isVal]
          · cases hc
        · cases hc

/-- **A preserving kind's base rule keeps the heap on its normal exit.** -/
theorem base_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι} {k out : HeapKnowledge.Knowledge}
    {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : checkStepUsing G images j k e codes sums = some out) (hp : kindPreserving e = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) : KeepsPost G j ρ n W h := by
  have hs := erase (checkStep_sound hc hcodes hsums he hk hw hh)
  rcases base_shape hc hp he hk with hi | ⟨_, _, _, _, _, _, _, ht⟩
  · exact inspection_keeps hs hi hw hh
  · unfold KeepsPost; rw [ht] at hs ⊢; exact created_keeps hs

/-! ## The calls the pass frames -/

/-- A call promising its receiver's elements keeps the heap: its selected
signature does (`PromiseCalls.keepsHeap_prefix`). -/
theorem elementsCall_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {x : Nat}
    {R : CallEffects.ElemPred} (hc : PromiseCalls.elementsCall G images j e codes sums = some (x, R))
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) : KeepsPost G j ρ n W h := by
  unfold PromiseCalls.elementsCall at hc
  split at hc
  · rename_i p _
    by_cases hcond : (decide (claim p = j) && ExpressionEffects.selectedOperands p &&
        checkTreeUsing G images p codes sums && PromiseCalls.onlyBool G j.type) = true
    · rw [if_pos hcond] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨rfl, hops⟩, ht⟩, -⟩ := hcond
      cases hsel : ExpressionEffects.selectedEffect p with
      | none => simp [hsel] at hc
      | some eff =>
        cases hrs : PromiseCalls.receiverSlot (claim p).term with
        | none => simp [hsel, hrs] at hc
        | some x' =>
          simp only [hsel, hrs] at hc
          by_cases hkeep : PromiseCalls.keepsHeap eff = true
          · exact PromiseCalls.post_with_type
              (fun _ _ _ _ _ hq => ⟨Footprints.Closed.holds_empty.mpr (PromiseCalls.keepsHeap_prefix hkeep hq), trivial⟩)
              (ExpressionEffects.selected_sound p ht hops hsel hcodes hsums he hw hh)
          · rw [if_neg hkeep] at hc; cases hc
    · rw [if_neg hcond] at hc; cases hc
  · cases hc

/-- A call at a precondition the step's facts establish, whose selected
signature keeps the heap, keeps the heap (`PromiseCalls.requiresTree_sound`). -/
theorem requiresCall_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {kE : HeapKnowledge.Knowledge} {p : ProgramCertificates.Evidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : PromiseCalls.requiresCall G images j kE (.ordinary p) codes sums = true)
    (hkeep : (ExpressionEffects.selectedEffect p).any PromiseCalls.keepsHeap = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) : KeepsPost G j ρ n W h := by
  simp only [PromiseCalls.requiresCall, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨rfl, hc⟩ := hc
  obtain ⟨eff, hsel, hs⟩ := PromiseCalls.requiresTree_sound hcodes hsums p hc
  rw [hsel] at hkeep
  exact PromiseCalls.post_with_type
    (fun _ _ _ _ _ hq => ⟨Footprints.Closed.holds_empty.mpr (PromiseCalls.keepsHeap_prefix hkeep hq), trivial⟩)
    (hs he hk hw hh)

/-- **Every call the pass frames keeps the heap.** -/
theorem callKeepsHeap_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {kE : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : callKeepsHeap G images j kE e codes sums = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) : KeepsPost G j ρ n W h := by
  cases e with
  | ordinary p =>
    simp only [callKeepsHeap, Bool.or_eq_true, Option.isSome_iff_exists] at hc
    rcases hc with ⟨⟨x, R⟩, hel⟩ | hc
    · exact elementsCall_keeps hel hcodes hsums he hw hh
    · split at hc
      · rename_i hreq; exact requiresCall_keeps hreq hc hcodes hsums he hk hw hh
      · simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
        rcases hc with hf | ⟨-, hkc⟩
        · exact freshCall_keeps hf hcodes hsums he hw hh
        · exact keepsCall_keeps hkc hcodes hsums he hw hh
  | _ => simp [callKeepsHeap] at hc

/-! ## The production checker -/

/-- **`Checker.ordinary` accepts a preserving kind only where its base rule or
`elementsCall` does**: every call layer but `elementsCall` reads an
`ordinary` step, and the others map the base's output. -/
theorem ordinary_run_base {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hp : kindPreserving e = true) (hr : ((Checker.ordinary G images).run j k e codes sums).value = some out) :
    (∃ out₀, checkStepUsing G images j k e codes sums = some out₀) ∨
      (PromiseCalls.elementsCall G images j e codes sums).isSome := by
  have hb : ∀ (e : StepEvidence ι), kindPreserving e = true → ∀ out,
      ((Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls.run
        j k e codes sums).value = some out →
      (∃ out₀, checkStepUsing G images j k e codes sums = some out₀) ∨
        (PromiseCalls.elementsCall G images j e codes sums).isSome := by
    intro e hp out hr
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
      Checker.keepingOwnCalls, Checker.keepingCalls, Checker.steps, h1, h2, h3, h4, h5] at hr
    cases hel : PromiseCalls.elementsCall G images j e codes sums with
    | some _ => exact .inr rfl
    | none =>
      simp only [hel, Bool.false_eq_true, if_false] at hr
      exact .inl ⟨out, hr⟩
  simp only [Checker.ordinary, Checker.keepingStable, Checker.boundedWrites, Checker.indexing,
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
      exact hb e hp o₅ hr
    · exact hb e hp o₄ hr

/-- A qualified body's checker (`Checker.withSubtyping`) accepts a preserving
kind only where its base rule does; its `select` is its `run`. -/
theorem withSubtyping_run_base {G : NormalGraph ι} {images : InstanceImageCheck G} {subtyping : BodySubtyping G}
    {ord : ∀ {A B p}, PositiveCertificates.checkUsing G images A B p = true → subtyping.check A B p = true}
    {j : Sequent ι} {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} (hp : kindPreserving e = true)
    (hr : ((Checker.withSubtyping G images subtyping ord).run j k e codes sums).value = some out) :
    ∃ out₀, checkStepUsing G images j k e codes sums = some out₀ := by
  simp only [Checker.withSubtyping, Checker.keepingStable, Checker.subtypingSteps, CheckResult.map,
    Option.map_eq_some_iff] at hr
  obtain ⟨o, hr, -⟩ := hr
  cases e <;> first | exact ⟨o, hr⟩ | cases hp

/-- **Every step the pass classifies preserving keeps the heap**, at the
production checker, where `run` accepts it. -/
theorem passPreserving_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {kE out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hpres : passPreserving G images j kE e codes sums = true)
    (hr : ((Checker.ordinary G images).run j kE e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) : KeepsPost G j ρ n W h := by
  simp only [passPreserving, Bool.or_eq_true] at hpres
  rcases hpres with hc | hp
  · exact callKeepsHeap_keeps hc hcodes hsums he hk hw hh
  · rcases ordinary_run_base hp hr with ⟨o, hb⟩ | hel
    · exact base_keeps hb hp hcodes hsums he hk hw hh
    · obtain ⟨⟨x, R⟩, hel⟩ := Option.isSome_iff_exists.mp hel
      exact elementsCall_keeps hel hcodes hsums he hw hh

/-! ## Both exits of a preserving step -/

/-- **The selective frame at a preserving step, both exits.** A step whose
normal exit keeps the heap (`KeepsPost`) and whose checker's `run` accepted
it with output `out`, from the facts `k` handed to its rule and the store's
facts `S` at the name valuation `η`: a normal return is an action of
`{values: keep, stores: keep}` with the residual budget, the result's type,
the rule's output, and every fact of `S`, handed or not, at `η[r ↦ v]`; a
throw is an action of `{values: any, stores: any}` with the raised value
closed and of the exception family and the facts of `S` reading no heap. -/
theorem preserving_step_frame {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {kn out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hr : (checker.run j kn e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ η : Env} {r m : Nat} {s : IndexedHeap} {S : List Atom}
    (he : EnvOk G j.context ρ s.n s.W) (hkn : HeapKnowledge.Holds kn ε ρ s.h)
    (hkeep : KeepsPost G j ρ s.n s.W s.h)
    (hS : Named ε S η ρ m s) (hfr : ∀ a ∈ S, r ∉ a.names)
    {k : Nat} {h' : Heap} {t' : Tm} (hst : Steps k s.h (instantiate 0 ρ j.term) h' t') (hk : k < s.n) :
    (isVal t' = true → ∃ s' : IndexedHeap, Action Footprints.Closed.empty.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ meaning G j.type s'.n s'.W t' ∧
        HeapKnowledge.Holds out ε (push t' ρ) h' ∧ Named ε S (Env.set η r t') ρ m s') ∧
      (∀ x, Raises t' x → ∃ s' : IndexedHeap, Action Footprints.Closed.top.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ Scoped 0 x ∧ excOf G s'.n s'.W x ∧ Named ε (S.filter (·.heapFree)) η ρ m s') := by
  have hout := checker.sound hr hcodes hsums he hkn s.adm s.ok
  have hboth := cross_upto s.n (fun _ _ _ _ _ _ _ _ hb _ => hb) s.W s.W s.h _ s.ok s.ok hkeep hout
  have hj : SafePost (excOf G) (meaning G j.type)
      (fun h' v => Footprints.Closed.empty.Holds s.h h' ∧ HeapKnowledge.Holds out ε (push v ρ) h') s.n s.W s.h
      (instantiate 0 ρ j.term) := weaken (fun _ _ hq => ⟨hq.1.1, hq.2⟩) hboth
  refine ⟨fun hv => ?_, fun x hx => preserving_throw hj hst hx hk hS⟩
  obtain ⟨s', ha, he', hn, hT, hq, hS'⟩ := preserving_normal (Footprints.Closed.empty_le _) hj hst hv hk hS hfr
  exact ⟨s', ha, he', hn, hT, hq, hS'⟩

/-- **The pass's preserving steps at the production checker, both exits**:
`preserving_step_frame` with the heap kept by the pass's own classification
(`passPreserving_keeps`). -/
theorem pass_preserving_frame {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {kE out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hpres : passPreserving G images j kE e codes sums = true)
    (hr : ((Checker.ordinary G images).run j kE e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ η : Env} {r m : Nat} {s : IndexedHeap} {S : List Atom}
    (he : EnvOk G j.context ρ s.n s.W) (hkE : HeapKnowledge.Holds kE ε ρ s.h)
    (hS : Named ε S η ρ m s) (hfr : ∀ a ∈ S, r ∉ a.names)
    {k : Nat} {h' : Heap} {t' : Tm} (hst : Steps k s.h (instantiate 0 ρ j.term) h' t') (hk : k < s.n) :
    (isVal t' = true → ∃ s' : IndexedHeap, Action Footprints.Closed.empty.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ meaning G j.type s'.n s'.W t' ∧
        HeapKnowledge.Holds out ε (push t' ρ) h' ∧ Named ε S (Env.set η r t') ρ m s') ∧
      (∀ x, Raises t' x → ∃ s' : IndexedHeap, Action Footprints.Closed.top.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ Scoped 0 x ∧ excOf G s'.n s'.W x ∧ Named ε (S.filter (·.heapFree)) η ρ m s') :=
  preserving_step_frame _ hr hcodes hsums he hkE
    (passPreserving_keeps hpres hr hcodes hsums he hkE s.adm s.ok) hS hfr hst hk

end Steps

end Verification.TolerantFrames
