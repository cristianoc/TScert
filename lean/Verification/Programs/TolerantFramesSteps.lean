import Verification.Programs.TolerantFramesNamed

/-! # Tolerant frames: a step's checked normal effect

The pass applies a step's output with the frame of the facts it was not
handed (`applyDelta … true`) where the step's checked normal effect
(`PromiseCalls.stepNormal`) is `{values: keep, spines: keep}`: the tolerant
frame at the support `all` keeps every fact there (`named_keep_box`). This
module proves the effect sound (`stepNormal_sound`):

- a step other than a call or a write states the empty effect where its base
  rule (`HeapExpressionRules.checkStepUsing`) accepts it, which fixes the
  term's shape, an inspection or a graph closure's creation (`base_shape`,
  `base_keeps`);
- a call states it by its selected signature (`elementsCall_keeps`,
  `requiresCall_keeps`, `freshCall_keeps`, `keepsCall_keeps`);
- with the output a checker's `run` gives, both exits of the step: the
  action, the residual budget, the type, the rule's output, and the store's
  facts at the name valuation (`preserving_step_frame`). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom)

section Steps
variable {ι : Type} [DecidableEq ι]
open ProgramTyping PositiveCertificates ProgramCertificates PositiveGraphs PositiveRules HeapExpressionRules

/-- The step's normal exit is within `{values: keep, spines: keep}` from `h`. -/
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
  | zero => exact hs
  | succ n =>
    refine ⟨hs.1, ?_⟩
    rcases hs.2 with (⟨hv, _⟩ | ⟨_, hr, _⟩) | ⟨U, h', t', hx, hu, step, hh', hs'⟩
    · simp [instantiate, isVal] at hv
    · simp only [instantiate, instantiateArgs_eq_map, List.map] at hr
      cases hr with | makeArg hg _ hr => obtain ⟨rfl, rfl⟩ := singleton_get hg; cases hr
    · simp only [instantiate, instantiateArgs_eq_map, List.map] at step hs' ⊢
      obtain ⟨rfl, rfl⟩ := makeFn_step_inv rfl step
      exact Or.inr ⟨U, _, _, hx, hu, step, hh',
        refine_value rfl ⟨Footprints.Closed.holds_empty.mpr ⟨[.nul, .nul], by simp⟩, trivial⟩ hs'⟩

/-- **The base rule of a step other than a call or a write fixes the term's
shape**: the instantiated term is an inspection, or the term creates a graph
closure. -/
theorem base_shape {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι} {k out : HeapKnowledge.Knowledge}
    {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : checkStepUsing G images j k e codes sums = some out) (hord : ∀ p, e ≠ .ordinary p)
    (hwr : ∀ i v R q, e ≠ .written i v R q)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h) :
    Purity.inspectTerm (instantiate 0 ρ j.term) = true ∨
      ∃ arity E K start caps kind rest, j.term = .makeFn (.graph arity E K start caps kind rest) .nul := by
  have read : ∀ fld i, j.term = .readAt fld (.var i) → Purity.inspectTerm (ρ i) = true →
      Purity.inspectTerm (instantiate 0 ρ j.term) = true := fun fld i ht hi => by
    rw [ht]; simpa [instantiate, Purity.inspectTerm] using hi
  rw [checkStepUsing_eq] at hc
  cases e with
  | ordinary p => exact absurd rfl (hord p)
  | written i v R q => exact absurd rfl (hwr i v R q)
  | boundedWrite => simp at hc
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
            rw [spineSlots_eq hs]
            simp only [instantiate, instantiateArgs_eq_map, Purity.inspectTerm, List.map_map, List.all_eq_true,
              List.mem_map]
            rintro _ ⟨i, hi, rfl⟩
            have hv := (meaning_value (he.2 i _ (List.getElem?_eq_getElem (hin i hi)))).1
            simp only [Function.comp, instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero]
            cases hr : ρ i <;> simp_all [Purity.initTerm, Purity.operandTerm, isVal]
          · cases hc
        · cases hc

/-- **The base rule of a step other than a call or a write keeps the heap on
its normal exit.** -/
theorem base_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι} {k out : HeapKnowledge.Knowledge}
    {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : checkStepUsing G images j k e codes sums = some out) (hord : ∀ p, e ≠ .ordinary p)
    (hwr : ∀ i v R q, e ≠ .written i v R q) (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) : KeepsPost G j ρ n W h := by
  have hs := erase (checkStep_sound hc hcodes hsums he hk hw hh href)
  rcases base_shape hc hord hwr he hk with hi | ⟨_, _, _, _, _, _, _, ht⟩
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
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) : KeepsPost G j ρ n W h := by
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
              (fun _ _ _ _ _ hq => ⟨Footprints.Closed.holds_empty.mpr (PromiseCalls.keepsHeap_prefix hkeep (CallEffects.Effect.callPost_within hq)), trivial⟩)
              (ExpressionEffects.selected_sound p ht hops hsel hcodes hsums he hw hh href)
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
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) : KeepsPost G j ρ n W h := by
  simp only [PromiseCalls.requiresCall, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨rfl, hc⟩ := hc
  obtain ⟨eff, hsel, hs⟩ := PromiseCalls.requiresTree_sound hcodes hsums p hc
  rw [hsel] at hkeep
  exact PromiseCalls.post_with_type
    (fun _ _ _ _ _ hq => ⟨Footprints.Closed.holds_empty.mpr (PromiseCalls.keepsHeap_prefix hkeep (CallEffects.Effect.callPost_within hq)), trivial⟩)
    (hs he hk hw hh href)

/-- The two closed footprints differ. -/
theorem top_ne_empty : Footprints.Closed.top ≠ Footprints.Closed.empty := by
  intro h; injection h with h1; cases h1

/-- **A step's checked normal effect is sound** (`PromiseCalls.stepNormal`):
where it is `{values: keep, spines: keep}`, the step's normal exit keeps the
heap, by the call's selected signature or by the base rule's shape. -/
theorem stepNormal_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {kE : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hn : PromiseCalls.stepNormal G images j kE e codes sums = Footprints.Closed.empty)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) : KeepsPost G j ρ n W h := by
  have base : ∀ (e : StepEvidence ι), (∀ p, e ≠ .ordinary p) → (∀ i v R q, e ≠ .written i v R q) →
      (checkStepUsing G images j kE e codes sums).isSome = true → KeepsPost G j ρ n W h := by
    intro e hord hwr hs
    obtain ⟨out, hb⟩ := Option.isSome_iff_exists.mp hs
    exact base_keeps hb hord hwr hcodes hsums he hk hw hh href
  cases e with
  | ordinary p =>
    simp only [PromiseCalls.stepNormal] at hn
    split at hn
    · rename_i hel
      obtain ⟨⟨x, R⟩, hel⟩ := Option.isSome_iff_exists.mp hel
      exact elementsCall_keeps hel hcodes hsums he hw hh href
    · split at hn
      · rename_i hreq
        split at hn
        · rename_i hkeep; exact requiresCall_keeps hreq hkeep hcodes hsums he hk hw hh href
        · exact absurd hn top_ne_empty
      · split at hn
        · rename_i hc
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
          rcases hc with hf | ⟨-, hkc⟩
          · exact freshCall_keeps hf hcodes hsums he hw hh href
          · exact keepsCall_keeps hkc hcodes hsums he hw hh href
        · exact absurd hn top_ne_empty
  | written => exact absurd hn top_ne_empty
  | boundedWrite => exact absurd hn top_ne_empty
  | _ =>
    simp only [PromiseCalls.stepNormal] at hn
    split at hn
    · rename_i hs
      refine base _ ?_ ?_ hs
      · intro _ h; cases h
      · intro _ _ _ _ h; cases h
    · exact absurd hn top_ne_empty

/-! ## Both exits of a preserving step -/

/-- **The selective frame at a preserving step, both exits.** A step whose
normal exit keeps the heap (`KeepsPost`) and whose checker's `run` accepted
it with output `out`, from the facts `k` handed to its rule and the store's
facts `S` at the name valuation `η`: a normal return is an action of
`{values: keep, spines: keep}` with the residual budget, the result's type,
the rule's output, and every fact of `S`, handed or not, at `η[r ↦ v]`; a
throw is an action of `{values: any, spines: any}` with the raised value
closed and of the exception family and the facts of `S` reading no heap. -/
theorem preserving_step_frame {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {kn out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hr : (checker.run j kn e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ η : Env} {r m : Nat} {s : IndexedHeap} {S : List Atom}
    (he : EnvOk G j.context ρ s.n s.W) (hkn : HeapKnowledge.Holds kn ε ρ s.h) (hρ : RootsOk s.W ρ)
    (hkeep : KeepsPost G j ρ s.n s.W s.h)
    (hS : Named ε S η ρ m s) (hfr : ∀ a ∈ S, r ∉ a.names)
    {k : Nat} {h' : Heap} {t' : Tm} (hst : Steps k s.h (instantiate 0 ρ j.term) h' t') (hk : k < s.n) :
    (isVal t' = true → ∃ s' : IndexedHeap, Action Footprints.Closed.empty.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ meaning G j.type s'.n s'.W t' ∧
        HeapKnowledge.Holds out ε (push t' ρ) h' ∧ Named ε S (Env.set η r t') ρ m s') ∧
      (∀ x, Raises t' x → ∃ s' : IndexedHeap, Action Footprints.Closed.top.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ Scoped 0 x ∧ excOf G s'.n s'.W x ∧ Named ε (S.filter (·.heapFree)) η ρ m s') := by
  have hout := checker.sound hr hcodes hsums he hkn s.adm s.ok (SafePostW.refs hkeep) hρ
  have hboth := cross_upto s.n (fun _ _ _ _ _ _ _ _ hb _ => hb) s.W s.W s.h _ s.ok s.ok hkeep hout
  have hj : SafePost (excOf G) (meaning G j.type)
      (fun h' v => Footprints.Closed.empty.Holds s.h h' ∧ HeapKnowledge.Holds out ε (push v ρ) h') s.n s.W s.h
      (instantiate 0 ρ j.term) := weaken (fun _ _ hq => ⟨hq.1.1, hq.2⟩) hboth
  refine ⟨fun hv => ?_, fun x hx => preserving_throw hj hst hx hk hS⟩
  obtain ⟨s', ha, he', hn, hT, hq, hS'⟩ := preserving_normal (Footprints.Closed.empty_le _) hj hst hv hk hS hfr
  exact ⟨s', ha, he', hn, hT, hq, hS'⟩

end Steps

end Verification.TolerantFrames
