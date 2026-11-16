import Verification.Programs.TolerantFramesSteps
import Verification.Semantics.TolerantFramesCells

/-! # Tolerant frames: the pass's writing steps

A step the pass does not frame (`ordinary`, `written`, `boundedWrite`, and the
calls its predicates do not find keeping the heap) reads every fact
(`SinglePass.materialize … true`, `SinglePass.lean` 1322) and the store keeps
what its rule's output states (`applyDelta`). This module states, for such a
step:

- its judgment in the two-exit form `NodesChecked` takes, its rule's output on
  the normal exit (`judgment_with_output`), from an effect judgment: a typed
  field write within `{values: any, spines: keep}`
  (`field_write_judgment`), an element write within
  `{values: any, spines: grow}` (`element_write_judgment`), an allocation
  within `{values: keep, spines: keep}` (`allocated_judgment`), and a step
  with no effect judgment within `{values: any, spines: any}` on both exits
  (`top_judgment`, from `safePost_grow`: a run only grows the heap);
- which named facts survive an action of a closed effect: those reading no
  heap and the index facts the effect's change keeps (`Atom.keptBy`,
  `atom_kept`); a length lower bound under the field write's and the element
  write's effects by the tolerant frame at `{x.spine: grow}` (Grow:
  `named_lowerBound_grow`, `named_lowerBound_field`);
- both exits of the step (`writing_frame`): the action of each exit's effect,
  the residual budget, the type, the rule's output and the named facts each
  exit's effect keeps. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom)

/-! ## Named facts an effect keeps -/

/-- A named fact every action of the closed effect `c` keeps: one reading no
heap, or an index fact `c`'s change keeps (`IndexFact.keptBy`, no stable first
field). -/
def _root_.Verification.SinglePass.Atom.keptBy (c : Footprints.Closed) : Atom → Bool
  | .index x => x.fact.envOnly || x.fact.keptBy (HeapKnowledge.Changes.ofClosed c) (fun _ _ => false)
  | a => a.heapFree

/-- **A kept named fact survives an action of its effect.** -/
theorem atom_kept {c : Footprints.Closed} {a : Atom} (hk : a.keptBy c = true) {η ρ : Env} {s s' : IndexedHeap}
    (hact : Action c.fp ρ s s') (ha : AtomHolds ε a η s.h) : AtomHolds ε a η s'.h := by
  cases a with
  | index x =>
    simp only [Atom.keptBy, Bool.or_eq_true] at hk
    rcases hk with he | hk
    · exact atomHolds_heapFree (a := .index x) he ha s'.h
    · intro x' hx hcnd
      simp only [List.mem_singleton] at hx
      subst hx
      have hc : (HeapKnowledge.Changes.ofClosed c).Holds s.h s'.h :=
        HeapKnowledge.Changes.ofClosed_holds (Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp hact.2))
      exact HeapKnowledge.IndexFact.holdsAt_kept hc (fun _ _ _ _ _ _ _ hf => by simp at hf) hk
        (ha x' (List.mem_singleton_self _) hcnd)
  | _ => exact atomHolds_heapFree (by simpa only [Atom.keptBy] using hk) ha s'.h

/-- **(Grow) as a named fact** (the note, Proposition "Axioms of the
atoms"): a length lower bound over names survives every action of
`{values: any, spines: grow}`: the tolerant frame at `{x.spine: grow}`
(`grow`, `Parity.atom_frame`), the effect reading its classes at no name. -/
theorem named_lowerBound_grow {y x : Nat} {η ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : Named ε [.index ⟨lowerBoundFact y x, none, false⟩] η ρ m s) :
    Box growEffect.fp (Named ε [.index ⟨lowerBoundFact y x, none, false⟩] η) ρ m s := by
  intro s' ha a hm
  simp only [List.mem_singleton] at hm
  subst hm
  intro a' ha' _
  simp only [List.mem_singleton] at ha'
  subst ha'
  have hb : LowerBound ε y x η m s :=
    hS _ (List.mem_singleton_self _) _ (List.mem_singleton_self _) (fun _ h => by cases h)
  exact grow hb s' ⟨ha.1, Footprints.Closed.post_iff.mpr (Footprints.Closed.post_iff.mp ha.2)⟩

/-- (Grow) under the field write's effect, within the element write's. -/
theorem named_lowerBound_field {y x : Nat} {η ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : Named ε [.index ⟨lowerBoundFact y x, none, false⟩] η ρ m s) :
    Box fieldWriteEffect.fp (Named ε [.index ⟨lowerBoundFact y x, none, false⟩] η) ρ m s :=
  fun s' ha => named_lowerBound_grow hS s' (action_le_closed (by decide) ha)

/-! ## A run only grows the heap -/

/-- **A run only grows the heap**: a normal-only judgment holds on both exits
with each exit's heap at least as long as the first one. -/
theorem safePost_grow {Ξ T : Fam} {Q : Post} : ∀ {n W h t} (b : Nat), b ≤ h.length →
    SafePost Ξ T Q n W h t →
    SafePostExc Ξ T (fun h' v => b ≤ h'.length ∧ Q h' v) (fun h' => b ≤ h'.length) n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ hs; exact hs
  | succ n ih =>
    intro W h t b hb hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, ht, hq⟩ | hr) | ⟨U, h', t', hx, hu, st, hh, hs'⟩
    · exact .inl (.inl ⟨hv, ht, hb, hq⟩)
    · exact .inl (.inr ⟨hr, hb⟩)
    · exact .inr ⟨U, h', t', hx, hu, st, hh, ih b (Nat.le_trans hb (Footprints.step_length_le st)) hs'⟩

section Writes
variable {ι : Type} [DecidableEq ι]
open ProgramTyping PositiveCertificates ProgramCertificates PositiveGraphs PositiveRules HeapExpressionRules

/-! ## Judgments with the rule's output -/

/-- **A step's effect judgment with its rule's output**: the checker's `run`
accepted the step with output `out` from the facts `k`, and the step's term
meets `cn` and `ce` from `h`: the form `NodesChecked` takes, with `out` the
normal exit's post. -/
theorem judgment_with_output {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} (hr : (checker.run j k e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {cn ce : Footprints.Closed} {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) (hρ : RootsOk W ρ)
    (hexc : SafePostExc (excOf G) (meaning G j.type) (fun h' _ => cn.Holds h h') (fun h' => ce.Holds h h') n W h
      (instantiate 0 ρ j.term)) :
    SafePostExc (excOf G) (meaning G j.type) (fun h' v => cn.Holds h h' ∧ HeapKnowledge.Holds out ε (push v ρ) h')
      (fun h' => ce.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) :=
  SafePostExc.weaken (fun _ _ hq => hq) (fun _ hq => ⟨hq.1, trivial⟩)
    (SafePostExc.cross_upto n (fun _ _ _ _ _ _ _ _ hb _ => hb) W W h _ hh hh hexc
      (SafePostExc.of_post (R := fun _ => True) (fun _ => trivial)
        (checker.sound hr hcodes hsums he hk hw hh (SafePostExcW.refs hexc) hρ)))

/-- **A step with no effect judgment**, an ordinary call or expression: its
rule's output, both exits within `{values: any, spines: any}`. -/
theorem top_judgment {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} (hr : (checker.run j k e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) (hρ : RootsOk W ρ)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePostExc (excOf G) (meaning G j.type)
      (fun h' v => Footprints.Closed.top.Holds h h' ∧ HeapKnowledge.Holds out ε (push v ρ) h')
      (fun h' => Footprints.Closed.top.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) := by
  exact SafePostExc.weaken (fun _ _ hq => ⟨Footprints.Closed.holds_top.mpr hq.1, hq.2⟩)
    (fun _ hq => ⟨Footprints.Closed.holds_top.mpr hq, trivial⟩)
    (safePost_grow h.length (Nat.le_refl _) (checker.sound hr hcodes hsums he hk hw hh href hρ))

/-- **A write within a closed effect, with its rule's output**: a field or
element write the pass's footprint check admits within `c`
(`ExpressionEffects.writeWithin`, `SinglePass.lean` 1360), in the form
`NodesChecked` takes. -/
theorem write_judgment {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} (hr : (checker.run j k e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) {c : Footprints.Closed}
    (hc : ExpressionEffects.writeWithin G j.context c j.term = true)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) (hρ : RootsOk W ρ)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePostExc (excOf G) (meaning G j.type) (fun h' v => c.Holds h h' ∧ HeapKnowledge.Holds out ε (push v ρ) h')
      (fun h' => c.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) :=
  judgment_with_output checker hr hcodes hsums he hk hw hh hρ
    (ExpressionEffects.write_within_exc hc he hh (erase (checker.sound hr hcodes hsums he hk hw hh href hρ)))

/-- **A typed field write**, within `{values: any, spines: keep}`
(`ExpressionEffects.field_write_within_exc`), with its rule's output. -/
theorem field_write_judgment {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} (hr : (checker.run j k e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (hc : ExpressionEffects.fieldWriteWithin G j.context fieldWriteEffect j.term = true)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) (hρ : RootsOk W ρ)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePostExc (excOf G) (meaning G j.type)
      (fun h' v => fieldWriteEffect.Holds h h' ∧ HeapKnowledge.Holds out ε (push v ρ) h')
      (fun h' => fieldWriteEffect.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) :=
  judgment_with_output checker hr hcodes hsums he hk hw hh hρ
    (ExpressionEffects.field_write_within_exc hc he hh (erase (checker.sound hr hcodes hsums he hk hw hh href hρ)))

/-- **An element write at any index of any array**, within
`{values: any, spines: grow}`, with its rule's output (`write_judgment` at
`growEffect`). -/
theorem element_write_judgment {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} (hr : (checker.run j k e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (hc : ExpressionEffects.writeWithin G j.context growEffect j.term = true)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) (hρ : RootsOk W ρ)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePostExc (excOf G) (meaning G j.type)
      (fun h' v => growEffect.Holds h h' ∧ HeapKnowledge.Holds out ε (push v ρ) h')
      (fun h' => growEffect.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) :=
  write_judgment checker hr hcodes hsums hc he hk hw hh hρ href

/-- **A step whose checked normal effect is empty, an allocation among them**,
at the production checker: its normal exit within `{values: keep, spines: keep}` with its rule's
output, its throw within `{values: any, spines: any}`. -/
theorem preserving_judgment {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {kE out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hpres : (Checker.ordinary G images).normal j kE e codes sums = Footprints.Closed.empty)
    (hr : ((Checker.ordinary G images).run j kE e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ε ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) (hρ : RootsOk W ρ)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePostExc (excOf G) (meaning G j.type)
      (fun h' v => Footprints.Closed.empty.Holds h h' ∧ HeapKnowledge.Holds out ε (push v ρ) h')
      (fun h' => Footprints.Closed.top.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) := by
  have hboth := cross_upto n (fun _ _ _ _ _ _ _ _ hb _ => hb) W W h _ hh hh
    ((Checker.ordinary G images).normal_sound hr hcodes hsums he hk hw hh href hpres)
    ((Checker.ordinary G images).sound hr hcodes hsums he hk hw hh href hρ)
  exact SafePostExc.weaken (fun _ _ hq => ⟨hq.2.1.1, hq.2.2⟩)
    (fun _ hq => ⟨Footprints.Closed.holds_top.mpr hq, trivial⟩) (safePost_grow h.length (Nat.le_refl _) hboth)

end Writes

/-! ## Both exits of a writing step -/

/-- **A step's exits with the named facts its effects keep.** A judgment whose
normal exit is within `cn` with post `Qn` and whose throw is within `ce`, run
with budget left: a normal return is an action of `cn` with the residual
budget, the value's type, `Qn`, and the named facts `Sn` that hold after
every action of `cn`, at `η[r ↦ v]`; a throw is an action of `ce` with the
raised value closed and of the exception family, and the named facts `Se`
that hold after every action of `ce`. -/
theorem writing_frame {Ξ T : Fam} {cn ce : Footprints.Closed} {Qn : Post} {Sn Se : List Atom} {η ρ : Env}
    {r m : Nat} {s : IndexedHeap} {t t' : Tm} {h' : Heap} {k : Nat}
    (hsafe : SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ True)
      s.n s.W s.h t)
    (hst : Steps k s.h t h' t') (hk : k < s.n)
    (hSn : Box cn.fp (Named ε Sn η) ρ m s) (hSe : Box ce.fp (Named ε Se η) ρ m s)
    (hr : ∀ a ∈ Sn, r ∉ a.names) :
    (isVal t' = true → ∃ s' : IndexedHeap, Action cn.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        T s'.n s'.W t' ∧ Qn h' t' ∧ Named ε Sn (Env.set η r t') ρ m s') ∧
      (∀ x, Raises t' x → ∃ s' : IndexedHeap, Action ce.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        Scoped 0 x ∧ Ξ s'.n s'.W x ∧ Named ε Se η ρ m s') := by
  refine ⟨fun hv => ?_, fun x hx => ?_⟩
  · obtain ⟨s', ha, he', hn', hT, hq⟩ := action_normal (ρ := ρ) hsafe hst hv hk
    exact ⟨s', ha, he', hn', hT, hq, named_set t' hr (hSn s' ha)⟩
  · obtain ⟨s', ha, he', hn', hsc, hΞ, -⟩ := action_throw (ρ := ρ) hsafe hst hx hk
    exact ⟨s', ha, he', hn', hsc, hΞ, hSe s' ha⟩

end Verification.TolerantFrames
