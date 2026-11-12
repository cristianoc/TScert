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
  field write within `{values: any, stores: keep}`
  (`field_write_judgment`), an element write within
  `{values: any, stores: grow}` (`element_write_judgment`), an allocation
  within `{values: keep, stores: keep}` (`allocated_judgment`), and a step
  with no effect judgment within `{values: any, stores: any}` on both exits
  (`top_judgment`, from `safePost_grow`: a run only grows the heap);
- which named facts survive an action of a closed effect: those reading no
  heap and the index facts the effect's change keeps (`Atom.keptBy`,
  `named_kept_box`), among them every length lower bound under the field
  write's and the element write's effects (Grow);
- both exits of the step (`writing_frame`): the action of each exit's effect,
  the residual budget, the type, the rule's output and the kept named
  facts. -/
namespace Verification.TolerantFrames
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
    (hact : Action c.fp ρ s s') (ha : AtomHolds a η s.h) : AtomHolds a η s'.h := by
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

/-- **(Keep by atom)** `Named S η ⊢ □_c Named S η` for `S` kept by `c`. -/
theorem named_kept_box {c : Footprints.Closed} {S : List Atom} (hk : ∀ a ∈ S, a.keptBy c = true) {η ρ : Env}
    {m : Nat} {s : IndexedHeap} (hS : Named S η ρ m s) : Box c.fp (Named S η) ρ m s :=
  fun _ ha a hm => atom_kept (hk a hm) ha (hS a hm)

/-- (Grow) as a named fact: a length lower bound over names is kept by the
element write's effect. -/
theorem lowerBound_keptBy_grow (y x : Nat) :
    (Atom.index ⟨lowerBoundFact y x, none, false⟩).keptBy growEffect = true := rfl

/-- The same bound is kept by the field write's effect. -/
theorem lowerBound_keptBy_field (y x : Nat) :
    (Atom.index ⟨lowerBoundFact y x, none, false⟩).keptBy fieldWriteEffect = true := rfl

/-! ## A run only grows the heap -/

/-- **A run only grows the heap**: a normal-only judgment holds on both exits
with each exit's heap at least as long as the first one. -/
theorem safePost_grow {Ξ T : Fam} {Q : Post} : ∀ {n W h t} (b : Nat), b ≤ h.length →
    SafePost Ξ T Q n W h t →
    SafePostExc Ξ T (fun h' v => b ≤ h'.length ∧ Q h' v) (fun h' => b ≤ h'.length) n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t b hb hs
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
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hexc : SafePostExc (excOf G) (meaning G j.type) (fun h' _ => cn.Holds h h') (fun h' => ce.Holds h h') n W h
      (instantiate 0 ρ j.term)) :
    SafePostExc (excOf G) (meaning G j.type) (fun h' v => cn.Holds h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => ce.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) :=
  SafePostExc.weaken (fun _ _ hq => hq) (fun _ hq => ⟨hq.1, trivial⟩)
    (SafePostExc.cross_upto n (fun _ _ _ _ _ _ _ _ hb _ => hb) W W h _ hh hh hexc
      (SafePostExc.of_post (R := fun _ => True) (fun _ => trivial) (checker.sound hr hcodes hsums he hk hw hh)))

/-- **A step with no effect judgment**, an ordinary call or expression: its
rule's output, both exits within `{values: any, stores: any}`. -/
theorem top_judgment {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} (hr : (checker.run j k e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G j.type)
      (fun h' v => Footprints.Closed.top.Holds h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => Footprints.Closed.top.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) := by
  exact SafePostExc.weaken (fun _ _ hq => ⟨Footprints.Closed.holds_top.mpr hq.1, hq.2⟩)
    (fun _ hq => ⟨Footprints.Closed.holds_top.mpr hq, trivial⟩)
    (safePost_grow h.length (Nat.le_refl _) (checker.sound hr hcodes hsums he hk hw hh))

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
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G j.type) (fun h' v => c.Holds h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => c.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) :=
  judgment_with_output checker hr hcodes hsums he hk hw hh
    (ExpressionEffects.write_within_exc hc he hh (erase (checker.sound hr hcodes hsums he hk hw hh)))

/-- **A typed field write**, within `{values: any, stores: keep}`
(`ExpressionEffects.field_write_within_exc`), with its rule's output. -/
theorem field_write_judgment {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} (hr : (checker.run j k e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (hc : ExpressionEffects.fieldWriteWithin G j.context fieldWriteEffect j.term = true)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G j.type)
      (fun h' v => fieldWriteEffect.Holds h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => fieldWriteEffect.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) :=
  judgment_with_output checker hr hcodes hsums he hk hw hh
    (ExpressionEffects.field_write_within_exc hc he hh (erase (checker.sound hr hcodes hsums he hk hw hh)))

/-- **An element write at any index of any array**, within
`{values: any, stores: grow}`, with its rule's output (`write_judgment` at
`growEffect`). -/
theorem element_write_judgment {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} (hr : (checker.run j k e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (hc : ExpressionEffects.writeWithin G j.context growEffect j.term = true)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G j.type)
      (fun h' v => growEffect.Holds h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => growEffect.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) :=
  write_judgment checker hr hcodes hsums hc he hk hw hh

/-- **A step the pass frames, an allocation among them**, at the production
checker: its normal exit within `{values: keep, stores: keep}` with its rule's
output, its throw within `{values: any, stores: any}`. -/
theorem preserving_judgment {G : NormalGraph ι} {images : InstanceImageCheck G}
    {j : Sequent ι} {kE out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hpres : passPreserving G images j kE e codes sums = true)
    (hr : ((Checker.ordinary G images).run j kE e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds kE ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G j.type)
      (fun h' v => Footprints.Closed.empty.Holds h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => Footprints.Closed.top.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) := by
  have hboth := cross_upto n (fun _ _ _ _ _ _ _ _ hb _ => hb) W W h _ hh hh
    (passPreserving_keeps hpres hr hcodes hsums he hk hw hh) ((Checker.ordinary G images).sound hr hcodes hsums he hk hw hh)
  exact SafePostExc.weaken (fun _ _ hq => ⟨hq.2.1.1, hq.2.2⟩)
    (fun _ hq => ⟨Footprints.Closed.holds_top.mpr hq, trivial⟩) (safePost_grow h.length (Nat.le_refl _) hboth)

end Writes

/-! ## Both exits of a writing step -/

/-- **A step's exits with the named facts its effects keep.** A judgment whose
normal exit is within `cn` with post `Qn` and whose throw is within `ce`, run
with budget left: a normal return is an action of `cn` with the residual
budget, the value's type, `Qn`, and the named facts `Sn` that `cn` keeps at
`η[r ↦ v]`; a throw is an action of `ce` with the raised value closed and of
the exception family, and the named facts `Se` that `ce` keeps. -/
theorem writing_frame {Ξ T : Fam} {cn ce : Footprints.Closed} {Qn : Post} {Sn Se : List Atom} {η ρ : Env}
    {r m : Nat} {s : IndexedHeap} {t t' : Tm} {h' : Heap} {k : Nat}
    (hsafe : SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ True)
      s.n s.W s.h t)
    (hst : Steps k s.h t h' t') (hk : k < s.n)
    (hn : ∀ a ∈ Sn, a.keptBy cn = true) (he : ∀ a ∈ Se, a.keptBy ce = true)
    (hSn : Named Sn η ρ m s) (hSe : Named Se η ρ m s) (hr : ∀ a ∈ Sn, r ∉ a.names) :
    (isVal t' = true → ∃ s' : IndexedHeap, Action cn.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        T s'.n s'.W t' ∧ Qn h' t' ∧ Named Sn (Env.set η r t') ρ m s') ∧
      (∀ x, Raises t' x → ∃ s' : IndexedHeap, Action ce.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        Scoped 0 x ∧ Ξ s'.n s'.W x ∧ Named Se η ρ m s') := by
  refine ⟨fun hv => ?_, fun x hx => ?_⟩
  · obtain ⟨s', ha, he', hn', hT, hq⟩ := action_normal (ρ := ρ) hsafe hst hv hk
    exact ⟨s', ha, he', hn', hT, hq, named_set t' hr (named_kept_box hn hSn s' ha)⟩
  · obtain ⟨s', ha, he', hn', hsc, hΞ, -⟩ := action_throw (ρ := ρ) hsafe hst hx hk
    exact ⟨s', ha, he', hn', hsc, hΞ, named_kept_box he hSe s' ha⟩

/-! ## Allocated cells from the array invariant -/

/-- **A built-in array's store location lists only cells of its world**: the
array invariant (`PositiveGraphs.arrayInvariant`) gives the store field a
location whose contract's stores are `builtinStoreT`, a tuple contract, so
`StoreCells` holds of a slot holding such an array. -/
theorem storeCells_of_arrayInvariant {P U : Fam} {N : List PropKey} {x : Nat} {ρ : Env} {m : Nat}
    {s : IndexedHeap} {flds : List (PropKey × Nat)} {oid : Nat} (hv : ρ x = .objAt flds .absent oid)
    (hs : (flds.lookup CallArguments.arrayStoreField).isSome = true)
    (hinv : PositiveGraphs.arrayInvariant P U N s.n s.W (ρ x)) : StoreCells x ρ m s := by
  obtain ⟨hview, -, -⟩ := hinv flds oid hv hs
  obtain ⟨flds', l, c, oid', he, hl, hc, hag⟩ := hview _ _ (List.mem_cons_self ..)
  rw [hv] at he
  cases he
  refine storeCells_of_listT (st := l) (c := c) ?_ hc
    (fun j hj U' u hu => ⟨⟨[], [], some U, true, .sparse⟩, hag j hj U' u hu⟩)
  simpa [storeOf, fieldsOf, hv, CallArguments.arrayStoreField] using hl

end Verification.TolerantFrames
