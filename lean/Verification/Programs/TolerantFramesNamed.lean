import Verification.Programs.TolerantFramesRuns
import Verification.Programs.SinglePass

/-! # Tolerant frames: the facts a step is not handed

The single pass stores facts over names (`SinglePass.Atom`) and hands a step's
rule only the facts over the names its expression mentions
(`SinglePass.materialize`); `SinglePass.applyDelta` removes a handed fact the
rule's output lost and keeps every other fact of the store. This module states
what keeps the facts that are not handed.

A **named fact** is read at a name valuation `η` (each name its value) and a
heap (`AtomHolds`); its meaning needs no slot. On the normal exit of a step
whose footprint is within `{values: keep, stores: keep}` (the preserving
cases: inspections, allocations and the calls keeping the heap), every named
fact holds after every action, whatever its names (`named_keep_box`): the
heap only grows (`atomHolds_extend`). On the exceptional exit the heap may
change arbitrarily, and the facts reading no heap hold (`named_any_box`): the
filter the pass applies at a handler edge (`Atom.heapFree`). The result's name
is fresh, so naming it keeps every stored fact (`named_set`). A fact the
effect does not tolerate is not kept by any action of a writing effect
(`slotless_not_framed`). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom)

/-! ## Named facts -/

/-- A named fact at the name valuation `η` and the heap `h`: the fact read
with each name for a slot. A separation fact relates the fields of its
subject's value to its partners' (its slots are names, not levels). -/
def AtomHolds (ε : HeapKnowledge.EntryState) : Atom → Env → Heap → Prop
  | .cell f, η, h => HeapFacts.Holds [f] η h
  | .value f, η, _ => HeapKnowledge.ValueHolds [f] η
  | .link g, η, h => HeapLinks.Holds [g] η h
  | .elem a, η, h => HeapKnowledge.ElemsHolds [a] η h
  | .index a, η, h => HeapKnowledge.IndexHolds ε [a] η h
  | .sep f, η, _ => ∀ p ∈ f.partners, ∀ g ∈ p.2, HeapSeparation.Apart η f.slot f.fields p.1 g

/-- The facts the pass keeps at a handler edge (`SinglePass`'s edge store of
a throw): values, alias links, separation and index facts reading the
environment alone. -/
def _root_.Verification.SinglePass.Atom.heapFree : Atom → Bool
  | .cell _ | .elem _ => false
  | .link g => g.alias
  | .index x => x.fact.envOnly
  | .value _ | .sep _ => true

/-- **Every named fact survives an extension of the heap**, whether or not
its names have slots. -/
theorem atomHolds_extend {a : Atom} {η : Env} {h : Heap} (vs : List Val) (ha : AtomHolds ε a η h) :
    AtomHolds ε a η (h ++ vs) := by
  cases a with
  | cell f =>
    intro f' hf
    obtain ⟨flds, c, oid, u, he, hr, hm⟩ := ha f' hf
    exact ⟨flds, c, oid, u, he, hr.alloc_frames vs, hm⟩
  | value f => exact ha
  | link g => exact HeapLinks.alloc_frames vs ha
  | elem e => exact HeapKnowledge.elemsHolds_extend vs ha
  | index x => exact HeapKnowledge.indexHolds_extend vs ha
  | sep f => exact ha

/-- **A fact reading no heap holds in every heap.** -/
theorem atomHolds_heapFree {a : Atom} {η : Env} {h : Heap} (hf : a.heapFree = true) (ha : AtomHolds ε a η h)
    (h' : Heap) : AtomHolds ε a η h' := by
  cases a with
  | cell f => simp [Atom.heapFree] at hf
  | elem e => simp [Atom.heapFree] at hf
  | value f => exact ha
  | sep f => exact ha
  | link g =>
    simp only [Atom.heapFree] at hf
    intro g' hg
    simp only [List.mem_singleton] at hg
    subst hg
    have := ha g' (List.mem_singleton_self _)
    simp only [hf, ite_true] at this ⊢
    exact this
  | index x =>
    simp only [Atom.heapFree] at hf
    intro x' hx hc
    simp only [List.mem_singleton] at hx
    subst hx
    exact HeapKnowledge.IndexFact.holdsAt_envOnly hf (ha x' (List.mem_singleton_self _) hc) h'

/-- A named fact reads only the values of its names. -/
theorem atomHolds_congr {a : Atom} {η η' : Env} {h : Heap} (hs : ∀ x ∈ a.names, η x = η' x) :
    AtomHolds ε a η h ↔ AtomHolds ε a η' h := by
  cases a with
  | cell f =>
    have e : η f.slot = η' f.slot := hs _ (by simp [Atom.names])
    simp only [AtomHolds, HeapFacts.Holds, List.mem_singleton, forall_eq, e]
  | value f =>
    have e : η f.slot = η' f.slot := hs _ (by simp [Atom.names])
    simp only [AtomHolds, HeapKnowledge.ValueHolds, List.mem_singleton, forall_eq, e]
  | link g =>
    have e₁ : η g.cell = η' g.cell := hs _ (by simp [Atom.names])
    have e₂ : η g.value = η' g.value := hs _ (by simp [Atom.names])
    simp only [AtomHolds, HeapLinks.Holds, List.mem_singleton, forall_eq, e₁, e₂]
  | elem e =>
    have e₁ : η e.slot = η' e.slot := hs _ (by simp [Atom.names])
    have e₂ : ∀ b, e.cond = some b → η b = η' b := fun b hb => hs _ (by simp [Atom.names, hb])
    simp only [AtomHolds, HeapKnowledge.ElemsHolds, List.mem_singleton, forall_eq, e₁]
    constructor
    · intro H hc; exact H fun b hb => (e₂ b hb) ▸ hc b hb
    · intro H hc; exact H fun b hb => (e₂ b hb).symm ▸ hc b hb
  | index x =>
    have e₁ : ∀ s ∈ x.fact.slots, η s = η' s := fun s hs' => hs _ (by simp [Atom.names, hs'])
    have e₂ : ∀ b, x.cond = some b → η b = η' b := fun b hb => hs _ (by simp [Atom.names, hb])
    simp only [AtomHolds, HeapKnowledge.IndexHolds, List.mem_singleton, forall_eq,
      HeapKnowledge.IndexFact.holdsAt_congr e₁]
    constructor
    · intro H hc; exact H fun b hb => (e₂ b hb) ▸ hc b hb
    · intro H hc; exact H fun b hb => (e₂ b hb).symm ▸ hc b hb
  | sep f =>
    have e₁ : η f.slot = η' f.slot := hs _ (by simp [Atom.names])
    have e₂ : ∀ p ∈ f.partners, η p.1 = η' p.1 := fun p hp => hs _ (by
      simp only [Atom.names, List.mem_cons, List.mem_map]
      exact .inr ⟨p, hp, rfl⟩)
    simp only [AtomHolds, HeapSeparation.Apart, e₁]
    constructor
    · intro H p hp g hg; rw [← e₂ p hp]; exact H p hp g hg
    · intro H p hp g hg; rw [e₂ p hp]; exact H p hp g hg

/-- The name valuation with the name `r` holding `v`. -/
def Env.set (η : Env) (r : Nat) (v : Tm) : Env := fun x => if x = r then v else η x

/-- The facts `S` hold at the name valuation `η`: an assertion of the state's
heap alone, its slots and entry mark unread. -/
def Named (ε : HeapKnowledge.EntryState) (S : List Atom) (η : Env) : Assertion := fun _ _ s => ∀ a ∈ S, AtomHolds ε a η s.h

/-- **Naming a step's result keeps every stored fact**, its name fresh. -/
theorem named_set {S : List Atom} {η : Env} {r : Nat} (v : Tm) (hr : ∀ a ∈ S, r ∉ a.names) {ρ : Env}
    {m : Nat} {s : IndexedHeap} (hS : Named ε S η ρ m s) : Named ε S (Env.set η r v) ρ m s := by
  intro a ha
  refine (atomHolds_congr fun x hx => ?_).mp (hS a ha)
  have : x ≠ r := fun e => hr a ha (e ▸ hx)
  simp [Env.set, this]

/-! ## The frame of the facts not handed to a step -/

/-- **(Keep) Every named fact survives every action of an effect within
`{values: keep, stores: keep}`**, its names held by slots or not. -/
theorem named_keep_box {c : Footprints.Closed} (hle : c.le Footprints.Closed.empty = true) {S : List Atom}
    {η ρ : Env} {m : Nat} {s : IndexedHeap} (hS : Named ε S η ρ m s) : Box c.fp (Named ε S η) ρ m s := by
  intro s' ha a hm
  have hc : c.Holds s.h s'.h := Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp ha.2)
  obtain ⟨vs, hvs⟩ := Footprints.Closed.holds_empty.mp (hc.mono hle)
  rw [← hvs]
  exact atomHolds_extend vs (hS a hm)

/-- **The facts reading no heap survive every admissible transition**: under
the effect `{values: any, stores: any}` of an exceptional exit. -/
theorem named_any_box {Φ : Footprint} {S : List Atom} (hf : ∀ a ∈ S, a.heapFree = true) {η ρ : Env} {m : Nat}
    {s : IndexedHeap} (hS : Named ε S η ρ m s) : Box Φ (Named ε S η) ρ m s :=
  fun s' _ a hm => atomHolds_heapFree (hf a hm) (hS a hm) s'.h

/-- The pass's handler store: the facts of the entry's that read no heap. -/
theorem named_filter_heapFree {S : List Atom} {η ρ : Env} {m : Nat} {s : IndexedHeap} (hS : Named ε S η ρ m s) :
    Named ε (S.filter (·.heapFree)) η ρ m s :=
  fun a ha => hS a (List.mem_filter.mp ha).1

/-- An effect within another by class evidence valid at the step's first heap
keeps what the other keeps: the frame of a syntactic weakening reads its
class evidence at the action's source state (`action_le`). -/
theorem named_le_box {cl : ClassEvidence} {Φ : Footprint} {c : Footprints.Closed}
    (hle : Footprint.le cl Φ c.fp = true) (hcE : c.le Footprints.Closed.empty = true) {S : List Atom}
    {η ρ : Env} {m : Nat} {s : IndexedHeap} (hc : ClassOk cl ρ s.h) (hS : Named ε S η ρ m s) :
    Box Φ (Named ε S η) ρ m s :=
  box_anti (fun _ ha => action_le hle hc ha) (named_keep_box hcE hS)

/-! ## The step: both exits -/

/-- **The normal exit of a preserving step frames every fact it was not
handed.** A step's judgment whose normal exit is within `cn ≤ empty` from its
first heap, and a run to a value with budget left: the endpoint is an action
of `cn`, with the residual budget, the value's type, the exact post, and every
named fact of `S` at the valuation naming the result `r`. The facts' names
need no slot. -/
theorem preserving_normal {Ξ T : Fam} {cn : Footprints.Closed} {Qn : Post} {S : List Atom} {η ρ : Env} {r m : Nat}
    {s : IndexedHeap} {t v : Tm} {h' : Heap} {k : Nat}
    (hle : cn.le Footprints.Closed.empty = true)
    (hsafe : SafePost Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) s.n s.W s.h t)
    (hst : Steps k s.h t h' v) (hv : isVal v = true) (hk : k < s.n)
    (hS : Named ε S η ρ m s) (hr : ∀ a ∈ S, r ∉ a.names) :
    ∃ s' : IndexedHeap, Action cn.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ T s'.n s'.W v ∧ Qn h' v ∧
      Named ε S (Env.set η r v) ρ m s' := by
  obtain ⟨s', ha, he, hn, hT, hc, hq⟩ :=
    run_normal (SafePostExc.of_post (R := fun _ => True) (fun _ => trivial) hsafe) hst hv hk
  subst he
  have hact : Action cn.fp ρ s s' := ⟨ha, Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp hc)⟩
  exact ⟨s', hact, rfl, hn, hT, hq, named_set v hr (named_keep_box hle hS s' hact)⟩

/-- **The exceptional exit of a step frames the facts reading no heap.** A
normal-only judgment leaves a throw at `{values: any, stores: any}`; the
facts the pass keeps at a handler edge (`Atom.heapFree`) hold at the
endpoint, with the raised value closed and of the exception family. -/
theorem preserving_throw {Ξ T : Fam} {Q : Post} {S : List Atom} {η ρ : Env} {m : Nat} {s : IndexedHeap}
    {t t' e : Tm} {h' : Heap} {k : Nat} (hsafe : SafePost Ξ T Q s.n s.W s.h t) (hst : Steps k s.h t h' t')
    (hr : Raises t' e) (hk : k < s.n) (hS : Named ε S η ρ m s) :
    ∃ s' : IndexedHeap, Action Footprints.Closed.top.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
      Scoped 0 e ∧ Ξ s'.n s'.W e ∧ Named ε (S.filter (·.heapFree)) η ρ m s' := by
  obtain ⟨s', ha, he, hn, hsc, hΞ⟩ := action_throw_top (ρ := ρ) hsafe hst hr hk
  exact ⟨s', ha, he, hn, hsc, hΞ,
    named_any_box (fun a ha => (List.mem_filter.mp ha).2) (named_filter_heapFree hS) s' ha⟩

/-! ## The preserving judgments -/

/-- An inspection's normal exit is within `{values: keep, stores: keep}`
(`HeapExpressionRules.inspect_frame`): reads, tests, arithmetic and
allocations of evaluated operands. -/
theorem inspection_keeps {Ξ T : Fam} {n W h t} (hs : Safe Ξ T n W h t) (hp : Purity.inspectTerm t = true)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost Ξ T (fun h' _ => Footprints.Closed.empty.Holds h h' ∧ True) n W h t :=
  HeapExpressionRules.inspect_frame hs hp hw hh fun _ _ hpre => ⟨Footprints.Closed.holds_empty.mpr hpre, trivial⟩

section Calls
variable {ι : Type} [DecidableEq ι]
open ProgramTyping PositiveCertificates ProgramCertificates PositiveGraphs PositiveRules

/-- **A call the pass keeps the heap across (`PromiseCalls.keepsCall`)** has
its normal exit within `{values: keep, stores: keep}`: its selected signature
is within the empty footprint (`ExpressionEffects.selectedCall_sound`). -/
theorem keepsCall_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : PromiseCalls.keepsCall G images j e codes sums = true) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums) {ρ n W h} (he : EnvOk G j.context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type) (fun h' _ => Footprints.Closed.empty.Holds h h' ∧ True) n W h
      (instantiate 0 ρ j.term) := by
  unfold PromiseCalls.keepsCall at hc
  split at hc
  · rename_i p
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hsel⟩, -⟩, ht⟩ := hc
    exact PromiseCalls.post_with_type (fun _ _ _ _ _ hq => ⟨hq, trivial⟩)
      (ExpressionEffects.selectedCall_sound p ht hsel hcodes hsums he hw hh href)
  · contradiction

/-- A call allocating its result (`PromiseCalls.freshCall`) has its normal
exit within `{values: keep, stores: keep}`: its selected signature keeps the
heap (`PromiseCalls.keepsHeap_prefix`). -/
theorem freshCall_keeps {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : PromiseCalls.freshCall G images j e codes sums = true) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums) {ρ n W h} (he : EnvOk G j.context ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (href : RefsOk W (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type) (fun h' _ => Footprints.Closed.empty.Holds h h' ∧ True) n W h
      (instantiate 0 ρ j.term) := by
  unfold PromiseCalls.freshCall at hc
  split at hc
  · rename_i p
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hops⟩, hsel⟩, ht⟩ := hc
    split at hsel
    · rename_i eff heff
      simp only [Bool.and_eq_true] at hsel
      exact PromiseCalls.post_with_type
        (fun _ _ _ _ _ hq => ⟨Footprints.Closed.holds_empty.mpr (PromiseCalls.keepsHeap_prefix hsel.1 hq), trivial⟩)
        (ExpressionEffects.selected_sound p ht hops heff hcodes hsums he hw hh href)
    · cases hsel
  · contradiction

/-- **The selective frame at a call keeping the heap, both exits.** At a node
whose step is a call `keepsCall` accepts, with the facts `k` handed to its
rule holding at the node's slots and the store's facts `S` at the name
valuation `η`, a run with budget left ends, on a normal return, in an action
of `{values: keep, stores: keep}` where the result meets its type, the rule's
output (`HeapKnowledge.shift k`) holds, and every fact of `S`, handed or not,
holds with the result named `r`; on a throw, in an action of
`{values: any, stores: any}` where the raised value is of the exception family
and the facts of `S` reading no heap hold. -/
theorem keepsCall_frame {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : PromiseCalls.keepsCall G images j e codes sums = true) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums) {ρ η : Env} {r m : Nat} {s : IndexedHeap}
    {kn : HeapKnowledge.Knowledge} {S : List Atom} (he : EnvOk G j.context ρ s.n s.W)
    (href : RefsOk s.W (instantiate 0 ρ j.term))
    (hkn : HeapKnowledge.Holds kn ε ρ s.h) (hS : Named ε S η ρ m s) (hr : ∀ a ∈ S, r ∉ a.names)
    {k : Nat} {h' : Heap} {t' : Tm} (hst : Steps k s.h (instantiate 0 ρ j.term) h' t') (hk : k < s.n) :
    (isVal t' = true → ∃ s' : IndexedHeap, Action Footprints.Closed.empty.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ meaning G j.type s'.n s'.W t' ∧
        HeapKnowledge.Holds (HeapKnowledge.shift kn) ε (push t' ρ) h' ∧ Named ε S (Env.set η r t') ρ m s') ∧
      (∀ x, Raises t' x → ∃ s' : IndexedHeap, Action Footprints.Closed.top.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ Scoped 0 x ∧ excOf G s'.n s'.W x ∧ Named ε (S.filter (·.heapFree)) η ρ m s') := by
  have hj := keepsCall_keeps hc hcodes hsums he s.adm s.ok href
  refine ⟨fun hv => ?_, fun x hx => preserving_throw hj hst hx hk hS⟩
  obtain ⟨s', ha, he', hn, hT, -, hS'⟩ := preserving_normal (Footprints.Closed.empty_le _) hj hst hv hk hS hr
  have hc' : Footprints.Closed.empty.Holds s.h h' := by
    rw [← he']; exact Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp ha.2)
  obtain ⟨vs, rfl⟩ := Footprints.Closed.holds_empty.mp hc'
  exact ⟨s', ha, he', hn, hT, HeapKnowledge.shift_holds (HeapKnowledge.alloc_frames vs hkn), hS'⟩

end Calls

/-! ## A fact the effect does not tolerate

A fact over a name no slot holds is not handed to a step even when the step
reads every fact (`SinglePass.materialize` with `whole`: its renaming fails),
so `applyDelta` keeps it. Across a writing step nothing justifies it: a cell
fact of the object the name holds fails after an action of
`{values: any, stores: any}`. -/

/-- A state of one location holding `v`, at budget 1. -/
def oneState (v : Val) (hv : isVal v = true) (hs : isSourceVal v = true) (hn : refs v = []) : IndexedHeap :=
  ⟨1, ofEntries [(.field, anyCtr)], [v], Nat.one_pos,
    fun l c hl => by
      simp only [lookup, toList, entries_ofEntries] at hl
      rcases l with _ | l <;> simp at hl
      subst hl
      exact ⟨fun _ _ _ _ _ _ hv => hv, fun _ _ _ _ hv => hv⟩,
    ⟨⟨by simp, fun l c hl => by
      simp only [lookup, toList, entries_ofEntries] at hl
      rcases l with _ | l <;> simp at hl
      subst hl
      exact ⟨v, rfl, fun _ _ => hv⟩⟩,
    fun l r hl => by
      simp only [roleAt, roles, entries_ofEntries] at hl
      rcases l with _ | l <;> simp at hl
      subst hl
      exact ⟨v, rfl, hs, RefsOk_of_nil hn⟩⟩⟩

/-- **A cell fact over a name is not framed by a writing effect**: name 0
holds an object whose field `f` is location 0; the fact that the field holds
`null` holds before an action of `{values: any, stores: any}` and not after. -/
theorem slotless_not_framed :
    ¬ ∀ (η ρ : Env) (m : Nat) (s : IndexedHeap),
      Named ε [.cell ⟨0, { nul := true }, "f"⟩] η ρ m s →
        Box Footprints.Closed.top.fp (Named ε [.cell ⟨0, { nul := true }, "f"⟩] η) ρ m s := by
  intro H
  let η : Env := fun _ => .objAt [("f", 0)] .absent 0
  have hb := H η η 0 (oneState .nul rfl rfl rfl) (fun a ha => by
    simp only [List.mem_singleton] at ha; subst ha
    intro f hf; simp only [List.mem_singleton] at hf; subst hf
    exact ⟨[("f", 0)], .absent, 0, .nul, rfl, by simp [HeapFacts.ReadGave, oneState], by decide⟩)
  have ha : Action Footprints.Closed.top.fp η (oneState .nul rfl rfl rfl) (oneState .tru rfl rfl rfl) :=
    action_top ⟨Nat.le_refl 1, by
      show WExt (trunc 1 (Nat.le_refl 1) (ofEntries [(.field, anyCtr)])) (ofEntries [(.field, anyCtr)]); rw [trunc_id]; exact WExt_refl _⟩
  have := hb _ ha _ (List.mem_singleton_self _) _ (List.mem_singleton_self _)
  obtain ⟨flds, c, oid, u, he, hr, hm⟩ := this
  simp only [η, Tm.objAt.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  simp [HeapFacts.ReadGave, oneState] at hr
  subst hr
  exact absurd hm (by decide)

end Verification.TolerantFrames
