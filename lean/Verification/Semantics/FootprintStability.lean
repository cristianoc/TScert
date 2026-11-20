import Verification.Semantics.SeparationEvidence

/-! # The stability check

A **fact kind** has a meaning at a heap and a **support**: the regions it
reads, each with the largest change it tolerates. Its support lemma says that
it survives every change within its support. **Separation** of a support
region from a footprint region is the one disjointness check of separation
evidence (`SepEvidence.query`, `Semantics/SeparationEvidence.lean`). The
**stability check** of a fact under a footprint accepts when every footprint
entry either changes the support's regions within their tolerance or is
apart from them; its soundness theorem gives the support's premise from the
footprint's postcondition at a well-formed state, and the **frame** keeps
exactly the facts that pass it. -/
namespace Verification.Footprints

/-! ## Fact kinds -/

/-- The fact kinds today's knowledge holds, and density. -/
inductive FactKind where
  /-- An observation of a field's current contents (`HeapFacts.Fact`). -/
  | cell (f : HeapFacts.Fact)
  /-- A link: alias or a read of a field (`HeapLinks.Link`). -/
  | link (g : HeapLinks.Link)
  /-- A primitive predicate of a slot's value. -/
  | value (f : HeapFacts.Fact)
  /-- The first `n` indices of `x`'s spine are present. -/
  | dense (x n : Nat)
  /-- Every present element of `x`'s spine satisfies `R` (`CallEffects.ElemsAt`). -/
  | elems (x : Nat) (R : CallEffects.ElemPred)

def FactKind.Holds : FactKind → Env → Heap → Prop
  | .cell f, ρ, h => HeapFacts.Holds [f] ρ h
  | .link g, ρ, h => HeapLinks.Holds [g] ρ h
  | .value f, ρ, _ => f.contents.mem (ρ f.slot) = true
  | .dense x n, ρ, h => Dense x n ρ h
  | .elems x R, ρ, h => CallEffects.ElemsAt R (ρ x) h

def FactKind.support : FactKind → Footprint
  | .cell f => [(.field f.slot f.field, .keep)]
  | .link g => if g.alias then [] else [(.field g.cell g.field, .keep)]
  | .value _ => []
  | .dense x _ => [(.field x arraySpineKey, .grow)]
  | .elems x _ => [(.field x arraySpineKey, .keep), (.cells x, .keep)]

/-- The elements fact survives every change keeping its spine's location and
each element location the spine lists. -/
theorem elems_support {x : Nat} {R : CallEffects.ElemPred} {ρ : Env} {h h' : Heap}
    (hF : CallEffects.ElemsAt R (ρ x) h)
    (hs : Supported [(.field x arraySpineKey, .keep), (.cells x, .keep)] ρ h h') :
    CallEffects.ElemsAt R (ρ x) h' := by
  obtain ⟨s, ls, hst, hl, hall⟩ := hF
  have hkeep : ∀ e ∈ [((Region.field x arraySpineKey), Change.keep), (Region.cells x, Change.keep)],
      ∀ l v, e.1.mem ρ h l = true → h[l]? = some v → h'[l]? = some v := by
    intro e he l v hm hv
    obtain ⟨v', hv', hk⟩ := hs e he l v hm hv
    have hk' : e.2 = .keep := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl
    rw [hk'] at hk
    simp only [Change.Holds] at hk
    rw [← hk]; exact hv'
  have hfield : (Region.field x arraySpineKey).mem ρ h s = true := by
    simpa [Region.mem] using Footprints.spineOf_lookup hst
  refine ⟨s, ls, hst, hkeep _ (List.mem_cons_self ..) s _ hfield hl, fun l hm => ?_⟩
  obtain ⟨v, hv, hr⟩ := hall l hm
  have hel : (Region.cells x).mem ρ h l = true := by
    simp only [Region.mem, List.contains_iff_mem, spineCells]
    refine List.mem_append_left _ ?_
    simpa [entriesAt, Footprints.spineOf_lookup hst, hl, spineEntries] using hm
  exact ⟨v, hkeep (Region.cells x, .keep) (by simp) l v hel hv, hr⟩

/-- A field's contents are unchanged where the support keeps them. -/
theorem readGave_support {flds : List (PropKey × Nat)} {k : PropKey} {h h' : Heap} {v : Val}
    {ρ : Env} {x : Nat} (hx : fieldsOf (ρ x) = flds)
    (hs : Supported [(.field x k, .keep)] ρ h h') (hr : HeapFacts.ReadGave flds k h v) :
    HeapFacts.ReadGave flds k h' v := by
  unfold HeapFacts.ReadGave at hr ⊢
  cases hl : flds.lookup k with
  | none => rw [hl] at hr; exact hr
  | some l =>
    rw [hl] at hr
    obtain ⟨v', hv', hk⟩ := hs _ (List.mem_singleton_self _) l v
      (by simp [Region.mem, hx, hl]) hr
    simp only [Change.Holds] at hk
    rw [hk] at hv'; exact hv'

/-- **The support lemma**, for every fact kind. -/
theorem FactKind.support_sound {F : FactKind} {ρ h h'} (hF : F.Holds ρ h)
    (hs : Supported F.support ρ h h') : F.Holds ρ h' := by
  cases F with
  | value f => exact hF
  | dense x n => exact dense_support hF hs
  | elems x R => exact elems_support hF hs
  | cell f =>
    intro f' hf'
    simp only [List.mem_singleton] at hf'
    subst hf'
    obtain ⟨flds, c, oid, v, hx, hr, hv⟩ := hF f' (List.mem_singleton_self _)
    exact ⟨flds, c, oid, v, hx, readGave_support (by simp [hx, fieldsOf]) hs hr, hv⟩
  | link g =>
    intro g' hg'
    simp only [List.mem_singleton] at hg'
    subst hg'
    have hg := hF g' (List.mem_singleton_self _)
    by_cases ha : g'.alias = true
    · simpa [ha] using hg
    · have hs' : Supported [(.field g'.cell g'.field, .keep)] ρ h h' := by
          simpa [FactKind.support, ha] using hs
      simp only [ha, ite_false, Bool.false_eq_true] at hg ⊢
      by_cases ho : g'.optional = true
      · simp only [ho, ite_true] at hg ⊢
        obtain ⟨flds, c, oid, hx, hr⟩ := hg
        exact ⟨flds, c, oid, hx, readGave_support (by simp [hx, fieldsOf]) hs' hr⟩
      · simp only [ho, ite_false, Bool.false_eq_true] at hg ⊢
        obtain ⟨flds, c, oid, l, hx, hl, hv⟩ := hg
        obtain ⟨v', hv', hk⟩ := hs' _ (List.mem_singleton_self _) l _
          (by simp [Region.mem, hx, fieldsOf, hl]) hv
        simp only [Change.Holds] at hk
        exact ⟨flds, c, oid, l, hx, hl, by rw [← hk]; exact hv'⟩

/-! ## The tolerant frame

The note's Theorem *Tolerant frame* is `frame_step` (`Semantics/Support.lean`),
over any assertion (FOOTPRINTS.md, "Support and respect"); the fact kinds and
the stability check below are its instances. -/

/-- Each fact kind's support supports it, in every context
(`FactKind.support_sound`). -/
theorem FactKind.supports (F : FactKind) : Supports (fun _ _ _ => True) F.Holds F.support :=
  Supports.intro fun _ _ _ _ hF hs => FactKind.support_sound hF hs

/-! ## The check and the frame -/

/-- **The stability check**: respect under the one disjointness check of
separation evidence. -/
def stable (K : SepEvidence) (S Φ : Footprint) : Bool := respects K.query S Φ

theorem stable_sound {K : SepEvidence} {S Φ μ ρ h h'} {n : Nat} {W : WorldT n} (hc : stable K S Φ = true)
    (hK : K.Holds μ ρ h) (hok : HeapOk n W h) (hρ : RootsOk W ρ) (hp : Post Φ ρ h h') : Supported S ρ h h' :=
  respect_sound (q := K.query) hc (SepEvidence.query_sound hK hok hρ) hp

/-- **A fact kind the stability check keeps holds after the transition**
from a well-formed state (`frame_step`, `FactKind.supports`). -/
theorem FactKind.frame_step {K : SepEvidence} {F : FactKind} {Φ : Footprint} {μ ρ h h'} {n : Nat}
    {W : WorldT n} (hc : stable K F.support Φ = true) (hK : K.Holds μ ρ h) (hok : HeapOk n W h)
    (hρ : RootsOk W ρ) (hp : Post Φ ρ h h') (hF : F.Holds ρ h) : F.Holds ρ h' :=
  Footprints.frame_step (D := heaps) (m := 0) F.supports hc (SepEvidence.query_sound hK hok hρ) hp trivial
    trivial hF

/-- The facts the check keeps across a footprint. -/
def frame (K : SepEvidence) (fs : List FactKind) (Φ : Footprint) : List FactKind :=
  fs.filter fun F => stable K F.support Φ

theorem frame_sound {K : SepEvidence} {fs Φ μ ρ h h'} {n : Nat} {W : WorldT n} (hK : K.Holds μ ρ h)
    (hok : HeapOk n W h) (hρ : RootsOk W ρ) (hf : ∀ F ∈ fs, F.Holds ρ h) (hp : Post Φ ρ h h') :
    ∀ F ∈ frame K fs Φ, F.Holds ρ h' := by
  intro F hF
  obtain ⟨hm, hs⟩ := List.mem_filter.mp hF
  exact FactKind.frame_step hs hK hok hρ hp (hf F hm)

/-! ## A callee's frame at the caller's slots -/

/-- A footprint at the values the caller's slots hold is the renamed
footprint at the caller's environment. -/
theorem Post.rename {Φ : Footprint} {σ : Nat → Nat} {ρ env : Env} {h h' : Heap}
    (hσ : ∀ i, ρ (σ i) = env i) (hp : Post Φ env h h') : Post (Φ.rename σ) ρ h h' := by
  have henv : (fun i => ρ (σ i)) = env := funext hσ
  refine ⟨hp.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with h | ⟨e, he, hm, hh⟩
  · exact .inl h
  · refine .inr ⟨(e.1.rename σ, e.2), List.mem_map.mpr ⟨e, he, rfl⟩, ?_, hh⟩
    rw [Region.mem_rename, henv]; exact hm

/-- **Keeping a fact across a call.** A call meeting its frame at its
positions' values, each the value of a caller slot, keeps every fact whose
support passes the stability check against the renamed frame under the
caller's separation evidence, at a well-formed state. -/
theorem keep_across_call {K : SepEvidence} {F : FactKind} {Φ : Footprint} {σ : Nat → Nat}
    {μ : Nat → Nat} {ρ env : Env} {h h' : Heap} {n : Nat} {W : WorldT n}
    (hσ : ∀ i, ρ (σ i) = env i) (hp : Post Φ env h h') (hK : K.Holds μ ρ h) (hok : HeapOk n W h)
    (hρ : RootsOk W ρ) (hs : stable K F.support (Φ.rename σ) = true) (hF : F.Holds ρ h) : F.Holds ρ h' :=
  FactKind.frame_step hs hK hok hρ (Post.rename hσ hp) hF

/-- The class evidence a density fact supplies: its spine holds a spine. -/
def denseClass (x : Nat) : ClassEvidence := fun y k => if y = x ∧ k = arraySpineKey then some .spines else none

theorem dense_classOk {x n ρ h} (hd : Dense x n ρ h) : ClassOk (denseClass x) ρ h := by
  intro y k c l hc hl _
  simp only [denseClass] at hc
  split at hc
  · rename_i hyk
    obtain ⟨rfl, rfl⟩ := hyk
    cases hc
    exact dense_class hd (by simp [Region.mem, hl])
  · cases hc

end Verification.Footprints
