import Verification.Semantics.FootprintProvenance
import Verification.Semantics.HeapLinks
import Verification.Semantics.Support

/-! # The stability check

A **fact kind** has a meaning at a heap and a **support**: the regions it
reads, each with the largest change it tolerates. Its support lemma says that
it survives every change within its support. **Separation** of a support
region from a footprint region is derived from three sources of knowledge:
the class of a field's contents, provenance stamps, and distinct pairs. The
**stability check** of a fact under a footprint accepts when every footprint
entry either changes the support's regions within their tolerance or is
apart from them; its soundness theorem gives the support's premise from the
footprint's postcondition, and the **frame** keeps exactly the facts that
pass it. -/
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
      simp only [ha, if_false, Bool.false_eq_true] at hg ⊢
      by_cases ho : g'.optional = true
      · simp only [ho, if_true] at hg ⊢
        obtain ⟨flds, c, oid, hx, hr⟩ := hg
        exact ⟨flds, c, oid, hx, readGave_support (by simp [hx, fieldsOf]) hs' hr⟩
      · simp only [ho, if_false, Bool.false_eq_true] at hg ⊢
        obtain ⟨flds, c, oid, l, hx, hl, hv⟩ := hg
        obtain ⟨v', hv', hk⟩ := hs' _ (List.mem_singleton_self _) l _
          (by simp [Region.mem, hx, fieldsOf, hl]) hv
        simp only [Change.Holds] at hk
        exact ⟨flds, c, oid, l, hx, hl, by rw [← hk]; exact hv'⟩

/-! ## Separation -/

/-- What separation may use: the class of fields' contents, provenance
stamps, and distinct field pairs; the paths whose spine location differs from
a slot's spine location (`spineApart`, the chain1 `SpineApart`), and the
paths whose spine lists only cells holding no spine (`elemsValue`). -/
structure SepKnowledge where
  cl : ClassEvidence
  stamps : Stamps
  typed : Nat → List PropKey
  distinct : List (Nat × PropKey × Nat × PropKey)
  spineApart : List (Nat × List String × Nat) := []
  elemsValue : List (Nat × List String) := []

def SepKnowledge.Holds (K : SepKnowledge) (μ : Nat → Nat) (ρ : Env) (h : Heap) : Prop :=
  ClassOk K.cl ρ h ∧ StampsHold K.stamps K.typed μ ρ ∧ (∀ i j, i ≤ j → μ i ≤ μ j) ∧
    (∀ d ∈ K.distinct, ∀ l l', (fieldsOf (ρ d.1)).lookup d.2.1 = some l →
      (fieldsOf (ρ d.2.2.1)).lookup d.2.2.2 = some l' → l ≠ l') ∧
    (∀ a ∈ K.spineApart, ∀ l, (Region.path a.1 a.2.1 arraySpineKey).mem ρ h l = true →
      (Region.field a.2.2 arraySpineKey).mem ρ h l = false) ∧
    (∀ a ∈ K.elemsValue, ∀ l, (Region.pathCells a.1 a.2).mem ρ h l = true →
      (Region.cls .values).mem ρ h l = true)

/-- Own locations of `x` against typed field `k` of `y`, by stamps. -/
def SepKnowledge.provenance (K : SepKnowledge) (x y : Nat) (k : PropKey) : Bool :=
  (K.typed y).contains k && match K.stamps.after x, K.stamps.before y with
    | some m, some m' => decide (m' ≤ m)
    | _, _ => false

def SepKnowledge.linked (K : SepKnowledge) (x : Nat) (k : PropKey) (y : Nat) (k' : PropKey) : Bool :=
  K.distinct.contains (x, k, y, k') || K.distinct.contains (y, k', x, k)

/-- Whether a field's location lies, by class evidence, in a class region
disjoint from that of `c`. -/
def SepKnowledge.otherClass (K : SepKnowledge) (x : Nat) (k : PropKey) (c : Selector) : Bool :=
  match K.cl x k with
  | some c' => c'.disjoint c
  | none => false

/-- One orientation of separation. -/
def SepKnowledge.apart₁ (K : SepKnowledge) : Region → Region → Bool
  | .field x k, .cls c => K.otherClass x k c
  | .field x k, .field y k' => K.provenance x y k' || K.provenance y x k || K.linked x k y k'
  | .fields x, .field y k' => K.provenance x y k'
  | .field x k, .cell _ => K.otherClass x k .values
  | .field x k, .inCls _ c => K.otherClass x k c
  | .path x p k, .field y k' => k == arraySpineKey && k' == arraySpineKey &&
      K.spineApart.contains (x, p, y)
  | .pathCells x p, .field y k => K.elemsValue.contains (x, p) && K.cl y k == some .spines
  | .pathCells x p, .cls c => K.elemsValue.contains (x, p) && Selector.values.disjoint c
  | .inCls _ c, .cls c' => c.disjoint c'
  | .inCls r _, s => K.apart₁ r s
  | _, _ => false

def SepKnowledge.apart (K : SepKnowledge) (r s : Region) : Bool := K.apart₁ r s || K.apart₁ s r

private theorem cls_disjoint {c c' : Selector} (hd : c.disjoint c' = true) {v : Val}
    (h₁ : c.selects v = true) (h₂ : c'.selects v = true) : False := by
  rw [Selector.selects_disjoint hd h₁] at h₂; cases h₂

private theorem provenance_sound {K : SepKnowledge} {μ ρ h x y k l l'} (hK : K.Holds μ ρ h)
    (hp : K.provenance x y k = true) (hl : l ∈ (fieldsOf (ρ x)).map Prod.snd)
    (hl' : (fieldsOf (ρ y)).lookup k = some l') : l ≠ l' := by
  simp only [SepKnowledge.provenance, Bool.and_eq_true, List.contains_iff_mem] at hp
  obtain ⟨hk, hm⟩ := hp
  cases ha : K.stamps.after x with
  | none => simp [ha] at hm
  | some m =>
    cases hb : K.stamps.before y with
    | none => simp [ha, hb] at hm
    | some m' =>
      simp only [ha, hb, decide_eq_true_eq] at hm
      exact stamps_separate (r := .fields x) (h := h) hK.2.1 hK.2.2.1 ha hb hm (.inr rfl)
        (by simpa [Region.mem] using hl) hk hl'

/-- A field whose contents have, by class evidence, a class other than `c`
holds no contents of class `c`. -/
private theorem otherClass_sound {K : SepKnowledge} {μ ρ h x k c l} (hK : K.Holds μ ρ h)
    (ho : K.otherClass x k c = true) (hr : (Region.field x k).mem ρ h l = true)
    (hs : (Region.cls c).mem ρ h l = true) : False := by
  unfold SepKnowledge.otherClass at ho
  cases hc : K.cl x k with
  | none => simp [hc] at ho
  | some c' =>
    simp only [hc] at ho
    simp only [Region.mem, beq_iff_eq] at hr
    simp only [Region.mem] at hs
    split at hs
    · rename_i v hv
      have hlt := (List.getElem?_eq_some_iff.mp hv).1
      have hc' := hK.1 x k c' l hc hr hlt
      simp only [Region.mem, hv] at hc'
      exact cls_disjoint ho hc' hs
    · cases hs

private theorem inCls_cls {ρ h r c l} (hm : (Region.inCls r c).mem ρ h l = true) :
    r.mem ρ h l = true ∧ (Region.cls c).mem ρ h l = true := by
  simp only [Region.mem, Bool.and_eq_true] at hm
  exact ⟨hm.1, by simpa [Region.mem] using hm.2⟩

private theorem apart₁_sound {K : SepKnowledge} {μ ρ h l} (hK : K.Holds μ ρ h) :
    ∀ {r s : Region}, K.apart₁ r s = true → r.mem ρ h l = true → s.mem ρ h l = true → False := by
  intro r
  induction r with
  | inCls r c ih =>
    intro s ha hr hs
    obtain ⟨hr, hc⟩ := inCls_cls hr
    cases s
    case cls c' =>
      simp only [SepKnowledge.apart₁] at ha
      simp only [Region.mem] at hc hs
      split at hc
      · rename_i v hv; rw [hv] at hs; exact cls_disjoint ha hc hs
      · cases hc
    all_goals exact ih (by simpa [SepKnowledge.apart₁] using ha) hr hs
  | field x k =>
    intro s ha hr hs
    cases s <;> (try simp only [SepKnowledge.apart₁] at ha) <;> try contradiction
    case cls c => exact otherClass_sound hK ha hr hs
    case cell b => exact otherClass_sound hK ha hr (by simpa [Region.mem] using hs)
    case inCls r c => exact otherClass_sound hK ha hr (inCls_cls hs).2
    case field y k' =>
      simp only [Bool.or_eq_true] at ha
      simp only [Region.mem, beq_iff_eq] at hr hs
      rcases ha with (ha | ha) | ha
      · exact provenance_sound hK ha (lookup_mem_snd hr) hs rfl
      · exact provenance_sound hK ha (lookup_mem_snd hs) hr rfl
      · simp only [SepKnowledge.linked, Bool.or_eq_true, List.contains_iff_mem] at ha
        rcases ha with ha | ha
        · exact hK.2.2.2.1 _ ha l l hr hs rfl
        · exact hK.2.2.2.1 _ ha l l hs hr rfl
  | fields x =>
    intro s ha hr hs
    cases s <;> (try simp only [SepKnowledge.apart₁] at ha) <;> try contradiction
    case field y k' =>
      simp only [Region.mem, beq_iff_eq] at hs
      exact provenance_sound hK ha (by simpa [Region.mem] using hr) hs rfl
  | path x p k =>
    intro s ha hr hs
    cases s <;> (try simp only [SepKnowledge.apart₁] at ha) <;> try contradiction
    case field y k' =>
      simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at ha
      obtain ⟨⟨rfl, rfl⟩, ha⟩ := ha
      have := hK.2.2.2.2.1 _ ha l hr
      rw [hs] at this; cases this
  | pathCells x p =>
    intro s ha hr hs
    have hv := fun hm => hK.2.2.2.2.2 (x, p) hm l hr
    cases s <;> (try simp only [SepKnowledge.apart₁] at ha) <;> try contradiction
    case field y k =>
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at ha
      exact otherClass_sound (c := .values) hK (by simp [SepKnowledge.otherClass, ha.2]; rfl) hs (hv ha.1)
    case cls c =>
      simp only [Bool.and_eq_true, List.contains_iff_mem] at ha
      have h₁ := hv ha.1
      simp only [Region.mem] at h₁ hs
      split at h₁
      · rename_i v hv'; rw [hv'] at hs; exact cls_disjoint ha.2 h₁ hs
      · cases h₁
  | cells | cls | all | pathFields | cell | spine =>
    intro s ha
    simp [SepKnowledge.apart₁] at ha

/-- **Separation is sound**: apart regions share no location. -/
theorem Sep.sound {K : SepKnowledge} {μ ρ h r s l} (hK : K.Holds μ ρ h)
    (ha : K.apart r s = true) (hr : r.mem ρ h l = true) (hs : s.mem ρ h l = true) : False := by
  simp only [SepKnowledge.apart, Bool.or_eq_true] at ha
  rcases ha with ha | ha
  · exact apart₁_sound hK ha hr hs
  · exact apart₁_sound hK ha hs hr

/-! ## The tolerant frame at a transition

The note's Theorem *Tolerant frame*, over any assertion (FOOTPRINTS.md,
"Support and respect"); its Definitions *Support* and *Respect* are
`Supports` and `respects` (`Semantics/Support.lean`). -/

/-- **The tolerant frame, at a transition**: an assertion with a support
the effect respects under a query sound at the prestate holds after every
transition within the effect that meets the support's context. -/
theorem keeps_sound {C : Env → Heap → Heap → Prop} {P : Env → Heap → Prop} {S Φ : Footprint}
    {q : SepQuery} {ρ h h'} (hs : Supports C P S) (hr : respects q S Φ = true) (hq : q.Sound ρ h)
    (hp : Post Φ ρ h h') (hc : C ρ h h') (hP : P ρ h) : P ρ h' :=
  hs.apply hc hP (respect_sound hr hq hp)

/-- Separation knowledge answers a query (`Sep.sound`). -/
def SepKnowledge.query (K : SepKnowledge) : SepQuery := ⟨K.apart⟩

theorem SepKnowledge.query_sound {K : SepKnowledge} {μ ρ h} (hK : K.Holds μ ρ h) : K.query.Sound ρ h :=
  fun _ _ _ hd hr hs => Sep.sound hK hd hr hs

/-- Each fact kind's support supports it, in every context
(`FactKind.support_sound`). -/
theorem FactKind.supports (F : FactKind) : Supports (fun _ _ _ => True) F.Holds F.support :=
  Supports.intro fun _ _ _ _ hF hs => FactKind.support_sound hF hs

/-! ## The check and the frame -/

/-- **The stability check**: respect under separation knowledge. -/
def stable (K : SepKnowledge) (S Φ : Footprint) : Bool := respects K.query S Φ

theorem stable_sound {K : SepKnowledge} {S Φ μ ρ h h'} (hc : stable K S Φ = true)
    (hK : K.Holds μ ρ h) (hp : Post Φ ρ h h') : Supported S ρ h h' :=
  respect_sound (q := K.query) hc (SepKnowledge.query_sound hK) hp

/-- The facts the check keeps across a footprint. -/
def frame (K : SepKnowledge) (fs : List FactKind) (Φ : Footprint) : List FactKind :=
  fs.filter fun F => stable K F.support Φ

theorem frame_sound {K : SepKnowledge} {fs Φ μ ρ h h'} (hK : K.Holds μ ρ h)
    (hf : ∀ F ∈ fs, F.Holds ρ h) (hp : Post Φ ρ h h') : ∀ F ∈ frame K fs Φ, F.Holds ρ h' := by
  intro F hF
  obtain ⟨hm, hs⟩ := List.mem_filter.mp hF
  exact FactKind.support_sound (hf F hm) (stable_sound hs hK hp)

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
caller's separation knowledge. -/
theorem keep_across_call {K : SepKnowledge} {F : FactKind} {Φ : Footprint} {σ : Nat → Nat}
    {μ : Nat → Nat} {ρ env : Env} {h h' : Heap}
    (hσ : ∀ i, ρ (σ i) = env i) (hp : Post Φ env h h') (hK : K.Holds μ ρ h)
    (hs : stable K F.support (Φ.rename σ) = true) (hF : F.Holds ρ h) : F.Holds ρ h' :=
  FactKind.support_sound hF (stable_sound hs hK (Post.rename hσ hp))

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
