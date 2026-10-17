import Verification.Semantics.FootprintProvenance
import Verification.Semantics.HeapLinks

/-! # The stability check

A **fact kind** has a meaning at a heap and a **support**: the regions it
reads, each with the largest change it tolerates. Its support lemma says that
it survives every change within its support. **Separation** of a support
region from a footprint region is derived from three sources of knowledge:
the class of a field's contents, provenance stamps, and distinct links. The
**stability check** of a fact under a footprint accepts when every footprint
entry either changes the support's regions within their tolerance or is
apart from them; its soundness theorem gives the support's premise from the
footprint's postcondition, and the **frame** keeps exactly the facts that
pass it. Nothing uses this module yet.

Also here: heaps only grow under steps, and the six closed footprints are
ordered exactly by their entries. -/
namespace Verification.Footprints

/-! ## Fact kinds -/

/-- The fact kinds today's knowledge holds, and density. -/
inductive FactKind where
  /-- An observation of a field's current contents (`HeapFacts.Fact`). -/
  | cell (f : HeapFacts.Fact)
  /-- A link: alias, distinct, or a read of a field (`HeapLinks.Link`). -/
  | link (g : HeapLinks.Link)
  /-- A primitive predicate of a slot's value. -/
  | value (f : HeapFacts.Fact)
  /-- The first `n` indices of `x`'s store are present. -/
  | dense (x n : Nat)

def FactKind.Holds : FactKind → Env → Heap → Prop
  | .cell f, ρ, h => HeapFacts.Holds [f] ρ h
  | .link g, ρ, h => HeapLinks.Holds [g] ρ h
  | .value f, ρ, _ => ∃ a ∈ f.contents, a.holds (ρ f.slot)
  | .dense x n, ρ, h => Dense x n ρ h

def FactKind.support : FactKind → Footprint
  | .cell f => [(.field f.slot f.field, .keep)]
  | .link g => if g.distinct || g.alias then [] else [(.field g.cell g.field, .keep)]
  | .value _ => []
  | .dense x _ => [(.field x arrayStoreKey, .grow)]

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
  | cell f =>
    intro f' hf'
    simp only [List.mem_singleton] at hf'
    subst hf'
    obtain ⟨flds, c, oid, v, hx, hr, a, ha, hv⟩ := hF f' (List.mem_singleton_self _)
    exact ⟨flds, c, oid, v, hx, readGave_support (by simp [hx, fieldsOf]) hs hr, a, ha, hv⟩
  | link g =>
    intro g' hg'
    simp only [List.mem_singleton] at hg'
    subst hg'
    have hg := hF g' (List.mem_singleton_self _)
    by_cases hd : g'.distinct = true
    · simpa [hd] using hg
    · by_cases ha : g'.alias = true
      · simpa [hd, ha] using hg
      · have hs' : Supported [(.field g'.cell g'.field, .keep)] ρ h h' := by
          simpa [FactKind.support, hd, ha] using hs
        simp only [hd, ha, if_false, Bool.false_eq_true] at hg ⊢
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
stamps, and distinct field pairs. -/
structure SepKnowledge where
  cl : ClassEvidence
  stamps : Stamps
  typed : Nat → List PropKey
  distinct : List (Nat × PropKey × Nat × PropKey)

def SepKnowledge.Holds (K : SepKnowledge) (μ : Nat → Nat) (ρ : Env) (h : Heap) : Prop :=
  ClassOk K.cl ρ h ∧ StampsHold K.stamps K.typed μ ρ ∧ (∀ i j, i ≤ j → μ i ≤ μ j) ∧
    ∀ d ∈ K.distinct, ∀ l l', (fieldsOf (ρ d.1)).lookup d.2.1 = some l →
      (fieldsOf (ρ d.2.2.1)).lookup d.2.2.2 = some l' → l ≠ l'

/-- Own locations of `x` against typed field `k` of `y`, by stamps. -/
def SepKnowledge.provenance (K : SepKnowledge) (x y : Nat) (k : PropKey) : Bool :=
  (K.typed y).contains k && match K.stamps.after x, K.stamps.before y with
    | some m, some m' => decide (m' ≤ m)
    | _, _ => false

def SepKnowledge.linked (K : SepKnowledge) (x : Nat) (k : PropKey) (y : Nat) (k' : PropKey) : Bool :=
  K.distinct.contains (x, k, y, k') || K.distinct.contains (y, k', x, k)

/-- One orientation of separation. -/
def SepKnowledge.apart₁ (K : SepKnowledge) : Region → Region → Bool
  | .field x k, .cls c => match K.cl x k with
    | some c' => c' != c
    | none => false
  | .field x k, .field y k' => K.provenance x y k' || K.provenance y x k || K.linked x k y k'
  | .own x, .field y k' => K.provenance x y k'
  | _, _ => false

def SepKnowledge.apart (K : SepKnowledge) (r s : Region) : Bool := K.apart₁ r s || K.apart₁ s r

private theorem cls_disjoint {c c' : Cls} (hne : c ≠ c') {v : Val} (h₁ : c.has v = true)
    (h₂ : c'.has v = true) : False := by
  cases c <;> cases c' <;> simp_all [Cls.has]

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
      exact stamps_separate (r := .own x) (h := h) hK.2.1 hK.2.2.1 ha hb hm (.inr rfl)
        (by simpa [Region.mem] using hl) hk hl'

private theorem apart₁_sound {K : SepKnowledge} {μ ρ h r s l} (hK : K.Holds μ ρ h)
    (ha : K.apart₁ r s = true) (hr : r.mem ρ h l = true) (hs : s.mem ρ h l = true) : False := by
  cases r <;> cases s <;> simp only [SepKnowledge.apart₁] at ha <;> try contradiction
  case field.cls x k c =>
    cases hc : K.cl x k with
    | none => simp [hc] at ha
    | some c' =>
      simp only [hc, bne_iff_ne, ne_eq] at ha
      simp only [Region.mem, beq_iff_eq] at hr
      simp only [Region.mem] at hs
      split at hs
      · rename_i v hv
        have hlt := (List.getElem?_eq_some_iff.mp hv).1
        have hc' := hK.1 x k c' l hc hr hlt
        simp only [Region.mem, hv] at hc'
        exact cls_disjoint ha hc' hs
      · cases hs
  case field.field x k y k' =>
    simp only [Bool.or_eq_true] at ha
    simp only [Region.mem, beq_iff_eq] at hr hs
    rcases ha with (ha | ha) | ha
    · exact provenance_sound hK ha (lookup_mem_snd hr) hs rfl
    · exact provenance_sound hK ha (lookup_mem_snd hs) hr rfl
    · simp only [SepKnowledge.linked, Bool.or_eq_true, List.contains_iff_mem] at ha
      rcases ha with ha | ha
      · exact hK.2.2.2 _ ha l l hr hs rfl
      · exact hK.2.2.2 _ ha l l hs hr rfl
  case own.field x y k' =>
    simp only [Region.mem, beq_iff_eq] at hs
    exact provenance_sound hK ha (by simpa [Region.mem] using hr) hs rfl

/-- **Separation is sound**: apart regions share no location. -/
theorem Sep.sound {K : SepKnowledge} {μ ρ h r s l} (hK : K.Holds μ ρ h)
    (ha : K.apart r s = true) (hr : r.mem ρ h l = true) (hs : s.mem ρ h l = true) : False := by
  simp only [SepKnowledge.apart, Bool.or_eq_true] at ha
  rcases ha with ha | ha
  · exact apart₁_sound hK ha hr hs
  · exact apart₁_sound hK ha hs hr

/-! ## The check and the frame -/

/-- **The stability check**: every footprint entry changes every support
region within its tolerance, or is apart from it. -/
def stable (K : SepKnowledge) (S Φ : Footprint) : Bool :=
  S.all fun e => Φ.all fun f => f.2.le e.2 || K.apart e.1 f.1

theorem stable_sound {K : SepKnowledge} {S Φ μ ρ h h'} (hc : stable K S Φ = true)
    (hK : K.Holds μ ρ h) (hp : Post Φ ρ h h') : Supported S ρ h h' := by
  intro e he l v hm hv
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with rfl | ⟨f, hf, hfm, hh⟩
  · exact Change.Holds.refl _ _ _
  · have := List.all_eq_true.mp (List.all_eq_true.mp hc e he) f hf
    simp only [Bool.or_eq_true] at this
    rcases this with hle | hap
    · exact hh.mono hle
    · exact (Sep.sound hK hap hm hfm).elim

/-- The facts the check keeps across a footprint. -/
def frame (K : SepKnowledge) (fs : List FactKind) (Φ : Footprint) : List FactKind :=
  fs.filter fun F => stable K F.support Φ

theorem frame_sound {K : SepKnowledge} {fs Φ μ ρ h h'} (hK : K.Holds μ ρ h)
    (hf : ∀ F ∈ fs, F.Holds ρ h) (hp : Post Φ ρ h h') : ∀ F ∈ frame K fs Φ, F.Holds ρ h' := by
  intro F hF
  obtain ⟨hm, hs⟩ := List.mem_filter.mp hF
  exact FactKind.support_sound (hf F hm) (stable_sound hs hK hp)

/-- The class evidence a density fact supplies: its store holds a store. -/
def denseClass (x : Nat) : ClassEvidence := fun y k => if y = x ∧ k = arrayStoreKey then some .store else none

theorem dense_classOk {x n ρ h} (hd : Dense x n ρ h) : ClassOk (denseClass x) ρ h := by
  intro y k c l hc hl _
  simp only [denseClass] at hc
  split at hc
  · rename_i hyk
    obtain ⟨rfl, rfl⟩ := hyk
    cases hc
    exact dense_class hd (by simp [Region.mem, hl])
  · cases hc

/-- **Class evidence from contracts.** Evidence that names, for each field it
covers, a location whose world contract admits only source values (class
`value`) or only stores (class `store`) holds at a heap meeting the world.
This is the class theorem of a `cell` or `read` fact's support, which the
fact's own meaning does not give. -/
theorem classOk_of_contracts {n W h ρ} {cl : ClassEvidence} (hh : HeapOk (n+1) W h)
    (hcl : ∀ x k c l, cl x k = some c → (fieldsOf (ρ x)).lookup k = some l →
      ∃ ctr, lookup W l = some ctr ∧
        (c = .value → ∀ U u, ctr 0 (Nat.zero_lt_succ n) U u → isSourceVal u = true) ∧
        (c = .store → ∀ U u, ctr 0 (Nat.zero_lt_succ n) U u → isArr u = true)) :
    ClassOk cl ρ h := by
  intro x k c l hc hl hlt
  obtain ⟨ctr, hw, hv, hs⟩ := hcl x k c l hc hl
  have hget : h[l]? = some h[l] := List.getElem?_eq_getElem hlt
  cases c with
  | value => simp [Region.mem, hget, Cls.has, contract_class hh hw (hv rfl) hget]
  | store => simp [Region.mem, hget, Cls.has, contract_store hh hw (hs rfl) hget]

/-! ## Allocation of arrays and closures

An array literal allocates its element locations at the heap's length and
beyond, so they are fresh too. A closure is allocated by `makeAt` with its
code (`alloc_after` covers every call code). -/

theorem elemSlots_ge (b n : Nat) : ∀ l, some l ∈ elemSlots b n → b ≤ l := by
  intro l hl
  simp only [elemSlots, List.mem_map, List.mem_range, Option.some.injEq] at hl
  obtain ⟨i, -, rfl⟩ := hl
  exact Nat.le_add_right b i

theorem arrLit_fresh {h vs h' r} (st : Step h (.arrLit vs) h' r) (hv : ∀ v ∈ vs, isVal v = true) :
    ∃ ls, r = .arr ls ∧ ∀ l, some l ∈ ls → h.length ≤ l := by
  cases st with
  | arrArg _ _ s =>
    rename_i i a _ hi _
    exact absurd s (value_no_step (hv a (List.mem_of_getElem? hi)))
  | arrAlloc => exact ⟨_, rfl, elemSlots_ge h.length vs.length⟩
  | arrSpread he _ _ =>
    have := hv _ (by rw [he]; exact List.mem_append_right _ (List.mem_cons_self ..))
    simp [isVal] at this

/-! ## Heaps grow -/

theorem step_length_le {h t h' t'} (st : Step h t h' t') : h.length ≤ h'.length := by
  induction st <;> simp_all [List.length_append, List.length_set] <;> omega

theorem steps_grow {k h t h' t'} (st : HeapObservations.Steps k h t h' t') : h.length ≤ h'.length := by
  induction st with
  | refl => exact Nat.le_refl _
  | next s _ ih => exact Nat.le_trans (step_length_le s) ih

/-! ## Closed footprints -/

/-- A closed footprint: a change for each class of contents. -/
structure Closed where
  value : Change
  store : Change
  deriving DecidableEq, Repr

def Closed.fp (c : Closed) : Footprint := [(.cls .value, c.value), (.cls .store, c.store)]

/-- On contents of class `value`, `grow` is `keep`. -/
def Change.onValue : Change → Change
  | .grow => .keep
  | d => d

def Closed.le (a b : Closed) : Bool := a.value.onValue.le b.value.onValue && a.store.le b.store

private theorem value_change {δ δ' : Change} {b v v'} (hv : isArr v = false)
    (hle : δ.onValue.le δ'.onValue = true) (h : δ.Holds b v v') : δ'.Holds b v v' := by
  cases δ with
  | grow => rw [h.grow_value hv]; exact Change.Holds.refl _ _ _
  | keep => simp only [Change.Holds] at h; rw [h]; exact Change.Holds.refl _ _ _
  | any => cases δ' <;> simp_all [Change.onValue, Change.le, Change.Holds]

theorem Closed.post_mono {a b : Closed} (hle : a.le b = true) {ρ h h'} (hp : Post a.fp ρ h h') :
    Post b.fp ρ h h' := by
  simp only [Closed.le, Bool.and_eq_true] at hle
  refine ⟨hp.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact .inl rfl
  · simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · have hc : isArr v = false := by simpa [Region.mem, hv, Cls.has] using hm
      exact .inr ⟨_, List.mem_cons_self .., hm, value_change hc hle.1 hh⟩
    · exact .inr ⟨(.cls .store, b.store), by simp [Closed.fp], hm, hh.mono hle.2⟩

private def ρ₀ : Env := fun _ => .undef

private theorem single_post {Φ : Footprint} {v v' : Val} (hp : Post Φ ρ₀ [v] [v']) :
    v' = v ∨ ∃ e ∈ Φ, e.1.mem ρ₀ [v] 0 = true ∧ e.2.Holds 1 v v' := by
  obtain ⟨v₁, hv₁, ha⟩ := hp.2 0 v rfl
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hv₁
  subst hv₁
  exact ha

/-- **The closed footprints are ordered exactly by their entries.** -/
theorem closed_order_exact (a b : Closed) :
    a.le b = true ↔ ∀ ρ h h', Post a.fp ρ h h' → Post b.fp ρ h h' := by
  refine ⟨fun hle _ _ _ => Closed.post_mono hle, fun H => ?_⟩
  simp only [Closed.le, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- a value location changes arbitrarily
    cases ha : a.value <;> cases hb : b.value <;> simp [Change.onValue, Change.le] <;>
    · have hp : Post a.fp ρ₀ [.nul] [.tru] :=
        ⟨by simp, fun l v hv => by
          cases l with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
            exact ⟨.tru, rfl, .inr ⟨(.cls .value, a.value), List.mem_cons_self .., by simp [Region.mem, Cls.has, isArr], by
              show a.value.Holds _ _ _
              rw [ha]; trivial⟩⟩
          | succ l => simp at hv⟩
      rcases single_post (H _ _ _ hp) with h | ⟨e, he, hm, hh⟩
      · cases h
      · simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · simp only [hb] at hh
          simp [Change.Holds] at hh
        · simp [Region.mem, Cls.has, isArr] at hm
  · cases ha : a.store <;> cases hb : b.store <;> simp [Change.le]
    · -- grow against keep: a store gains a fresh element location
      have hp : Post a.fp ρ₀ [.arr []] [.arr [some 1]] :=
        ⟨by simp, fun l v hv => by
          cases l with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
            exact ⟨_, rfl, .inr ⟨(.cls .store, a.store), by simp [Closed.fp], by simp [Region.mem, Cls.has, isArr], by
              show a.store.Holds _ _ _
              rw [ha]; exact (Change.holdsB_iff _ _ _ _).mp (by decide)⟩⟩
          | succ l => simp at hv⟩
      rcases single_post (H _ _ _ hp) with h | ⟨e, he, hm, hh⟩
      · cases h
      · simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · simp [Region.mem, Cls.has, isArr] at hm
        · simp only [hb] at hh
          simp [Change.Holds] at hh
    all_goals
      -- any against keep or grow: a dense store loses its index
      have hp : Post a.fp ρ₀ [.arr [some 0]] [.arr []] :=
        ⟨by simp, fun l v hv => by
          cases l with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
            exact ⟨_, rfl, .inr ⟨(.cls .store, a.store), by simp [Closed.fp], by simp [Region.mem, Cls.has, isArr], by
              show a.store.Holds _ _ _
              rw [ha]; trivial⟩⟩
          | succ l => simp at hv⟩
      rcases single_post (H _ _ _ hp) with h | ⟨e, he, hm, hh⟩
      · cases h
      · simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · simp [Region.mem, Cls.has, isArr] at hm
        · simp only [hb] at hh
          exact absurd ((Change.holdsB_iff _ _ _ _).mpr hh) (by decide)

end Verification.Footprints
