import Verification.Semantics.Footprints

/-! # Provenance and classes of contents

**Marks** are ghost heap lengths at allocation points, with mark 0 the
invocation's entry heap. A slot's **stamps** bound its locations against
marks: `after x = m` says every own location of `x` is at least mark `m`;
`before y = m` says every **typed** field location of `y` (one its type gives
a world contract) is below mark `m`. Two slots are apart when `after` of one
is at least `before` of the other, and only in the regions those stamps
cover: the own locations of the first, the typed fields of the second. An
array's listed element locations are not own locations of the array, and a
fresh store may list old element locations.

An edge renames marks by a map from target marks to source marks. A target
valuation is the source's composed with that map. The map must fix mark 0
and be monotone, and each target stamp must be implied by a source stamp in
its direction: `after` may only weaken toward an earlier source mark,
`before` only toward a later one.

The **classes** of contents follow from world contracts, at a positive step
index, and an element location's class from its store's contract one level
deeper. -/
namespace Verification.Footprints

/-! ## Marks and stamps -/

structure Stamps where
  after : Nat → Option Nat
  before : Nat → Option Nat

/-- `typed y` lists the keys of `y`'s typed fields. -/
def StampsHold (st : Stamps) (typed : Nat → List PropKey) (μ : Nat → Nat) (ρ : Env) : Prop :=
  (∀ x m, st.after x = some m → ∀ l ∈ (fieldsOf (ρ x)).map Prod.snd, μ m ≤ l) ∧
  (∀ y m, st.before y = some m → ∀ k ∈ typed y, ∀ l, (fieldsOf (ρ y)).lookup k = some l → l < μ m)

/-- **Provenance separation**, for the regions the stamps cover. -/
theorem stamps_separate {st typed μ ρ h x y m m' r l k l'} (hs : StampsHold st typed μ ρ)
    (hμ : ∀ i j, i ≤ j → μ i ≤ μ j) (ha : st.after x = some m) (hb : st.before y = some m')
    (hm : m' ≤ m) (hr : (∃ k, r = Region.field x k) ∨ r = .own x) (hrm : r.mem ρ h l = true)
    (hk : k ∈ typed y) (hl' : (fieldsOf (ρ y)).lookup k = some l') : l ≠ l' := by
  have hown : (Region.own x).mem ρ h l = true := by
    rcases hr with ⟨k, rfl⟩ | rfl
    · exact field_mem_own hrm
    · exact hrm
  have h₁ := hs.1 x m ha l (by simpa [Region.mem] using hown)
  have h₂ := hs.2 y m' hb k hk l' hl'
  have h₃ := hμ m' m hm
  omega

/-! ## Edges: renaming marks -/

/-- A target mark's source mark; marks past the list keep the last one. -/
def markAt : List Nat → Nat → Nat
  | [], _ => 0
  | [a], _ => a
  | a :: _ :: _, 0 => a
  | _ :: b :: t, i + 1 => markAt (b :: t) i

/-! ## Establishing stamps -/

/-! ## Classes of contents -/

/-- `x`'s store holds an array whose first `n` indices are present. -/
def Dense (x n : Nat) (ρ : Env) (h : Heap) : Prop :=
  ∃ s ls, (fieldsOf (ρ x)).lookup arrayStoreKey = some s ∧ h[s]? = some (.arr ls) ∧ DensePrefix n ls

theorem dense_class {x n ρ h l} (hd : Dense x n ρ h)
    (hm : (Region.field x arrayStoreKey).mem ρ h l = true) : (Region.cls .store).mem ρ h l = true := by
  obtain ⟨s, ls, hs, hv, -⟩ := hd
  simp only [Region.mem, beq_iff_eq] at hm
  rw [hs] at hm; cases hm
  simp [Region.mem, hv, Cls.has, isArr]

/-- **The support lemma of `Dense`.** It depends only on its store's
location, and survives any change of it by `grow`. -/
theorem dense_support {x n ρ h h'} (hd : Dense x n ρ h)
    (hs : Supported [(.field x arrayStoreKey, .grow)] ρ h h') : Dense x n ρ h' := by
  obtain ⟨s, ls, hsl, hv, hn⟩ := hd
  obtain ⟨v', hv', hh⟩ := hs _ (List.mem_singleton_self _) s _ (by simp [Region.mem, hsl]) hv
  rcases hh with rfl | ⟨ls₁, ls', h₁, rfl, hd, -⟩ | hi
  · exact ⟨s, ls, hsl, hv', hn⟩
  · cases h₁; exact ⟨s, ls', hsl, hv', hd n hn⟩
  · exact absurd hi.2.1 (by simp [isArr])

/-- A footprint whose entries covering the store change it at most by `grow`
supports `Dense`. -/
theorem dense_stable {x n ρ h h' Φ} (hd : Dense x n ρ h) (hp : Post Φ ρ h h')
    (hΦ : ∀ e ∈ Φ, ∀ l, (Region.field x arrayStoreKey).mem ρ h l = true → e.1.mem ρ h l = true →
      e.2.le .grow = true) : Dense x n ρ h' := by
  refine dense_support hd fun e he l v hm hv => ?_
  simp only [List.mem_singleton] at he
  subst he
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with rfl | ⟨f, hf, hfm, hh⟩
  · exact Change.Holds.refl _ _ _
  · exact hh.mono (hΦ f hf l hm hfm)

/-- The stability check of `Dense` under a closed footprint with no
knowledge: `class(value)` entries are apart from the store by class, every
other entry must change at most by `grow`. -/
def stableDenseClosed (Φ : Footprint) : Bool :=
  Φ.all fun e => e.1 == .cls .value || e.2.le .grow

theorem stableDenseClosed_sound {x n ρ h h' Φ} (hc : stableDenseClosed Φ = true)
    (hd : Dense x n ρ h) (hp : Post Φ ρ h h') : Dense x n ρ h' := by
  refine dense_stable hd hp fun e he l hsm hem => ?_
  have := List.all_eq_true.mp hc e he
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with hcls | hle
  · have hst := dense_class hd hsm
    rw [hcls] at hem
    obtain ⟨s, ls, hs, hv, -⟩ := hd
    simp only [Region.mem] at hst hem
    split at hst <;> simp_all [Cls.has]
  · exact hle

/-! ## Elements -/

end Verification.Footprints
