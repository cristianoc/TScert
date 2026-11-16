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
fresh spine may list old element locations.

An edge renames marks by a map from target marks to source marks. A target
valuation is the source's composed with that map. The map must fix mark 0
and be monotone, and each target stamp must be implied by a source stamp in
its direction: `after` may only weaken toward an earlier source mark,
`before` only toward a later one.

The **classes** of contents follow from world contracts, at a positive step
index, and an element location's class from its spine's contract one level
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
    (hm : m' ≤ m) (hr : (∃ k, r = Region.field x k) ∨ r = .fields x) (hrm : r.mem ρ h l = true)
    (hk : k ∈ typed y) (hl' : (fieldsOf (ρ y)).lookup k = some l') : l ≠ l' := by
  have hown : l ∈ (fieldsOf (ρ x)).map Prod.snd := by
    rcases hr with ⟨k, rfl⟩ | rfl
    · simp only [Region.mem, beq_iff_eq] at hrm; exact lookup_mem_snd hrm
    · exact fieldLocs_own (by simpa [Region.mem] using hrm)
  have h₁ := hs.1 x m ha l hown
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

/-- `x`'s spine holds an array whose first `n` indices are present. -/
def Dense (x n : Nat) (ρ : Env) (h : Heap) : Prop :=
  ∃ s ls, (fieldsOf (ρ x)).lookup arraySpineKey = some s ∧ h[s]? = some (.arr ls) ∧ DensePrefix n ls

theorem dense_class {x n ρ h l} (hd : Dense x n ρ h)
    (hm : (Region.field x arraySpineKey).mem ρ h l = true) : (Region.cls .spines).mem ρ h l = true := by
  obtain ⟨s, ls, hs, hv, -⟩ := hd
  simp only [Region.mem, beq_iff_eq] at hm
  rw [hs] at hm; cases hm
  simp [Region.mem, hv, isArr]

/-- **A change within `grow` of an array spine** (`Change.Holds`, `grow`):
an array spine keeping every dense prefix, its length growing. -/
theorem grow_arr {b : Nat} {ls : List (Option Nat)} {v' : Val} (hh : Change.grow.Holds b (.arr ls) v') :
    ∃ ls', v' = .arr ls' ∧ (∀ n, DensePrefix n ls → DensePrefix n ls') ∧ LengthGrows ls ls' := by
  rcases hh with rfl | ⟨ls₁, ls', h₁, rfl, hd, -, hl⟩ | hi | ⟨_, _, _, he, -⟩
  · exact ⟨ls, rfl, fun _ h => h, LengthGrows.refl ls⟩
  · cases h₁; exact ⟨ls', rfl, hd, hl⟩
  · exact absurd hi.2.1 (by simp [isArr])
  · cases he

/-- **The support lemma of `Dense`** (the note, §5, Definition "Support",
the row of `dense(x, n)`: `{x.spine: grow}`). It depends only on its
spine's location, and survives any change of it by `grow`. -/
theorem dense_support {x n ρ h h'} (hd : Dense x n ρ h)
    (hs : Supported [(.field x arraySpineKey, .grow)] ρ h h') : Dense x n ρ h' := by
  obtain ⟨s, ls, hsl, hv, hn⟩ := hd
  obtain ⟨v', hv', hh⟩ := hs _ (List.mem_singleton_self _) s _ (by simp [Region.mem, hsl]) hv
  obtain ⟨ls', rfl, hd, -⟩ := grow_arr hh
  exact ⟨s, ls', hsl, hv', hd n hn⟩

/-! ## Elements -/

end Verification.Footprints
