import Verification.Semantics.ClosedFootprints

/-! Store regions read from entry values through data-field paths: the store
a call position's path selects at the call's entry, and the closed bound on
every other location. A region excepts the store location alone. -/
namespace Verification.Footprints

/-- A call position (`0` is the receiver) and a path of own data fields. -/
structure ArgumentStoreRegion where
  position : Nat
  path : List String
  deriving Repr, DecidableEq

/-- The store selected in the entry heap. A failed read selects no location. -/
def ArgumentStoreRegion.resolve (r : ArgumentStoreRegion) (ρ : Env) (h : Heap) : Option Nat :=
  (HeapKnowledge.readPath h (ρ r.position) r.path).bind storeOf

/-- A footprint on all old locations except the selected entry stores. -/
def ArgumentStoreRegionsWithin (c : Closed) (regions : List ArgumentStoreRegion)
    (ρ : Env) (entry after : Heap) : Prop :=
  c.HoldsOn (fun l => ∀ r ∈ regions, r.resolve ρ entry ≠ some l) entry after

/-- **No regions.** With no region the exclusion predicate holds of every
location: the closed footprint itself. -/
theorem ArgumentStoreRegionsWithin.nil_holds {c : Closed} {ρ : Env} {entry after : Heap}
    (h : ArgumentStoreRegionsWithin c [] ρ entry after) : c.Holds entry after :=
  Closed.holds_of_on (h.weaken fun _ _ _ hr => nomatch hr)

/-! ## The regions as entries of the regional footprint -/

/-- The region's entry: its selected store's location, at `any`. -/
def ArgumentStoreRegion.entry (r : ArgumentStoreRegion) : Region × Change :=
  (.path r.position r.path arrayStoreKey, .any)

theorem ArgumentStoreRegion.mem_entry (r : ArgumentStoreRegion) (ρ : Env) (h : Heap) (l : Nat) :
    r.entry.1.mem ρ h l = true ↔ r.resolve ρ h = some l := by
  simp only [ArgumentStoreRegion.entry, Region.mem, ArgumentStoreRegion.resolve]
  cases HeapKnowledge.readPath h (ρ r.position) r.path <;> simp [storeOf]

/-- **The bridge.** A closed footprint excepting the selected stores is the
regional footprint of its two classes and each selected store at `any`. -/
theorem ArgumentStoreRegionsWithin.iff_post {c : Closed} {regions : List ArgumentStoreRegion}
    {ρ : Env} {entry after : Heap} :
    ArgumentStoreRegionsWithin c regions ρ entry after ↔
      Post (c.fp ++ regions.map ArgumentStoreRegion.entry) ρ entry after := by
  constructor
  · intro hw
    refine ⟨hw.1, fun l v hv => ?_⟩
    have hl := (List.getElem?_eq_some_iff.mp hv).1
    by_cases hsel : ∀ r ∈ regions, r.resolve ρ entry ≠ some l
    · obtain ⟨v', hv', hc⟩ := hw.2 l v hsel hv
      refine ⟨v', hv', ?_⟩
      rcases (Closed.allowed_iff (ρ := ρ) (v' := v') hv).mpr hc with h | ⟨e, he, hm, hh⟩
      · exact .inl h
      · exact .inr ⟨e, List.mem_append_left _ he, hm, hh⟩
    · obtain ⟨r, hr, hres⟩ : ∃ r ∈ regions, r.resolve ρ entry = some l :=
        Classical.byContradiction fun hn => hsel fun r hr hres => hn ⟨r, hr, hres⟩
      have hla : l < after.length := Nat.lt_of_lt_of_le hl hw.1
      refine ⟨after[l], List.getElem?_eq_getElem hla, .inr
        ⟨r.entry, List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩),
          (r.mem_entry ρ entry l).mpr hres, trivial⟩⟩
  · intro hp
    refine ⟨hp.1, fun l v hsel hv => ?_⟩
    obtain ⟨v', hv', ha⟩ := hp.2 l v hv
    refine ⟨v', hv', (Closed.allowed_iff (ρ := ρ) hv).mp ?_⟩
    rcases ha with h | ⟨e, he, hm, hh⟩
    · exact .inl h
    · rcases List.mem_append.mp he with he | he
      · exact .inr ⟨e, he, hm, hh⟩
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
        exact absurd ((r.mem_entry ρ entry l).mp hm) (hsel r hr)

end Verification.Footprints
