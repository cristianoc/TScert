import Verification.Semantics.ClosedFootprints

/-! Spine regions read from entry values through data-field paths: the spine
a call position's path selects at the call's entry, and the closed bound on
every other location. A region excepts the spine location alone. -/
namespace Verification.Footprints

/-- A call position (`0` is the receiver) and a path of own data fields. -/
structure ArgumentSpineRegion where
  position : Nat
  path : List String
  deriving Repr, DecidableEq

/-- The spine selected in the entry heap. A failed read selects no location. -/
def ArgumentSpineRegion.resolve (r : ArgumentSpineRegion) (ρ : Env) (h : Heap) : Option Nat :=
  (HeapKnowledge.readPath h (ρ r.position) r.path).bind spineOf

/-- A footprint on all old locations except the selected entry spines. -/
def ArgumentSpineRegionsWithin (c : Closed) (regions : List ArgumentSpineRegion)
    (ρ : Env) (entry after : Heap) : Prop :=
  c.HoldsOn (fun l => ∀ r ∈ regions, r.resolve ρ entry ≠ some l) entry after

/-- **No regions.** With no region the exclusion predicate holds of every
location: the closed footprint itself. -/
theorem ArgumentSpineRegionsWithin.nil_holds {c : Closed} {ρ : Env} {entry after : Heap}
    (h : ArgumentSpineRegionsWithin c [] ρ entry after) : c.Holds entry after :=
  Closed.holds_of_on (h.weaken fun _ _ _ hr => nomatch hr)

/-! ## The regions as entries of the regional footprint -/

/-- The region's entry: its selected spine's location, at `any`. -/
def ArgumentSpineRegion.entry (r : ArgumentSpineRegion) : Region × Change :=
  (.path r.position r.path arraySpineKey, .any)

theorem ArgumentSpineRegion.mem_entry (r : ArgumentSpineRegion) (ρ : Env) (h : Heap) (l : Nat) :
    r.entry.1.mem ρ h l = true ↔ r.resolve ρ h = some l := by
  simp only [ArgumentSpineRegion.entry, Region.mem, ArgumentSpineRegion.resolve]
  cases HeapKnowledge.readPath h (ρ r.position) r.path <;> simp [spineOf]

/-- **The bridge.** A closed footprint excepting the selected spines is the
regional footprint of its two classes and each selected spine at `any`. -/
theorem ArgumentSpineRegionsWithin.iff_post {c : Closed} {regions : List ArgumentSpineRegion}
    {ρ : Env} {entry after : Heap} :
    ArgumentSpineRegionsWithin c regions ρ entry after ↔
      Post (c.fp ++ regions.map ArgumentSpineRegion.entry) ρ entry after := by
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
