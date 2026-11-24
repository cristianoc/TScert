import Verification.Semantics.ArgumentSpineRegions

/-! # The support of a region fact

Stated for the acceptance path (`IndexWrites.grownRegions_holds`) and the
model (`TolerantFrames.apart_grow_keep`) alike. -/

namespace Verification.IndexWrites
open Verification HeapKnowledge

/-- **The note's support of a region fact** `apart(x, y)` (the note, §5,
after Definition "Support": $`\{x[\ast]{:}\,\mathsf{grow},\ y[\ast]{:}\,\mathsf{keep}\}`$):
`x`'s array spine at `grow`, which lists only its old cells and cells past
the heap's end, and `y`'s at `keep`. -/
def apartGrowSupport (x y : Nat) : Footprints.Footprint :=
  [(.field x arraySpineKey, .grow), (.field y arraySpineKey, .keep)]

/-- A value's region lies in the heap: its array spine's location and the
cells it lists below the heap's length. -/
def RegionBelow (h : Heap) (v : Val) : Prop :=
  ∃ st ls, Footprints.spineOf v = some st ∧ h[st]? = some (.arr ls) ∧ st < h.length ∧ ElementsBelow h.length ls

/-- **`apartGrowSupport x y` supports `apart(x, y)`** where `y`'s region lies
in the heap: `x`'s spine gains only cells past the heap's end, and `y`'s is
kept. -/
theorem apartGrow_supports (x y : Nat) :
    Footprints.Supports (fun ρ h _ => RegionBelow h (ρ y)) (fun ρ h => RegionsApart h (ρ x) (ρ y))
      (apartGrowSupport x y) := by
  refine Footprints.Supports.intro fun ρ h h' hc hA hs => ?_
  obtain ⟨sy, ys, hsy, hys, hylt, hyb⟩ := hc
  obtain ⟨sa, xs, sb, ys0, hra, hrb, hsep⟩ := hA
  obtain ⟨rfl, rfl⟩ := regionOf_unique hrb (.inr ⟨sy, rfl, hsy, hys⟩)
  have hmy : (Footprints.Region.field y arraySpineKey).mem ρ h sy = true := by
    simp [Footprints.Region.mem, Footprints.spineOf_lookup hsy]
  obtain ⟨vy, hvy, hky⟩ := hs (.field y arraySpineKey, .keep)
    (by simp [apartGrowSupport]) sy _ hmy hys
  simp only [Footprints.Change.Holds] at hky
  subst hky
  have hx' : ∃ sa' xs', RegionOf h' (ρ x) sa' xs' ∧
      ∀ l, InRegion sa' xs' l → InRegion sa xs l ∨ h.length ≤ l := by
    rcases hra with ⟨rfl, hv⟩ | ⟨sx, rfl, hsx, hxs⟩
    · exact ⟨none, xs, .inl ⟨rfl, hv⟩, fun l hl => .inl hl⟩
    · have hmx : (Footprints.Region.field x arraySpineKey).mem ρ h sx = true := by
        simp [Footprints.Region.mem, Footprints.spineOf_lookup hsx]
      obtain ⟨vx, hvx, hkx⟩ := hs (.field x arraySpineKey, .grow)
        (by simp [apartGrowSupport]) sx _ hmx hxs
      rcases hkx with rfl | ⟨ls, ls', heq, rfl, -, hnew, -⟩ | hsc | ⟨f, cs, cs', hvw, -⟩
      · exact ⟨some sx, xs, .inr ⟨sx, rfl, hsx, hvx⟩, fun l hl => .inl hl⟩
      · cases heq
        refine ⟨some sx, ls', .inr ⟨sx, rfl, hsx, hvx⟩, fun l hl => ?_⟩
        rcases hl with hl | hl
        · exact .inl (.inl hl)
        · exact (hnew l hl).imp .inr id
      · simp [Footprints.ScalarStep, Footprints.isArr] at hsc
      · cases hvw
  obtain ⟨sa', xs', hra', hgrow⟩ := hx'
  refine ⟨sa', xs', some sy, _, hra', .inr ⟨sy, rfl, hsy, hvy⟩, fun l hl m hm => ?_⟩
  have hmb : m < h.length := by
    rcases hm with hm | hm
    · cases hm; exact hylt
    · exact hyb m hm
  rcases hgrow l hl with hl | hl
  · exact hsep l hl m hm
  · omega

/-- **The mirror support** `apartGrowSupport y x` supports `apart(x, y)`
where `x`'s region lies in the heap. -/
theorem apartGrow_supports_mirror (x y : Nat) :
    Footprints.Supports (fun ρ h _ => RegionBelow h (ρ x)) (fun ρ h => RegionsApart h (ρ x) (ρ y))
      (apartGrowSupport y x) :=
  Footprints.Supports.intro fun _ _ _ hc hA hs =>
    regionsApart_symm ((apartGrow_supports y x).apply hc (regionsApart_symm hA) hs)

end Verification.IndexWrites
