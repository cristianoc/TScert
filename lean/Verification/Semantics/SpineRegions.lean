import Verification.Semantics.ClosedFootprints

/-! Argument regions read from entry values through data-field paths: the
locations a call position's path selects at the call's entry, each at a
change, beside the closed bound on every location. The selected locations
are the object's field at a key (`key = some k`; the spine key `[]` selects
the spine), or every field of the object (`key = none`). -/
namespace Verification.Footprints

/-- **An argument region**: a call position (`0` is the receiver), a path of
own data fields, what it selects of the object the path reads (its field at
`k` where `key = some k`, its spine at the spine key; every field of it
where `key = none`) and the change the selected locations may undergo. -/
structure ArgumentSpineRegion where
  position : Nat
  path : List String
  key : Option PropKey := some arraySpineKey
  change : Change := .any
  deriving Repr, DecidableEq

/-- The region's entry of the regional footprint: its selected locations at
its change. -/
def ArgumentSpineRegion.entry (r : ArgumentSpineRegion) : Region × Change :=
  match r.key with
  | some k => (.path r.position r.path k, r.change)
  | none => (.pathFields r.position r.path, r.change)

/-- The stated frame of a closed bound and argument regions: the closed
bound on every location, each region's selected locations at its change,
regions read at the entry heap. -/
def ArgumentSpineRegionsWithin (c : Closed) (regions : List ArgumentSpineRegion)
    (ρ : Env) (entry after : Heap) : Prop :=
  Post (c.fp ++ regions.map ArgumentSpineRegion.entry) ρ entry after

/-- **No regions.** With no region the frame is the closed footprint
itself. -/
theorem ArgumentSpineRegionsWithin.nil_holds {c : Closed} {ρ : Env} {entry after : Heap}
    (h : ArgumentSpineRegionsWithin c [] ρ entry after) : c.Holds entry after := by
  have hp : Post c.fp ρ entry after := by simpa [ArgumentSpineRegionsWithin] using h
  rw [Closed.holds_iff]
  exact Closed.post_iff.mp hp

/-- **The bridge**: the regions' frame is the regional footprint of the
closed bound's classes and each region's entry. -/
theorem ArgumentSpineRegionsWithin.iff_post {c : Closed} {regions : List ArgumentSpineRegion}
    {ρ : Env} {entry after : Heap} :
    ArgumentSpineRegionsWithin c regions ρ entry after ↔
      Post (c.fp ++ regions.map ArgumentSpineRegion.entry) ρ entry after :=
  Iff.rfl

end Verification.Footprints
