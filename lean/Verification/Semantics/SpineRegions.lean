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


/-- Shift an argument region past the receiver slot: a region naming the
receiver (`0`) has no slot past it; each parameter position moves down by
one. -/
def ArgumentSpineRegion.pastReceiver (r : ArgumentSpineRegion) : Option ArgumentSpineRegion :=
  if r.position = 0 then none else some { r with position := r.position - 1 }

/-- **Environment transfer for regional footprints** (proved): a run within
`c` and `qregs` under `ρ₁` is within `c` and `regs` under `ρ₂` whenever
each entry of `qregs` matches an entry of `regs` with the same path, key,
change and entry value under `ρ₂`. -/
theorem ArgumentSpineRegionsWithin.of_env {c : Closed} {qregs regs : List ArgumentSpineRegion}
    {ρ₁ ρ₂ : Env} {entry after : Heap}
    (hmatch : ∀ g' ∈ qregs, ∃ g ∈ regs,
      g.path = g'.path ∧ g.key = g'.key ∧ g.change = g'.change ∧ ρ₂ g.position = ρ₁ g'.position)
    (h : ArgumentSpineRegionsWithin c qregs ρ₁ entry after) :
    ArgumentSpineRegionsWithin c regs ρ₂ entry after := by
  refine ⟨h.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := h.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact .inl rfl
  · rw [List.mem_append] at he
    rcases he with hc | hr
    · refine .inr ⟨e, List.mem_append_left _ hc, ?_, hh⟩
      have hcls : e.1.isClass = true := by
        cases c with
        | mk va ar vi =>
          simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl <;> rfl
      cases er : e.1 <;> simp [Region.isClass, er] at hcls
      simpa [Region.mem, er] using hm
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hr
      obtain ⟨g, hg, hpath, hkey, hch, hpos⟩ := hmatch g' hg'
      refine .inr ⟨g.entry, List.mem_append_right _ (List.mem_map.mpr ⟨g, hg, rfl⟩), ?_, ?_⟩
      · cases hgk : g'.key with
        | some k => simpa [ArgumentSpineRegion.entry, hkey, hgk, hpath, Region.mem, hpos] using hm
        | none => simpa [ArgumentSpineRegion.entry, hkey, hgk, hpath, Region.mem, hpos] using hm
      · cases hgk : g'.key <;> simpa [ArgumentSpineRegion.entry, hkey, hgk, hch] using hh

end Verification.Footprints
