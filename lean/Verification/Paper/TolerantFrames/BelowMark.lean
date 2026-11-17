import Verification.Paper.TolerantFrames.ModalReplacement
import Verification.Semantics.RegionBounds

/-! # Regions below the invocation entry mark

The existing mechanisms are valid references in an entry world and shared
region role bounds. The entry here is the enclosing INVOCATION entry, with mark
its heap length. A later command-entry heap does not supply this bound.
Immutable field/spine descriptors of an old value refer below that mark;
spine cell sets are deliberately excluded because growth may add new cells.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames
open Verification.Parity (Path)

inductive DescriptorRegion where
  | field (name : String)
  | fields
  | spine

def descriptorRegion (p : Path) : DescriptorRegion → Region
  | .field f => .path p.root p.fields (.str f)
  | .fields => .pathFields p.root p.fields
  | .spine => .spine p.root p.fields

/-- An entry-world role is below the length of the invocation-entry heap. -/
theorem entry_role_below {entry : IndexedHeap} {l : Nat} {r : Role}
    (hr : roleAt entry.W l = some r) : l < entry.h.length := by
  have hlen : entry.h.length = (entries entry.W).length := by simpa using entry.ok.1.1
  rw [hlen]
  exact roleAt_lt hr

/-- Bounds of an invocation-entry logical value come from its heap validity.
Only immutable descriptor regions are covered, not a growing spine's cells. -/
theorem belowMark_of_entry_heap (entry : IndexedHeap) {current : IndexedHeap} {ρ : Env} {p : Path} {v : Val}
    (hold : HeapRefs entry.h v) (hp : p.read ρ current.h = some v) (kind : DescriptorRegion) :
    BelowMark (descriptorRegion p kind) ρ entry.h.length current := by
  intro l hm
  have hread : readPath current.h (ρ p.root) p.fields = some v := hp
  cases v with
  | objAt fs c i =>
    cases kind with
    | field f =>
      have hmem : fs.lookup (.str f) = some l := by
        simpa only [descriptorRegion, Region.mem, hread, fieldsOf, beq_iff_eq] using hm
      exact hold.slot hmem
    | fields =>
      have hmem : (fieldLocs (.objAt fs c i)).contains l = true := by
        simpa only [descriptorRegion, Region.mem, hread] using hm
      simp only [fieldLocs, fieldsOf, List.contains_iff_mem, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at hmem
      obtain ⟨⟨k, l'⟩, ⟨hkl, _⟩, rfl⟩ := hmem
      exact HeapRefOk.allocated (hold _ (slot_mem_refs hkl))
    | spine =>
      have hmem : elementsOf (.objAt fs c i) = some l := by
        simpa only [descriptorRegion, Region.mem, hread, beq_iff_eq] using hm
      cases hk : fs.lookup arraySpineKey with
      | some st =>
        simp only [elementsOf, hk] at hmem; cases hmem
        exact hold.slot hk
      | none =>
        cases c <;> simp only [elementsOf, hk] at hmem <;> try cases hmem
        rename_i f n
        exact HeapRefOk.allocated (hold (.view l f n (fs.lookup arraySpineKey).isNone) (by simp [refs]))
  | _ => cases kind <;> simp [descriptorRegion, Region.mem, hread, fieldsOf, fieldLocs, elementsOf] at hm

/-- Entry-world reference validity is a sufficient origin-specific bridge. -/
theorem belowMark_of_entry_refs (entry : IndexedHeap) {current : IndexedHeap} {ρ : Env} {p : Path} {v : Val}
    (hold : RefsOk entry.W v) (hp : p.read ρ current.h = some v) (kind : DescriptorRegion) :
    BelowMark (descriptorRegion p kind) ρ entry.h.length current :=
  belowMark_of_entry_heap entry (HeapRefs.of_world hold) hp kind

/-- A parameter that still holds its invocation-entry value supplies the
entry references. Agreement is needed only for this root binding. -/
theorem belowMark_of_entry_variable (entry : IndexedHeap) {current : IndexedHeap} {ρ₀ ρ : Env} {x : Nat}
    (hroots : RootsOk entry.W ρ₀) (hx : ρ x = ρ₀ x) (kind : DescriptorRegion) :
    BelowMark (descriptorRegion ⟨x, []⟩ kind) ρ entry.h.length current := by
  apply belowMark_of_entry_refs entry (hroots x)
  simpa only [Parity.Path.read, readPath] using congrArg some hx

/-- A rigid path from an unchanged invocation-entry root supplies exactly
its old value, not merely a value valid in the later world. -/
theorem belowMark_of_rigid_entry (entry : IndexedHeap) {current : IndexedHeap} {ρ₀ ρ : Env} {p : Path}
    (hrigid : RigidPath p ρ₀ entry.h.length entry) (ha : Admissible entry current)
    (hroot : ρ p.root = ρ₀ p.root) (kind : DescriptorRegion) :
    BelowMark (descriptorRegion p kind) ρ entry.h.length current := by
  obtain ⟨v, _, hrefs, hread⟩ := hrigid
  apply belowMark_of_entry_heap entry hrefs
  have hp := hread current ha
  simpa only [Parity.Path.read, hroot] using hp

/-- Freshness separates a region from each descriptor region justified by
an invocation-entry value. It does not assume every old receiver's cells old. -/
theorem fresh_disjoint_entry_refs (entry : IndexedHeap) {current : IndexedHeap} {ρ : Env}
    {p : Path} {v : Val} {r : Region} (hold : RefsOk entry.W v)
    (hp : p.read ρ current.h = some v) (hf : Fresh r ρ entry.h.length current) (kind : DescriptorRegion) :
    ∀ l, r.mem ρ current.h l = true → (descriptorRegion p kind).mem ρ current.h l = true → False :=
  fresh_disjoint_below hf (belowMark_of_entry_refs entry hold hp kind)

end Verification.Paper.TolerantFrames
