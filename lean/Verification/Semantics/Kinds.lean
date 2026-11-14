import Verification.Semantics.Heaps
/-!
# Fixed location kinds: what kinded satisfaction excludes

Kinded worlds (`Semantics/Worlds.lean`) give every location a role, fixed for
its life; heap satisfaction (`Semantics/Heaps.lean`) requires each location's
contents to have its role's shape. The heaps below meet no world.
-/
namespace Verification.Kinds

/-- **The audit's counter-heap is excluded.** In `[[1], 0, null]` the array
`z` holds its store at 0 and the object `o` its field `f` at 1, which `z`'s
store lists: location 1 would be both a field (or cell) location and an
element cell. No world, at any level, satisfies the heap with both values
valid. -/
theorem counterheap_excluded {n : Nat} (W : WorldT n) :
    ¬ (HeapOk n W [.arr [some 1], .num 0, .nul] ∧
      RefsOk W (.objAt [(arrayStoreKey, 0)] .absent 2) ∧
      RefsOk W (.objAt [(.str "f", 1)] .absent 2)) := by
  rintro ⟨hok, hz, ho⟩
  have h0 := (HeapOk.kinds hok).2.2 0 [some 1] rfl 1 (by simp)
  have h1 := ho (.slot (.str "f") 1) (by simp [refs, objRefs])
  simp only [RefOk] at h1
  simp only [K, kindAt, Option.map_eq_some_iff] at h0
  obtain ⟨r, hr, hk⟩ := h0.1
  rw [hr] at h1
  cases r <;> simp_all [SlotRole, Role.kind]

/-- **The dangling-store transition of the untyped model is
excluded**: no kinded world, at any level, is satisfied by a heap of three
locations whose store at 0 lists location 5. -/
theorem dangling_excluded {n : Nat} (W : WorldT n) :
    ¬ HeapOk n W [.arr [some 5], .nul, .nul] := by
  intro hok
  have := (HeapOk.kinds hok).2.2 0 [some 5] rfl 5 (by simp)
  simp at this

end Verification.Kinds
