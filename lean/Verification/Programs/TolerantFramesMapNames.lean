import Verification.Programs.TolerantFramesStoreOpsEdge
import Verification.Programs.TolerantFramesEdge

/-! # The name mapping reads the source slots it names -/
namespace Verification.TolerantFrames
open Verification SinglePass

/-- A cursor whose suffix matches its position reads the original list. -/
theorem cursor_get_eq {α : Type} (c : Cursor α) (hc : c.rest = c.all.drop c.pos) (i : Nat) :
    (c.get i).1 = c.all[i]? ∧ (c.get i).2.all = c.all ∧
      (c.get i).2.rest = (c.get i).2.all.drop (c.get i).2.pos := by
  unfold Cursor.get
  split
  · rename_i h
    simp only [hc, List.drop_drop]
    have he : c.pos + (i - c.pos) = i := by omega
    rw [he]
    exact ⟨List.head?_drop, trivial, rfl⟩
  · exact ⟨List.head?_drop, rfl, rfl⟩

/-- The prefix part of `mapNames` is indexed lookup through its cursor. -/
theorem mapNames_fold (slots : List Nat) (cur : Cursor Nat) (out : Array Nat)
    (hc : cur.rest = cur.all.drop cur.pos) :
    (slots.foldl (fun ((c : Cursor Nat), (o : Array Nat)) s =>
      let (x, c') := c.get s
      (c', o.push (x.getD 0))) (cur, out)).2.toList =
      out.toList ++ slots.map (fun i => (cur.all[i]?).getD 0) := by
  induction slots generalizing cur out with
  | nil => simp
  | cons i slots ih =>
    have hg := cursor_get_eq cur hc i
    simp only [List.foldl_cons]
    rw [ih _ _ hg.2.2, hg.2.1, Array.toList_push, hg.1]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

/-- Each slot in the ordered suffix reads the corresponding position at
its distance from the end of the source. -/
theorem orderedSuffix_slots (n : Nat) (arr : Array Nat) : ∀ k,
    k ≤ arr.size → ∀ j, orderedSuffix.down n arr k ≤ j → j < k →
      arr[j]! + (arr.size - (j + 1)) + 1 = n
  | 0, _, _, _, hj => by omega
  | k + 1, hk, j, hlo, hj => by
    unfold orderedSuffix.down at hlo
    split at hlo
    · rename_i hh
      by_cases hjk : j < k
      · exact orderedSuffix_slots n arr k (by omega) j hlo hjk
      · have : j = k := by omega
        subst j
        exact beq_iff_eq.mp hh
    · omega

/-- The optimized mapping agrees with direct indexed lookup, including
its default at an out-of-range source slot. -/
theorem mapNames_eq (names slots : List Nat) :
    mapNames names (some slots) = slots.map (fun i => (names[i]?).getD 0) := by
  unfold mapNames
  dsimp only
  rw [mapNames_fold _ _ _ rfl]
  let k := orderedSuffix slots names.length
  have hk : k ≤ slots.length := (orderedSuffix_down names.length slots.toArray slots.toArray.size).1
  have hslots : ∀ j, k ≤ j → j < slots.length →
      slots.toArray[j]! + (slots.length - (j + 1)) + 1 = names.length := by
    intro j hj hlt
    exact orderedSuffix_slots names.length slots.toArray slots.toArray.size (Nat.le_refl _) j hj hlt
  change (slots.take k).map (fun i => (names[i]?).getD 0) ++
    (if k < slots.toArray.size then names.drop slots.toArray[k]! else []) =
    slots.map (fun i => (names[i]?).getD 0)
  conv => rhs; rw [← List.take_append_drop k slots, List.map_append]
  congr 1
  split
  · rename_i hlt
    simp only [List.size_toArray] at hlt
    apply List.ext_getElem
    · have hs := hslots k (Nat.le_refl _) hlt
      simp only [List.length_drop, List.length_map]
      omega
    · intro j hj hj'
      simp only [List.getElem_map, List.getElem_drop]
      have hkj : k + j < slots.length := by
        simp only [List.length_drop, List.length_map] at hj'
        omega
      have h0 := hslots k (Nat.le_refl _) hlt
      have h1 := hslots (k + j) (by omega) hkj
      have he : slots[k + j] = slots.toArray[k]! + j := by
        simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
          List.getElem?_eq_getElem hkj, Option.getD_some] at h1
        omega
      rw [he, List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rename_i hlt
    have he : k = slots.length := by
      simp only [List.size_toArray] at hlt
      omega
    simp only [he, List.drop_length, List.map_nil]

/-- A bounded mapping assigns each target slot the source name it reads. -/
theorem mapNamesSound_some (names slots : List Nat) (hb : ∀ i ∈ slots, i < names.length) :
    MapNamesSound names (some slots) := by
  intro j x hx
  rw [mapNames_eq, List.getElem?_map] at hx
  obtain ⟨i, hi, hix⟩ := Option.map_eq_some_iff.mp hx
  have hbi := hb i (List.mem_of_getElem? hi)
  simp only [PointClaims.slot, hi, Option.getD_some]
  rw [List.getElem?_eq_getElem hbi]
  simpa only [List.getElem?_eq_getElem hbi, Option.getD_some] using congrArg some hix

end Verification.TolerantFrames
