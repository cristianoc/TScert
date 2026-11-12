import Verification.Programs.TolerantFramesStoreOpsEdge
import Verification.Programs.TolerantFramesEdge

/-! # Tolerant frames: an edge's mapped names where its slots are below the source's width

`mapNames` names a target's slots: the slots before the mapping's last run
by a cursor over the source's names (`Cursor.get`, the name at the slot,
`0` past the end), the run's slots by the source's suffix from its first
slot. Proved: (`cursor_get`) a cursor reads the element at its index;
(`mapNames_some`) `mapNames` is the source's name at each slot before the
run, then the suffix; (`orderedSuffix_run`) every slot of the run reads the
source in order to its end; (`mapNamesSound_of_lt`) where every slot of the
mapping is below the source's width, each target slot is named by its
source slot's name (`MapNamesSound`). -/
namespace Verification.TolerantFrames
open Verification SinglePass

section MapNames

/-- A cursor whose remaining elements are its list from its position. -/
def CursorAt {α : Type} (c : Cursor α) : Prop := c.rest = c.all.drop c.pos

/-- **A cursor reads the element at its index** and stays a cursor over
the same list. -/
theorem cursor_get {α : Type} {c : Cursor α} (hc : CursorAt c) (i : Nat) :
    (c.get i).1 = c.all[i]? ∧ CursorAt (c.get i).2 ∧ (c.get i).2.all = c.all := by
  unfold Cursor.get CursorAt at *
  split
  · rename_i hi
    refine ⟨?_, ?_, rfl⟩
    · simp only [hc, List.drop_drop, List.head?_drop]
      congr 1; omega
    · simp only [hc, List.drop_drop]
      congr 1; omega
  · exact ⟨by simp [List.head?_drop], rfl, rfl⟩

/-- The cursor fold of `mapNames` pushes the source's name at each slot,
`0` past the end. -/
theorem cursor_fold (names : List Nat) : ∀ (l : List Nat) (c : Cursor Nat) (out : Array Nat),
    CursorAt c → c.all = names →
    (l.foldl (fun ((cur : Cursor Nat), (out : Array Nat)) s =>
      let (x, c) := cur.get s
      (c, out.push (x.getD 0))) (c, out)).2.toList = out.toList ++ l.map fun s => (names[s]?).getD 0
  | [], _, out, _, _ => by simp
  | s :: l, c, out, hc, ha => by
    obtain ⟨h1, h2, h3⟩ := cursor_get hc s
    rw [List.foldl_cons]
    simp only
    rw [cursor_fold names l _ _ h2 (h3.trans ha), h1, ha]
    simp

/-- **`mapNames` at a mapping of slots**: the source's name at each slot
before the last run (`orderedSuffix`), `0` past the end, then the source's
suffix from the run's first slot. -/
theorem mapNames_some (names slots : List Nat) :
    mapNames names (some slots) =
      (slots.take (orderedSuffix slots names.length)).map (fun s => (names[s]?).getD 0) ++
        (if orderedSuffix slots names.length < slots.toArray.size then
          names.drop slots.toArray[orderedSuffix slots names.length]! else []) := by
  unfold mapNames
  simp only
  rw [cursor_fold names _ (Cursor.of names) _ (show CursorAt (Cursor.of names) from rfl) rfl]
  simp [Array.mkEmpty]

/-- **Every slot of the mapping's last run reads the source in order to
its end** (`orderedSuffix.down` continues only past such a slot). -/
theorem orderedSuffix_run (n : Nat) (arr : Array Nat) : ∀ k i, orderedSuffix.down n arr k ≤ i → i < k →
    arr[i]! + (arr.size - (i + 1)) + 1 = n
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, i, h1, h2 => by
    unfold orderedSuffix.down at h1
    split at h1
    · rename_i hc
      by_cases hik : i = k
      · subst hik; simpa using hc
      · exact orderedSuffix_run n arr k i h1 (by omega)
    · omega

/-- **A mapping's target slots are named by their source slots' names**
(`MapNamesSound`) where every slot it reads is below the source's width. -/
theorem mapNamesSound_of_lt {names : List Nat} {m : PointClaims.Mapping}
    (hlt : ∀ slots, m = some slots → ∀ s ∈ slots, s < names.length) : MapNamesSound names m := by
  cases m with
  | none => exact mapNamesSound_none names
  | some slots =>
    have hs := hlt slots rfl
    intro j x hj
    simp only [PointClaims.slot]
    rw [mapNames_some] at hj
    have hd := orderedSuffix_down names.length slots.toArray slots.toArray.size
    have hrun := orderedSuffix_run names.length slots.toArray slots.toArray.size
    unfold orderedSuffix at hj hd hrun
    simp only [List.size_toArray] at hd hrun hj
    generalize hk : orderedSuffix.down names.length slots.toArray slots.length = k at hj hd hrun
    obtain ⟨hkle, hkrun⟩ := hd
    by_cases hjk : j < k
    · rw [List.getElem?_append_left (by simp; omega)] at hj
      rw [List.getElem?_map, List.getElem?_take, if_pos hjk] at hj
      have hjs : j < slots.length := by omega
      rw [List.getElem?_eq_getElem hjs] at hj ⊢
      simp only [Option.map_some, Option.some.injEq, Option.getD_some] at hj ⊢
      have := hs _ (List.getElem_mem hjs)
      rw [List.getElem?_eq_getElem this] at hj ⊢
      simpa using hj
    · have hlen : ((slots.take k).map fun s => (names[s]?).getD 0).length = k := by simp; omega
      rw [List.getElem?_append_right (by omega), hlen] at hj
      split at hj
      · rename_i hkl
        have hkl' : k < slots.length := by simpa using hkl
        have hrk := hrun k (Nat.le_refl _) hkl'
        rw [List.getElem?_drop] at hj
        have hjl : j < slots.length := by
          refine Nat.lt_of_not_le fun hn => ?_
          have : names.length ≤ slots.toArray[k]! + (j - k) := by
            simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray] at hrk ⊢
            omega
          rw [List.getElem?_eq_none this] at hj; cases hj
        have hrj := hrun j (by omega) hjl
        rw [List.getElem?_eq_getElem hjl]
        simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
          List.getElem?_eq_getElem hjl, List.getElem?_eq_getElem hkl', Option.getD_some] at hrk hrj hj ⊢
        rw [← hj]; congr 1; omega
      · simp at hj

end MapNames

end Verification.TolerantFrames
