import Verification.Programs.TolerantFramesMergeNear
import Verification.Programs.TolerantFramesStore

/-! # Tolerant frames: the rounds of the search near a merge's names

`linearNearFuel s names limit fuel` (`TolerantFramesMergeNear`) runs at most
`fuel` rounds. Over a well-formed store (`StoreWF`: each fact an `about`
list holds is live), `s.size + 1` rounds reach the loop's end: more fuel
returns the same facts (`linearNearFuel_rounds`). A round that leaves the
next frontier non-empty kept a fact (`nearRound_progress`); the facts kept
are distinct live facts, so at most `s.size` of them are listed
(`NearInv.out_le`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations HeapKnowledge
open Verification.SinglePass (Atom Store State NearState nearStep nearRound nearLoop linearNearFuel)

/-- A list without repeats inside another is no longer. -/
theorem nodup_length_le {α : Type} [DecidableEq α] :
    ∀ (L M : List α), L.Nodup → L ⊆ M → L.length ≤ M.length
  | [], _, _, _ => by simp
  | a :: L, M, hn, hs => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ M := hs (List.mem_cons_self ..)
    have := nodup_length_le L (M.erase a) hn.2 fun x hx =>
      (List.mem_erase_of_ne (fun h => hn.1 (by subst h; exact hx))).mpr (hs (List.mem_cons_of_mem _ hx))
    rw [List.length_erase_of_mem ha] at this
    have : 0 < M.length := List.length_pos_of_mem ha
    simp; omega

/-- **The search's invariant**: every listed fact is kept, the listed facts
are distinct, and each is a live fact of the store. -/
structure NearInv (s : Store) (st : NearState) : Prop where
  kept : ∀ i ∈ st.out.toList, Atom.index i ∈ st.kept
  nodup : (st.out.toList.map Atom.index).Nodup
  live : ∀ i ∈ st.out.toList, Atom.index i ∈ s.live

/-- **At most the store's size is listed.** -/
theorem NearInv.out_le {s : Store} {st : NearState} (h : NearInv s st) : st.out.size ≤ s.size := by
  have := nodup_length_le _ s.live.toList h.nodup fun a ha => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact Std.HashSet.mem_toList.mpr (h.live i hi)
  simpa [Store.size, Std.HashSet.length_toList] using this

/-- The names' fold of a step changes the seen names and the next frontier
only. -/
theorem nearNames_out (L : List Nat) (st : NearState) :
    let st' := L.foldl (fun (st : NearState) y =>
      if !st.seen.contains y then { st with seen := st.seen.insert y, next := y :: st.next } else st) st
    st'.out = st.out ∧ st'.kept = st.kept := by
  induction L generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons y L ih =>
    simp only [List.foldl_cons]
    split
    · exact ih _
    · exact ih _

/-- **One step keeps the invariant, and either changes nothing listed and
next or lists one fact more.** -/
theorem nearStep_inv {s : Store} (w : StoreWF s) {limit x : Nat} {a : Atom} (ha : a ∈ s.about x)
    {st : NearState} (hst : NearInv s st) :
    NearInv s (nearStep limit st a) ∧
      ((nearStep limit st a).out.size = st.out.size + 1 ∨
        ((nearStep limit st a).out = st.out ∧ (nearStep limit st a).next = st.next)) := by
  unfold nearStep
  split
  · rename_i i
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      have hnk : Atom.index i ∉ st.kept := by
        intro hm; rw [Std.HashSet.contains_iff_mem.mpr hm] at hc; exact absurd hc.1.2 (by simp)
      have hpush : NearInv s { st with kept := st.kept.insert (.index i), out := st.out.push i } := by
        refine ⟨fun j hj => ?_, ?_, fun j hj => ?_⟩
        · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hj
          rcases hj with hj | rfl
          · exact Std.HashSet.mem_insert.mpr (.inr (hst.kept j hj))
          · exact Std.HashSet.mem_insert.mpr (.inl (by simp))
        · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
          refine List.nodup_append.mpr ⟨hst.nodup, (by simp), ?_⟩
          intro b hb c hc' hbc
          rw [List.mem_singleton] at hc'
          subst hc' hbc
          obtain ⟨j, hj, he⟩ := List.mem_map.mp hb
          exact hnk (he ▸ hst.kept j hj)
        · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hj
          rcases hj with hj | rfl
          · exact hst.live j hj
          · exact w.indexed x _ ha
      split
      · rename_i hf
        obtain ⟨ho, hk⟩ := nearNames_out (Atom.index i).names { st with kept := st.kept.insert (.index i), out := st.out.push i }
        refine ⟨?_, .inl ?_⟩
        · exact { kept := fun j hj => by rw [hk]; rw [ho] at hj; exact hpush.kept j hj
                  nodup := by rw [ho]; exact hpush.nodup
                  live := fun j hj => by rw [ho] at hj; exact hpush.live j hj }
        · rw [ho]; simp
      · exact ⟨hpush, .inl (by simp)⟩
    · exact ⟨hst, .inr ⟨rfl, rfl⟩⟩
  · exact ⟨hst, .inr ⟨rfl, rfl⟩⟩

/-- The steps over one name's facts keep the invariant; the listed facts
only grow; where the next frontier changes, a fact was listed. -/
theorem nearSteps_inv {s : Store} (w : StoreWF s) {limit x : Nat} :
    ∀ (L : List Atom), (∀ a ∈ L, a ∈ s.about x) → ∀ (st : NearState), NearInv s st →
      NearInv s (L.foldl (nearStep limit) st) ∧ st.out.size ≤ (L.foldl (nearStep limit) st).out.size ∧
        ((L.foldl (nearStep limit) st).next ≠ st.next → st.out.size < (L.foldl (nearStep limit) st).out.size)
  | [], _, st, h => ⟨h, Nat.le_refl _, fun hne => absurd rfl hne⟩
  | a :: L, hL, st, h => by
    obtain ⟨h1, hstep⟩ := nearStep_inv w (hL a (List.mem_cons_self ..)) (limit := limit) h
    obtain ⟨h2, hle, hlt⟩ := nearSteps_inv w L (fun b hb => hL b (List.mem_cons_of_mem _ hb)) _ h1
    simp only [List.foldl_cons]
    refine ⟨h2, ?_, fun hne => ?_⟩
    · rcases hstep with he | ⟨he, -⟩ <;> rw [he] at hle <;> omega
    · rcases hstep with he | ⟨he, hn⟩
      · rw [he] at hle; omega
      · rw [he] at hle hlt
        exact hlt (fun h' => hne (h'.trans hn))

/-- **A round keeps the invariant; a round leaving a non-empty next
frontier listed a fact more.** -/
theorem nearRound_progress {s : Store} (w : StoreWF s) {limit : Nat} (frontier : List Nat) {st : NearState}
    (hst : NearInv s st) :
    NearInv s (nearRound s limit frontier st) ∧
      ((nearRound s limit frontier st).next ≠ [] → st.out.size < (nearRound s limit frontier st).out.size) := by
  unfold nearRound
  have key : ∀ (F : List Nat) (st' : NearState), NearInv s st' → st.out.size ≤ st'.out.size →
      (st'.next ≠ [] → st.out.size < st'.out.size) →
      NearInv s (F.foldl (fun st x => (s.about x).foldl (nearStep limit) st) st') ∧
        ((F.foldl (fun st x => (s.about x).foldl (nearStep limit) st) st').next ≠ [] →
          st.out.size < (F.foldl (fun st x => (s.about x).foldl (nearStep limit) st) st').out.size) := by
    intro F
    induction F with
    | nil => intro st' h hle hlt; exact ⟨h, hlt⟩
    | cons x F ih =>
      intro st' h hle hlt
      obtain ⟨h2, hle2, hlt2⟩ := nearSteps_inv w (limit := limit) (x := x) (s.about x) (fun _ ha => ha) st' h
      refine ih _ h2 (Nat.le_trans hle hle2) fun hne => ?_
      by_cases hn : ((s.about x).foldl (nearStep limit) st').next = st'.next
      · rw [hn] at hne; exact Nat.lt_of_lt_of_le (hlt hne) hle2
      · exact Nat.lt_of_le_of_lt hle (hlt2 hn)
  exact key frontier { st with next := [] } ⟨hst.kept, hst.nodup, hst.live⟩ (Nat.le_refl _) (fun h => absurd rfl h)

/-- The loop over an empty frontier returns its state. -/
theorem nearLoop_nil {s : Store} {limit : Nat} : ∀ (n : Nat) (st : NearState), nearLoop s limit n [] st = st
  | 0, _ => rfl
  | _ + 1, _ => by simp [nearLoop]

/-- **The loop has ended once its fuel exceeds the facts left to list**:
from a state meeting the invariant, with fewer than `n` facts of the store
left unlisted, more fuel returns the same state. -/
theorem nearLoop_stable {s : Store} (w : StoreWF s) {limit : Nat} :
    ∀ (n : Nat) (frontier : List Nat) (st : NearState), NearInv s st → s.size - st.out.size < n →
      ∀ k, nearLoop s limit (n + k) frontier st = nearLoop s limit n frontier st
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, frontier, st, hst, hlt, k => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [nearLoop]
    split
    · obtain ⟨hinv, hprog⟩ := nearRound_progress w (limit := limit) frontier hst
      by_cases hn : (nearRound s limit frontier st).next = []
      · rw [hn, nearLoop_nil, nearLoop_nil]
      · have hgt := hprog hn
        have hle := hinv.out_le
        exact nearLoop_stable w n _ _ hinv (by omega) k
    · rfl

/-- **`s.size + 1` rounds suffice**: over a well-formed store, the search
near `names` returns the same facts at any fuel past `s.size + 1`, so the
equation `LinearNearFuelEq` is with the loop run to its end. -/
theorem linearNearFuel_rounds {s : Store} (w : StoreWF s) (names : List Nat) (limit k : Nat) :
    linearNearFuel s names limit (s.size + 1 + k) = linearNearFuel s names limit := by
  unfold linearNearFuel
  rw [nearLoop_stable w (s.size + 1) names _ ⟨fun _ h => by simp at h, by simp, fun _ h => by simp at h⟩
    (by simp) k]

end Verification.TolerantFrames
