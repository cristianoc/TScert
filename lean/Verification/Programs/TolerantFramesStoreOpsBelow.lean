import Verification.Programs.TolerantFramesStoreOpsDrop

/-! # Tolerant frames: the store's names below the counter

`StateWF.below` asks every name of the stored facts to be below the pass's
next fresh name. This module proves that adding a fact whose names are below
it and removing any fact keep that (`addRaw_below`, `remove_below`,
`addBound_below`, `add_below`), from the facts each operation adds: the
fact's canonical form, which names what the fact names (`canon_names`), and
of a length fact its linear facts, over its names. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

/-- Every name of every stored fact is below `next`. -/
def FactsBelow (s : Store) (next : Nat) : Prop := ∀ a ∈ storeAll s, ∀ x ∈ a.names, x < next

theorem canon_names (a : Atom) : a.canon.names = a.names := by
  cases a with
  | index x => rcases x with ⟨f, c, neg⟩; cases c <;> cases neg <;> rfl
  | elem e => simp only [Atom.canon]; split <;> rfl
  | cell _ | value _ | link _ | sep _ => rfl

theorem addRaw_below {s : Store} {a : Atom} {next : Nat} (hs : FactsBelow s next) (ha : ∀ x ∈ a.names, x < next) :
    FactsBelow (s.addRaw a) next := by
  have hc : ∀ x ∈ a.canon.names, x < next := by rw [canon_names]; exact ha
  unfold Store.addRaw
  dsimp only
  split
  · exact hs
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · rcases keys_insert _ _ _ hy with rfl | hy
      · exact hc
      · exact hs y (List.mem_append_left _ hy)
    · refine vals_foldl (fun y => ∀ x ∈ y.names, x < next) _ (fun m n hm y hy => ?_) _ _
        (fun y hy => hs y (List.mem_append_right _ hy)) y hy
      rcases vals_insert _ _ _ _ hy with hy | hy
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hc
        · exact hm y (findD_vals _ _ _ hy)
      · exact hm y hy

theorem remove_below {s : Store} {a : Atom} {next : Nat} (hs : FactsBelow s next) : FactsBelow (s.remove a) next := by
  unfold Store.remove
  dsimp only
  split
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hs y (List.mem_append_left _ (keys_erase _ _ _ hy))
    · refine vals_foldl (fun y => ∀ x ∈ y.names, x < next) _ (fun m n hm y hy => ?_) _ _
        (fun y hy => hs y (List.mem_append_right _ hy)) y hy
      rcases vals_insert _ _ _ _ hy with hy | hy
      · exact hm y (findD_vals _ _ _ (List.mem_of_mem_erase hy))
      · exact hm y hy
  · exact hs

theorem foldl_remove_below {next : Nat} :
    ∀ (as : List Atom) (s : Store), FactsBelow s next → FactsBelow (as.foldl Store.remove s) next
  | [], _, hs => hs
  | _ :: as, _, hs => foldl_remove_below as _ (remove_below hs)

theorem addBound_below {s : Store} {a : Atom} {next : Nat} (hs : FactsBelow s next)
    (ha : ∀ x ∈ a.names, x < next) : FactsBelow (s.addBound a) next := by
  have hc : ∀ x ∈ a.canon.names, x < next := by rw [canon_names]; exact ha
  unfold Store.addBound
  dsimp only
  split
  · exact hs
  · split
    · split
      · exact hs
      · exact addRaw_below (foldl_remove_below _ _ hs) hc
    · exact addRaw_below hs hc

theorem foldl_addBound_below {next : Nat} {c : Option Nat} {neg : Bool} :
    ∀ (Fs : List (Linear.Fact HeapKnowledge.Term)) (s : Store), FactsBelow s next →
      (∀ F ∈ Fs, ∀ y ∈ (Atom.index ⟨.linear F, c, neg⟩).names, y < next) →
      FactsBelow (Fs.foldl (fun (s : Store) F => s.addBound (.index ⟨.linear F, c, neg⟩)) s) next
  | [], _, hs, _ => hs
  | F :: Fs, _, hs, hx => foldl_addBound_below Fs _ (addBound_below hs (hx F (List.mem_cons_self ..)))
      fun G hG => hx G (List.mem_cons_of_mem _ hG)

/-- **Adding a fact whose names are below `next` keeps every stored fact's
names below it** (`Store.add`): a length fact's linear facts name its two
names. -/
theorem add_below {s : Store} {a : Atom} {next : Nat} (hs : FactsBelow s next) (ha : ∀ x ∈ a.names, x < next) :
    FactsBelow (s.add a) next := by
  have hc : ∀ x ∈ a.canon.names, x < next := by rw [canon_names]; exact ha
  unfold Store.add
  dsimp only
  split
  · exact hs
  · refine addBound_below ?_ hc
    split
    · rename_i _ x n c neg heq
      rw [heq] at hc
      have hx : ∀ F ∈ HeapKnowledge.atomLinear (.length x n), ∀ y ∈ (Atom.index ⟨.linear F, c, neg⟩).names, y < next := by
        intro F hF y hy
        simp only [HeapKnowledge.atomLinear, List.mem_cons, List.mem_nil_iff, or_false] at hF
        apply hc
        have hy' : y = x ∨ y = n ∨ c = some y := by
          rcases hF with rfl | rfl <;>
            simp [Atom.names, HeapKnowledge.IndexFact.slots, Linear.Fact.vars, HeapKnowledge.Term.slots,
              HeapKnowledge.Term.length, HeapKnowledge.Term.value] at hy <;>
            rcases hy with h | h | h <;> simp [h]
        rcases hy' with rfl | rfl | h <;> simp_all [Atom.names, HeapKnowledge.IndexFact.slots]
      exact foldl_addBound_below _ _ hs hx
    · exact hs

end Verification.TolerantFrames
