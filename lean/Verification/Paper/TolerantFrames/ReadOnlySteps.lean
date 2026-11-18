import Verification.Paper.TolerantFrames.ReadOnlyChecks
import Verification.Semantics.KindsWrites

/-! # Read-only handles: what a step of the calculus changes

The draft's lemma (L1) assumes of a step of code that is not the
package's that it changes only storage its frames reach
(`ReadOnlyFrame.OutsideStep.reach`). Of the paper model's reduction
(`Step`) this holds with the term as the frame: every old location a step
changes is a slot or an element cell the term references directly
(`step_changes`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

/-- **A location the term references as a slot or an element cell.** -/
def RefAt (l : Nat) (t : Tm) : Prop := (∃ k, Ref.slot k l ∈ refs t) ∨ Ref.elem l ∈ refs t

theorem RefAt.mono {l : Nat} {a b : Tm} (hsub : ∀ r, r ∈ refs a → r ∈ refs b) (ha : RefAt l a) : RefAt l b :=
  ha.elim (fun ⟨k, hk⟩ => .inl ⟨k, hsub _ hk⟩) (fun he => .inr (hsub _ he))

theorem refs_of_get {args : List Tm} {i : Nat} {a : Tm} {r : Ref} (h : args[i]? = some a) (hr : r ∈ refs a) :
    r ∈ refsArgs args := by
  rw [refsArgs_eq]
  exact List.mem_flatMap.mpr ⟨a, List.mem_of_getElem? h, hr⟩

/-- **A step of the calculus changes only what its term references**: every
old location whose contents a step changes is a slot of an object, or an
element cell of a spine, the term holds. -/
theorem step_changes {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    ∀ {l : Nat} {v : Val}, h[l]? = some v → h'[l]? ≠ some v → RefAt l t := by
  induction hs
  all_goals intro l v hv hn
  all_goals try first
    | exact (hn hv).elim
    | exact (hn (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv)).elim
    | exact (hn (by
        rw [List.append_assoc, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv)).elim
    | (rename_i ih; exact (ih hv hn).mono fun r hr => by
        simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
        first
          | simp [hr]
          | exact .inr ⟨_, List.mem_of_getElem? ‹_ = some _›, hr⟩
          | exact .inl (.inr ⟨_, List.mem_of_getElem? ‹_ = some _›, hr⟩))

  case makeArg c ns inits i _ _ a _ hget _ _ ih =>
    exact (ih hv hn).mono fun r hr => by
      have hx : ∃ x ∈ inits, r ∈ refs x := ⟨a, List.mem_of_getElem? hget, hr⟩
      cases c <;> simp [refs, refsArgs_eq, hx]
  case arrArg inits i _ _ a _ hget _ _ ih =>
    exact (ih hv hn).mono fun r hr => by
      have hx : ∃ x ∈ inits, r ∈ refs x := ⟨a, List.mem_of_getElem? hget, hr⟩
      simp [refs, refsArgs_eq, hx]
  case writeField oid f fs c l' _ w _ hf _ =>
    by_cases he : l = l'
    · subst he
      exact .inl ⟨f, by simp only [refs, List.mem_append]; exact .inl (slot_mem_refs (lookup_mem_pair hf))⟩
    · exact (hn (by rw [List.getElem?_set_ne (Ne.symm he)]; exact hv)).elim
  case setPresent ls b l' _ w _ hl _ =>
    by_cases he : l = l'
    · subst he
      refine .inr ?_
      simp only [refs, List.mem_append, spineRefs, List.mem_filterMap]
      exact .inl (.inl ⟨some l, Kinds.elemLoc_mem hl, rfl⟩)
    · exact (hn (by rw [List.getElem?_set_ne (Ne.symm he)]; exact hv)).elim

end Verification.TolerantFrames.ReadOnly
