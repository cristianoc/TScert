import Verification.Programs.TolerantFramesModelRules
import Verification.Semantics.KindsStates
/-!
# The note's (View) and Alloc over well-formed states

The rules of `Programs/TolerantFramesModelRules.lean` that carry a premise of
the world there, stated over the well-formed states of
`Semantics/KindsStates.lean`, where the premise is part of the state:

- **(View)**: a linear fact whose current terms are slots' integers and
  typed-array lengths holds after every admissible transition (`view_box`);
  the two heaps of that module's `view_not_invariant` are no admissible
  transition between states validating the view (`view_change_excluded`);
- **Alloc**: the allocated array is fresh, empty and apart from every array
  of the well-formed heap it was allocated in (`alloc_post`), and the heap
  after the allocation is well-formed with the array valid (`alloc_wellformed`).
-/
namespace Verification.Kinds
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints
open Verification.TolerantFrames (allocated viewObj viewObj_length oneBits oneBits_safe)

/-! ## (View) -/

/-- **(View)**: a linear fact whose current terms are slots' integers and
typed-array lengths holds after every admissible transition; its entry
terms, of any kind and path, read the entry state. -/
theorem view_box {F : Linear.Fact HeapKnowledge.Term} {ρ : Env} {m : Nat} {s : State ρ}
    (hv : ∀ t ∈ F.vars, t.atEntry = false → t.path = [] ∧ (t.kind = .value ∨ t.kind = .view))
    (hF : (HeapKnowledge.IndexFact.linear F).HoldsAt ε ρ s.h) :
    Box Footprints.Closed.top.fp
      (fun ρ _ s => (HeapKnowledge.IndexFact.linear F).HoldsAt ε ρ s.h) ρ m s := by
  intro s' ha
  show (HeapKnowledge.IndexFact.linear F).HoldsAt ε ρ s'.h
  have he : ∀ t ∈ F.vars, HeapKnowledge.termValue ε ρ s'.h t = HeapKnowledge.termValue ε ρ s.h t := by
    intro t ht
    obtain ⟨k, slot, p, e⟩ := t
    cases e
    case true => exact HeapKnowledge.termValue_entry_invariant rfl
    obtain ⟨hp, hk⟩ := hv _ ht rfl
    simp only at hp hk
    subst hp
    rcases hk with rfl | rfl
    · rfl
    · simp only [HeapKnowledge.termValue_nil, HeapKnowledge.kindValue]
      exact viewLengthOf_kept (s.roots slot) ha.1
  obtain ⟨hd, hh⟩ := hF
  refine ⟨fun t ht => by rw [he t ht]; exact hd t ht, ?_⟩
  refine (Linear.Fact.holds_congr fun t ht => ?_).mpr hh
  simp only [HeapKnowledge.termValuation, he t ht]

/-- **No admissible transition changes a valid view's length**: from a state
validating the typed array `viewObj` whose heap gives it the length 1, no
admissible transition reaches the heap giving it the length 2. -/
theorem view_change_excluded {s s' : IndexedHeap} (ha : Admissible s s') (hv : RefsOk s.W viewObj)
    (h₁ : s.h = [.nul, .num oneBits, .nul]) : s'.h ≠ [.nul, .num (bitsOfNat 2), .nul] := by
  intro h₂
  have two : SafeIntegers.SafeInt (bitsOfNat 2) 2 := ⟨by decide, .inl ⟨by decide, rfl⟩⟩
  have hk := viewLengthOf_kept hv ha
  rw [h₁, h₂, viewObj_length oneBits_safe (by decide), viewObj_length two (by decide)] at hk
  cases hk

/-! ## Alloc -/

/-- **Alloc**: the array allocated in a well-formed heap is fresh against
it, has length 0, and is apart, at the heap after the allocation, from every
value whose store is a store of the entry heap. -/
theorem alloc_post {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) :
    FreshAt h.length (allocated h) ∧
      HeapKnowledge.lengthOf (h ++ [.arr []] ++ [.nul]) (allocated h) = some 0 ∧
      ∀ (u : Val) (sy : Nat) (ys : List (Option Nat)), storeOf u = some sy → h[sy]? = some (.arr ys) →
        HeapKnowledge.RegionsApart (h ++ [.arr []] ++ [.nul]) (allocated h) u :=
  let ⟨hf, hl, ha⟩ := TolerantFrames.alloc_post h
  ⟨hf, hl, fun u sy ys hs hy => ha u sy ys hs hy (hok.elementsBelow hy)⟩

/-- **The allocation keeps the heap well-formed.** The rule gives the store
slot the role of an array store and the identity its own, with contracts
`c` and `cid` that survive allocation and admit the empty store and `null`;
the allocated array's references are valid in the extended world. -/
theorem alloc_wellformed {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) (hadm : WorldAdm W)
    {c cid : Ctr n} (hc : CtrAdm c) (hcid : CtrAdm cid)
    (hcv : ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) (.arr []))
    (hiv : ∀ (j : Nat) (hj : j < n), cid j hj (trunc j (Nat.le_of_lt hj) W) .nul) :
    HeapOk n (appendWs W (objectEntries [.store .array] [c] cid)) (h ++ [.arr []] ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries [.store .array] [c] cid)) (allocated h) := by
  have hlen : h.length = (entries W).length := by simpa using hok.1.1
  obtain ⟨hsh, href⟩ := arrayObject_shaped (ls := []) c cid hlen hok.2 (fun _ hr => by simp [refs, storeRefs] at hr)
  refine ⟨⟨?_, hsh⟩, href⟩
  rw [List.append_assoc]
  refine HeapMeets_appendWs hok.1 hadm (fun e he => ?_) rfl (fun i d v hd hv => ?_)
  · simp only [objectEntries, List.nil_append, List.zip_cons_cons, List.zip_nil_right,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hc
    · exact hcid
  · match i with
    | 0 => simp [objectEntries] at hd hv; subst hd hv; exact hcv
    | 1 => simp [objectEntries] at hd hv; subst hd hv; exact hiv
    | i + 2 => simp [objectEntries] at hd

end Verification.Kinds
