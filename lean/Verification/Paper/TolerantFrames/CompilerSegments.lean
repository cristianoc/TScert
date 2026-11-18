import Verification.Paper.TolerantFrames.CommandCompiler

/-! # Finite offset lookup preservation

A segment records concrete list containment and lookup equality, not an
execution or safety summary. Concatenation and nesting generate its evidence.
-/
namespace Verification.Paper.TolerantFrames.Compiler

structure Segment {α : Type} (whole : List α) (offset : Nat) (part : List α) : Prop where
  bounds : offset + part.length ≤ whole.length
  lookup : ∀ i, i < part.length → whole[offset + i]? = part[i]?

theorem Segment.refl (xs : List α) : Segment xs 0 xs := by
  exact ⟨by simp, fun _ _ => by simp⟩

theorem Segment.left (a b : List α) : Segment (a ++ b) 0 a := by
  refine ⟨by simp, ?_⟩
  intro i hi
  simpa using (List.getElem?_append_left (l₂ := b) hi)

theorem Segment.right (a b : List α) : Segment (a ++ b) a.length b := by
  refine ⟨by simp, ?_⟩
  intro i _
  rw [List.getElem?_append_right (by omega)]
  simp

theorem Segment.trans {whole middle part : List α} {outer inner : Nat}
    (hm : Segment whole outer middle) (hp : Segment middle inner part) :
    Segment whole (outer + inner) part := by
  refine ⟨by have := hm.bounds; have := hp.bounds; omega, ?_⟩
  intro i hi
  have hmid : inner + i < middle.length := by have := hp.bounds; omega
  rw [Nat.add_assoc, hm.lookup _ hmid, hp.lookup i hi]

theorem Segment.head {whole : List α} {offset : Nat} {first : α} {rest : List α}
    (segment : Segment whole offset (first :: rest)) : whole[offset]? = some first := by
  simpa using segment.lookup 0 (by simp)

theorem Segment.tail {whole : List α} {offset : Nat} {first : α} {rest : List α}
    (segment : Segment whole offset (first :: rest)) : Segment whole (offset + 1) rest := by
  exact segment.trans (Segment.right [first] rest)

theorem Segment.block_entry_site {whole bound c stack next broken returned thrown offset}
    (segment : Segment whole offset (block bound c stack next broken returned thrown offset)) :
    (whole[offset]?).map AnnotatedNode.site = some (frontSite c stack) := by
  have present : 0 < (block bound c stack next broken returned thrown offset).length := by
    rw [block_length]; exact codeSize_pos c
  have entry := congrArg (Option.map AnnotatedNode.site) (segment.lookup 0 present)
  simpa only [Nat.add_zero] using entry.trans (block_entry bound c stack next broken returned thrown offset)

end Verification.Paper.TolerantFrames.Compiler
