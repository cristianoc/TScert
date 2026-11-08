import Verification.Semantics.IndexFacts

/-! Arithmetic obligations of the audited string contracts. Native execution
is supplied by the host contract, as for `codePointAt`; these lemmas establish
its code-unit and substring bounds in the model's UTF-16 representation. -/
namespace Verification.StringPostconditions
open HeapKnowledge

/-- Every unit in the model's UTF-16 expansion is a 16-bit integer. -/
theorem unit_bound {s : String} {u : Nat} (hu : u ∈ utf16Units s) : u ≤ 65535 := by
  obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hu
  simp only at hc
  split at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst u
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    have hv := c.valid
    simp only [UInt32.isValidChar, Nat.isValidChar] at hv
    rcases hc with hc | hc <;> omega

/-- A bounded code-unit result is represented by an exact safe integer. -/
theorem code_unit_safe {s : String} {u : Nat} (hu : u ∈ utf16Units s) :
    SafeIntegers.SafeInt (bitsOfNat u) (u : Int) ∧ 0 ≤ (u : Int) ∧ (u : Int) ≤ 65535 := by
  have hb := unit_bound hu
  refine ⟨⟨?_, .inl ⟨?_, ?_⟩⟩, by omega, by omega⟩
  · omega
  · omega
  · simp

/-- The UTF-16 subsequence selected by bounded slice has exactly b-a units. -/
theorem slice_length {s : String} {a b : Nat} (hab : a ≤ b)
    (hb : b ≤ (utf16Units s).length) :
    (((utf16Units s).drop a).take (b - a)).length = b - a := by
  simp only [List.length_take, List.length_drop]
  omega

/-- A failed search or a matching substring's start is in the inclusive range.
A nonempty needle makes the upper bound strict, including failure at length zero. -/
theorem search_bounds {len needle : Nat} {r : Int}
    (hr : r = -1 ∨ ∃ p : Nat, r = p ∧ p + needle ≤ len) :
    -1 ≤ r ∧ r ≤ len ∧ (0 < needle → r < len) := by
  rcases hr with rfl | ⟨p, rfl, hp⟩ <;> omega

end Verification.StringPostconditions
