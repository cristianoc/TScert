import Verification.Semantics.IndexFacts

/-! # Unified length reading

The paper's length operator chooses the shared array, typed-array or string
reader from the runtime value. It reads the heap and no world. The choice is
made before reading: a malformed view never falls back to an array reader.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge

/-- Runtime classification for the paper's single length operator. -/
def lengthKind : Val → Option HeapKnowledge.Term.Kind
  | .objAt _ .absent _ => some .length
  | .objAt _ (.view ..) _ => some .view
  | .str _ => some .strLength
  | _ => none

/-- The paper’s partial length of an array, typed array or UTF-16 string. -/
def lengthReading (h : Heap) (v : Val) : Option Int :=
  (lengthKind v).bind fun k => kindValue h k v

theorem lengthKind_cases {v : Val} {k : HeapKnowledge.Term.Kind}
    (hk : lengthKind v = some k) : k = .length ∨ k = .view ∨ k = .strLength := by
  cases v <;> simp only [lengthKind] at hk <;> try cases hk
  case objAt fs code oid => cases code <;> simp only at hk <;> cases hk <;> simp
  case str => simp

/-- Extensionality uses the existing shared meanings, including undefinedness. -/
theorem lengthReading_congr {h h' : Heap} {v : Val}
    (he : ∀ k, kindValue h k v = kindValue h' k v) :
    lengthReading h v = lengthReading h' v := by
  unfold lengthReading
  cases lengthKind v with
  | none => rfl
  | some k => exact he k

/-- Successful readings survive heap extension without changing their value. -/
theorem lengthReading_extend {h : Heap} (vs : List Val) {v : Val} {n : Int}
    (he : lengthReading h v = some n) : lengthReading (h ++ vs) v = some n := by
  simp only [lengthReading, Option.bind_eq_some_iff] at he ⊢
  obtain ⟨k, hk, he⟩ := he
  exact ⟨k, hk, kindValue_extend vs he⟩

/-- Every defined unified length is between zero and the largest safe integer. -/
theorem lengthReading_range {h : Heap} {v : Val} {n : Int}
    (he : lengthReading h v = some n) : 0 ≤ n ∧ n ≤ 2 ^ 53 - 1 := by
  simp only [lengthReading, Option.bind_eq_some_iff] at he
  obtain ⟨k, hk, he⟩ := he
  rcases lengthKind_cases hk with rfl | rfl | rfl
  · obtain ⟨_, es, _, _, rfl, hm⟩ := lengthOf_spine he
    simp only [maxArrayLength] at hm
    exact ⟨by omega, by omega⟩
  · exact viewLengthOf_range he
  · exact strLengthOf_range he

/-- Category-qualified equivalence retains partial definedness in both directions. -/
theorem lengthReading_array (h : Heap) (fs : List (PropKey × Nat)) (oid : Nat) :
    lengthReading h (.objAt fs .absent oid) = lengthOf h (.objAt fs .absent oid) := rfl

theorem lengthReading_view (h : Heap) (fs : List (PropKey × Nat)) (oid st : Nat)
    (fmt : ViewFormat) (n : Nat) :
    lengthReading h (.viewAt fs oid st fmt n) = viewLengthOf (.viewAt fs oid st fmt n) := rfl

theorem lengthReading_string (h : Heap) (s : String) :
    lengthReading h (.str s) = strLengthOf (.str s) := rfl

end Verification.Paper.TolerantFrames
