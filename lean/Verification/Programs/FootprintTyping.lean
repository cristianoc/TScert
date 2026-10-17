import Verification.Programs.HeapExpressionRules
import Verification.Semantics.FootprintStability

/-! # Typed fields from a point's types

A slot's **typed fields** are the fields its type names as a record's
(`HeapExpressionRules.contractFields`): each has a location with a world
contract. This is the proof role of today's allocation separation, and what
`before` stamps need: at a new mark equal to the heap's length, every typed
field of every slot lies below it. Nothing uses this module yet. -/
namespace Verification.Footprints
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization HeapExpressionRules

/-- The keys of slot `s`'s typed fields. -/
@[nospecialize] def typedFields [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (s : Nat) : List PropKey :=
  (contractFields G Γ).filterMap fun p => if p.1 = s then some p.2 else none

theorem mem_typedFields [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {s k}
    (hk : k ∈ typedFields G Γ s) : (s, k) ∈ contractFields G Γ := by
  obtain ⟨⟨t, f⟩, hm, he⟩ := List.mem_filterMap.mp hk
  simp only at he
  split at he
  · rename_i ht; cases he; subst ht; exact hm
  · cases he

/-- **A typed field has a world contract.** -/
theorem typedField_contract [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W}
    (he : EnvOk G Γ ρ n W) {s k l} (hk : k ∈ typedFields G Γ s)
    (hl : (fieldsOf (ρ s)).lookup k = some l) : ∃ c, lookup W l = some c := by
  obtain ⟨Ref, hidx, hfo⟩ := contractFields_mem (mem_typedFields hk)
  obtain ⟨B, El, hmem, hbag⟩ := fieldOperand_sound hfo (he.2 s Ref hidx)
  obtain ⟨flds0, code0, oid0, hl0, _, hrec⟩ := hbag
  obtain ⟨flds1, l1, c1, oid', hproj, hfd1, hlookup, _⟩ :=
    recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) hrec
  rw [hl0] at hl
  cases hproj
  simp only [fieldsOf] at hl
  rw [hl] at hfd1
  cases hfd1
  exact ⟨c1, hlookup⟩

/-- At a new mark equal to the heap's length, every slot's typed fields lie
below it. -/
theorem before_typedFields [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W h}
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h) {μ : Nat → Nat} {m : Nat} (hm : μ m = h.length)
    (y : Nat) : ∀ k ∈ typedFields G Γ y, ∀ l, (fieldsOf (ρ y)).lookup k = some l → l < μ m :=
  before_of_typed hh hm fun _ hk _ hl => typedField_contract he hk hl

end Verification.Footprints
