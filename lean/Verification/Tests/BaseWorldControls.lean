import Verification.Source.Claims.PassUnitCross

/-! The outside contracts (`OutsideContracts`, `KindMet`, `Realizes`) state
an outside slot's value at every budget in every world above a base world
(`Above`). A slot of a record type, as an import's object, a host object or
a module cell is: no value meets the type in every world, the empty one
included (`recT_not_every_world`); a value meets it in every world above a
base world holding its field's location (`recT_above`), so the contract's
premise is satisfiable for such a slot. -/
namespace Verification.Tests.BaseWorldControls
open Verification Verification.SourceClaimJson.PassUnit

/-- The empty world of a level. -/
def emptyW (k : Nat) : WorldT k := ofEntries []

theorem lookup_emptyW (k l : Nat) : lookup (emptyW k) l = none := by
  simp [lookup, toList, emptyW]

/-- No value meets a record type with a field in the empty world. -/
theorem recT_emptyW {fs : Fields} {f : PropKey} {s : StorageRole} {T : Fam} (hm : (f, s, T) ∈ fs)
    (k : Nat) (v : Val) : ¬ recT fs k (emptyW k) v := by
  rintro ⟨flds, oid, -, -, h⟩
  obtain ⟨l, c, -, hl, -⟩ := h f s T hm
  rw [lookup_emptyW] at hl; cases hl

/-- **No value meets a record type with a field in every world** (proved). -/
theorem recT_not_every_world {fs : Fields} {f : PropKey} {s : StorageRole} {T : Fam} (hm : (f, s, T) ∈ fs)
    (k : Nat) : ¬ ∃ v, ∀ W : WorldT k, recT fs k W v :=
  fun ⟨v, h⟩ => recT_emptyW hm k v (h _)

/-- The field the record of these controls names. -/
def key : PropKey := .str "x"

/-- A base world at level `N` holding one field location, of contract
`numT`. -/
def base (N : Nat) : WorldT N := ofEntries [(.field key, fun j _ W v => numT j W v)]

/-- The object whose field `x` is the base world's location `0`. -/
def obj : Val := .objAt [(key, 0)] .absent 0

/-- **A record value meets its type above the base world** (proved): at
every depth `i`, at every budget `j ≤ i`, in every world above the base
world, the object meets `{x: number}`: the outside contract's form at a
slot of that type holds of the constant value `obj`. -/
theorem recT_above (N : Nat) :
    ∀ i : Nat, ∀ j ≤ i, ∀ V : WorldT j, Above (base N) V →
      recT [(key, .field, numT)] j V ((fun _ => obj) i) := by
  intro i j _ V ⟨hjN, hx⟩
  have hl0 : lookup (base N) 0 = some (fun j _ W v => numT j W v) := by
    simp [lookup, toList, base]
  have hr0 : roleAt (base N) 0 = some (.field key) := by
    simp [roleAt, roles, base]
  refine ⟨[(key, 0)], 0, rfl, ?_, ?_⟩
  · intro f s T hm l _ g hg
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, -, -⟩ := hm
    simp only [List.lookup] at hg
    split at hg
    · rename_i h; exact (beq_iff_eq.mp h)
    · cases hg
  · intro f s T hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    refine ⟨0, _, by simp [List.lookup], WExt_lookup hx (lookup_trunc hjN _ 0 _ hl0), ?_, ?_⟩
    · exact ⟨.field key, WExt_roleAt hx (by rw [roleAt_trunc]; exact hr0), key, rfl⟩
    · intro _ _ _ _; exact Iff.rfl

/-- So the premise is inhabited at a record-typed slot, where in every world
it was not. -/
example (N : Nat) : ∃ v : Nat → Val, ∀ i, ∀ j ≤ i, ∀ V : WorldT j, Above (base N) V →
    recT [(key, .field, numT)] j V (v i) :=
  ⟨fun _ => obj, recT_above N⟩

example (k : Nat) : ¬ ∃ v, ∀ W : WorldT k, recT [(key, .field, numT)] k W v :=
  recT_not_every_world (List.mem_singleton.mpr rfl) k

end Verification.Tests.BaseWorldControls
