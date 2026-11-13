import Verification.Types.StoreMapsCheck

/-! # Store maps and the built-ins

Every arrow, method and constructor signature of a graph reads the graph's
exception family (`excOf`: `builtinExc` at the built-in values), which is the
built-ins' array invariant where the graph states built-ins and the store
being a list where it states none. A store map relates the two graphs'
built-ins, so:

- along a store map the exception families are equal (`StoreMap.excOf_eq`);
- no store map relates a graph stating no built-ins to one stating them
  (`StoreMap.builtins_isSome`), and the check refuses such a pair
  (`matchStores_none_of_builtins`);
- where both graphs state built-ins (a published module's store states the
  standard ones, as the importer's does), an accepted check gives a store
  map relating the two tables and the two exception families
  (`matchStores_sound_builtins`).

docs/SINGLE-PASS-THEOREM.md, section 7, "Built-ins in one graph
only". -/

namespace Verification.StoreMaps
open PositiveGraphs PositiveNormalization PositiveRules

variable {ι κ : Type}

namespace StoreMap
variable {G : NormalGraph ι} {H : NormalGraph κ}

/-- **The exception families agree along a store map** (proved). -/
theorem excOf_eq (m : StoreMap G H) : excOf H = excOf G :=
  m.builtinExc_eq fun S T hS hT => by
    show mixedValues H _ T = mixedValues G _ S
    unfold mixedValues
    rw [setSem_ext hT]
    exact m.setSem_map fun j hj => m.denote_eq m.related_empty (hS j hj)

/-- **A store map relates built-ins to built-ins** (proved): both graphs
state them or neither does. -/
theorem builtins_isSome (m : StoreMap G H) : G.builtins.isSome = H.builtins.isSome := by
  have hb := m.builtins
  cases hg : G.builtins <;> cases hh : H.builtins <;> simp_all [BuiltinsRel]

end StoreMap

variable [DecidableEq ι] [Hashable ι] [DecidableEq κ] [Hashable κ]

/-- **The check refuses built-ins in one graph only** (proved). -/
theorem matchStores_none_of_builtins [Inhabited κ] {G : NormalGraph ι} {H : NormalGraph κ}
    {canon : List κ → List κ} {fuel : Nat} {I : List ι} {A : List κ}
    (h : G.builtins.isSome ≠ H.builtins.isSome) : matchStores G H canon fuel I A = none := by
  unfold matchStores
  have hb : ∀ φ inD, builtinsOkB G H φ inD = false := by
    intro φ inD
    unfold builtinsOkB
    cases hg : G.builtins <;> cases hh : H.builtins <;> simp_all
  simp [checkMap, hb]

/-- **The store-map check where both graphs state built-ins** (proved): an
accepted check gives a store map whose region holds the root `I` and the
built-ins' types, renaming `I` to a union of `A`'s members, relating the two
built-in tables (the same keys, prototype and `unknown` types of the
renamed labels) and the two exception families. -/
theorem matchStores_sound_builtins [Inhabited κ] {G : NormalGraph ι} {H : NormalGraph κ}
    {canon : List κ → List κ} (hcanon : ∀ S x, x ∈ canon S ↔ x ∈ S) (henv : ∀ p q, H.env.1 q = G.env.1 p)
    {fuel : Nat} {I : List ι} {A : List κ} {mp : Std.HashMap ι κ} {r : ArrayBuiltins ι}
    (hG : G.builtins = some r) (h : matchStores G H canon fuel I A = some mp) :
    ∃ (m : StoreMap G H) (r' : ArrayBuiltins κ), (∀ j ∈ I, m.D j) ∧ (∀ x, x ∈ A ↔ x ∈ I.map m.φ) ∧
      H.builtins = some r' ∧ r'.keys = r.keys ∧ (∀ x, x ∈ r'.proto ↔ x ∈ r.proto.map m.φ) ∧
      (∀ x, x ∈ r'.unknown ↔ x ∈ r.unknown.map m.φ) ∧ (∀ j ∈ r.proto, m.D j) ∧ (∀ j ∈ r.unknown, m.D j) ∧
      excOf H = excOf G := by
  obtain ⟨m, hI, hA⟩ := matchStores_sound hcanon henv h
  have hb := m.builtins
  rw [hG] at hb
  cases hh : H.builtins with
  | none => rw [hh] at hb; exact absurd hb (by simp [BuiltinsRel])
  | some r' =>
    rw [hh] at hb
    obtain ⟨hk, hp, hu⟩ := hb
    obtain ⟨hpD, huD⟩ := m.builtinsIn r hG
    exact ⟨m, r', hI, hA, rfl, hk, hp, hu, hpD, huD, m.excOf_eq⟩

end Verification.StoreMaps
