import Verification.Programs.HeapExpressionRules
import Verification.Semantics.FootprintStability

/-! # Typed fields from a point's types

A slot's **typed fields** are the fields every alternative of its type
names as an invariant field or a readonly view, an array's store under
either: each has a location with a world contract. This is the proof role of today's allocation separation, and what
`before` stamps need: at a new mark equal to the heap's length, every typed
field of every slot lies below it. Nothing uses this module yet. -/
namespace Verification.Footprints
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization HeapExpressionRules

/-- A clause's readonly named views. -/
def clauseViewOperand : PositiveNormalization.Clause α → Option (List (PropKey × α))
  | .refs _ _ vs .. | .dict _ _ vs .. => some vs
  | _ => none

/-- Whether a clause gives `fld` a location with a world contract: as an
invariant field, or as a readonly view other than `length`, which arrays
answer from their store. -/
def clauseTyped (c : PositiveNormalization.Clause α) (fld : PropKey) : Bool :=
  (match clauseBagOperand c with
    | some B => B.any fun p => decide (p.1 = fld)
    | none => false) ||
  (fld != lengthKey && match clauseViewOperand c with
    | some vs => vs.any fun p => decide (p.1 = fld)
    | none => false)

/-- Whether every alternative gives `fld` a located field, an invariant field
in one and a view in another included. -/
def typedOperand (cs : List (PositiveNormalization.Clause α)) (fld : PropKey) : Bool :=
  !cs.isEmpty && cs.all (clauseTyped · fld)

/-- The located field of a value bound by an invariant bag. -/
private theorem bag_contract {B : List (PropKey × Fam)} {fld El n W v}
    (hmem : (fld, El) ∈ B) (hbag : bagT B n W v) :
    ∀ l, (fieldsOf v).lookup fld = some l → ∃ c, lookup W l = some c := by
  intro l hl
  obtain ⟨flds0, code0, oid0, hl0, _, hrec⟩ := hbag
  obtain ⟨flds1, l1, c1, oid', hproj, hfd1, hlookup, _⟩ := recT_at hmem hrec
  rw [hl0] at hl
  cases hproj
  simp only [fieldsOf] at hl
  rw [hl] at hfd1
  cases hfd1
  exact ⟨c1, hlookup⟩

theorem typedOperand_contract [DecidableEq ι] {G : NormalGraph ι} {Ref fld n W v}
    (hr : typedOperand (expand G Ref) fld = true) (hv : meaning G Ref n W v) :
    ∀ l, (fieldsOf v).lookup fld = some l → ∃ c, lookup W l = some c := by
  simp only [typedOperand, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hr
  obtain ⟨hne, hall⟩ := hr
  have hp : G.plainTy Ref = true := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    exact plain_of_mem_expand (c := c) hc
  obtain ⟨c, hm, hc, -⟩ := (expand_sem G Ref hp n W v).mp hv
  have hb := hall c hm
  simp only [clauseTyped, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
  rcases hb with hb | ⟨hlen, hb⟩
  · cases c <;> simp only [clauseBagOperand] at hb
    all_goals try contradiction
    all_goals
      obtain ⟨⟨g, El⟩, hmem, hg⟩ := List.any_eq_true.mp hb
      simp only [decide_eq_true_eq] at hg
      subst hg
    · exact bag_contract (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) (recT_bag hc.1.1)
    · exact bag_contract (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) hc.1.1.1
  · cases c <;> simp only [clauseViewOperand] at hb
    all_goals try contradiction
    all_goals
      obtain ⟨⟨g, El⟩, hmem, hg⟩ := List.any_eq_true.mp hb
      simp only [decide_eq_true_eq] at hg
      subst hg
      intro l hl
      rcases hc.2.1 _ _ (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) with hview | ⟨hl', -⟩
      · obtain ⟨flds, l', c, oid, hv, hl', hw, -⟩ := hview _ _ (List.mem_singleton_self _)
        rw [hv] at hl
        simp only [fieldsOf] at hl
        rw [hl] at hl'
        cases hl'
        exact ⟨c, hw⟩
      · exact absurd hl' hlen

/-- The keys of slot `s`'s typed fields: those every alternative of its type
gives a located field, as an invariant field or a readonly view. The
candidates are the first alternative's. -/
@[nospecialize] def typedFields [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (s : Nat) : List PropKey :=
  match Γ[s]? with
  | some A => match (expand G A).head? with
    | some c => ((((clauseBagOperand c).getD []) ++ (clauseViewOperand c).getD []).map Prod.fst).eraseDups.filter
        (typedOperand (expand G A))
    | none => []
  | none => []

theorem mem_typedFields [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {s k}
    (hk : k ∈ typedFields G Γ s) : ∃ A, Γ[s]? = some A ∧ typedOperand (expand G A) k = true := by
  unfold typedFields at hk
  split at hk
  · rename_i A hA
    split at hk
    · exact ⟨A, hA, (List.mem_filter.mp hk).2⟩
    · simp at hk
  · simp at hk

/-- **A typed field has a world contract.** -/
theorem typedField_contract [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W}
    (he : EnvOk G Γ ρ n W) {s k l} (hk : k ∈ typedFields G Γ s)
    (hl : (fieldsOf (ρ s)).lookup k = some l) : ∃ c, lookup W l = some c := by
  obtain ⟨A, hA, ht⟩ := mem_typedFields hk
  exact typedOperand_contract ht (he.2 s A hA) l hl

/-- At a new mark equal to the heap's length, every slot's typed fields lie
below it. -/
theorem before_typedFields [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W h}
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h) {μ : Nat → Nat} {m : Nat} (hm : μ m = h.length)
    (y : Nat) : ∀ k ∈ typedFields G Γ y, ∀ l, (fieldsOf (ρ y)).lookup k = some l → l < μ m :=
  before_of_typed hh hm fun _ hk _ hl => typedField_contract he hk hl

end Verification.Footprints
