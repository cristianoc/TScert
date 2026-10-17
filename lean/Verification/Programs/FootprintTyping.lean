import Verification.Programs.HeapExpressionRules
import Verification.Semantics.FootprintStability

/-! # Typed fields from a point's types

A slot's **typed fields** are the fields its type names as a record's
invariant fields (`HeapExpressionRules.contractFields`) or readonly views
(`viewFields`), an array's store under either: each has a location with a
world contract. This is the proof role of today's allocation separation, and what
`before` stamps need: at a new mark equal to the heap's length, every typed
field of every slot lies below it. Nothing uses this module yet. -/
namespace Verification.Footprints
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization HeapExpressionRules

/-- A clause's readonly named views. -/
def clauseViewOperand : PositiveNormalization.Clause α → Option (List (PropKey × α))
  | .refs _ _ vs .. | .dict _ _ vs .. => some vs
  | _ => none

/-- Whether every alternative is an object with the readonly view `fld`,
other than `length`, which arrays answer from their store: a view, like an
invariant field, is a location of the object with a world contract. -/
def viewOperand (cs : List (PositiveNormalization.Clause α)) (fld : PropKey) : Bool :=
  !cs.isEmpty && fld != lengthKey && cs.all fun c => match clauseViewOperand c with
    | some vs => vs.any fun p => decide (p.1 = fld)
    | none => false

theorem viewOperand_contract [DecidableEq ι] {G : NormalGraph ι} {Ref fld n W v}
    (hr : viewOperand (expand G Ref) fld = true) (hv : meaning G Ref n W v) :
    ∃ flds l c oid, v = .objAt flds .absent oid ∧ flds.lookup fld = some l ∧ lookup W l = some c := by
  simp only [viewOperand, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, bne_iff_ne, ne_eq] at hr
  obtain ⟨⟨hne, hlen⟩, hall⟩ := hr
  have hp : G.plainTy Ref = true := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    exact plain_of_mem_expand (c := c) hc
  obtain ⟨c, hm, hc, -⟩ := (expand_sem G Ref hp n W v).mp hv
  have hb := hall c hm
  cases c <;> simp only [clauseViewOperand] at hb
  all_goals try contradiction
  all_goals
    obtain ⟨⟨g, El⟩, hmem, hg⟩ := List.any_eq_true.mp hb
    simp only [decide_eq_true_eq] at hg
    subst hg
    rcases hc.2.1 _ _ (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) with hview | ⟨hl, -⟩
    · obtain ⟨flds, l, c, oid, hv, hl, hw, -⟩ := hview _ _ (List.mem_singleton_self _)
      exact ⟨flds, l, c, oid, hv, hl, hw⟩
    · exact absurd hl hlen

/-- The readonly views of every slot whose type names them in every
alternative, as `contractFields` lists invariant fields. -/
@[nospecialize] def viewFields [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) : List (Nat × PropKey) :=
  Γ.zipIdx.flatMap fun (A, s) => match (expand G A).head? >>= clauseViewOperand with
    | some vs => (vs.map Prod.fst).eraseDups.filterMap fun f =>
        if viewOperand (expand G A) f then some (s, f) else none
    | none => []

theorem viewFields_mem [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {s f}
    (hm : (s, f) ∈ viewFields G Γ) : ∃ Ref, Γ[s]? = some Ref ∧ viewOperand (expand G Ref) f = true := by
  obtain ⟨⟨A, s'⟩, hA, hsel⟩ := List.mem_flatMap.mp hm
  simp only at hsel
  split at hsel
  · obtain ⟨g, _, hg⟩ := List.mem_filterMap.mp hsel
    split at hg
    · rename_i hf
      cases hg
      exact ⟨A, List.mem_zipIdx_iff_getElem?.mp hA, hf⟩
    · cases hg
  · simp at hsel

/-- The keys of slot `s`'s typed fields: its invariant fields and its
readonly views, an array's store under either. -/
@[nospecialize] def typedFields [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (s : Nat) : List PropKey :=
  (contractFields G Γ ++ viewFields G Γ).filterMap fun p => if p.1 = s then some p.2 else none

theorem mem_typedFields [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {s k}
    (hk : k ∈ typedFields G Γ s) : (s, k) ∈ contractFields G Γ ∨ (s, k) ∈ viewFields G Γ := by
  obtain ⟨⟨t, f⟩, hm, he⟩ := List.mem_filterMap.mp hk
  simp only at he
  split at he
  · rename_i ht; cases he; subst ht; exact List.mem_append.mp hm
  · cases he

/-- **A typed field has a world contract.** -/
theorem typedField_contract [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W}
    (he : EnvOk G Γ ρ n W) {s k l} (hk : k ∈ typedFields G Γ s)
    (hl : (fieldsOf (ρ s)).lookup k = some l) : ∃ c, lookup W l = some c := by
  rcases mem_typedFields hk with hc | hv
  case inr =>
    obtain ⟨Ref, hidx, hvo⟩ := viewFields_mem hv
    obtain ⟨flds, l', c, oid, hρ, hl', hw⟩ := viewOperand_contract hvo (he.2 s Ref hidx)
    rw [hρ] at hl
    simp only [fieldsOf] at hl
    rw [hl] at hl'
    cases hl'
    exact ⟨c, hw⟩
  obtain ⟨Ref, hidx, hfo⟩ := contractFields_mem hc
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
