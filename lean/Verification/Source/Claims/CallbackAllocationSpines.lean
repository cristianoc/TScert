import Verification.Source.Claims.CallbackOrigins

namespace Verification.SourceClaimJson.CallbackOrigins
open Footprints HeapObservations

theorem slots_range {key : PropKey} {l : Nat} : ∀ (ns : List PropKey) (base : Nat),
    (Verification.slots base ns).lookup key = some l → base ≤ l ∧ l < base + ns.length := by
  intro ns
  induction ns with
  | nil => simp [Verification.slots]
  | cons a tail ih =>
    intro base found
    simp only [Verification.slots,List.lookup] at found
    split at found
    · cases found
      simp <;> omega
    · obtain ⟨lo,hi⟩ := ih _ found
      simp <;> omega

theorem substAlloc {t : Tm} (h : allocates t = true) (i : Nat) (a : Tm) :
    allocates (subst i a t) = true := by
  cases t <;> try first | contradiction | rfl
  case letE t u => exact substAlloc (t := u) h (i+1) a
  case makeAt c ns as => cases c <;> rfl
termination_by sizeOf t

theorem instantiateAlloc {t : Tm} (h : allocates t = true) (ρ : Env) (i : Nat) :
    allocates (instantiate i ρ t) = true := by
  cases t <;> try first | contradiction | rfl
  case letE t u => exact instantiateAlloc (t := u) h ρ (i+1)
  case makeAt c ns as => cases c <;> rfl
termination_by sizeOf t

private def AllocStage (b : Nat) (h : Heap) (u : Tm) : Prop :=
  allocates u = true ∨ (isVal u = true ∧ ∀ key l, (fieldsOf u).lookup key = some l → b ≤ l ∧ l < h.length) ∨ ∃ v, Raises u v

private theorem allocStage_step {b h u h' u'} (below : b ≤ h.length) (state : AllocStage b h u)
    (tr : Step h u h' u') : AllocStage b h' u' := by
  rcases state with ha | ⟨val,_⟩ | ⟨v,ex⟩
  · cases u <;> simp only [allocates, Bool.false_eq_true] at ha
    case letE =>
      cases tr with
      | letC => exact .inl ha
      | letV => exact .inl (substAlloc ha _ _)
    case makeAt =>
      cases tr with
      | makeArg => exact .inl rfl
      | makeFields eq len =>
        refine .inr (.inl ⟨rfl,fun key l hl => ?_⟩)
        obtain ⟨lo,hi⟩ := slots_range _ _ hl
        simp only [List.length_append,List.length_cons,List.length_nil] at *
        omega
    case merge => cases tr <;> exact .inl rfl
    case makeKey => cases tr <;> exact .inl rfl
    case arrLit =>
      cases tr <;> first | exact .inl rfl | exact .inr (.inl ⟨rfl,by simp [fieldsOf]⟩) |
        exact .inr (.inr ⟨_,.throwV rfl rfl⟩)
  · exact (value_no_step val tr).elim
  · exact (raises_no_step ex tr).elim

theorem allocationField_range {node : Tm} {ρ j before after v} (alloc : allocates node = true)
    (steps : Steps j before (instantiate 0 ρ node) after v) (value : isVal v = true) {l : Nat}
    {key : PropKey} (field : (fieldsOf v).lookup key = some l) : before.length ≤ l ∧ l < after.length := by
  have keep {j h a h' c} (r : Steps j h a h' c) :
      before.length ≤ h.length → AllocStage before.length h a → AllocStage before.length h' c := by
    induction r with
    | refl => exact fun _ ha => ha
    | next tr _ ih => exact fun b ha => ih (Nat.le_trans b (step_length_le tr)) (allocStage_step b ha tr)
  rcases keep steps (Nat.le_refl _) (.inl (instantiateAlloc alloc ρ 0)) with shape | ⟨_,range⟩ | ⟨_,raised⟩
  · cases v <;> simp_all [isVal,allocates]
  · exact range key l field
  · exact (Bool.noConfusion (value.symm.trans (raises_not_val raised)))

theorem allocationSpine_range {node : Tm} {ρ j before after v} (alloc : allocates node = true)
    (steps : Steps j before (instantiate 0 ρ node) after v) (value : isVal v = true) {l : Nat}
    (spine : spineOf v = some l) : before.length ≤ l ∧ l < after.length :=
  allocationField_range alloc steps value spine

end Verification.SourceClaimJson.CallbackOrigins
