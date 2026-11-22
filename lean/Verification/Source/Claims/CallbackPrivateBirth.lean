import Verification.Source.Claims.CallbackPrivateFlow
import Verification.Source.Claims.CallbackAllocationSpines

namespace Verification.SourceClaimJson.CallbackInferencePlan
open PointClaims CallbackOrigins ControlFlow CertificateProducer GraphCode TolerantFrames TolerantFrames.ReadOnly Footprints HeapObservations

/-- The heap and current expression have valid references at a concrete
expression reduction. -/
def TypedMoment (h : Heap) (t : Tm) := ∃ s : IndexedHeap, s.h = h ∧ RefsOk s.W t

def BirthStage (h : Heap) (t : Tm) : Prop :=
  allocates t = true ∨ (isVal t = true ∧ ∀ key l, (fieldsOf t).lookup key = some l → hiddenInHeap h l) ∨
    ∃ v, Raises t v

theorem birthStep {h h' t t'} (state : BirthStage h t) (typed : TypedMoment h t) (step : Step h t h' t') :
    BirthStage h' t' := by
  rcases state with alloc | ⟨val,_⟩ | ⟨v,raised⟩
  · cases t <;> simp only [allocates,Bool.false_eq_true] at alloc
    case letE =>
      cases step with
      | letC => exact .inl alloc
      | letV => exact .inl (substAlloc alloc _ _)
    case makeAt =>
      cases step with
      | makeArg => exact .inl rfl
      | makeFields vals len =>
        obtain ⟨s,rfl,vr⟩ := typed
        exact .inr (.inl ⟨rfl,fun key l lookup => makeFields_hidden vr (slots_range _ _ lookup).1⟩)
    case merge => cases step <;> exact .inl rfl
    case makeKey => cases step <;> exact .inl rfl
    case arrLit =>
      cases step <;> first | exact .inl rfl | exact .inr (.inl ⟨rfl,by simp [fieldsOf]⟩) |
        exact .inr (.inr ⟨_,.throwV rfl rfl⟩)
  · exact (value_no_step val step).elim
  · exact (raises_no_step raised step).elim

theorem birth_heap_hidden {h h' ρ expr v n} (alloc : allocates expr = true) (value : isVal v = true)
    (run : Steps n h (instantiate 0 ρ expr) h' v)
    (typed : ∀ i hi t, i < n → Steps i h (instantiate 0 ρ expr) hi t → TypedMoment hi t)
    {key l} (field : (fieldsOf v).lookup key = some l) : hiddenInHeap h' l := by
  have keep {k h t h' t'} (r : Steps k h t h' t') (start : BirthStage h t)
      (valid : ∀ i hi u, i < k → Steps i h t hi u → TypedMoment hi u) : BirthStage h' t' := by
    induction r with
    | refl => exact start
    | next tr _ ih =>
      exact ih (birthStep start (valid 0 _ _ (by omega) .refl) tr)
        (fun i hi u bound pre => valid (i+1) hi u (by omega) (.next tr pre))
  rcases keep run (.inl (instantiateAlloc alloc ρ 0)) typed with impossible | ⟨_,result⟩ | ⟨_,raised⟩
  · cases v <;> simp_all [allocates,isVal]
  · exact result key l field
  · exact Bool.noConfusion (value.symm.trans (raises_not_val raised))

/-- The concrete birth supplies the starting invariant at every normal
successor. Multiple executions of the same site are permitted. -/
theorem birth_privateAt_of_hidden {P : Program} {table site node ρ before after v k target key field}
    (checked : checkPrivateSite P.toArray table site = true)
    (atSite : P[site]? = some node) (ready : privateReady P.toArray table site = true)
    (allocation : allocates node.expression = true)
    (run : Steps k before (instantiate 0 ρ node.expression) after v)
    (value : isVal v = true) (lookup : (fieldsOf v).lookup key = some field)
    (start : IndexedHeap) (startHeap : start.h = before) (refs : RootsOk start.W ρ)
    (values : ∀ i < (table.at site).size, isVal (ρ i) = true)
    (hidden : hiddenInHeap after field)
    (chosen : target ∈ successors node.continuation) :
    PrivateAt P table site field target.label
      (mapEnv target.mapping (if pushes node.continuation then push v ρ else ρ)) after := by
  obtain ⟨fresh,old⟩ := allocationField_range allocation run value lookup
  have slots : PrivateSlots site field (table.at site) ρ :=
    ⟨values, fun i _ leaf => (Nat.not_lt_of_ge (startHeap ▸ fresh : start.h.length ≤ field))
      (Leaves.lt (s := start) (RefsOk.refsOkN (refs i)) leaf)⟩
  have negative : resultClean site site (table.at site) node.expression = false := by
    cases hx : node.expression <;> first | rfl | simp [resultClean] | simp [hx,allocates] at allocation
    simp [hx,allocates] at allocation
  have edge := List.all_eq_true.mp (checkSiteAt checked atSite ready).2.1 target chosen
  obtain ⟨active,newSlots⟩ := mappedPrivate edge slots value (by simp [negative])
  exact ⟨active,old,hidden,newSlots⟩

end Verification.SourceClaimJson.CallbackInferencePlan
