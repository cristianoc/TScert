import Verification.Source.Claims.CallbackInferencePlan

namespace Verification.SourceClaimJson.CallbackInferencePlan
open CallArguments

private theorem actualStep {h t h' t'} (hs : Step h t h' t') (ok : readActual t = true)
    (values : ∀ (l : Nat) (v : Tm), h[l]? = some v → isVal v = true) :
    h' = h ∧ readActual t' = true := by
  by_cases spread : ∃ a, t = .spread a
  · obtain ⟨a,rfl⟩ := spread
    cases hs with
    | spreadC st => exact Purity.read_step st ok values
  · have read : Purity.readTerm t = true := by cases t <;> simp_all [readActual]
    obtain ⟨heq,next⟩ := Purity.read_step hs read values
    exact ⟨heq, by cases t' <;> simp_all [readActual,Purity.readTerm,isVal]⟩

private theorem argsStep {h args h' args'} (hs : ArgStep h args h' args')
    (ok : args.all readActual = true) (values : ∀ (l : Nat) (v : Tm), h[l]? = some v → isVal v = true) :
    h' = h ∧ args'.all readActual = true := by
  induction hs with
  | head step =>
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨rfl,good⟩ := actualStep step head values
    exact ⟨rfl,Bool.and_eq_true_iff.mpr ⟨good,tail⟩⟩
  | tail _ _ ih =>
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨rfl,good⟩ := ih tail values
    exact ⟨rfl,Bool.and_eq_true_iff.mpr ⟨head,good⟩⟩

/-- Every preparation step of a checked producer call retains the entire
heap and all remaining operand checks, including after a dynamic splice. -/
theorem readCall_prepare {h frame h' next} (hs : Prepare h frame h' next)
    (ok : readCall (.invoke frame.callee frame.recv frame.args) = true)
    (values : ∀ (l : Nat) (v : Tm), h[l]? = some v → isVal v = true) :
    h' = h ∧ readCall (.invoke next.callee next.recv next.args) = true := by
  cases hs with
  | callee st =>
    obtain ⟨⟨f,r⟩,a⟩ := (Bool.and_eq_true_iff.mp ok).imp_left Bool.and_eq_true_iff.mp
    obtain ⟨rfl,f'⟩ := Purity.read_step st f values
    exact ⟨rfl, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨f',r⟩,a⟩⟩
  | recv _ st =>
    obtain ⟨⟨f,r⟩,a⟩ := (Bool.and_eq_true_iff.mp ok).imp_left Bool.and_eq_true_iff.mp
    obtain ⟨rfl,r'⟩ := Purity.read_step st r values
    exact ⟨rfl, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨f,r'⟩,a⟩⟩
  | args _ _ st =>
    obtain ⟨fr,a⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨rfl,a'⟩ := argsStep st a values
    exact ⟨rfl,Bool.and_eq_true_iff.mpr ⟨fr,a'⟩⟩
  | splice _ _ eq _ reads =>
    obtain ⟨fr,a⟩ := Bool.and_eq_true_iff.mp ok
    rw [eq] at a
    simp only [List.all_append,List.all_cons,Bool.and_eq_true] at a
    refine ⟨rfl,Bool.and_eq_true_iff.mpr ⟨fr,?_⟩⟩
    simp only [List.all_append,Bool.and_eq_true]
    refine ⟨⟨a.1,List.all_eq_true.mpr ?_⟩,a.2.2⟩
    intro t ht
    have hv := Purity.readElems_values reads values t ht
    cases t <;> simp_all [isVal,readActual,Purity.readTerm]

theorem read_instantiate {t : Tm} {ρ : Env} {d : Nat}
    (ok : Purity.readTerm t = true) (values : ∀ i, isVal (ρ i) = true) :
    Purity.readTerm (instantiate d ρ t) = true := by
  induction t using Tm.induct generalizing d <;> simp_all [Purity.readTerm,isVal,instantiate]
  case var i =>
    split
    · rfl
    · exact Purity.read_value (values _)

theorem readCall_instantiate {f recv args ρ} (ok : readCall (.invoke f recv args) = true)
    (values : ∀ i, isVal (ρ i) = true) : readCall (instantiate 0 ρ (.invoke f recv args)) = true := by
  simp only [readCall,instantiate,instantiateArgs_eq_map,List.all_map,Bool.and_eq_true] at ok ⊢
  refine ⟨⟨read_instantiate ok.1.1 values,read_instantiate ok.1.2 values⟩,?_⟩
  apply List.all_eq_true.mpr
  intro t ht
  have ha := List.all_eq_true.mp ok.2 t ht
  change readActual (instantiate 0 ρ t) = true
  cases t <;> first | exact read_instantiate ha values | simp_all [readActual,Purity.readTerm,instantiate,isVal]
  case var i =>
    have hv := values i
    cases eq : ρ i <;> simp_all [Purity.readTerm,isVal]
  case objAt fs c oid => cases c <;> rfl

inductive Prepared (h : Heap) : Nat → Frame → Frame → Prop where
  | refl : Prepared h 0 f f
  | next : Prepare h f h mid → Prepared h k mid last → Prepared h (k+1) f last

/-- A completed normal call reaches a dispatch after read-only preparation.
The remaining budget counts only the expression produced by dispatch. -/
theorem readCall_dispatch {k h f recv args after v}
    (run : HeapObservations.Steps k h (.invoke f recv args) after v) (value : isVal v = true)
    (ok : readCall (.invoke f recv args) = true) (heapValues : ∀ (l : Nat) (x : Tm), h[l]? = some x → isVal x = true) :
    ∃ p q frame body, k = p + 1 + q ∧ Prepared h p ⟨f,recv,args⟩ frame ∧ CallArguments.Invoke frame body ∧
      HeapObservations.Steps q h body after v := by
  induction k generalizing h f recv args with
  | zero => cases run; contradiction
  | succ k ih =>
    cases run with
    | next step tail =>
      rcases call_step_iff.mp step with ⟨next,prep,rfl⟩ | ⟨rfl,dispatch⟩
      · obtain ⟨rfl,ready⟩ := readCall_prepare prep ok heapValues
        obtain ⟨p,q,frame,body,count,trace,inv,rest⟩ := ih tail ready heapValues
        exact ⟨p+1,q,frame,body,by omega,.next prep trace,inv,rest⟩
      · exact ⟨0,k,_,_,by omega,.refl,dispatch,tail⟩

end Verification.SourceClaimJson.CallbackInferencePlan
