import Verification.Source.Claims.CallbackCallPreparation
namespace Verification.SourceClaimJson.CallbackInferencePlan
open CallArguments

/-- A named value with only nonspreading read operands before it. -/
inductive Positioned (v : Tm) : Nat → List Tm → Prop where
  | here : isVal v = true → Positioned v 0 (v :: rest)
  | there : Purity.readTerm t = true → Positioned v i rest → Positioned v (i+1) (t :: rest)

private theorem Positioned.argStep {v i args h h' args'} (held : Positioned v i args)
    (step : ArgStep h args h' args') (values : ∀ (l : Nat) (x : Tm), h[l]? = some x → isVal x = true) :
    Positioned v i args' := by
  induction held generalizing h h' args' with
  | here hv =>
    cases step with
    | head s => exact (value_no_step hv s).elim
    | tail => exact .here hv
  | there hr _ ih =>
    cases step with
    | head s => exact .there (Purity.read_step s hr values).2 ‹_›
    | tail _ s => exact .there hr (ih s values)

private theorem Positioned.splice {v i post ls pre vs}
    (held : Positioned v i (pre ++ .spread (.arr ls) :: post)) :
    Positioned v i (pre ++ vs ++ post) := by
  induction pre generalizing i with
  | nil => cases held <;> contradiction
  | cons t pre ih =>
    cases held with
    | here hv => exact .here hv
    | there hr pos => exact .there hr (ih pos)

theorem Positioned.prepared {v i h p f next} (held : Positioned v i f.args)
    (trace : Prepared h p f next) (values : ∀ (l : Nat) (x : Tm), h[l]? = some x → isVal x = true) :
    Positioned v i next.args := by
  induction trace with
  | refl => exact held
  | next step _ ih =>
    apply ih
    cases step with
    | callee | recv => exact held
    | args _ _ st => exact held.argStep st values
    | splice _ _ eq _ _ => exact Positioned.splice (eq ▸ held)

theorem Positioned.lookup {v i args} (held : Positioned v i args) : args[i]? = some v := by
  induction held <;> simp_all

/-- Preparation retains a callee and receiver that were already values. -/
theorem Prepared.keepsCallee {v h p f next} (trace : Prepared h p f next)
    (same : f.callee = v) (value : isVal v = true) : next.callee = v := by
  induction trace with
  | refl => exact same
  | next st _ ih =>
    apply ih
    cases st with
    | callee step => exact (value_no_step (by simpa only [← same] using value) step).elim
    | recv | args | splice => exact same

theorem Prepared.keepsRecv {v h p f next} (trace : Prepared h p f next)
    (same : f.recv = v) (value : isVal v = true) : next.recv = v := by
  induction trace with
  | refl => exact same
  | next st _ ih =>
    apply ih
    cases st with
    | recv _ step => exact (value_no_step (by simpa only [← same] using value) step).elim
    | callee | args | splice => exact same

private theorem actual_read {t} (ok : readActual t = true) (regular : ∀ a, t ≠ .spread a) :
    Purity.readTerm t = true := by cases t <;> simp_all [readActual]

private theorem sourcePosition {args i slot ρ} (named : (positionalPrefix args)[i]? = some (.var slot))
    (ok : args.all readActual = true) (values : ∀ j, isVal (ρ j) = true) :
    Positioned (ρ slot) i (instantiateArgs 0 ρ args) := by
  induction args generalizing i with
  | nil => simp [positionalPrefix] at named
  | cons t ts ih =>
    unfold positionalPrefix at named
    simp only [List.takeWhile] at named
    split at named
    next test =>
      obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
      have hr := actual_read head (fun a eq => by subst t; contradiction)
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at named
        subst t
        simpa only [instantiateArgs,instantiate,Nat.not_lt_zero,ite_false,Nat.sub_zero] using
          (Positioned.here (rest := instantiateArgs 0 ρ ts) (values slot))
      | succ i =>
        exact .there (read_instantiate hr values) (ih (by simpa [positionalPrefix] using named) tail)
    next => simp at named

theorem atCall_actualRoots {slots roots param state fn recv args ρ entry h p n final}
    (resolved : CallbackPreservation.RealizesRoots (CallbackOrigins.entryRoot slots) ρ entry h)
    (ok : readCall (.invoke fn recv args) = true) (values : ∀ i, isVal (ρ i) = true)
    (heapValues : ∀ (l : Nat) (x : Tm), h[l]? = some x → isVal x = true)
    (trace : Prepared h n ⟨instantiate 0 ρ fn,instantiate 0 ρ recv,instantiateArgs 0 ρ args⟩ final)
    {x} (hit : (atCall slots roots param state (.invoke fn recv args)).demand.actualRoots[p]? = some (some (x,[]))) :
    entry x = CallEffects.callEnv final.recv final.args p := by
  simp only [atCall] at hit
  rw [List.getElem?_map] at hit
  obtain ⟨t,ht,root⟩ := Option.map_eq_some_iff.mp hit
  cases t <;> try contradiction
  rename_i slot
  have equal := resolved slot x [] root
  simp only [HeapKnowledge.readPath,Option.some.injEq] at equal
  cases p with
  | zero =>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at ht
    subst recv
    have heq := trace.keepsRecv (v := ρ slot) (by simp [instantiate]) (values slot)
    simpa [CallEffects.callEnv,heq] using equal
  | succ p =>
    have pos := sourcePosition (by simpa only [List.getElem?_cons_succ] using ht)
      (Bool.and_eq_true_iff.mp ok).2 values
    have found := (pos.prepared trace heapValues).lookup
    simpa [CallEffects.callEnv,List.getD_eq_getElem?_getD,found] using equal

end Verification.SourceClaimJson.CallbackInferencePlan
