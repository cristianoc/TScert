import Verification.Paper.TolerantFrames.NativeExecution

/-! # Explicit supplied native contracts and actual command execution

Contracts are parameters for concrete supplied callees, not global axioms or
implementations of real libraries. Their safety field covers the actual receiver
and evaluated positional arguments; exact normal/exceptional raw predicates and
regional effects retain the entry environment and heap. Safety allows divergence.
The separate callee binding/identity condition supplies the declared native.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints TolerantFrames HeapObservations

abbrev NativePost := Env → Nat → Heap → Heap → Val → Prop

/-- A host assumption for one concrete supplied callee. Exception predicates
can read the actual thrown value (for example a native range error). -/
structure NativeContract (callee : Val) (receiver : Argument) (arguments : List Argument)
    (P : Assertion) (normal exceptional : NativePost) (Φ Φe : Footprint) : Prop where
  source : isSourceVal callee = true
  executionSafe : ∀ ρ m (s : IndexedHeap), ValidContext ρ m s → RefsOk s.W callee → P ρ m s →
    SafePostExcV NativeSourceValues NativeSourceValues
      (fun _ _ h' v => normal ρ m s.h h' v ∧ Footprints.Post Φ ρ s.h h')
      (fun _ _ h' v => exceptional ρ m s.h h' v ∧ Footprints.Post Φe ρ s.h h')
      s.n s.W s.h (.invoke callee (receiver.eval ρ) (arguments.map (Argument.eval ρ)))

/-- With already evaluated inputs, the supplied execution-safety contract
forces a real invocation step. It guarantees neither termination nor normality. -/
theorem NativeContract.can_step {callee receiver arguments P normal exceptional Φ Φe}
    (contract : NativeContract callee receiver arguments P normal exceptional Φ Φe)
    {ρ m s} (valid : ValidContext ρ m s) (calleeRefs : RefsOk s.W callee) (pre : P ρ m s) :
    ∃ h' term', Step s.h (.invoke callee (receiver.eval ρ) (arguments.map (Argument.eval ρ))) h' term' := by
  have safety := contract.executionSafe ρ m s valid calleeRefs pre
  have noRaise {term v : Tm} (value : isVal term = true) (raised : Raises term v) : False := by
    rw [raises_not_val raised] at value
    cases value
  rcases native_safe_progress s.pos safety with value | ⟨v, raised⟩ | step
  · cases value
  · cases raised with
    | callL raised => exact (noRaise (sourceVal_isVal contract.source) raised).elim
    | callRecv _ raised => exact (noRaise (sourceVal_isVal (receiver.valid valid).1) raised).elim
    | callArg _ _ found _ raised =>
      have member := List.mem_of_getElem? found
      obtain ⟨a, _, equal⟩ := List.mem_map.mp member
      subst equal
      exact (noRaise (sourceVal_isVal (a.valid valid).1) raised).elim
  · exact step

/-- Native identity is an input binding, independent of its behavioral contract. -/
def ResolvedNativePre (callee : Val) (f : Nat) (P : Assertion) : Assertion :=
  fun ρ m s => ρ f = callee ∧ P ρ m s

/-- Normal raw outcomes retain the exact result and binding relation, also
for a perform whose result is discarded. Paper formula bridges use consequence. -/
def NativeNormalPost (p : Primitive) (normal : NativePost) : Postcondition :=
  fun ρ ρ' m s t => ∃ v, ρ' = p.bindResult ρ v ∧ normal ρ m s.h t.h v

/-- A command's exceptional post has no exception name; retain a witness.
The exit's source/world validity is guaranteed independently by Triple. -/
def NativeExceptionalPost (exceptional : NativePost) : Postcondition :=
  fun ρ _ m s t => ∃ v, exceptional ρ m s.h t.h v

private theorem Primitive.valid_bindResult {p : Primitive} {ρ m s v}
    (valid : ValidContext ρ m s) (value : isSourceVal v = true ∧ RefsOk s.W v) :
    ValidContext (p.bindResult ρ v) m s := by
  cases p with
  | bind _ _ => exact valid.bindName value
  | perform _ => exact valid

/-- Actual native primitive execution obtains its chosen indexed exit from
shared safety. No supplied partial command summary stands for that safety. -/
theorem native_primitive_exit {callee receiver arguments P normal exceptional Φ Φe}
    (contract : NativeContract callee receiver arguments P normal exceptional Φ Φe)
    {host p f ρ m s n ρ' h' e} (operation : p.operation = .nativeCall f receiver arguments)
    (valid : ValidContext ρ m s) (pre : ResolvedNativePre callee f P ρ m s)
    (run : PrimitiveRun host p ρ s.h n ρ' h' e) (budget : n < s.n) :
    ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧
      ValidContext ρ' m t ∧ ExitValid e t ∧
      ExitPost (NativeNormalPost p normal) (NativeExceptionalPost exceptional)
        (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) e ρ ρ' m s t ∧
      Footprints.Post (match e with | .thrown _ => Φe | _ => Φ) ρ s.h h' := by
  obtain ⟨calleeBinding, pre⟩ := pre
  have calleeRefs : RefsOk s.W callee := calleeBinding ▸ valid.1 f
  have safety := contract.executionSafe ρ m s valid calleeRefs pre
  have code : p.operation.code host ρ =
      .invoke callee (receiver.eval ρ) (arguments.map (Argument.eval ρ)) := by
    rw [operation]
    simp only [Operation.code, calleeBinding]
  cases run with
  | normal execution value =>
    rw [code] at execution
    obtain ⟨t, reachable, heap, count, continuing⟩ := run_native_safety execution s rfl budget safety
    obtain ⟨member, post, effect⟩ := native_exit_value t.pos value continuing
    refine ⟨t, reachable, heap, count, Primitive.valid_bindResult (valid.admissible reachable) member,
      trivial, ?_, by simpa only [heap] using effect⟩
    exact ⟨_, rfl, by simpa only [heap] using post⟩
  | thrown execution raised =>
    rw [code] at execution
    obtain ⟨t, reachable, heap, count, continuing⟩ := run_native_safety execution s rfl budget safety
    obtain ⟨member, post, effect⟩ := native_exit_raise t.pos raised continuing
    exact ⟨t, reachable, heap, count, valid.admissible reachable, member,
      ⟨_, by simpa only [heap] using post⟩, by simpa only [heap] using effect⟩

/-- Bind and perform instances share the same operational proof. The record
remains an explicit parameter until a host or implementation supplies it. -/
theorem native_command_rule {callee receiver arguments P normal exceptional Φ Φe}
    (contract : NativeContract callee receiver arguments P normal exceptional Φ Φe)
    {host p f} (operation : p.operation = .nativeCall f receiver arguments) :
    Triple host (ResolvedNativePre callee f P) (.step p)
      (NativeNormalPost p normal) (NativeExceptionalPost exceptional)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) ∧
    Effects host (ResolvedNativePre callee f P) (.step p) Φ Φe := by
  constructor
  · intro ρ m s n ρ' h' e valid pre run budget
    cases run with
    | step primitive =>
      obtain ⟨t, reachable, heap, count, valid', exit, post, _⟩ :=
        native_primitive_exit contract operation valid pre primitive budget
      exact ⟨t, reachable, heap, count, valid', exit, post⟩
  · intro ρ m s n ρ' h' e valid pre run budget
    cases run with
    | step primitive =>
      obtain ⟨_, _, _, _, _, _, _, effect⟩ := native_primitive_exit contract operation valid pre primitive budget
      cases e <;> exact effect

end Verification.Paper.TolerantFrames
