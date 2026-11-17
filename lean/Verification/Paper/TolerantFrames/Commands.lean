import Verification.Paper.TolerantFrames.Consequences

/-! # Commands and partial correctness

The existing mechanisms extended here are the deterministic calculus `Steps`,
`Raises`, `IndexedHeap`, and `Action`. Commands add the paper's explicit normal,
break, return, and throw control exits. Runs carry heaps and environments, not
worlds. A triple supplies an admissible exit world; two proofs may supply
different worlds. This distinction is essential to Conj.

Typed-array primitives are native calls, as in the shared model. `NativeCode`
selects their code; no property of it is globally assumed. Its contracts must
be supplied where a primitive rule is used.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations
open Verification.TolerantFrames

/-- Atoms of commands are distinct from atoms of assertions. -/
inductive Argument where
  | variable (slot : Nat)
  | literal (value : ScalarLiteral)

def Argument.eval (ρ : Env) : Argument → Val
  | .variable x => ρ x
  | .literal v => v.eval

/-- The step forms of Definition 3. A result is bound by `Step.bind`; a
mutation is represented by `Step.perform` and binds no source variable. -/
inductive Operation where
  | value (a : Argument)
  | binary (op : Arith) (a b : Argument)
  | not (a : Argument)
  | and (a b : Argument)
  | or (a b : Argument)
  | fieldRead (x : Nat) (field : String)
  | fieldWrite (x : Nat) (field : String) (value : Argument)
  | elementRead (x : Nat) (index : Argument)
  | elementWrite (x : Nat) (index value : Argument)
  | arrayLength (x : Nat)
  | viewRead (x : Nat) (index : Argument)
  | viewWrite (x : Nat) (index value : Argument)
  | viewLength (x : Nat)
  | stringRead (x : Nat) (index : Argument)
  | stringLength (x : Nat)
  | objectLiteral (fields : List (String × Argument))
  | arrayLiteral (elements : List Argument)
  | methodCall (x : Nat) (method : String) (arguments : List Argument)
  | call (f : Nat) (arguments : List Argument)
  | construct (f : Nat) (arguments : List Argument)

inductive Primitive where
  | bind (result : Nat) (operation : Operation)
  | perform (operation : Operation)

/-- Code for the paper's three host-defined typed-array operations. -/
structure NativeCode where
  viewRead : Tm
  viewWrite : Tm
  viewLength : Tm

/-- The shared calculus interpretation. Ordinary array element access first
reads the array's spine; a write stores the resulting spine back. A missing own field reads undefined, without consulting the shared calculus's
prototype extension. The method
receiver and arguments are already named, so none is evaluated twice. -/
def Operation.code (host : NativeCode) (ρ : Env) : Operation → Tm
  | .value a => a.eval ρ
  | .binary op a b => .arith op (a.eval ρ) (b.eval ρ)
  | .not a => .ite (.test .truthy (a.eval ρ)) .fls .tru
  | .and a b => .ite (.test .truthy (a.eval ρ)) (b.eval ρ) (a.eval ρ)
  | .or a b => .ite (.test .truthy (a.eval ρ)) (a.eval ρ) (b.eval ρ)
  | .fieldRead x f => match ρ x with
    | .objAt fs _ _ => if (fs.lookup (.str f)).isSome then .readAt (.str f) (ρ x) else .undef
    | v => .readAt (.str f) v
  | .fieldWrite x f a => .writeAt (.str f) (ρ x) (a.eval ρ)
  | .elementRead x i => .elemAt (.readAt arraySpineKey (ρ x)) (i.eval ρ)
  | .elementWrite x i v => .letE (.writeAt arraySpineKey (ρ x)
      (.setElem (.readAt arraySpineKey (ρ x)) (i.eval ρ) (v.eval ρ))) (v.eval ρ)
  | .arrayLength x => .lenOf (.readAt arraySpineKey (ρ x))
  | .viewRead x i => .invoke host.viewRead (ρ x) [i.eval ρ]
  | .viewWrite x i v => .invoke host.viewWrite (ρ x) [i.eval ρ, v.eval ρ]
  | .viewLength x => .invoke host.viewLength (ρ x) []
  | .stringRead x i => .elemAt (ρ x) (i.eval ρ)
  | .stringLength x => .lenOf (ρ x)
  | .objectLiteral fs => .makeAt .absent (fs.map fun p => .str p.1) (fs.map fun p => p.2.eval ρ)
  | .arrayLiteral es => .makeAt .absent [arraySpineKey] [.arrLit (es.map (Argument.eval ρ))]
  | .methodCall x f args => .invoke (.readAt (.str f) (ρ x)) (ρ x) (args.map (Argument.eval ρ))
  | .call f args => .invoke (ρ f) .undef (args.map (Argument.eval ρ))
  | .construct f args => .construct (ρ f) (args.map (Argument.eval ρ))

/-- Four ways of leaving a command. Break and return are not normal exits. -/
inductive Exit where
  | normal | break | returned (value : Val) | thrown (value : Val)
  deriving DecidableEq

/-- The command grammar is independent of proof certificates. -/
inductive Command where
  | step (primitive : Primitive)
  | seq (first second : Command)
  | choice (test : Argument) (yes no : Command)
  | loop (body : Command)
  | handle (body : Command) (caught : Nat) (handler : Command)
  | return_ (value : Argument)
  | throw_ (value : Argument)
  | break_

/-- Binding a fresh source name. Scope checks decide freshness separately. -/
def bindName (ρ : Env) (x : Nat) (v : Val) : Env := fun y => if y = x then v else ρ y

def Primitive.operation : Primitive → Operation
  | .bind _ op | .perform op => op

def Primitive.bindResult (ρ : Env) (v : Val) : Primitive → Env
  | .bind x _ => bindName ρ x v
  | .perform _ => ρ

/-- Primitive completion is actual execution in the shared deterministic
calculus. Safety and world existence are conclusions of triples, not silently
inserted premises of this execution relation. -/
inductive PrimitiveRun (host : NativeCode) : Primitive → Env → Heap → Nat → Env → Heap → Exit → Prop where
  | normal {p ρ h n h' v} : Steps n h (p.operation.code host ρ) h' v → isSourceVal v = true →
      PrimitiveRun host p ρ h n (p.bindResult ρ v) h' .normal
  | thrown {p ρ h n h' t v} : Steps n h (p.operation.code host ρ) h' t → Raises t v →
      PrimitiveRun host p ρ h n ρ h' (.thrown v)

/-- Finite command execution. Sequence propagates all abrupt exits; a loop
consumes break but propagates return and throw; a handler consumes only throw.
The step count counts the shared calculus reductions of its primitives. -/
inductive Executes (host : NativeCode) : Command → Env → Heap → Nat → Env → Heap → Exit → Prop where
  | step {p ρ h n ρ' h' e} : PrimitiveRun host p ρ h n ρ' h' e → Executes host (.step p) ρ h n ρ' h' e
  | seq {a b ρ h n ρ₁ h₁ k ρ₂ h₂ e} : Executes host a ρ h n ρ₁ h₁ .normal →
      Executes host b ρ₁ h₁ k ρ₂ h₂ e → Executes host (.seq a b) ρ h (n + k) ρ₂ h₂ e
  | seq_exit {a b ρ h n ρ' h' e} : Executes host a ρ h n ρ' h' e → e ≠ .normal →
      Executes host (.seq a b) ρ h n ρ' h' e
  | yes {v a b ρ h n ρ' h' e} : tagHolds .truthy (v.eval ρ) = true → Executes host a ρ h n ρ' h' e →
      Executes host (.choice v a b) ρ h n ρ' h' e
  | no {v a b ρ h n ρ' h' e} : tagHolds .truthy (v.eval ρ) = false → Executes host b ρ h n ρ' h' e →
      Executes host (.choice v a b) ρ h n ρ' h' e
  | loop_next {b ρ h n ρ₁ h₁ k ρ₂ h₂ e} : Executes host b ρ h n ρ₁ h₁ .normal →
      Executes host (.loop b) ρ₁ h₁ k ρ₂ h₂ e → Executes host (.loop b) ρ h (n + k) ρ₂ h₂ e
  | loop_break {b ρ h n ρ' h'} : Executes host b ρ h n ρ' h' .break →
      Executes host (.loop b) ρ h n ρ' h' .normal
  | loop_return {b ρ h n ρ' h' v} : Executes host b ρ h n ρ' h' (.returned v) →
      Executes host (.loop b) ρ h n ρ' h' (.returned v)
  | loop_throw {b ρ h n ρ' h' v} : Executes host b ρ h n ρ' h' (.thrown v) →
      Executes host (.loop b) ρ h n ρ' h' (.thrown v)
  | handle_catch {b x d ρ h n ρ₁ h₁ k ρ₂ h₂ e v} : Executes host b ρ h n ρ₁ h₁ (.thrown v) →
      Executes host d (bindName ρ₁ x v) h₁ k ρ₂ h₂ e → Executes host (.handle b x d) ρ h (n + k) ρ₂ h₂ e
  | handle_exit {b x d ρ h n ρ' h' e} : Executes host b ρ h n ρ' h' e →
      (∀ v, e ≠ .thrown v) → Executes host (.handle b x d) ρ h n ρ' h' e
  | return_ {a ρ h} : isSourceVal (a.eval ρ) = true → Executes host (.return_ a) ρ h 0 ρ h (.returned (a.eval ρ))
  | throw_ {a ρ h} : isSourceVal (a.eval ρ) = true → Executes host (.throw_ a) ρ h 0 ρ h (.thrown (a.eval ρ))
  | break_ {ρ h} : Executes host .break_ ρ h 0 ρ h .break

/-- Returned and thrown values are valid values of the chosen exit world.
This is the type system's result guarantee, distinct from user postconditions. -/
def ExitValid (e : Exit) (s : IndexedHeap) : Prop := match e with
  | .normal | .break => True
  | .returned v | .thrown v => isSourceVal v = true ∧ RefsOk s.W v

private theorem ScalarLiteral.valid (v : ScalarLiteral) {k : Nat} (W : WorldT k) :
    isSourceVal v.eval = true ∧ RefsOk W v.eval := by
  cases v
  all_goals try exact ⟨rfl, RefsOk_of_nil rfl⟩
  rename_i b
  cases b <;> exact ⟨rfl, RefsOk_of_nil rfl⟩

/-- Arguments of commands read valid values at valid input contexts. -/
theorem Argument.valid (a : Argument) {ρ m s} (hv : ValidContext ρ m s) :
    isSourceVal (a.eval ρ) = true ∧ RefsOk s.W (a.eval ρ) := by
  cases a with
  | «variable» x => exact ⟨hv.2.1 x, hv.1 x⟩
  | literal v => exact v.valid s.W

/-- Binding a valid value preserves the context, including a caught value. -/
theorem ValidContext.bindName {ρ m s x v} (hv : ValidContext ρ m s)
    (hval : isSourceVal v = true ∧ RefsOk s.W v) : ValidContext (Verification.Paper.TolerantFrames.bindName ρ x v) m s := by
  refine ⟨fun y => ?_, fun y => ?_, hv.2.2⟩
  · by_cases hy : y = x
    · simpa [Verification.Paper.TolerantFrames.bindName, hy] using hval.2
    · simpa [Verification.Paper.TolerantFrames.bindName, hy] using hv.1 y
  · by_cases hy : y = x
    · simpa [Verification.Paper.TolerantFrames.bindName, hy] using hval.1
    · simpa [Verification.Paper.TolerantFrames.bindName, hy] using hv.2.1 y

/-- Exit assertions include obligations of the enclosing loop/function.
Those obligations are the meaning of the displayed Break and Return rules. -/
def ExitPost (Q Qe J : Postcondition) (Ret : Val → Postcondition) : Exit → Postcondition
  | .normal => Q
  | .thrown _ => Qe
  | .break => J
  | .returned v => Ret v

/-- A partial correctness triple supplies an exit world for every completed
execution with budget left. It is not universal over arbitrary supplied exit
worlds. The mark is unchanged through command composition. -/
def Triple (host : NativeCode) (P : Assertion) (c : Command) (Q Qe J : Postcondition)
    (Ret : Val → Postcondition) : Prop :=
  ∀ ρ m s n ρ' h' e, ValidContext ρ m s → P ρ m s → Executes host c ρ s.h n ρ' h' e → n < s.n →
    ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧ ValidContext ρ' m t ∧ ExitValid e t ∧ ExitPost Q Qe J Ret e ρ ρ' m s t

/-- Effect judgments constrain raw completed runs. Break and return use the
normal effect. Admissible world existence is supplied separately by typing. -/
def Effects (host : NativeCode) (P : Assertion) (c : Command) (Φ Φe : Footprint) : Prop :=
  ∀ ρ m s n ρ' h' e, ValidContext ρ m s → P ρ m s → Executes host c ρ s.h n ρ' h' e → n < s.n →
    Post (match e with | .thrown _ => Φe | _ => Φ) ρ s.h h'

/-- General consequence, without a finite proof search completeness claim. -/
theorem triple_consequence {host P P' c Q Qe J Ret Q' Qe' J' Ret'}
    (ht : Triple host P c Q Qe J Ret) (hp : Entails P' P)
    (hq : ∀ e ρ ρ' m s t, ExitPost Q Qe J Ret e ρ ρ' m s t → ExitPost Q' Qe' J' Ret' e ρ ρ' m s t) :
    Triple host P' c Q' Qe' J' Ret' := by
  intro ρ m s n ρ' h' e hv hP hr hn
  obtain ⟨t, ha, hh, hk, hvt, hve, hpost⟩ := ht ρ m s n ρ' h' e hv (hp ρ m s hP) hr hn
  exact ⟨t, ha, hh, hk, hvt, hve, hq e ρ ρ' m s t hpost⟩

/-- Definition 16 for arbitrary two-state postconditions. -/
def Independent (Q : Postcondition) : Prop :=
  ∀ ρ ρ' m s u v, ValidContext ρ m s → ValidContext ρ' m u → ValidContext ρ' m v →
    Admissible s u → Admissible s v → u.h = v.h → u.n = v.n →
    (Q ρ ρ' m s u ↔ Q ρ ρ' m s v)

/-- Conj retains the first proof's exit world and transports only the second
postcondition. The corresponding abrupt obligations must also be independent. -/
theorem triple_conj {host P P' c Q Qe J Ret Q' Qe' J' Ret'}
    (h₁ : Triple host P c Q Qe J Ret) (h₂ : Triple host P' c Q' Qe' J' Ret')
    (hind : ∀ e, Independent (ExitPost Q' Qe' J' Ret' e)) :
    Triple host (fun ρ m s => P ρ m s ∧ P' ρ m s) c (PostAnd Q Q') (PostAnd Qe Qe')
      (PostAnd J J') (fun v => PostAnd (Ret v) (Ret' v)) := by
  intro ρ m s n ρ' h' e hv ⟨hp, hp'⟩ hr hn
  obtain ⟨t, ha, hh, hk, hvt, hve, ht⟩ := h₁ ρ m s n ρ' h' e hv hp hr hn
  obtain ⟨u, hau, hhu, hku, hvu, hveu, hu⟩ := h₂ ρ m s n ρ' h' e hv hp' hr hn
  have hs : ExitPost Q' Qe' J' Ret' e ρ ρ' m s t :=
    (hind e ρ ρ' m s t u hv hvt hvu ha hau (hh.trans hhu.symm) (by omega)).mpr hu
  refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
  cases e <;> exact ⟨ht, hs⟩

/-- Break's normal postcondition is false and its contextual obligation J
is established at the unchanged state. -/
theorem break_rule {host : NativeCode} {J : Assertion} {Ret : Val → Postcondition} :
    Triple host J .break_ (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => True) (Now J) Ret := by
  intro ρ m s n ρ' h' e hv hp hr _
  cases hr
  exact ⟨s, Admissible.refl s, rfl, by omega, hv, trivial, hp⟩

/-- A local return obligation. Use `return_function_rule` to freeze old at
the function entry, rather than the current command entry. -/
theorem return_rule {host : NativeCode} {a : Argument} {Ret : Val → Postcondition}
    {P : Assertion} {J : Postcondition}
    (hp : ∀ ρ m s, P ρ m s → Ret (a.eval ρ) ρ ρ m s s) :
    Triple host P (.return_ a) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => True) J Ret := by
  intro ρ m s n ρ' h' e hv hP hr _
  cases hr
  exact ⟨s, Admissible.refl s, rfl, by omega, hv, a.valid hv, hp ρ m s hP⟩

/-- Throw preserves R at the state passed to the handler. -/
theorem throw_rule {host : NativeCode} {a : Argument} {R : Assertion} {J : Postcondition} {Ret : Val → Postcondition} :
    Triple host R (.throw_ a) (fun _ _ _ _ _ => False) (Now R) J Ret := by
  intro ρ m s n ρ' h' e hv hp hr _
  cases hr
  exact ⟨s, Admissible.refl s, rfl, by omega, hv, a.valid hv, hp⟩

/-- Freeze a function's entry in its result obligation. Command sequencing
changes its local entry, but cannot change what old means in this obligation. -/
def FunctionReturn (entryEnv : Env) (entry : IndexedHeap) (Q : Val → Postcondition) :
    Val → Postcondition := fun v _ ρ' m _ t => Q v entryEnv ρ' m entry t

/-- Return of §6, with old explicitly referring to the enclosing function. -/
theorem return_function_rule {host : NativeCode} {a : Argument} {Q : Val → Postcondition}
    {J : Postcondition} (entryEnv : Env) (entry : IndexedHeap) :
    Triple host (fun ρ m s => Q (a.eval ρ) entryEnv ρ m entry s) (.return_ a)
      (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => True) J (FunctionReturn entryEnv entry Q) :=
  return_rule (fun _ _ _ h => h)

/-- The displayed Conj rule needs independence only of the second normal
and exceptional posts. Contextual break/return obligations are shared and
retained from the first proof, so no independence of them is needed. -/
theorem conj_rule {host P P' c Q Qe J Ret Q' Qe'}
    (h₁ : Triple host P c Q Qe J Ret) (h₂ : Triple host P' c Q' Qe' J Ret)
    (hq : Independent Q') (hqe : Independent Qe') :
    Triple host (fun ρ m s => P ρ m s ∧ P' ρ m s) c (PostAnd Q Q') (PostAnd Qe Qe') J Ret := by
  intro ρ m s n ρ' h' e hv ⟨hp, hp'⟩ hr hn
  obtain ⟨t, ha, hh, hk, hvt, hve, ht⟩ := h₁ ρ m s n ρ' h' e hv hp hr hn
  obtain ⟨u, hau, hhu, hku, hvu, hveu, hu⟩ := h₂ ρ m s n ρ' h' e hv hp' hr hn
  refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
  cases e with
  | normal => exact ⟨ht, (hq _ _ _ _ _ _ hv hvt hvu ha hau (hh.trans hhu.symm) (by omega)).mpr hu⟩
  | thrown _ => exact ⟨ht, (hqe _ _ _ _ _ _ hv hvt hvu ha hau (hh.trans hhu.symm) (by omega)).mpr hu⟩
  | «break» => exact ht
  | returned _ => exact ht

end Verification.Paper.TolerantFrames
