import Verification.Paper.TolerantFrames.Commands

/-! # A finite-trace control machine for the paper's commands

Only control is made explicit. Heap-changing steps are the existing actual
PrimitiveRun; worlds, marks and frozen function entry do not occur here.
Continuation interpretation references existing structured Executes, and its
backward preservation proves terminating machine traces yield that relation.
-/
namespace Verification.Paper.TolerantFrames.CommandMachine
open Verification

inductive Frame where
  | sequence (next : Command)
  | loop (body : Command)
  | catcher (name : Nat) (handler : Command)

abbrev Stack := List Frame

inductive Control where
  | run (command : Command) (stack : Stack)
  | exit (outcome : Exit) (stack : Stack)

/-- Interpretation of the remaining stack. Each recursive Finish premise
uses the shorter stack. A repeated loop is an existing structured execution,
not a supplied summary of its safety or postcondition. -/
inductive Finish (host : NativeCode) : Stack → Exit → Env → Heap → Nat → Env → Heap → Exit → Prop where
  | done : Finish host [] e ρ h 0 ρ h e
  | seq_normal : Executes host b ρ h p ρ₁ h₁ e → Finish host stack e ρ₁ h₁ q ρ₂ h₂ f →
      Finish host (.sequence b :: stack) .normal ρ h (p + q) ρ₂ h₂ f
  | seq_exit : e ≠ .normal → Finish host stack e ρ h n ρ' h' f →
      Finish host (.sequence b :: stack) e ρ h n ρ' h' f
  | loop_normal : Executes host (.loop b) ρ h p ρ₁ h₁ e → Finish host stack e ρ₁ h₁ q ρ₂ h₂ f →
      Finish host (.loop b :: stack) .normal ρ h (p + q) ρ₂ h₂ f
  | loop_break : Finish host stack .normal ρ h n ρ' h' f →
      Finish host (.loop b :: stack) .break ρ h n ρ' h' f
  | loop_return : Finish host stack (.returned v) ρ h n ρ' h' f →
      Finish host (.loop b :: stack) (.returned v) ρ h n ρ' h' f
  | loop_throw : Finish host stack (.thrown v) ρ h n ρ' h' f →
      Finish host (.loop b :: stack) (.thrown v) ρ h n ρ' h' f
  | catch_throw : Executes host d (bindName ρ x v) h p ρ₁ h₁ e → Finish host stack e ρ₁ h₁ q ρ₂ h₂ f →
      Finish host (.catcher x d :: stack) (.thrown v) ρ h (p + q) ρ₂ h₂ f
  | catch_exit : (∀ v, e ≠ .thrown v) → Finish host stack e ρ h n ρ' h' f →
      Finish host (.catcher x d :: stack) e ρ h n ρ' h' f

inductive Complete (host : NativeCode) : Control → Env → Heap → Nat → Env → Heap → Exit → Prop where
  | running : Executes host c ρ h p ρ₁ h₁ e → Finish host stack e ρ₁ h₁ q ρ₂ h₂ f →
      Complete host (.run c stack) ρ h (p + q) ρ₂ h₂ f
  | exiting : Finish host stack e ρ h n ρ' h' f → Complete host (.exit e stack) ρ h n ρ' h' f

/-- Administrative control costs zero in B. Primitive transitions carry the
actual shared reduction count, which can also be zero. -/
inductive Step (host : NativeCode) : Control → Env → Heap → Nat → Control → Env → Heap → Prop where
  | primitive : PrimitiveRun host p ρ h n ρ' h' e → Step host (.run (.step p) stack) ρ h n (.exit e stack) ρ' h'
  | sequence : Step host (.run (.seq a b) stack) ρ h 0 (.run a (.sequence b :: stack)) ρ h
  | yes : tagHolds .truthy (test.eval ρ) = true →
      Step host (.run (.choice test a b) stack) ρ h 0 (.run a stack) ρ h
  | no : tagHolds .truthy (test.eval ρ) = false →
      Step host (.run (.choice test a b) stack) ρ h 0 (.run b stack) ρ h
  | loop : Step host (.run (.loop b) stack) ρ h 0 (.run b (.loop b :: stack)) ρ h
  | handler : Step host (.run (.handle b x d) stack) ρ h 0 (.run b (.catcher x d :: stack)) ρ h
  | returned : isVal (a.eval ρ) = true → Step host (.run (.return_ a) stack) ρ h 0 (.exit (.returned (a.eval ρ)) stack) ρ h
  | thrown : isVal (a.eval ρ) = true → Step host (.run (.throw_ a) stack) ρ h 0 (.exit (.thrown (a.eval ρ)) stack) ρ h
  | broken : Step host (.run .break_ stack) ρ h 0 (.exit .break stack) ρ h
  | seq_normal : Step host (.exit .normal (.sequence b :: stack)) ρ h 0 (.run b stack) ρ h
  | seq_exit : e ≠ .normal → Step host (.exit e (.sequence b :: stack)) ρ h 0 (.exit e stack) ρ h
  | loop_normal : Step host (.exit .normal (.loop b :: stack)) ρ h 0 (.run (.loop b) stack) ρ h
  | loop_break : Step host (.exit .break (.loop b :: stack)) ρ h 0 (.exit .normal stack) ρ h
  | loop_return : Step host (.exit (.returned v) (.loop b :: stack)) ρ h 0 (.exit (.returned v) stack) ρ h
  | loop_throw : Step host (.exit (.thrown v) (.loop b :: stack)) ρ h 0 (.exit (.thrown v) stack) ρ h
  | catch_throw : Step host (.exit (.thrown v) (.catcher x d :: stack)) ρ h 0 (.run d stack) (bindName ρ x v) h
  | catch_exit : (∀ v, e ≠ .thrown v) →
      Step host (.exit e (.catcher x d :: stack)) ρ h 0 (.exit e stack) ρ h

/-- Every machine transition preserves the existing structured meaning
backward and adds exactly its primitive weight. -/
theorem Step.backward {host ctrl ρ h p ctrl' ρ' h' q ρ₂ h₂ f}
    (step : Step host ctrl ρ h p ctrl' ρ' h')
    (complete : Complete host ctrl' ρ' h' q ρ₂ h₂ f) :
    Complete host ctrl ρ h (p + q) ρ₂ h₂ f := by
  cases step with
  | primitive hr => cases complete with | exiting finish => exact .running (.step hr) finish
  | sequence =>
    cases complete with
    | running first finish =>
      cases finish with
      | seq_normal second rest => simpa [Nat.add_assoc] using Complete.running (.seq first second) rest
      | seq_exit ne rest => simpa using Complete.running (.seq_exit first ne) rest
  | yes ht => cases complete with | running body rest => simpa using Complete.running (.yes ht body) rest
  | no ht => cases complete with | running body rest => simpa using Complete.running (.no ht body) rest
  | loop =>
    cases complete with
    | running body finish =>
      cases finish with
      | loop_normal again rest => simpa [Nat.add_assoc] using Complete.running (.loop_next body again) rest
      | loop_break rest => simpa using Complete.running (.loop_break body) rest
      | loop_return rest => simpa using Complete.running (.loop_return body) rest
      | loop_throw rest => simpa using Complete.running (.loop_throw body) rest
  | handler =>
    cases complete with
    | running body finish =>
      cases finish with
      | catch_throw handler rest => simpa [Nat.add_assoc] using Complete.running (.handle_catch body handler) rest
      | catch_exit ne rest => simpa using Complete.running (.handle_exit body ne) rest
  | returned hv => cases complete with | exiting finish => simpa using Complete.running (.return_ hv) finish
  | thrown hv => cases complete with | exiting finish => simpa using Complete.running (.throw_ hv) finish
  | broken => cases complete with | exiting finish => simpa using Complete.running .break_ finish
  | seq_normal => cases complete with | running body rest => simpa using Complete.exiting (Finish.seq_normal body rest)
  | seq_exit ne => cases complete with | exiting rest => simpa using Complete.exiting (Finish.seq_exit ne rest)
  | loop_normal => cases complete with | running body rest => simpa using Complete.exiting (Finish.loop_normal body rest)
  | loop_break => cases complete with | exiting rest => simpa using Complete.exiting (Finish.loop_break rest)
  | loop_return => cases complete with | exiting rest => simpa using Complete.exiting (Finish.loop_return rest)
  | loop_throw => cases complete with | exiting rest => simpa using Complete.exiting (Finish.loop_throw rest)
  | catch_throw => cases complete with | running body rest => simpa using Complete.exiting (Finish.catch_throw body rest)
  | catch_exit ne => cases complete with | exiting rest => simpa using Complete.exiting (Finish.catch_exit ne rest)

/-- A trace is finite by its inductive construction; a zero primitive weight
does not supply or imply a decreasing execution measure. -/
inductive Runs (host : NativeCode) : Control → Env → Heap → Nat → Control → Env → Heap → Prop where
  | refl : Runs host ctrl ρ h 0 ctrl ρ h
  | next : Step host ctrl ρ h p middle ρ₁ h₁ → Runs host middle ρ₁ h₁ q final ρ₂ h₂ →
      Runs host ctrl ρ h (p + q) final ρ₂ h₂

theorem Runs.backward {host ctrl ρ h p ctrl' ρ' h'}
    (run : Runs host ctrl ρ h p ctrl' ρ' h') :
    ∀ {q ρ₂ h₂ f}, Complete host ctrl' ρ' h' q ρ₂ h₂ f → Complete host ctrl ρ h (p + q) ρ₂ h₂ f := by
  induction run with
  | refl => intro q ρ₂ h₂ f finish; simpa using finish
  | next step _ ih =>
    intro q ρ₂ h₂ f finish
    simpa [Nat.add_assoc] using step.backward (ih finish)

/-- Terminating command control has EXACTLY the existing raw structured
execution, with no reference/host/world premise silently added. -/
theorem Runs.executes {host c ρ h p ρ' h' e}
    (run : Runs host (.run c []) ρ h p (.exit e []) ρ' h') : Executes host c ρ h p ρ' h' e := by
  have complete := run.backward (Complete.exiting Finish.done)
  cases complete with
  | running body finish => cases finish; simpa using body

end Verification.Paper.TolerantFrames.CommandMachine
