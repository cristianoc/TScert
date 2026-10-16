import Verification.Source.RequestJson

/-! Where the execution model must agree with JavaScript and no proof states
it (DESIGN.md, the trusted tools): each witness runs the machine, or evaluates
a trusted definition, on a hand-written program and states the outcome
JavaScript gives. A pipeline case does not show these: a verified claim holds
of the model whichever way the model runs, and TypeScript admits no source
comparing a NaN with a literal, calling `null` or applying `new` to an
arrow. -/
namespace Verification.ExecutionModelTests
open PositiveNormalization PositiveGraphs ProgramTyping ControlFlow

/-- One-node code of `arity` returning `body`, capturing the `context` slots of
the context it is created in. A closure whose code is one expression is graph
code of one node, `return e`, run from the frame its signature describes: the
receiver, the parameters, then every slot of the context the closure is
created in, which it captures in order. -/
def oneNode (arity : Nat) (body : Tm) (context : Nat) (kind : Invoke := .call) : CallCode :=
  .graph arity [body] [(.ret, none)] 0 ((List.range context).map .var) kind

end Verification.ExecutionModelTests

/-- One step of the machine on a test program's ground term: the step rules a
hand-written program takes, a run of graph code's included, inside the
evaluation contexts it takes them in. -/
syntax "machine_step" : tactic
macro_rules
  | `(tactic| machine_step) => `(tactic| first
    | exact .makeV rfl
    | exact .makeFnV rfl
    | exact .readV rfl
    | exact .writeV rfl (by decide)
    | exact .letV rfl
    | exact .iteT
    | exact .iteF
    | exact .testV rfl
    | exact .callGraph rfl (by decide) rfl
    | exact .constructGraph (by decide)
    | exact .callBound rfl (by decide)
    | exact .gotoEnter rfl rfl
    | exact .frameRet rfl
    | exact .frameEffect rfl
    | exact .frameBind rfl
    | (apply Verification.Step.frameC; machine_step)
    | (apply Verification.Step.letC; machine_step)
    | (apply Verification.Step.iteC; machine_step)
    | (apply Verification.Step.makeC; machine_step)
    | (apply Verification.Step.makeFnC; machine_step)
    | (apply Verification.Step.appR rfl; machine_step)
    | (apply Verification.Step.callL; machine_step))

/-- Run a hand-written program by the machine to its end. -/
macro "run_machine" : tactic => `(tactic| repeat first
  | exact Verification.ControlFlow.Execution.refl
  | apply Verification.ControlFlow.Execution.next (.enter rfl)
  | apply Verification.ControlFlow.Execution.next (.bind rfl)
  | apply Verification.ControlFlow.Execution.next (.effect rfl)
  | apply Verification.ControlFlow.Execution.next (.ret rfl)
  | apply Verification.ControlFlow.Execution.next (.tagBind rfl)
  | apply Verification.ControlFlow.Execution.next .yesBind
  | apply Verification.ControlFlow.Execution.next .noBind
  | apply Verification.ControlFlow.Execution.next .yes
  | apply Verification.ControlFlow.Execution.next .no
  | apply Verification.ControlFlow.Execution.next (.expr (by machine_step)))

namespace Verification.ExecutionModelTests
open PositiveNormalization PositiveGraphs ProgramTyping ControlFlow

/-! ## Numbers

`numberEqual` is IEEE equality on encodings: every NaN compares unequal,
infinities compare by sign, and distinct finite doubles stay distinct. -/

#guard !(numberEqual 0x7ff8000000000000 0x7ff8000000000000)
#guard !(numberEqual 0x7ff0000000000001 0)
#guard !(numberEqual 0 0xfff8000000000000)
#guard numberEqual 0x7ff0000000000000 0x7ff0000000000000
#guard !(numberEqual 0x7ff0000000000000 0xfff0000000000000)
#guard !(numberEqual 0x3ff0000000000000 0x3ff0000000000001)

/-! ## Primitive loose equality -/

#guard primitiveEquals .nul .undef
#guard !(primitiveEquals .nul (.num 0))
#guard primitiveEquals .fls (.str "")
#guard primitiveEquals .tru (.str "1")
#guard primitiveEquals (.num 0) (.num 0x8000000000000000)
#guard !(primitiveEquals (.num 0x7ff8000000000000) (.num 0x7ff8000000000000))
#guard primitiveEquals (.num 0) (.str " \t")
#guard primitiveEquals (.num (16.0 : Float).toBits) (.str "0x10")
#guard primitiveEquals (.str "0b10") (.num (2.0 : Float).toBits)
#guard primitiveEquals (.str "0o10") (.num (8.0 : Float).toBits)
#guard primitiveEquals (.str "+.5") (.num (0.5 : Float).toBits)
#guard primitiveEquals (.str "01.") (.num (1.0 : Float).toBits)
#guard primitiveEquals (.str "1e2") (.num (100.0 : Float).toBits)
#guard primitiveEquals (.str "Infinity") (.num 0x7ff0000000000000)
#guard primitiveEquals (.str "-Infinity") (.num 0xfff0000000000000)
#guard primitiveEquals (.str "1e309") (.num 0x7ff0000000000000)
#guard primitiveEquals (.str "5e-324") (.num 1)
#guard primitiveEquals (.str "2.2250738585072014e-308") (.num 0x0010000000000000)
#guard primitiveEquals (.str "1.7976931348623157e308") (.num 0x7fefffffffffffff)
#guard primitiveEquals (.str "0e9999") (.num 0)
#guard primitiveEquals (.str "1e-400") (.num 0)
#guard stringNumber "1e1000000000" == 0x7ff0000000000000
#guard stringNumber "-1e-1000000000" == 0x8000000000000000
#guard stringNumber "0e1000000000" == 0
#guard stringNumber "-0" == 0x8000000000000000
#guard ["1n", "1_0", "+0x10", "-0b1", "1e", ".", "infinity"].all fun s =>
  let n := stringNumber s; !(numberEqual n n)
#guard primitiveEquals (.bigint 0) (.str "")
#guard primitiveEquals (.str "0x10") (.bigint 16)
#guard primitiveEquals (.str "+01") (.bigint 1)
#guard !(primitiveEquals (.str "1.0") (.bigint 1))
#guard !(primitiveEquals (.str "1e2") (.bigint 100))
#guard !(primitiveEquals (.bigint 9007199254740993) (.num (9007199254740993.0 : Float).toBits))
#guard primitiveEquals (.bigint 9007199254740992) (.num (9007199254740992.0 : Float).toBits)
#guard !(primitiveEquals (.bigint 1) (.num (1.5 : Float).toBits))
#guard !(primitiveEquals (.bigint 0) (.num 0x7ff0000000000000))
#guard primitiveEquals (.sym 1) (.sym 1)
#guard !(primitiveEquals (.sym 1) (.sym 2))
#guard !(primitiveEquals (.sym 1) (.str "1"))
#guard primitiveEquals (.str (String.ofList [Char.ofNat 0xFEFF, '1', Char.ofNat 0x2028])) (.num (1.0 : Float).toBits)
#guard !(numericSpace (Char.ofNat 0x0085))

/-! ## Conditions and `let` -/

namespace KnownCondition
private def knownEffectProgram : Program :=
  [⟨.alloc .tru,.bind 1,none⟩,
   ⟨.ite (.letE (.write (.var 0) .fls) .tru) .fls (.read .nul),.ret,none⟩]

/-- Selecting a known arm must not erase the condition's write. -/
theorem known_condition_effects_preserved : Execution knownEffectProgram 8 []
    (.at 0 (fun _ => .nul)) [.fls, .nul] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.makeFnV rfl))
    | apply Execution.next (.expr (.iteC (.letC (.writeV rfl (by decide)))))
    | apply Execution.next (.expr (.iteC (.letV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.ret rfl)
end KnownCondition

namespace LetOrder
/-- An initializer's effects happen before its body. No body step is allowed
while the initializer is stuck, even when the body itself could allocate. -/
example (h : Heap) : ¬ Step h (.letE (.app .nul .nul) (.alloc .tru)) h' t' := by
  intro hs
  cases hs with
  | letC hs => exact stuck_no_step hs
  | letV hv => simp [isVal] at hv
end LetOrder

/-! ## `in` -/

namespace PrototypeChain
-- `key in o` reads the prototype chain: a class instance holds its
-- prototype, whose method it lacks as an own key, and `in` finds it there.
private def protoHeap : List Tm := [.objAt [("m", 1)] .absent 3, .num 0, .num 1]
private def instanceWithProto : Tm := .objAt [("x", 2), ("[[proto]]", 0)] .absent 4
#guard tagHoldsIn protoHeap (.hasKey "m") instanceWithProto
end PrototypeChain

/-! ## Calls and construction -/

-- `new` runs no call-only code: an arrow's `new` throws in JavaScript.
#guard (CallArguments.construction (.graph 1 [.var 1] [(.ret, none)] 0 [])).isNone

namespace CallOrder
-- The initializer writes true, allocates an intermediate object, and returns
-- false for the new function's bag. Its invocation body reads the captured bag,
-- past its parameter and receiver.
private def initial : Tm := .letE (.write (.var 0) .tru) (.letE (.alloc .tru) .fls)
private def callee : Tm := .makeAt (oneNode 1 (.read (.var 2)) 1) [valueField] [initial]
private def argument : Tm := .letE (.write (.var 0) .fls) .nul
private def program (callable : Bool) : Program :=
  [⟨if callable then .makeAt (oneNode 1 (.var 0) 0) [valueField] [.fls] else .alloc .fls,.bind 1,none⟩,
   ⟨.app callee argument,.ret,none⟩]
/-- Initializer write and intermediate allocation precede function allocation;
argument write then precedes the call and the body read. The heap holds the
captured bag, the initializer's object, and the newly allocated callable bag,
each followed by its identity cell. -/
theorem returns_false (callable : Bool) : Execution (program callable) 16 []
    (.at 0 (fun _ => .nul)) [.fls,.nul,.tru,.nul,.fls,.nul] (.done .fls) := by
  cases callable <;> run_machine

/-- A stuck initializer prevents both outer allocation and argument effects. -/
theorem initializer_blocks_argument {h h' t'} :
    ¬ Step h (.app (.makeAt (oneNode 1 .nul 0) [valueField] [.app .nul .nul])
      (.write (.obj 0 .absent) .fls)) h' t' := by
  intro step
  cases step with
  | callL step =>
    cases step with
    | @makeArg _ _ _ i _ _ a _ hg _ step =>
      cases i with
      | zero => simp at hg; subst a; exact stuck_no_step step
      | succ i => simp at hg
    | makeFields hv _ => have h := hv (.app .nul .nul) (by simp); simp [isVal] at h
  | callRecv hv _ => simp [isVal] at hv
  | callArg hv _ _ _ _ => simp [isVal] at hv
  | callSpread hv _ _ _ _ => simp [isVal] at hv

/-- Even a discarded extra argument must finish: a stuck second actual blocks
both a later argument write and the unary callee's mutating body. -/
theorem argument_blocks_body {h h' t'} :
    ¬ Step h (.call (.obj 1 (oneNode 1 (.write (.obj 0 .absent) .tru) 0))
      [.tru, .app .nul .nul, .write (.obj 0 .absent) .fls]) h' t' := by
  intro step
  rcases CallArguments.call_step_iff.mp step with ⟨frame, hp, _⟩ | ⟨_, hi⟩
  · cases hp with
    | callee hs => exact obj_no_step hs
    | recv _ hs => exact value_no_step rfl hs
    | args _ _ hs =>
      cases hs with
      | head hs => exact tru_no_step hs
      | tail _ hs =>
        cases hs with
        | head hs => exact stuck_no_step hs
        | tail hv _ => simp [isVal] at hv
    | @splice _ _ _ _ pre post ls vs _ _ he _ _ =>
      have hm : Tm.spread (.arr ls) ∈ pre ++ .spread (.arr ls) :: post := by simp
      rw [← he] at hm
      simp at hm
  · cases hi with
    | graph _ hv => simp [CallArguments.Values, isVal] at hv
end CallOrder

namespace Mutation
/-- The mutator writes the captured bag, its frame's slot 3, past its receiver
and parameter. -/
private def mutator : Tm := .write (.var 3) .tru
private def program (callable fresh : Bool) : Program :=
  [⟨.fls,.bind 1,none⟩,
   ⟨if callable then .makeAt (oneNode 1 (.var 0) 1) [valueField] [.var 0] else .alloc (.var 0),.bind 2,none⟩,
   ⟨.read (.var 0),.bind 3,none⟩,
   ⟨.makeFn (oneNode 1 mutator 3) .nul,.bind 4,none⟩,
   ⟨.app (.var 0) .nul,.effect 5,none⟩,
   ⟨if fresh then .read (.var 2) else .var 1,.ret,none⟩]
/-- The heap really changes to true; a saved immutable value remains false.
Creation of the mutator accounts for the third, null-initialized heap cell;
each allocation's identity takes the cell after its fields. -/
theorem returns_expected (callable fresh : Bool) :
    Execution (program callable fresh) (if fresh then 20 else 19) []
      (.at 0 (fun _ => .nul)) [.tru,.nul,.nul,.nul] (.done (if fresh then .tru else .fls)) := by
  cases callable <;> cases fresh <;>
    repeat first
      | exact Execution.refl
      | apply Execution.next (.enter rfl)
      | apply Execution.next (.expr (.makeV rfl))
      | apply Execution.next (.expr (.makeFnV rfl))
      | apply Execution.next (.expr (.readV rfl))
      | apply Execution.next (.expr (.writeV rfl (by decide)))
      | apply Execution.next (.expr (.callGraph rfl (by decide) rfl))
      | apply Execution.next (.expr (.gotoEnter rfl rfl))
      | apply Execution.next (.expr (.frameC (.writeV rfl (by decide))))
      | apply Execution.next (.expr (.frameRet rfl))
      | apply Execution.next (.bind rfl)
      | apply Execution.next (.effect rfl)
      | apply Execution.next (.ret rfl)
end Mutation

namespace Reentry
-- At entry: receiver, callback, captured bag. The two lets save a read, then a
-- callback result. Returning the saved read and rereading the bag are different
-- programs.
private def body (fresh : Bool) : Tm :=
  .letE (.read (.var 2))
    (.letE (.app (.var 2) .nul) (if fresh then .read (.var 4) else .var 1))
-- At entry: receiver, null argument, captured function, captured bag. The
-- nested callback returns false and performs no reentry, so the complete
-- invocation terminates.
private def callback : Tm :=
  .letE (.write (.var 3) .tru) (.app (.var 3) (.makeFn (oneNode 1 .fls 0) .nul))
private def program (callable fresh : Bool) : Program :=
  [⟨if callable then .makeAt (oneNode 1 (.var 1) 0) [valueField] [.fls] else .alloc .fls,.bind 1,none⟩,
   ⟨.makeFn (oneNode 1 (body fresh) 1) .nul,.bind 2,none⟩,
   ⟨.makeFn (oneNode 1 callback 2) .nul,.bind 3,none⟩,
   ⟨.app (.var 1) (.var 0),.ret,none⟩]
/-- Reentry writes true while the outer frame retains its saved false value.
The fourth allocation is the terminating inner callback's; each allocation's
identity takes the cell after its fields. -/
theorem returns_expected (callable fresh : Bool) :
    Execution (program callable fresh) (if fresh then 34 else 32) []
      (.at 0 (fun _ => .nul)) [.tru,.nul,.nul,.nul,.nul,.nul,.nul,.nul]
      (.done (if fresh then .tru else .fls)) := by
  cases callable <;> cases fresh <;> run_machine
end Reentry

#print axioms KnownCondition.known_condition_effects_preserved
#print axioms CallOrder.returns_false
#print axioms CallOrder.initializer_blocks_argument
#print axioms CallOrder.argument_blocks_body
#print axioms Mutation.returns_expected
#print axioms Reentry.returns_expected
end Verification.ExecutionModelTests
