import Verification.Paper.TolerantFrames.CallableEntryLayout
import Verification.Paper.TolerantFrames.CompilerCorrectness

/-! # Actual fixed-arity entry into generated command code

An appended adapter leaves all existing body labels unchanged. Invocation,
node entry and the adapter bind are three real heap-preserving reductions.
The self value comes from the invocation pack, not a circular capture list.
-/
namespace Verification.Paper.TolerantFrames.Compiler.Callable
open Verification ControlFlow HeapObservations

def entryLabel (c : Command) : Nat := (compile c.frameBound c).length

def functionExpressions (c : Command) : List Tm :=
  expressions (compile c.frameBound c) ++ [.undef]

def functionContinuations {arity captures} (c : Command) (layout : Layout arity captures) :
    List (Continuation × Option Target) :=
  continuations (compile c.frameBound c) ++ [(.bind ⟨4, layout.mapping c.frameBound⟩, none)]

def function {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) : Tm :=
  .objAt fields (.graph arity (functionExpressions c) (functionContinuations c layout)
    (entryLabel c) caps .call false) identity

def invocation {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) (receiver : Tm) (args : List Tm) : Tm :=
  .invoke (function c layout fields identity) receiver args

def bodyTerm {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) (receiver : Tm) (args : List Tm) : Tm :=
  .goto (functionExpressions c) (functionContinuations c layout) 4
    (slots c.frameBound (layout.env receiver args (function c layout fields identity)) layout.host .undef) .undef

/-- Appending paired code preserves the exact old program, with no label shift. -/
theorem program_append (nodes : List AnnotatedNode) (extraExpressions : List Tm)
    (extraContinuations : List (Continuation × Option Target)) :
    GraphCode.program (expressions nodes ++ extraExpressions) (continuations nodes ++ extraContinuations) =
      nodes.map AnnotatedNode.node ++ GraphCode.program extraExpressions extraContinuations := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => exact congrArg (List.cons node.node) ih

theorem code_agrees {arity captures} (c : Command) (layout : Layout arity captures) :
    CodeAgrees (compile c.frameBound c) (GraphCode.program (functionExpressions c) (functionContinuations c layout)) := by
  intro i node lookup
  rw [functionExpressions, functionContinuations, program_append,
    List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.mp lookup).1),
    List.getElem?_map, lookup]
  rfl

theorem entry_expression (c : Command) : (functionExpressions c)[entryLabel c]? = some .undef := by
  simp [functionExpressions, entryLabel, expressions]

theorem entry_continuation {arity captures} (c : Command) (layout : Layout arity captures) :
    (functionContinuations c layout)[entryLabel c]? = some (.bind ⟨4, layout.mapping c.frameBound⟩, none) := by
  simp [functionContinuations, entryLabel, continuations]

/-- This is an actual shared invocation prefix, with exact count three. -/
theorem invocation_prefix {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) (receiver : Tm) (args : List Tm) (h : Heap)
    (hr : isVal receiver = true) (ha : CallArguments.Values args) :
    Steps 3 h (invocation c layout fields identity receiver args) h (bodyTerm c layout fields identity receiver args) := by
  refine .next (Step.callGraph hr ha rfl) ?_
  change Steps 2 h (.goto (functionExpressions c) (functionContinuations c layout) (entryLabel c)
    (inputs arity receiver args caps (function c layout fields identity)) .nul) h _
  refine .next (Step.gotoEnter (entry_expression c) (entry_continuation c layout)) ?_
  have last : Step h
      (.frame (functionExpressions c) (functionContinuations c layout) .undef
        (inputs arity receiver args caps (function c layout fields identity)) .nul
        (.bind ⟨4, layout.mapping c.frameBound⟩) none)
      h (bodyTerm c layout fields identity receiver args) := by
    simpa only [bodyTerm, layout.map_inputs] using
      (Step.frameBind (h := h) (E := functionExpressions c) (K := functionContinuations c layout)
        (v := .undef) (L := inputs arity receiver args caps (function c layout fields identity))
        (d := .nul) (l := ⟨4, layout.mapping c.frameBound⟩) (x := none) rfl)
  exact .next last .refl

end Verification.Paper.TolerantFrames.Compiler.Callable
