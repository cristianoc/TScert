import Verification.Paper.TolerantFrames.CallableEntryCode

/-! # References of generated callable code

Shared refs traverses graph expressions and captures as well as identity and
own fields. Symbolic code contains variables/scalar literals, not embedded
heap references. Thus self reference validity follows from actual object roles
and capture references; it assumes no callable behavior or function summary.
-/
namespace Verification.Paper.TolerantFrames
open Verification

@[simp] theorem Argument.code_refs (a : Argument) (depth : Nat) : refs (a.code depth) = [] := by
  cases a with
  | «variable» _ => rfl
  | literal v => cases v <;> first | rfl | (rename_i b; cases b <;> rfl)

@[simp] theorem arguments_code_refs (args : List Argument) (depth : Nat) :
    refsArgs (args.map (Argument.code depth)) = [] := by
  rw [refsArgs_eq]
  apply List.flatMap_eq_nil_iff.mpr
  intro value member
  obtain ⟨arg, _, rfl⟩ := List.mem_map.mp member
  exact arg.code_refs depth

@[simp] theorem object_arguments_code_refs (fields : List (String × Argument)) (depth : Nat) :
    refsArgs (fields.map fun p => p.2.code depth) = [] := by
  rw [refsArgs_eq]
  apply List.flatMap_eq_nil_iff.mpr
  intro value member
  obtain ⟨field, _, rfl⟩ := List.mem_map.mp member
  exact field.2.code_refs depth

namespace Compiler

/-- Native helpers occur as variables in the fixed symbolic program. -/
@[simp] theorem operation_symbolic_refs (bound : Nat) (op : Operation) :
    refs (op.symbolic (hostTemplate bound)) = [] := by
  cases op
  case objectLiteral fields =>
    change refsArgs (fields.map fun p => p.2.code 0) = []
    exact object_arguments_code_refs fields 0
  all_goals simp [Operation.symbolic, ownFieldCode, hostTemplate, refs, refsArgs]

/-- Origin gives exact expression syntax, not merely a semantic property. -/
theorem Origin.expression_refs {nodes bound node} (origin : Origin nodes bound node) :
    refs node.node.expression = [] := by
  cases origin <;> simp [annotated, refs]

theorem generated_expressions_refs (c : Command) : refsArgs (expressions (compile c.frameBound c)) = [] := by
  rw [refsArgs_eq]
  apply List.flatMap_eq_nil_iff.mpr
  intro expression member
  obtain ⟨node, hn, rfl⟩ := List.mem_map.mp member
  exact (compile_origins c node hn).expression_refs

namespace Callable

theorem function_expressions_refs (c : Command) : refsArgs (functionExpressions c) = [] := by
  simp only [functionExpressions, refsArgs_eq, List.flatMap_append, List.flatMap_cons, refs,
    List.flatMap_nil, List.append_nil]
  simpa only [refsArgs_eq] using generated_expressions_refs c

/-- All remaining references are the actual object identity/fields and captures. -/
theorem function_refs {arity} {caps : List Tm} (c : Command) (layout : Layout arity caps.length)
    (fields : List (PropKey × Nat)) (identity : Nat) :
    refs (function c layout fields identity) = objRefs fields identity ++ refsArgs caps := by
  simp only [function, refs, function_expressions_refs, List.nil_append]

theorem function_refs_ok {arity k} {caps : List Tm} {W : WorldT k}
    (c : Command) (layout : Layout arity caps.length) (fields : List (PropKey × Nat)) (identity : Nat)
    (object : RefsOk W (.objAt fields .absent identity)) (captures : ∀ v ∈ caps, RefsOk W v) :
    RefsOk W (function c layout fields identity) := by
  intro r hr
  rw [function_refs] at hr
  rcases List.mem_append.mp hr with ho | hc
  · exact object r ho
  · rw [refsArgs_eq] at hc
    obtain ⟨v, hv, hr⟩ := List.mem_flatMap.mp hc
    exact captures v hv r hr

end Callable
end Compiler
end Verification.Paper.TolerantFrames
