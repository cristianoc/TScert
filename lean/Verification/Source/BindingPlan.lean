-- persistent lexical bindings and defaults follow a shared syntax-owned execution schedule.
import Verification.Source.ExpressionPlan
import Verification.Source.FlowGraph

namespace Verification.SourceExecution
open Fragment

/-- A binding schedule retains lexical names while its saved intermediates live
    only until the action or parameter prologue reaches its continuation. -/
inductive BindingPlan where
  | finish
  | evaluate (value : Saved) (plan : Plan) (next : BindingPlan)
  | defaultValue (value result : Saved) (fallback : Plan) (next : BindingPlan)
  | bind (name : String) (origin : Span) (value : Saved) (next : BindingPlan)
  | input (name : String) (index : Nat) (value : Saved) (next : BindingPlan)
  | readField (source : Span) (receiver : Saved) (field : String) (value : Saved) (next : BindingPlan)
  | readPosition (source : Span) (array : Saved) (index : Nat) (value : Saved) (next : BindingPlan)
  | objectRest (source : Span) (receiver : Saved) (drop : List String) (value : Saved) (next : BindingPlan)
  | arrayRest (source : Span) (array : Saved) (start : Nat) (slice : Bool) (value : Saved) (next : BindingPlan)
  deriving Nonempty

private abbrev BindingBuilder := StateM Nat
private def freshBinding (root origin : Span) : BindingBuilder Saved := do
  let id ← get
  set (id+1)
  pure ⟨id, s!"%binding@{root.1}:{root.2}:{id}%", origin, "binding"⟩

mutual
private partial def bindPattern (root : Span) (pattern : Pattern Expr) (value : Saved)
    (default_ : Option Expr) (next : BindingBuilder BindingPlan) : BindingBuilder BindingPlan := do
  match default_ with
  | none => patternBody root pattern value next
  | some expression =>
    let result ← freshBinding root pattern.span
    let after ← patternBody root pattern result next
    pure (.defaultValue value result (build expression) after)

private partial def patternBody (root : Span) (pattern : Pattern Expr) (value : Saved)
    (next : BindingBuilder BindingPlan) : BindingBuilder BindingPlan := do
  match pattern with
  | .name name _ => pure (.bind name root value (← next))
  | .object _ properties rest =>
    objectProperties root value properties (properties.map (·.1)) rest next
  | .array _ elements rest => arrayElements root value elements rest next

private partial def objectProperties (root : Span) (receiver : Saved)
    (properties : List (String × Pattern Expr × Option Expr)) (drop : List String)
    (rest : Option (Span × Pattern Expr)) (next : BindingBuilder BindingPlan) : BindingBuilder BindingPlan := do
  match properties with
  | (field, pattern, default_) :: more =>
    let value ← freshBinding root pattern.span
    let after ← bindPattern root pattern value default_ (objectProperties root receiver more drop rest next)
    pure (.readField pattern.span receiver field value after)
  | [] => match rest with
    | none => next
    | some (source, pattern) =>
      let value ← freshBinding root source
      pure (.objectRest source receiver drop value (← bindPattern root pattern value none next))

private partial def arrayElements (root : Span) (array : Saved)
    (elements : List (Nat × Pattern Expr × Option Expr))
    (rest : Option (Nat × Span × Bool × Pattern Expr)) (next : BindingBuilder BindingPlan) : BindingBuilder BindingPlan := do
  match elements with
  | (index, pattern, default_) :: more =>
    let value ← freshBinding root pattern.span
    let after ← bindPattern root pattern value default_ (arrayElements root array more rest next)
    pure (.readPosition pattern.span array index value after)
  | [] => match rest with
    | none => next
    | some (start, source, slice, pattern) =>
      let value ← freshBinding root source
      pure (.arrayRest source array start slice value (← bindPattern root pattern value none next))
end

/-- The whole initializer and destructuring action, including conditional
    defaults and persistent bindings, has one execution schedule. -/
def bindingAction : SourceFlow.Action → Option BindingPlan
  | .statement (.destructure source pattern default_ initial) _ => some ((do
      let value ← freshBinding source initial.span
      pure (BindingPlan.evaluate value (build initial) (← bindPattern source pattern value default_ (pure .finish)))).run' 0)
  | _ => none

/-- Parameters enter source scope in the supplied parameter order. Input
    indices designate their original frame positions after the receiver. -/
def bindingPrologue (owner : Span)
    (parameters : List (String × Span × Nat × Option Expr)) : Option BindingPlan :=
  if parameters.isEmpty then none else some ((do
    let rec schedule : List (String × Span × Nat × Option Expr) → BindingBuilder BindingPlan
      | [] => pure .finish
      | (name, origin, index, default_) :: rest => do
        let value ← freshBinding owner origin
        let after ← schedule rest
        let present := BindingPlan.bind name origin value after
        let next ← match default_ with
          | none => pure present
          | some expression => do
            let result ← freshBinding owner origin
            pure (.defaultValue value result (build expression) (.bind name origin result after))
        pure (.input name index value next)
    schedule parameters).run' 0)
end Verification.SourceExecution
