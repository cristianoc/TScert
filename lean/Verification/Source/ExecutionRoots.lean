-- Exporting plans requires the expressions owned by each action and closure entry.
import Verification.Source.FlowGraph
import Verification.Source.ExpressionPlan

/-! Expression occurrences owned by a source execution point. Deferred bodies
    have their own graphs; source spans identify operations within a point. -/
namespace Verification.SourceExecution
open Fragment SourceFlow ProgramTyping

/-- Executable expression occurrences in preorder. The closure value belongs
    to its creation point; its defaults and body belong to its body graph. -/
partial def expressionOccurrences (e : Expr) : List Expr :=
  let children := match e with
    | .var .. | .lit .. | .lambda .. | .ctor .. | .block .. => []
    | .shapeTest _ _ _ a | .not _ a | .unary _ _ a | .cast _ _ a | .read _ _ a
    | .assign _ _ _ a | .nullishAssign _ _ _ a => [a]
    | .alloc _ _ es | .build _ _ es | .arrayLit _ es _ => es
    | .logical _ _ a b | .coalesce _ a b | .equality _ _ a b
    | .singletonTest _ _ _ _ a b | .write _ _ a b | .index _ _ a b
    | .elemAt _ a b | .arith _ _ a b | .inKeys _ a b | .comma _ a b
    | .logicalAssign _ _ a b | .withValue _ a b _ _ | .optional _ _ a b => [a,b]
    | .elemWrite _ a b c | .indexWrite _ _ a b c | .ifBody _ a b c => [a,b,c]
    | .update _ _ target rhs _ => target :: rhs.toList
    | .objectAssign _ target sources => target :: sources
    | .arrayAssign _ targets rest rhs => rhs :: targets.flatMap (fun (t : ArrayElem Expr) =>
          t.target.referenceParts ++ t.default_.toList) ++
        ((rest.map fun (r : Span × Bool × ArrayElem Expr) => r.2.2.target.referenceParts).getD [])
    | .construct _ callee args _ _ | .call _ callee args _ _ | .invoke _ callee args _ _ => callee :: args
    | .bindWithReceiver _ callee receiver args | .callWithReceiver _ callee receiver args => callee :: receiver :: args
    | .applyWithReceiver _ callee receiver list => callee :: receiver :: list.toList
  match e with
  | .block .. => []
  | _ => e :: children.flatMap expressionOccurrences

/-- Roots evaluated by one statement action. Structural bodies are represented
    by successor actions in the shared graph. -/
def statementRoots : Stmt → List Expr
  | .ret _ e | .effect _ e | .throw _ e => [e]
  | .constants _ bindings | .mutables _ bindings => bindings.map (·.init)
  | .destructure _ target default_ init => init :: default_.toList ++ target.defaults
  | .ite _ condition _ _ | .loop _ condition _ _ => [condition]
  | .forOf _ _ _ _ iterable _ => [iterable]
  | .brk .. | .cont .. | .block .. | .tryStmt .. | .closing .. => []

/-- The source expressions elaborated at an action, in source preorder. -/
def actionRoots : Action → List Expr
  | .declaration _ _ binding _ => [binding.init]
  | .statement statement _ | .branch statement _ _ | .returnValue statement
  | .saveReturn statement _ _ | .iteratorStart statement _ _ => statementRoots statement
  | .finish | .jump _ | .returnHeld _ | .rethrow _ | .discardThrow _ _ | .iteratorStep .. => []

/-- One occurrence per source span, retaining the outer expression where the
    parser gives a wrapper and its operand the same span. -/
def uniqueOccurrences (roots : List Expr) : List Expr :=
  (roots.flatMap expressionOccurrences).foldl (fun found e =>
    if (found.map Expr.span).contains e.span then found else found ++ [e]) []

/-- Expressions evaluated by an action. Defaults supplied here execute in an
    expression-bodied closure's entry prologue before the body expression. -/
def actionExpressions (action : Action) (defaults : List Expr := []) : List Expr :=
  uniqueOccurrences (defaults ++ actionRoots action)

end Verification.SourceExecution
