import Verification.Source.LoweringState
import Verification.Source.BindingPlan

namespace Verification.SourceExtraction
open ProgramTyping ControlFlow
open Fragment LabelStore
open EquationGraphs (Tree)

/-- Recursive body, expression and binding entry points shared by typed lowering.
    Each operation runs in the caller's graph construction state. -/
structure RecursiveLowering where
  compileExpr : SourceClaims.Function Tree → List (ScopeBinding Tree) → List (Ty Tree) →
    Fragment.Expr → Target → Compiler Target
  executeBindingPlan : SourceClaims.Function Tree → List (ScopeBinding Tree) →
    List (ScopeBinding Tree) → List (ScopeBinding Tree) → List (Ty Tree) →
    SourceExecution.BindingPlan →
    (List (ScopeBinding Tree) → List (Ty Tree) → Compiler Target) → Compiler Target
  body : Span → SourceClaims.Function Tree → Ty Tree → List (ScopeBinding Tree) →
    List Fragment.Stmt → Compiler Target

end Verification.SourceExtraction
