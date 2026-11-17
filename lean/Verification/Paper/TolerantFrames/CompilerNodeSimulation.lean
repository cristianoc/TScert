import Verification.Paper.TolerantFrames.CompilerSinks

/-! # Every generated node simulates actual command control

The compiler proved Origin for every emitted node. At a real completed graph
node, it yields a finite command-machine trace with primitive weight no larger
than the expression's shared count, preserving heap and the mapped environment.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow HeapObservations

theorem Origin.node_result {P nodes bound outer graph host node a h h' term after}
    (origin : Origin nodes bound node) (values : ∀ i, isVal (graph i) = true)
    (stable : (hostTemplate bound).close graph = host)
    (steps : Steps a h (instantiate 0 graph node.node.expression) h' term)
    (leave : ControlFlow.Transition P h' (.eval term graph node.node.continuation node.node.handler) h' after)
    (outside : OutsideEvaluation after) :
    NodeResult nodes bound outer host node.site graph h a h' after := by
  cases origin with
  | primitive scope routing => exact primitive_node scope values stable routing steps leave outside
  | choice scope _ yesSite noSite => exact choice_node scope values stable yesSite noSite steps leave outside
  | loop routing bodySite => exact loop_node values stable routing bodySite steps leave outside
  | returned scope routing => exact return_node scope values stable routing steps leave outside
  | thrown scope routing => exact throw_node scope values stable routing steps leave outside
  | broken routing => exact break_node values stable routing steps leave outside
  | normal_sink => exact Verification.Paper.TolerantFrames.Compiler.normal_sink steps leave outside
  | break_sink => exact Verification.Paper.TolerantFrames.Compiler.break_sink steps leave outside
  | return_sink => exact Verification.Paper.TolerantFrames.Compiler.return_sink values steps leave outside
  | throw_sink => exact Verification.Paper.TolerantFrames.Compiler.throw_sink values steps leave outside

end Verification.Paper.TolerantFrames.Compiler
