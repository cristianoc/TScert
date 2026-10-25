import Verification.Programs.CertificateProducer

/-! Forged interfaces exercise failures that a source producer need not propose:
both outgoing edges and a handler fail beside the source expression. -/
namespace Verification.DiagnosticControls
open PositiveGraphs PositiveCertificates ProgramTyping ControlFlow CertificateProducer

private instance : Instantiates Nat := ⟨fun _ _ _ => none⟩

private def G : NormalGraph Nat where
  rows
    | 0 => [.num]
    | 1 => [.boolLit true, .boolLit false]
    | 2 => [.str]
    | _ => [.top]

private def program : Program := [
  ⟨.var 0, .branch ⟨1, none⟩ ⟨2, none⟩, some ⟨3, none⟩⟩,
  ⟨.var 0, .ret, none⟩,
  ⟨.var 0, .ret, none⟩,
  ⟨.var 0, .ret, none⟩]

private def claims : List (PointClaim Nat) := [
  ⟨[[0]], [1]⟩, ⟨[[2]], [2]⟩, ⟨[[2]], [2]⟩, ⟨[[3], [2]], [3]⟩]

private def failures : List (Failure Nat) :=
  diagnoseUsing G (finiteInstanceImages G) [0, 1, 2, 3] 12 program claims

#guard failures.any fun | .expression 0 => true | _ => false
#guard failures.any fun | .edge 0 1 0 => true | _ => false
#guard failures.any fun | .edge 0 2 1 => true | _ => false
#guard failures.any fun | .edge 0 3 2 => true | _ => false

-- The failed expression does not hide the promise about entry argument 0.
private def promised : List (Failure Nat) :=
  diagnoseUsing G (finiteInstanceImages G) [0, 1, 2, 3] 12
    [⟨.var 0, .ret, none⟩] [⟨[[0]], [1]⟩] (goal := .guards [2] 0)

#guard promised.any fun | .expression 0 => true | _ => false
#guard promised.any fun | .promise 0 [0] [2] => true | _ => false

-- Projection order and the first duplicate matter to deterministic search.
-- Repeated destination slots retain each alias while cached lookups avoid
-- rescanning the mapping inside the quadratic implication projection.
#guard
  let xs : List (PromiseCalls.Implication Nat) :=
    [⟨1, 0, [5]⟩, ⟨1, 0, [99]⟩, ⟨0, 1, [7]⟩]
  (projectImplications xs (some [1, 0, 1]) 3).map (fun x => (x.test, x.target, x.type)) ==
    [(0, 1, [5]), (1, 0, [7]), (1, 2, [7]), (2, 1, [5])]

end Verification.DiagnosticControls
