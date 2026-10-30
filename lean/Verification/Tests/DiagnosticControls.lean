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

-- An explicit handler requirement exercises diagnostic entailment independently
-- of which field facts the source producer proposes. The mapping drops the
-- thrown value: target slot 0 denotes source slot 1, the record binding.
private def fieldGraph : NormalGraph Nat where
  rows
    | 0 => [.refs [("f", [1])] [] []]
    | 1 => [.num]
    | _ => [.top]

private def fieldProgram : Program := [
  ⟨.var 0, .ret, some ⟨1, some [1]⟩⟩,
  ⟨.var 0, .ret, none⟩]

private def fieldClaims : List (PointClaim Nat) := [
  ⟨[[0]], [0]⟩, ⟨[[0]], [0]⟩]

private def fieldRequirements : List (Nat × HeapKnowledge.Knowledge) :=
  [(1, { cells := [⟨0, ValueSets.ofAtoms [.num], "f"⟩] })]

#guard (produceUsing fieldGraph (finiteInstanceImages fieldGraph) [0, 1, 2] 12
  (.plain [0]) fieldProgram fieldClaims 0 (inputs := [[0]])
  (requirements := fieldRequirements)).1.isOk

#guard (diagnoseUsing fieldGraph (finiteInstanceImages fieldGraph) [0, 1, 2] 12
  fieldProgram fieldClaims fieldRequirements (goal := .plain [0])).isEmpty

-- Projection order and the first duplicate matter to deterministic search.
-- Repeated destination slots retain each alias while cached lookups avoid
-- rescanning the mapping inside the quadratic implication projection.
#guard
  let xs : List (PromiseCalls.Implication Nat) :=
    [⟨1, 0, [5]⟩, ⟨1, 0, [99]⟩, ⟨0, 1, [7]⟩]
  (projectImplications xs (some [1, 0, 1]) 3).map (fun x => (x.test, x.target, x.type)) ==
    [(0, 1, [5]), (1, 0, [7]), (1, 2, [7]), (2, 1, [5])]

end Verification.DiagnosticControls
