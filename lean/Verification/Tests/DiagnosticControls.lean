import Verification.Programs.CertificateProducer

/-! A forged handler interface and implication-projection order. -/
namespace Verification.DiagnosticControls
open PositiveGraphs PositiveCertificates ProgramTyping ControlFlow CertificateProducer

private instance : Instantiates Nat := ⟨fun _ _ _ => none⟩

-- An explicit handler requirement exercises heap entailment independently
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

-- Projection order and the first duplicate matter to deterministic search.
-- Repeated destination slots retain each alias while cached lookups avoid
-- rescanning the mapping inside the quadratic implication projection.
#guard
  let xs : List (PromiseCalls.Implication Nat) :=
    [⟨1, 0, [5]⟩, ⟨1, 0, [99]⟩, ⟨0, 1, [7]⟩]
  (projectImplications xs (some [1, 0, 1]) 3).map (fun x => (x.test, x.target, x.type)) ==
    [(0, 1, [5]), (1, 0, [7]), (1, 2, [7]), (2, 1, [5])]

end Verification.DiagnosticControls
