import Verification.Programs.CertificateProducer

/-! Two checks of the certificate search, code no proof covers (the checker
reads its result and decides). A pipeline case shows neither: no source's
claims give a handler edge this requirement, and a source's projections do
not fix the order of duplicates the second check pins. -/
namespace Verification.DiagnosticControls
open PositiveGraphs PositiveCertificates ProgramTyping ControlFlow CertificateProducer

private instance : Instantiates Nat := ⟨fun _ _ _ => none⟩

-- A forged handler requirement: the search must entail it from the heap,
-- whichever field facts the source producer proposes. The mapping drops the
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

-- The implication projection's order and its first duplicate make the
-- search deterministic: repeated destination slots keep each alias, which
-- the cached lookups of the quadratic projection must preserve.
#guard
  let xs : List (PromiseCalls.Implication Nat) :=
    [⟨1, 0, [5]⟩, ⟨1, 0, [99]⟩, ⟨0, 1, [7]⟩]
  (projectImplications xs (some [1, 0, 1]) 3).map (fun x => (x.test, x.target, x.type)) ==
    [(0, 1, [5]), (1, 0, [7]), (1, 2, [7]), (2, 1, [5])]

end Verification.DiagnosticControls
