import Verification.Programs.LinkAssembly
import Verification.Source.PrimitiveAttachment
import Verification.Types.GraphRows
import Verification.Source.EvidenceWire

/-! Forged serialized assembly controls exercise the structural boundary.
Body certification is a separate input to the structural checker; these
controls supply an affirmative test hook and make no code-safety claim.
-/
namespace Verification.Linking.AssemblyControls
open RequestJson Lean PositiveGraphs PositiveNormalization ProgramTyping CallEffects

private def row : Arrow (Ty Nat) := ⟨[1], [], [0], .ordinary⟩

private def graph : NormalGraph Nat := NormalGraph.ofRowMap fun
  | 0 => .clauses [.num]
  | 1 => .clauses [.source]
  | 2 => .clauses [.arrs [row] []]
  | _ => .clauses [.str]

private def leaf : Export Nat := {
  graph, signature := [2], arity := 0, expressions := [.num 0]
  continuations := [(.ret, none)], start := 0, captureTypes := [], captures := []
  fields := [], identity := 0, kind := .call, arrows := [row], rests := [] }

private def parent : Export Nat := { leaf with
  identity := 1, captureTypes := [[2]], captures := [leaf.value]
  expressions := [.invoke (.var 1) .undef []] }

private def exports (i : Fin 2) : Export Nat := if i.val = 0 then leaf else parent

private def good : Assembly.Data := ⟨[0,1], [[], [some 0]]⟩

/-- Every control crosses the JSON decoder, as a forged assembly document does. -/
private def checked (data : Assembly.Data) : Bool :=
  match (decodeStrict "assembly" (toJson data) : Except String Assembly.Data) with
  | .error _ => false
  | .ok a => Assembly.check graph exports a (fun _ => true)

-- Positive structure, then wrong target, nondecreasing rank and an internal
-- function capture labeled external. None of these alters a source fixture.
#guard checked good
#guard !checked { good with slots := [[], [some 1]] }
#guard !checked { good with ranks := [1,0] }
#guard !checked { good with slots := [[], [none]] }

private def signature : PrimitiveBoundary.Signature := ⟨[], .number, .ordinary⟩

#guard PrimitiveBoundary.attachmentCheck graph [2] signature
-- The claimed attachment points at the string row, rather than the arrow.
#guard !PrimitiveBoundary.attachmentCheck graph [3] signature

end Verification.Linking.AssemblyControls
