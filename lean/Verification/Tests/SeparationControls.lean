import Verification.Semantics.HeapSeparation

/-! The producer's join of separations (`HeapSeparation.meet`, untrusted) keeps
every pair each state justifies: a pair one state states of every own
location of its subject and another of one field survives as that field's
residual fact, in either order of the states, and so does a pair stated in
either orientation. No source case reaches these joins: the lowering states
its cells' facts at cuts, which take their assertions alone. -/
namespace Verification.Tests.SeparationControls
open Verification HeapSeparation

private def whole : Separation := ⟨2, [⟨1, none, [(0, ["g"])]⟩]⟩
private def residual : Separation := ⟨2, [⟨1, some ["f"], [(0, ["g"])]⟩]⟩
private def reversed : Separation := ⟨2, [⟨0, some ["g"], [(1, ["f"])]⟩]⟩
private def twoFields : Separation := ⟨2, [⟨1, some ["f", "h"], [(0, ["g"])]⟩]⟩

#guard meet [whole, residual] == residual
#guard meet [residual, whole] == residual
#guard meet [whole, whole] == whole
#guard meet [residual, reversed] == residual
#guard meet [twoFields, residual] == residual
#guard meet [whole, reversed] == residual
-- Different depths, or a state stating nothing, share nothing.
#guard meet [whole, ⟨3, whole.facts⟩] == {}
#guard meet [whole, {}] == {}

end Verification.Tests.SeparationControls
