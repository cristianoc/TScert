import Verification.Semantics.HeapLinks

/-! The link check compares alias classes after mapping: an alias stated in
either orientation, implied by two others, or through a mapping swapping its
slots holds; a read holds through an alias of its receiver or of its value,
and one that found the field holds where the target's may not.
No source case is shown to meet these forms. -/
namespace Verification.Tests.LinkControls
open Verification HeapLinks

private def al (c v : Nat) : Link := ⟨c, v, true, valueField, false⟩
private def rd (c v : Nat) (f : String) : Link := ⟨c, v, false, .str f, false⟩

#guard check [al 0 1] [al 1 0] none
#guard check [al 0 1] [al 0 1] (some [1, 0])
#guard check [al 0 1, al 1 2] [al 0 2] none
-- An alias's ignored fields do not distinguish it.
#guard check [al 0 1] [⟨0, 1, true, .str "f", true⟩] none
#guard check [rd 0 2 "f", al 0 1] [rd 1 2 "f"] none
#guard check [rd 0 2 "f", al 2 3] [rd 0 3 "f"] none
-- Distinct classes or another field do not hold.
#guard !check [al 0 1] [al 0 2] none
#guard !check [rd 0 2 "f"] [rd 1 2 "f"] none
#guard !check [rd 0 2 "f"] [rd 0 2 "g"] none
-- A read that found the field justifies one that may not, not the reverse.
#guard check [rd 0 2 "f"] [⟨0, 2, false, .str "f", true⟩] none
#guard !check [⟨0, 2, false, .str "f", true⟩] [rd 0 2 "f"] none
#guard !check [rd 0 2 "f"] [al 0 2] none

end Verification.Tests.LinkControls
