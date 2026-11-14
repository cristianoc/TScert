import Verification.Source.Claims.PassUnitInterfaces

/-! # The single pass's unit theorem: the initialization's postcondition

A module constant's or cell's slot (kind `moduleCell`) holds the value the
initialization unit (`:init`) binds. This module states what the `:init`
request's acceptance gives at its finish states (`init_asserted`, proved
from `RequestSafe`'s assertions clause) and the typed form of that
postcondition the slot's contract (`KindMet` at `moduleCell`) needs, which
stays a named hypothesis: docs/SINGLE-PASS-THEOREM.md, section 4, "H5b". -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **The initialization's assertions hold at its finish states** (proved):
where the `:init` request is safe and states the assertion `(l, K)` (a
finish node and the facts the walk types propose there), every state
reached at `l` within the budget, from every entry, at every admitted
assignment, satisfies `K`. -/
theorem init_asserted {r : SourceRequest σ ι} (hsafe : RequestSafe r) {l : Nat} {K : HeapKnowledge.Knowledge}
    (hk : (l, K) ∈ r.assertions) :
    ∀ η, r.Admits η → ∀ n W h ρ,
      EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices ρ n W h →
      (∀ node ∈ r.program, RefsOk W node.expression) → (∀ i, RefsOk W (ρ i)) →
      ∀ j h' ρ', j < n → ReachesIn r.program j h (.at r.start ρ) h' (.at l ρ') → HeapKnowledge.Holds K ⟨ρ, h⟩ ρ' h' :=
  fun η hη n W h ρ he hP hρ j h' ρ' hj hr => hsafe.2.2.2.2.1 η hη n W h ρ he hP hρ l K hk j h' ρ' hj hr

end

end Verification.SourceClaimJson.PassUnit
