import Verification.Source.Claims.PassUnitInterfaces
import Verification.Types.StoreMaps

/-! # The single pass's unit theorem: signature agreement across two stores

An importer's slot reading an established entry is met where the two stores
agree on the entry's signature (`SignatureAgrees`). The module's store and
the importer's are two frozen equation stores, each with its own labels. A
store map from the module's graph to the importer's (`StoreMaps.StoreMap`)
on a region holding the entry's interface gives the agreement, both ways:
the interface renamed means in the importer's store what it means in the
module's (`StoreMaps.StoreMap.meaning_eq`). docs/drafts/pass-unit-theorem.md,
section 7. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean PositiveGraphs LabelStore StoreMaps

/-- **Signature agreement from a store map** (proved): where a store map from
the entry's module graph to the importer's graph has the interface's labels
in its region and the slot's type is a union of the interface's labels
renamed, the stores agree on the signature. -/
theorem signatureAgrees_of_storeMap {e : Entry} (src : EntryRealized e) {ι : Type} [Labels ι]
    {G : NormalGraph ι} (m : StoreMap (graphOf src.fm) G)
    (hD : ∀ j ∈ src.layout.iface src.unit, m.D j) {A : List ι}
    (hA : ∀ x, x ∈ A ↔ x ∈ (src.layout.iface src.unit).map m.φ) : SignatureAgrees src G A := by
  intro j V w hw
  rw [m.meaning_eq_of_mem hD hA]
  exact hw

end Verification.SourceClaimJson.PassUnit
