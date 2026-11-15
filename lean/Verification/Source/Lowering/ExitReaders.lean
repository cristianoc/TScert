import Verification.Semantics.ExitSummaries

/-! # What proposals read of a signature's exits

Readers of a signature's specification schema (`Effect.schema`) that the
front's proposals use: each reads the schema's frame or postconditions, and
each is equal to the reading of the signature's fields it replaces on every
signature (proved), so a proposal computed through it is the same. -/
namespace Verification.SourceExtraction
open Verification Footprints CallEffects

/-- **The fields a frame's path regions read through one field**: for each
entry whose region is reached from a call position through the one field
`f` (`.path _ [f] _`), the field `f`. -/
def regionFields (Φ : Footprint) : List String :=
  Φ.filterMap fun e => match e.1 with
    | .path _ [f] _ => some f
    | _ => none

/-- **A signature's frame reads through the fields its store regions do**
(proved): the frame's class entries and receiver entries are no path
regions, and each argument store region is the path region of its path. -/
theorem regionFields_schema (e : Effect) :
    regionFields e.schema.normal.frame = e.regions.filterMap fun r => match r.path with
      | [f] => some f
      | _ => none := by
  have hr : regionFields e.receiverEntries = [] := by
    unfold Effect.receiverEntries
    split
    · rfl
    · split <;> rfl
  have hc : regionFields e.closed.fp = [] := rfl
  simp only [Effect.schema, Effect.frame, regionFields, List.filterMap_append] at hr hc ⊢
  rw [hr, hc, List.nil_append, List.nil_append, List.filterMap_map]
  congr 1
  funext r
  rcases r with ⟨pos, _ | ⟨f, _ | ⟨g, t⟩⟩⟩ <;> rfl

end Verification.SourceExtraction
