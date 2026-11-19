import Verification.Source.Claims.FlowProbe

/-! Controls for the flow probe's protocol (`SourceClaimJson.probeProtocol`):
each counter-model a review found against an earlier reading of the
protocol is a check here that the part it changes is charged, and that the
frame's check at a call (`frameCheckAt`) then refuses a fact whose support
lies at that part. A protocol read back to the earlier form fails here.

- **A spine replaced through the spine key**: a write at the spine key
  (`writeAt arraySpineKey x (arr [])`, the form of the lowering's array
  update) changes the receiver's spine arbitrarily, as `Step.writeField`
  does; the earlier reading charged a write's key to a field only.
- **A local cursor written through a capture**: a closure of the
  component's code that captures a local cursor and writes its field
  (`setter(c)` returning `() => { c.i = 1 }`, given to outside code that
  calls it) changes a location of a local site existing at the call; the
  earlier reading kept every part of a local site. -/
namespace Verification.SourceClaimJson.FlowProbeControls
open Verification TolerantFrames.ReadOnly Footprints

/-- The component `0`, outside code seeing outside storage only: site `0`
is local. -/
private abbrev Pk : TolerantFrames.ReadOnly.Package := markedPackage (some 0) [none]

private def F0 : FFlow Pk := ⟨[none], [], []⟩

/-! ## A spine replaced through the spine key -/

/-- The writes of `writeAt arraySpineKey (var 0) (arr [])`, slot `0` holding
outside storage. -/
private def spineWrites : List (Sites Pk × List (Option Kind)) :=
  writesIn F0 (fun _ => [none]) (fun _ => none) FrameAt.outside entryCx 0 (fun _ => none)
    (.writeAt arraySpineKey (.var 0) (.arr []))

#guard probeProtocol spineWrites [] ⟨none, some .spine, none⟩ = .any
-- the spine key's slot is the spine: the receiver's fields are kept
#guard probeProtocol spineWrites [] ⟨none, some .field, none⟩ = .keep

-- `i + 1 ≤ xs.length` across a call, `xs` in slot `0`: its spine at `grow`,
-- refused
#guard frameCheckAt classQuery (probeProtocol spineWrites []) [] [(.spine 0 [], .grow)] F0.flow.H
  (fun _ => [none]) noKeys (fun _ => false) = false

/-! ## A local cursor written through a capture -/

/-- The writes of the closure's body `c.i = 1`, its capture slot `1`
holding the local site `0`. -/
private def setterWrites : List (Sites Pk × List (Option Kind)) :=
  writesIn F0 (fun i => if i = 1 then [some 0] else [none]) (fun _ => none) FrameAt.outside entryCx 0 (fun _ => none)
    (.writeAt (.str "i") (.var 1) (.num 1))

-- a capture may hold the site: its field is charged
#guard probeProtocol setterWrites [some 0] ⟨some 0, some .field, none⟩ = .any
-- no capture may hold the site: kept
#guard probeProtocol setterWrites [] ⟨some 0, some .field, none⟩ = .keep

-- `0 ≤ c.i` across a call, `c` in slot `0` of the local site `0`, its field
-- captured: refused
#guard frameCheckAt classQuery (probeProtocol setterWrites [some 0]) [] [(.field 0 (.str "i"), .keep)] F0.flow.H
  (fun _ => [some 0]) noKeys (fun _ => false) = false

end Verification.SourceClaimJson.FlowProbeControls
