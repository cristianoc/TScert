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
  earlier reading kept every part of a local site.
- **Storage reached through another closure's capture**
  (`nested-capture.mjs` of the framed acceptance draft's reviews): a
  wrapper captures `bump`, `bump` captures `holder`, and the changed field
  is at `holder.child`'s site; the closure of sites (`capClose`) reaches it
  through the wrapper's capture of `bump`'s token, `bump`'s capture of
  `holder` and `holder`'s contents, so the depth charges (`depthCharges`)
  charge it. A closure read at the capture slots' own sites alone keeps
  it. A closure check (`capClosedB`) passes the computed closure and
  refuses a set missing a site the closure reaches. -/
namespace Verification.SourceClaimJson.FlowProbeControls
open Verification TolerantFrames.ReadOnly Footprints

/-- The component `0`, outside code seeing outside storage only: site `0`
is local. -/
private abbrev Pk : TolerantFrames.ReadOnly.Package := markedPackage (· == some 0) [none]

private def F0 : FFlow Pk := { O := [none], heap := [], codes := [] }

/-! ## A spine replaced through the spine key -/

/-- The charges of the write `writeAt arraySpineKey (var 0) (arr [])`. -/
private def spineWrites : List Charge :=
  writesK (.writeAt arraySpineKey (.var 0) (.arr []))

#guard probeProtocol (P := Pk) spineWrites [] ⟨none, some .spine, none⟩ = .any
-- the spine key's slot is the spine: the receiver's fields are kept
#guard probeProtocol (P := Pk) spineWrites [] ⟨none, some .field, none⟩ = .keep

-- `i + 1 ≤ xs.length` across a call, `xs` in slot `0`: its spine at `grow`,
-- refused
#guard frameCheckAt classQuery (probeProtocol (P := Pk) spineWrites []) [] [(.spine 0 [], .grow)] F0.flow.H
  (fun _ => [none]) (fun _ => false) = false

/-! ## A local cursor written through a capture -/

/-- The charges of the closure's body `c.i = 1`. -/
private def setterWrites : List Charge :=
  writesK (.writeAt (.str "i") (.var 1) (.num 1))

-- a capture may hold the site: its field is charged
#guard probeProtocol (P := Pk) setterWrites [some 0] ⟨some 0, some .field, some (.str "i")⟩ = .any
-- its field at another key: kept
#guard probeProtocol (P := Pk) setterWrites [some 0] ⟨some 0, some .field, some (.str "j")⟩ = .keep
-- no capture may hold the site: kept
#guard probeProtocol (P := Pk) setterWrites [] ⟨some 0, some .field, some (.str "i")⟩ = .keep

-- `0 ≤ c.i` across a call, `c` in slot `0` of the local site `0`, its field
-- captured: refused
#guard frameCheckAt classQuery (probeProtocol (P := Pk) setterWrites [some 0]) [] [(.field 0 (.str "i"), .keep)] F0.flow.H
  (fun _ => [some 0]) (fun _ => false) = false

/-! ## Storage reached through another closure's capture -/

/-- `holder` at the local site `1`, holding `child` at the local site `2`. -/
private def F1 : FFlow Pk := { O := [none], heap := [(some 1, [some 2])], codes := [] }

/-- The capture sites a token stands for: the wrapper's token `4` captures
`bump`'s token `3`, which captures `holder`. -/
private def caps1 : Option Nat → Sites Pk
  | some 4 => [some 3]
  | some 3 => [some 1]
  | _ => []

-- the reach of the wrapper's call holds `holder.child`'s site
#guard (capClose F1 caps1 [some 4]).contains (some 2)
-- without captures, only the call's own sets
#guard !(capClose F1 (fun _ => []) [some 4]).contains (some 2)
-- the computed closure passes the closure check; a set missing `holder`'s
-- contents fails it
#guard capClosedB F1 caps1 [some 4] (capClose F1 caps1 [some 4])
#guard !capClosedB F1 caps1 [some 4] [some 4, some 3, some 1]
#guard !capClosedB F1 caps1 [some 4] [some 3, some 1, some 2]

/-- The charges of `bump`'s write `holder.child.i++`. -/
private def bumpWrites : List Charge := writesK (.writeAt (.str "i") (.readAt (.str "child") (.var 0)) (.num 1))

-- charged within the call's reach, kept outside it
#guard probeProtocol (P := Pk) bumpWrites (capClose F1 caps1 [some 4]) ⟨some 2, some .field, some (.str "i")⟩ = .any
#guard probeProtocol (P := Pk) bumpWrites [some 4, some 3, some 1] ⟨some 2, some .field, some (.str "i")⟩ = .keep

end Verification.SourceClaimJson.FlowProbeControls
