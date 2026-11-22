import Verification.Source.Claims.CallbackOrigins

namespace Verification.SourceClaimJson.CallbackOrigins
open ControlFlow CertificateProducer GraphCode

/-- A slot without this allocation among its possible origins may be
substituted into an expression that must not publish the allocation. -/
def excludes (site : Nat) (slots : Slots) (i : Nat) : Bool :=
  slots[i]?.any fun origins => !origins.contains (.allocated site)

def cleanReads (site : Nat) (slots : Slots) (t : Tm) :=
  (SinglePass.mentioned 0 t).any fun ids => ids.all (excludes site slots)

def privateUse (site : Nat) (slots : Slots) : Tm → Bool
  | .var i | .readAt _ (.var i) => i < slots.size
  | .writeAt _ (.var i) rhs => i < slots.size && cleanReads site slots rhs
  | t => cleanReads site slots t

def resultClean (site label : Nat) (slots : Slots) : Tm → Bool
  | .var i => excludes site slots i
  | _ => !(site == label)

def privateReady (nodes : Array Node) (table : Table) (l : Nat) : Bool :=
  nodes.size ≤ l || table[l]?.join.isSome

def cleanEdge (nodes : Array Node) (site : Nat) (table : Table) (valid source : Nat → Bool) (target : Target) :=
  let dst := table.at target.label
  privateReady nodes table target.label && (List.range dst.size).all fun i =>
    let j := PointClaims.slot target.mapping i
    valid j && (!excludes site dst i || source j)

def afterSlot (slots : Nat → Bool) (pushed fresh : Bool) (i : Nat) : Bool :=
  if pushed then match i with | 0 => fresh | j+1 => slots j else slots i

/-- Check the may-origin transfer for names the escape scan keeps as
private, on both normal and caught exits. Missing guidance grants no
exclusion. A local field read or write may hold the private receiver. -/
def checkPrivateSite (nodes : Array Node) (table : Table) (site : Nat) : Bool :=
  (List.range nodes.size).all fun label =>
    match table[label]?.join with
    | none => true
    | some slots =>
      let node := nodes[label]!
      let clean := excludes site slots
      let valid := fun i => decide (i < slots.size)
      privateUse site slots node.expression &&
        (successors node.continuation).all (cleanEdge nodes site table (afterSlot valid (pushes node.continuation) true)
          (afterSlot clean (pushes node.continuation) (resultClean site label slots node.expression))) &&
        node.handler.toList.all (cleanEdge nodes site table (afterSlot valid true true) (afterSlot clean true true))

def certifiedPrivate (nodes : Array Node) (table : Table) (proposed : List Nat) : List Nat :=
  proposed.filter (checkPrivateSite nodes table)

end Verification.SourceClaimJson.CallbackOrigins
