import Verification.Source.Claims.CallbackAllocationSites
import Verification.Source.Claims.RegionInference

/-! Provenance for a lowered callback invocation. The join keeps every
possible origin. A single origin is required to name an interface location;
all origins are inspected when checking whether an allocation escapes. -/
namespace Verification.SourceClaimJson.CallbackOrigins
open ControlFlow

inductive Origin where
  | input (slot : Nat)
  | allocated (label : Nat)
  | read (label : Nat)
  | other
  deriving BEq, DecidableEq, Repr, ReflBEq, LawfulBEq

abbrev Slots := Array (List Origin)
abbrev Table := Array (Option Slots)

def Table.at (table : Table) (label : Nat) : Slots := (table.getD label none).getD #[]

def allocates : Tm → Bool
  | .makeAt .. | .arrLit .. | .merge .. | .makeKey .. => true
  | .letE _ body => allocates body
  | _ => false

private def result (slots : Slots) (label : Nat) : Tm → List Origin
  | .var j => slots.getD j [.other]
  | .readAt _ (.var _) => [.read label]
  | term => if allocates term then [.allocated label] else [.other]

/-- The control-flow maps are the same maps the checking pass consumes.
An exceptional edge pushes the thrown value, whose origin is unknown. -/
def infer (nodes : Program) (widths : Array Nat) (start inputs : Nat) : Option Table := do
  let initial : Slots := ((List.range inputs).map fun j => [Origin.input j]).toArray
  let entries := (Array.replicate nodes.length none).setIfInBounds start (some initial)
  let graph := (nodes.map (·, ())).zipIdx
  let step := fun (((node, _), l) : (Node × Unit) × Nat) (table : Table) => Id.run do
    let some slots := table.getD l none | return table
    let out := if GraphCode.pushes node.continuation then
      #[result slots l node.expression] ++ slots else slots
    let edge := fun (t : Target) (source : Slots) (state : Table) =>
      let incoming := ((List.range (widths.getD t.label 0)).map fun slot =>
        source.getD (PointClaims.slot t.mapping slot) [.other]).toArray
      state.modify t.label fun old => some (match old with
        | none => incoming
        | some previous => (Array.zipWith (fun a b => (a ++ b).eraseDups) previous incoming))
    let normal := (CertificateProducer.successors node.continuation).foldl
      (fun state t => edge t out state) table
    return match node.handler with
      | some t => edge t (#[[.other]] ++ slots) normal
      | none => normal
  let limit := (inputs + nodes.length + 2) * (widths.foldl max 0 + 1)
  graphWorklist graph step (fun table l => table.getD l none) limit entries

/-- Repeated allocations cannot name a single object across a closure's
capture and a later call. Retain the other origin information at joins. -/
def nameable (allowed : Array Bool) (table : Table) : Table :=
  table.map fun row => row.map fun slots => slots.map fun origins => origins.map fun origin =>
    match origin with
    | .allocated l => if allowed.getD l false then origin else .other
    | value => value

/-- Only singleton input and allocation origins name values. Other entries
carry no equality obligation in the caller's execution history. -/
def namedAt (slots : Slots) (i : Nat) : Option Origin :=
  match slots[i]? with
  | some [.input j] => some (.input j)
  | some [.allocated l] => some (.allocated l)
  | _ => none

def namedResult (allowed : Array Bool) (slots : Slots) (l : Nat) (t : Tm) : Option Origin :=
  match t with
  | .var i => namedAt slots i
  | _ => if allowed.getD l false && allocates t then some (.allocated l) else none

def sourceName (slots : Slots) (pushed : Bool) (value : Option Origin) (i : Nat) : Option Origin :=
  if pushed then match i with
    | 0 => value
    | j+1 => namedAt slots j
  else namedAt slots i

def checkNameEdge (table : Table) (src : Nat → Option Origin) (target : Target) : Bool :=
  let dst := table.at target.label
  (List.range dst.size).all fun i => (namedAt dst i).all fun o =>
    src (PointClaims.slot target.mapping i) == some o

def checkNames (nodes : Array Node) (allowed : Array Bool) (start inputs : Nat) (table : Table) : Bool :=
  let initial := table.at start
  (table[start]?.join.isSome || nodes.size ≤ start) && (List.range initial.size).all (fun i => (namedAt initial i).all fun o => i < inputs && o == .input i) &&
    (List.range nodes.size).all fun l =>
      match table[l]?.join with
      | none => true
      | some slots =>
        let node := nodes[l]!
        let normal := sourceName slots (GraphCode.pushes node.continuation) (namedResult allowed slots l node.expression)
        let edge := fun src (t : Target) => (table[t.label]?.join.isSome || nodes.size ≤ t.label) &&
          checkNameEdge table src t
        (CertificateProducer.successors node.continuation).all (edge normal) &&
          node.handler.toList.all (edge (sourceName slots true none))

/-- An allocation is private if its value is used only by copying it or
accessing its own fields. The receiver of a field write stays private, but
storing the allocation as the written value exposes it. Returning a copy
also exposes it. Unknown operations conservatively expose their operands. -/
def privateAllocations (nodes : Program) (table : Table) : List Nat := Id.run do
  let mut allocations : List Nat := []
  let mut exposed : List Nat := []
  for (node, label) in nodes.zipIdx do
    let some slots := table.getD label none | continue
    if (result slots label node.expression).contains (.allocated label) then
      allocations := label :: allocations
    let readSlots := match node.expression with
      | .var j => if node.continuation == Continuation.ret then some [j] else some []
      | .readAt _ (.var _) => some []
      | .writeAt _ (.var _) value => SinglePass.mentioned 0 value
      | term => SinglePass.mentioned 0 term
    let values := match readSlots with
      | some js => js.flatMap (slots.getD · [])
      | none => slots.toList.flatten
    exposed := values.foldl (fun seen o => match o with | Origin.allocated a => a :: seen | _ => seen) exposed
  return allocations.filter (!exposed.contains ·)

def entryRoot (slots : Slots) (slot : Nat) : Option (Nat × List String) :=
  match slots[slot]? with
  | some [.input entry] => some (entry, [])
  | _ => none

end Verification.SourceClaimJson.CallbackOrigins
