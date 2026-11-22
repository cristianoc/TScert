import Verification.Programs.CertificateProducer
import Verification.Semantics.ExitComposition

/-! A worklist proposes entry footprints and exit footprints. Reading its
result once validates the entry and both exits of each reachable node. -/

namespace Verification.SourceClaimJson.CallbackEffectInference
open ControlFlow CallEffects Footprints CertificateProducer HeapObservations

abbrev Summary := Exits (Option Footprint)

abbrev Entries := Array (Option Footprint)

private def pointsTo (node : Node) (exit : Completion) : List (Option Nat) :=
  match exit with
  | .normal => if node.continuation == .ret then [none]
    else (successors node.continuation).map (some ∘ Target.label)
  | .exceptional => [node.handler.map Target.label]

private def boundAt (entries : Entries) (out : Summary) (exit : Completion) : Option Nat → Option Footprint
  | none => out.get exit
  | some l => entries.getD l none

private def checkFlowExit (entries : Entries) (out : Summary) (node : Node) (prior : Footprint)
    (ls : Summary) (exit : Completion) : Bool :=
  match ls.get exit with
  | none => true
  | some writes => (pointsTo node exit).all fun dest =>
    (boundAt entries out exit dest).any fun bound => (prior ++ writes).all bound.contains

private def checkFlowAt (nodes : Array Node) (locals : Array (Option Summary))
    (entries : Entries) (out : Summary) (l : Nat) : Bool :=
  match entries.getD l none with
  | none => true
  | some prior =>
    match nodes[l]?, locals.getD l none with
    | some node, some ls =>
      checkFlowExit entries out node prior ls .normal && checkFlowExit entries out node prior ls .exceptional
    | _, _ => false

def checkFlow (P : Program) (start : Nat) (locals : Array (Option Summary))
    (entries : Entries) (out : Summary) : Bool :=
  start < P.length && (entries.getD start none).isSome &&
    (List.range P.length).all (checkFlowAt P.toArray locals entries out)

end Verification.SourceClaimJson.CallbackEffectInference
