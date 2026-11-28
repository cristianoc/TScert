import Verification.Source.ReplayCodec
import Verification.Source.GroupProjection

/-! Constructor encodings of the terms, facts and effects in a group key. -/
namespace Verification.ReplayKey
open Lean

variable {α β γ ι ε : Type} [Codec α] [Codec β] [Codec γ] [Codec ι] [Codec ε]

replay_codec PropKey for PropKey
replay_codec Change for Footprints.Change
replay_codec ArgumentSpineRegion for Footprints.ArgumentSpineRegion
replay_codec Closed for Footprints.Closed
replay_codec StatedEffect for EffectJson.StatedEffect
replay_codec SourcePoint for SourcePoint
replay_codec FragmentRead for SourceClaimJson.FragmentRead
replay_codec GroupImports for SourceClaimJson.GroupImports
replay_codec Except for Except ε α
replay_codec UnitRef for SourceClaimJson.UnitRef
replay_codec Exits for CallEffects.Exits α
replay_codec StandIn for SourceClaimJson.StandIn
replay_codec TermKind for HeapKnowledge.Term.Kind
instance : Codec HeapKnowledge.Term :=
  ⟨fun t => put (t.kind, t.slot, t.path, t.atEntry), fun j => do
    let (k, s, p, b) ← get j
    return if (b : Bool) then .old k s p else .now k s p,
   by intro t; simp [← HeapKnowledge.Term.eta]⟩
replay_codec IndexShift for HeapKnowledge.IndexShift
replay_codec ElemTarget for HeapKnowledge.ElemTarget
replay_codec GuardTag for HeapKnowledge.GuardTag
replay_codec Bound for HeapKnowledge.Bound
replay_codec Fact for Linear.Fact α
replay_codec LinearClause for HeapKnowledge.LinearClause α
replay_codec BodyClause for HeapKnowledge.BodyClause
replay_codec IndexBound for HeapKnowledge.IndexBound
replay_codec IndexFact for HeapKnowledge.IndexFact
replay_codec ElemPred for CallEffects.ElemPred
replay_codec TypePromise for CallEffects.TypePromise
replay_codec Selector for Footprints.Selector
replay_codec Region for Footprints.Region
replay_codec StepVar for HeapKnowledge.StepVar
replay_codec AssertionRef for Parity.AssertionRef
replay_codec ViewFormat for ViewFormat
replay_codec Arith for Arith
replay_codec Path for Parity.Path
replay_codec Phase for Parity.Phase
replay_codec Target for ControlFlow.Target
replay_codec Tag for Tag
replay_codec Continuation for ControlFlow.Continuation
replay_codec Invoke for Invoke
replay_codec Tm for CallCode, List Tm, Tm
replay_codec Witness for Parity.Witness
replay_codec WitnessSeq for Parity.WitnessSeq
replay_codec OperationPostF for Parity.OperationPostF α
replay_codec TransportSchema for Parity.TransportSchema
replay_codec FormulaF for Parity.FormulaF α β
replay_codec ExitSchema for CallEffects.ExitSchema
replay_codec Effect for CallEffects.Effect

end Verification.ReplayKey
