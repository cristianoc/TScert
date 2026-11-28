import Verification.Source.ReplayEffectCodec
import Verification.Source.ReplayText

/-! The exact key of a group operation, with one line per lower proposal. -/
namespace Verification.ReplayKey
open Lean

variable {α β γ ι ε : Type} [Codec α] [Codec β] [Codec γ] [Codec ι] [Codec ε]

replay_codec Contract for CallEffects.Contract α β γ
replay_codec StorageRole for StorageRole
replay_codec PUnit for PUnit
replay_codec IndexKeys for IndexKeys
replay_codec Sig for MethodMembers.Sig α
replay_codec OptionalField for OptionalField α
replay_codec ArrayPresence for ArrayPresence
replay_codec Tuple for PositiveNormalization.Tuple α
replay_codec KeyBound for KeyBound
replay_codec Clause for PositiveNormalization.Clause α
replay_codec ResolutionSlots for PositiveGraphs.ResolutionSlots
replay_codec ParameterKind for PositiveGraphs.ParameterKind
replay_codec GraphRow for PositiveGraphs.GraphRow ι α
replay_codec ArrayBuiltins for PositiveGraphs.ArrayBuiltins ι
replay_codec RowTable for SourceClaimJson.RowTable
replay_codec Tree for EquationGraphs.Types, EquationGraphs.Args, EquationGraphs.Tree
replay_codec Binder for EquationGraphs.Binder
replay_codec HeadKind for EquationLowering.HeadKind
replay_codec Draft for EquationLowering.Draft
replay_codec BindingKind for GroupProjection.BindingKind
replay_codec BindingEnvironment for GroupProjection.BindingEnvironment
replay_codec ImplicitDependency for EquationLowering.ImplicitDependency
replay_codec MissingReads for GroupProjection.MissingReads
replay_codec SearchBudget for PositiveCertificates.SearchBudget
replay_codec Slice for GroupProjection.Slice

end Verification.ReplayKey

namespace Verification.GroupProjection

def Slice.wire (s : Slice) : String :=
  let header := ReplayText.encode (ReplayKey.put {s with below := []})
  String.intercalate "\n" (header :: s.below.map fun a => ReplayText.encode (ReplayKey.put a))

private def decodeField [ReplayKey.Codec α] (cs : List Char) : Except String α := do
  let j ← ReplayText.decode (String.ofList cs)
  let some x := ReplayKey.get j | throw "invalid slice field"
  return x

private theorem decodeField_put [ReplayKey.Codec α] (x : α) :
    decodeField (ReplayText.encode (ReplayKey.put x)).toList = .ok x := by
  simp [decodeField, EffectCodec.ok_bind]

def Slice.decode (wire : String) : Except String Slice := do
  let header :: proposals := wire.toList.splitOn '\n' | throw "missing slice program"
  let s : Slice ← decodeField header
  let below ← proposals.mapM decodeField
  return {s with below}

theorem Slice.decode_wire (s : Slice) : Slice.decode s.wire = .ok s := by
  let line := fun (x : String × Option SourceClaimJson.StandIn) => ReplayText.encode (ReplayKey.put x)
  let header := ReplayText.encode (ReplayKey.put {s with below := []})
  have hx : ∀ cs ∈ header.toList :: s.below.map (fun x => (line x).toList), '\n' ∉ cs := by
    intro cs hm
    rcases List.mem_cons.mp hm with rfl | h
    · exact ReplayText.encode_no_lf _
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp h; exact ReplayText.encode_no_lf _
  have hsplit : s.wire.toList.splitOn '\n' = header.toList :: s.below.map (fun x => (line x).toList) := by
    simp only [Slice.wire, String.toList_intercalate, List.map_cons, List.map_map, Function.comp_def]
    exact List.splitOn_intercalate '\n' hx (by simp)
  rw [Slice.decode, hsplit]
  have hmap (xs : List (String × Option SourceClaimJson.StandIn)) :
      (xs.map (fun x => (line x).toList)).mapM decodeField = Except.ok xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [line, List.mapM_cons, decodeField_put, ih, EffectCodec.ok_bind, EffectCodec.pure_ok]
  simp only [header, decodeField_put, EffectCodec.ok_bind, hmap, EffectCodec.pure_ok]

theorem Slice.wire_injective {s t : Slice} (h : s.wire = t.wire) : s = t :=
  Except.ok.inj (s.decode_wire.symm.trans ((congrArg Slice.decode h).trans t.decode_wire))

end Verification.GroupProjection
