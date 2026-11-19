import Verification.Source.Claims.FramedSpec
import Verification.Paper.TolerantFrames.ReadOnlyIncoming
import Verification.Paper.TolerantFrames.ReadOnlyLocalReach

/-! # The history of a framed plan's frame

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The history of a program"). The
frame a framed plan defines (`FramedSpec.frame`) crosses at each step its
entering step's arguments into `C`, then every value reaching outside code
out of `C` (`FramedSpec.chk`): its crossings are `ActualCrossingsIn` at the
entering step's crossings (`FramedSpec.actualCrossingsIn`), each of which
crosses into `C` (`FramedSpec.entryXs_into`), so the restated `ChkSound`
lemmas (`ClientFrame.chkSound_of_flowIn`) read it. -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly

namespace FramedSpec
variable {σ ι : Type} [Labels ι] [StoreView σ ι] (spec : FramedSpec ι)

/-- **The frame's crossings are the entering step's, then the actual ones**
(proved, by definition). -/
theorem actualCrossingsIn (r : SourceRequest σ ι) :
    (spec.frame r).ActualCrossingsIn spec.outType (fun _ t _ t' => spec.entryXs r t t') :=
  fun _ _ _ _ => rfl

/-- **Every crossing of an entering step crosses into `C`** (proved). -/
theorem entryXs_into (r : SourceRequest σ ι) {t t' : Tm} {c : Crossing spec.view.view}
    (hc : c ∈ spec.entryXs r t t') : c.dir = .into := by
  unfold entryXs at hc
  split at hc
  · split at hc <;> first
      | (simp only [List.mem_map] at hc; obtain ⟨_, -, rfl⟩ := hc; rfl)
      | cases hc
  · cases hc

/-- **The entering step's crossings are roots of outside code, or hold no
location** (proved, the draft's `entryXs_roots`, `redex_arg_root`): each is
an argument of the call the step reduces, in a frame of outside code. -/
theorem entryXs_roots (r : SourceRequest σ ι) :
    (spec.frame r).IncomingRoots (fun _ t _ t' => spec.entryXs r t t') := by
  intro a b _ _ _ c hc
  have hc : c ∈ spec.entryXs r a.1.t b.1.t := hc
  unfold entryXs at hc
  split at hc
  · rename_i hcond
    have hroot : ∀ f r' (args : List Tm), ((activeFrame none a.1.t).2 = .invoke f r' args ∨
        (activeFrame none a.1.t).2 = .construct f args) → c ∈ ((args.take spec.arity).zip (r.inputs.take spec.arity)).map
          (fun (v, T) => (⟨.into, T, v⟩ : Crossing spec.view.view)) →
        c.val ∈ rootsOf spec.F spec.C none a.1.t ∨ ∀ l, ¬ Leaves (spec.F.at spec.C).ofC c.val l := by
      intro f r' args hp hm
      obtain ⟨⟨v, T⟩, hvT, rfl⟩ := List.mem_map.mp hm
      exact redex_arg_root (ofC := spec.F.ofC spec.C) hcond.1 hp
        (List.mem_of_mem_take (List.of_mem_zip hvT).1)
    split at hc
    · rename_i f r' args heq; exact hroot f r' args (.inl heq) hc
    · rename_i f args heq; exact hroot f .undef args (.inr heq) hc
    · cases hc
  · cases hc

end FramedSpec
end Verification.SourceClaimJson
