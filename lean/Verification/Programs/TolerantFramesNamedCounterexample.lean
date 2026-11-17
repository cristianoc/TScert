import Verification.Programs.TolerantFramesNamed
import Verification.Semantics.TolerantFrames

/-! # Tolerant frames: a fact the effect does not tolerate

A cell fact over a name is not framed by a writing effect
(`slotless_not_framed`): the counterexample to keeping, across a writing
step, a named fact the step is not handed. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom)

/-! ## A fact the effect does not tolerate

A fact over a name no slot holds is not handed to a step even when the step
reads every fact (`SinglePass.materialize` with `whole`: its renaming fails),
so `applyDelta` keeps it. Across a writing step nothing justifies it: a cell
fact of the object the name holds fails after an action of
`{values: any, spines: any}`. -/

/-- A state of one location holding `v`, at budget 1. -/
def oneState (v : Val) (hv : isVal v = true) (hs : isSourceVal v = true) (hn : refs v = []) : IndexedHeap :=
  ⟨1, ofEntries [(.field, anyCtr)], [v], Nat.one_pos,
    ⟨fun l c hl => by
      simp only [lookup, toList, entries_ofEntries] at hl
      rcases l with _ | l <;> simp at hl
      subst hl
      exact ⟨fun _ _ _ _ _ _ hv => hv, fun _ _ _ _ hv => hv⟩, fun l f N hr => by
      simp only [roleAt, roles, entries_ofEntries] at hr
      rcases l with _ | l <;> simp at hr⟩,
    ⟨⟨by simp, fun l c hl => by
      simp only [lookup, toList, entries_ofEntries] at hl
      rcases l with _ | l <;> simp at hl
      subst hl
      exact ⟨v, rfl, fun _ _ => hv⟩⟩,
    fun l r hl => by
      simp only [roleAt, roles, entries_ofEntries] at hl
      rcases l with _ | l <;> simp at hl
      subst hl
      exact ⟨v, rfl, hs, RefsOk_of_nil hn⟩⟩⟩

/-- **A cell fact over a name is not framed by a writing effect**: name 0
holds an object whose field `f` is location 0; the fact that the field holds
`null` holds before an action of `{values: any, spines: any}` and not after. -/
theorem slotless_not_framed :
    ¬ ∀ (η ρ : Env) (m : Nat) (s : IndexedHeap),
      Named ε [.cell ⟨0, { nul := true }, "f"⟩] η ρ m s →
        Box Footprints.Closed.top.fp (Named ε [.cell ⟨0, { nul := true }, "f"⟩] η) ρ m s := by
  intro H
  let η : Env := fun _ => .objAt [("f", 0)] .absent 0
  have hb := H η η 0 (oneState .nul rfl rfl rfl) (fun a ha => by
    simp only [List.mem_singleton] at ha; subst ha
    intro f hf; simp only [List.mem_singleton] at hf; subst hf
    exact ⟨[("f", 0)], .absent, 0, .nul, rfl, by simp [HeapFacts.ReadGave, oneState], by decide⟩)
  have ha : Action Footprints.Closed.top.fp η (oneState .nul rfl rfl rfl) (oneState .tru rfl rfl rfl) :=
    action_top ⟨Nat.le_refl 1, by
      show WExt (trunc 1 (Nat.le_refl 1) (ofEntries [(.field, anyCtr)])) (ofEntries [(.field, anyCtr)]); rw [trunc_id]; exact WExt_refl _⟩
  have := hb _ ha _ (List.mem_singleton_self _) _ (List.mem_singleton_self _)
  obtain ⟨flds, c, oid, u, he, hr, hm⟩ := this
  simp only [η, Tm.objAt.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  simp [HeapFacts.ReadGave, oneState] at hr
  subst hr
  exact absurd hm (by decide)

end Verification.TolerantFrames
