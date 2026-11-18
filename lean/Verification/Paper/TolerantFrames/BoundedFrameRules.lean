import Verification.Paper.TolerantFrames.BoundedCommands

/-! # Framing and entry for execution-count bounded body proofs

These are the existing semantic rules with an independent bound on completed
primitive execution. The chosen world, scope premises and regional effects are
unchanged. Unbounded primitive/return rules can also be lifted with Triple.below.
-/
namespace Verification.Paper.TolerantFrames.Bounded
open Verification Footprints HeapKnowledge HeapObservations TolerantFrames

/-- Entry with arbitrary old assertions and both regional exit effects. -/
theorem entry_rule {N host P c Q Qe J Ret Φ Φe} (B : Assertion)
    (ht : TripleBelow N host P c Q Qe J Ret) (he : EffectsBelow N host P c Φ Φe) :
    TripleBelow N host (fun ρ m s => P ρ m s ∧ B ρ m s) c
      (PostAnd Q (PostAnd (Old B) (Transition Φ)))
      (PostAnd Qe (PostAnd (Old B) (Transition Φe))) J Ret := by
  intro ρ m s n ρ' h' e hv ⟨hp, hb⟩ hr hn hN
  obtain ⟨t, ha, hh, hk, hvt, hve, hq⟩ := ht ρ m s n ρ' h' e hv hp hr hn hN
  have hφ := he ρ m s n ρ' h' e hv hp hr hn hN
  refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
  cases e with
  | normal => exact ⟨hq, hb, ha, hh ▸ hφ⟩
  | thrown _ => exact ⟨hq, hb, ha, hh ▸ hφ⟩
  | «break» => exact hq
  | returned _ => exact hq

/-- Frame, both exits, with exactly the binding-scope transport needed by
fresh variables. Neither R nor its effects may capture a command's new name. -/
theorem frame_rule {N host P c Q Qe J Ret Φ Φe} {R Re : Assertion}
    (ht : TripleBelow N host P c Q Qe J Ret) (he : EffectsBelow N host P c Φ Φe)
    (hs : ScopeStable host c R) (hse : ScopeStable host c Re) :
    TripleBelow N host (fun ρ m s => P ρ m s ∧ Box Φ R ρ m s ∧ Box Φe Re ρ m s) c
      (PostAnd Q (Now R)) (PostAnd Qe (Now Re)) J Ret := by
  intro ρ m s n ρ' h' e hv ⟨hp, hb, hbe⟩ hr hn hN
  obtain ⟨t, ha, hh, hk, hvt, hve, hq⟩ := ht ρ m s n ρ' h' e hv hp hr hn hN
  have hφ := he ρ m s n ρ' h' e hv hp hr hn hN
  refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
  cases e with
  | normal => exact ⟨hq, (hs _ _ _ _ _ _ hr m t).mp (hb t ⟨ha, hh ▸ hφ⟩)⟩
  | thrown _ => exact ⟨hq, (hse _ _ _ _ _ _ hr m t).mp (hbe t ⟨ha, hh ▸ hφ⟩)⟩
  | «break» => exact hq
  | returned _ => exact hq

/-- Frame+ retains the box using semantic rigidity, not a finite rigidity
certificate. The box's binding-scope obligation covers its effect as well. -/
theorem frame_plus_rule {N host P c Q Qe J Ret Φ Φe} {R : Assertion}
    (ht : TripleBelow N host P c Q Qe J Ret) (he : EffectsBelow N host P c Φ Φe)
    (hs : ScopeStable host c (Box Φ R)) (hrigid : RigidOn Φ) :
    TripleBelow N host (fun ρ m s => P ρ m s ∧ Box Φ R ρ m s) c
      (PostAnd Q (Now (Box Φ R))) Qe J Ret := by
  intro ρ m s n ρ' h' e hv ⟨hp, hb⟩ hr hn hN
  obtain ⟨t, ha, hh, hk, hvt, hve, hq⟩ := ht ρ m s n ρ' h' e hv hp hr hn hN
  have hφ := he ρ m s n ρ' h' e hv hp hr hn hN
  refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
  cases e with
  | normal => exact ⟨hq, (hs _ _ _ _ _ _ hr m t).mp
      (box_idem_on hrigid ρ m s hv.heap hb t ⟨ha, hh ▸ hφ⟩)⟩
  | thrown _ => exact hq
  | «break» => exact hq
  | returned _ => exact hq

/-- Loop of §6. The break obligation is I ∧ box R, as the displayed rule's
explanation requires. R and Φ cannot mention loop-carried or freshly bound
names, expressed by the scope premise and derivable by `scope_stable_of_avoids`.
The effect and rigidity premises are semantic, not finite certificates. -/
theorem loop_rule {N : Nat} {host : NativeCode} {b : Command} {I E R : Assertion} {Ret : Val → Assertion}
    {Φ Φe : Footprint}
    (hb : StateTripleBelow N host (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) b I E
      (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) Ret)
    (he : EffectsBelow N host (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) b Φ Φe)
    (hs : ScopeStable host b (Box Φ R)) (hΦ : RigidOn Φ) :
    StateTripleBelow N host (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) (.loop b)
      (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) E
      (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) Ret := by
  apply loop_invariant
  intro ρ m s n ρ' h' e hv hp hr hn hN
  obtain ⟨t, ha, hh, hk, hvt, hve, hq⟩ := hb _ _ _ _ _ _ _ hv hp hr hn hN
  have hφ := he _ _ _ _ _ _ _ hv hp hr hn hN
  refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
  cases e with
  | normal => exact ⟨hq, (hs _ _ _ _ _ _ hr m t).mp
      (box_idem_on hΦ ρ m s hv.heap hp.2 t ⟨ha, hh ▸ hφ⟩)⟩
  | «break» => exact hq
  | returned _ => exact hq
  | thrown _ => exact hq

end Verification.Paper.TolerantFrames.Bounded
