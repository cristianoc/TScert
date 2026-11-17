import Verification.Paper.TolerantFrames.Commands

/-! # Command rules over arbitrary assertions

This extends `Triple`, `Effects`, and the shared action. The finite arena's
certificates are not premises of these rules. Bindings of commands use fresh
names: `ScopeStable` states precisely the scope obligation for a framed formula,
which must be discharged by the caller's syntax/scope proof.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations
open Verification.TolerantFrames

/-- An assertion's existing variables are unchanged by a command's bindings.
This concerns only the valuation, not the heap; the formula is evaluated in
any chosen admissible exit world. -/
def ScopeStable (host : NativeCode) (c : Command) (F : Assertion) : Prop :=
  ∀ ρ h n ρ' h' e, Executes host c ρ h n ρ' h' e → ∀ m t, F ρ m t ↔ F ρ' m t

/-- Entry with arbitrary old assertions and both regional exit effects. -/
theorem entry_rule {host P c Q Qe J Ret Φ Φe} (B : Assertion)
    (ht : Triple host P c Q Qe J Ret) (he : Effects host P c Φ Φe) :
    Triple host (fun ρ m s => P ρ m s ∧ B ρ m s) c
      (PostAnd Q (PostAnd (Old B) (Transition Φ)))
      (PostAnd Qe (PostAnd (Old B) (Transition Φe))) J Ret := by
  intro ρ m s n ρ' h' e hv ⟨hp, hb⟩ hr hn
  obtain ⟨t, ha, hh, hk, hvt, hve, hq⟩ := ht ρ m s n ρ' h' e hv hp hr hn
  have hφ := he ρ m s n ρ' h' e hv hp hr hn
  refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
  cases e with
  | normal => exact ⟨hq, hb, ha, hh ▸ hφ⟩
  | thrown _ => exact ⟨hq, hb, ha, hh ▸ hφ⟩
  | «break» => exact hq
  | returned _ => exact hq

/-- Frame, both exits, with exactly the binding-scope transport needed by
fresh variables. Neither R nor its effects may capture a command's new name. -/
theorem frame_rule {host P c Q Qe J Ret Φ Φe} {R Re : Assertion}
    (ht : Triple host P c Q Qe J Ret) (he : Effects host P c Φ Φe)
    (hs : ScopeStable host c R) (hse : ScopeStable host c Re) :
    Triple host (fun ρ m s => P ρ m s ∧ Box Φ R ρ m s ∧ Box Φe Re ρ m s) c
      (PostAnd Q (Now R)) (PostAnd Qe (Now Re)) J Ret := by
  intro ρ m s n ρ' h' e hv ⟨hp, hb, hbe⟩ hr hn
  obtain ⟨t, ha, hh, hk, hvt, hve, hq⟩ := ht ρ m s n ρ' h' e hv hp hr hn
  have hφ := he ρ m s n ρ' h' e hv hp hr hn
  refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
  cases e with
  | normal => exact ⟨hq, (hs _ _ _ _ _ _ hr m t).mp (hb t ⟨ha, hh ▸ hφ⟩)⟩
  | thrown _ => exact ⟨hq, (hse _ _ _ _ _ _ hr m t).mp (hbe t ⟨ha, hh ▸ hφ⟩)⟩
  | «break» => exact hq
  | returned _ => exact hq

/-- Frame+ retains the box using semantic rigidity, not a finite rigidity
certificate. The box's binding-scope obligation covers its effect as well. -/
theorem frame_plus_rule {host P c Q Qe J Ret Φ Φe} {R : Assertion}
    (ht : Triple host P c Q Qe J Ret) (he : Effects host P c Φ Φe)
    (hs : ScopeStable host c (Box Φ R)) (hrigid : RigidOn Φ) :
    Triple host (fun ρ m s => P ρ m s ∧ Box Φ R ρ m s) c
      (PostAnd Q (Now (Box Φ R))) Qe J Ret := by
  intro ρ m s n ρ' h' e hv ⟨hp, hb⟩ hr hn
  obtain ⟨t, ha, hh, hk, hvt, hve, hq⟩ := ht ρ m s n ρ' h' e hv hp hr hn
  have hφ := he ρ m s n ρ' h' e hv hp hr hn
  refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
  cases e with
  | normal => exact ⟨hq, (hs _ _ _ _ _ _ hr m t).mp
      (box_idem_on hrigid ρ m s hv.heap hb t ⟨ha, hh ▸ hφ⟩)⟩
  | thrown _ => exact hq
  | «break» => exact hq
  | returned _ => exact hq

/-- A one-state exit assertion, including enclosing break/return obligations. -/
def StateExit (Q E J : Assertion) (Ret : Val → Assertion) : Exit → Assertion
  | .normal => Q
  | .thrown _ => E
  | .break => J
  | .returned v => Ret v

abbrev StateTriple (host : NativeCode) (P : Assertion) (c : Command)
    (Q E J : Assertion) (Ret : Val → Assertion) : Prop :=
  Triple host P c (Now Q) (Now E) (Now J) (fun v => Now (Ret v))

/-- Seq as displayed: intermediate and exit assertions are of one state.
The intermediate world comes from the first proof and is passed to the second. -/
theorem seq_rule {host P A R E J Ret a b}
    (h₁ : StateTriple host P a A E J Ret) (h₂ : StateTriple host A b R E J Ret) :
    StateTriple host P (.seq a b) R E J Ret := by
  intro ρ m s n ρ' h' e hv hp hr hn
  cases hr with
  | seq hfirst hsecond =>
    obtain ⟨t, ha, hh, hk, hvt, hve, ht⟩ := h₁ _ _ _ _ _ _ _ hv hp hfirst (by omega)
    rw [← hh] at hsecond
    obtain ⟨u, hau, hhu, hku, hvu, hveu, hu⟩ := h₂ _ _ _ _ _ _ _ hvt ht hsecond (by omega)
    refine ⟨u, ha.trans hau, hhu, by omega, hvu, hveu, ?_⟩
    cases e <;> exact hu
  | seq_exit hfirst hne =>
    obtain ⟨t, ha, hh, hk, hvt, hve, ht⟩ := h₁ _ _ _ _ _ _ _ hv hp hfirst hn
    refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
    cases e with
    | normal => exact (hne rfl).elim
    | thrown _ => exact ht
    | «break» => exact ht
    | returned _ => exact ht

/-- If with the actual truthiness test of its named atom. Comparison facts
are consequences of the binding which produced that atom. -/
theorem if_rule {host P Q E J Ret yes no} {test : Argument}
    (hy : Triple host (fun ρ m s => P ρ m s ∧ tagHolds .truthy (test.eval ρ) = true) yes Q E J Ret)
    (hn : Triple host (fun ρ m s => P ρ m s ∧ tagHolds .truthy (test.eval ρ) = false) no Q E J Ret) :
    Triple host P (.choice test yes no) Q E J Ret := by
  intro ρ m s n ρ' h' e hv hp hr hk
  cases hr with
  | yes hb hrun => exact hy _ _ _ _ _ _ _ hv ⟨hp, hb⟩ hrun hk
  | no hb hrun => exact hn _ _ _ _ _ _ _ hv ⟨hp, hb⟩ hrun hk

/-- The two branches' effects give the choice's effect, without a search
certificate and for arbitrary regional footprints. -/
theorem if_effects {host P yes no Φ Φe} {test : Argument}
    (hy : Effects host (fun ρ m s => P ρ m s ∧ tagHolds .truthy (test.eval ρ) = true) yes Φ Φe)
    (hn : Effects host (fun ρ m s => P ρ m s ∧ tagHolds .truthy (test.eval ρ) = false) no Φ Φe) :
    Effects host P (.choice test yes no) Φ Φe := by
  intro ρ m s n ρ' h' e hv hp hr hk
  cases hr with
  | yes hb hrun => exact hy _ _ _ _ _ _ _ hv ⟨hp, hb⟩ hrun hk
  | no hb hrun => exact hn _ _ _ _ _ _ _ hv ⟨hp, hb⟩ hrun hk

/-- Try for one-state assertions. R cannot mention the fresh caught name. -/
theorem try_rule {host P Q R E J Ret body handler x}
    (hb : StateTriple host P body Q R J Ret)
    (hd : StateTriple host R handler Q E J Ret)
    (hscope : ∀ ρ v m s, R ρ m s → R (bindName ρ x v) m s) :
    StateTriple host P (.handle body x handler) Q E J Ret := by
  intro ρ m s n ρ' h' e hv hp hr hn
  cases hr with
  | handle_catch hbody hhandler =>
    obtain ⟨t, ha, hh, hk, hvt, hve, ht⟩ := hb _ _ _ _ _ _ _ hv hp hbody (by omega)
    rw [← hh] at hhandler
    obtain ⟨u, hau, hhu, hku, hvu, hveu, hu⟩ := hd _ _ _ _ _ _ _ (hvt.bindName hve) (hscope _ _ _ _ ht) hhandler (by omega)
    refine ⟨u, ha.trans hau, hhu, by omega, hvu, hveu, ?_⟩
    cases e <;> exact hu
  | handle_exit hbody hne =>
    obtain ⟨t, ha, hh, hk, hvt, hve, ht⟩ := hb _ _ _ _ _ _ _ hv hp hbody hn
    refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
    cases e with
    | normal => exact ht
    | «break» => exact ht
    | returned _ => exact ht
    | thrown v => exact (hne v rfl).elim

end Verification.Paper.TolerantFrames
