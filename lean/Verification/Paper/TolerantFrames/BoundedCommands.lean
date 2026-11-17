import Verification.Paper.TolerantFrames.Loops

/-! # Command proofs below an independent execution-count bound

This refines the existing completed-run judgments, without restricting the
initial indexed heap. A recursive invocation can therefore use induction on
its actual shared reduction count while old retains the original entry.
Finite executions, rather than counts alone, support loop induction: commands
can perform arbitrarily many zero-cost administrative iterations.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations TolerantFrames

def TripleBelow (N : Nat) (host : NativeCode) (P : Assertion) (c : Command)
    (Q Qe J : Postcondition) (Ret : Val → Postcondition) : Prop :=
  ∀ ρ m s n ρ' h' e, ValidContext ρ m s → P ρ m s → Executes host c ρ s.h n ρ' h' e →
    n < s.n → n < N →
    ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧
      ValidContext ρ' m t ∧ ExitValid e t ∧ ExitPost Q Qe J Ret e ρ ρ' m s t

def EffectsBelow (N : Nat) (host : NativeCode) (P : Assertion) (c : Command) (Φ Φe : Footprint) : Prop :=
  ∀ ρ m s n ρ' h' e, ValidContext ρ m s → P ρ m s → Executes host c ρ s.h n ρ' h' e →
    n < s.n → n < N → Footprints.Post (match e with | .thrown _ => Φe | _ => Φ) ρ s.h h'

abbrev StateTripleBelow (N : Nat) (host : NativeCode) (P : Assertion) (c : Command)
    (Q E J : Assertion) (Ret : Val → Assertion) : Prop :=
  TripleBelow N host P c (Now Q) (Now E) (Now J) (fun v => Now (Ret v))

theorem Triple.below {host P c Q Qe J Ret} (h : Triple host P c Q Qe J Ret) (N : Nat) :
    TripleBelow N host P c Q Qe J Ret := fun ρ m s n ρ' h' e hv hp hr hn _ => h ρ m s n ρ' h' e hv hp hr hn

theorem Effects.below {host P c Φ Φe} (h : Effects host P c Φ Φe) (N : Nat) :
    EffectsBelow N host P c Φ Φe := fun ρ m s n ρ' h' e hv hp hr hn _ => h ρ m s n ρ' h' e hv hp hr hn

theorem TripleBelow.mono {N M host P c Q Qe J Ret} (h : TripleBelow N host P c Q Qe J Ret) (hm : M ≤ N) :
    TripleBelow M host P c Q Qe J Ret :=
  fun ρ m s n ρ' h' e hv hp hr hn hM => h ρ m s n ρ' h' e hv hp hr hn (Nat.lt_of_lt_of_le hM hm)

theorem EffectsBelow.mono {N M host P c Φ Φe} (h : EffectsBelow N host P c Φ Φe) (hm : M ≤ N) :
    EffectsBelow M host P c Φ Φe :=
  fun ρ m s n ρ' h' e hv hp hr hn hM => h ρ m s n ρ' h' e hv hp hr hn (Nat.lt_of_lt_of_le hM hm)

theorem triple_iff_below {host P c Q Qe J Ret} :
    Triple host P c Q Qe J Ret ↔ ∀ N, TripleBelow N host P c Q Qe J Ret := by
  refine ⟨fun h N => h.below N, ?_⟩
  intro h ρ m s n ρ' h' e hv hp hr hn
  exact h (n + 1) ρ m s n ρ' h' e hv hp hr hn (by omega)

theorem effects_iff_below {host P c Φ Φe} :
    Effects host P c Φ Φe ↔ ∀ N, EffectsBelow N host P c Φ Φe := by
  refine ⟨fun h N => h.below N, ?_⟩
  intro h ρ m s n ρ' h' e hv hp hr hn
  exact h (n + 1) ρ m s n ρ' h' e hv hp hr hn (by omega)

namespace Bounded

theorem consequence {N host P P' c Q Qe J Ret Q' Qe' J' Ret'}
    (ht : TripleBelow N host P c Q Qe J Ret) (hp : Entails P' P)
    (hq : ∀ e ρ ρ' m s t, ExitPost Q Qe J Ret e ρ ρ' m s t → ExitPost Q' Qe' J' Ret' e ρ ρ' m s t) :
    TripleBelow N host P' c Q' Qe' J' Ret' := by
  intro ρ m s n ρ' h' e hv hP hr hn hN
  obtain ⟨t, ha, hh, hk, hvt, hve, hpost⟩ := ht ρ m s n ρ' h' e hv (hp ρ m s hP) hr hn hN
  exact ⟨t, ha, hh, hk, hvt, hve, hq e ρ ρ' m s t hpost⟩

theorem seq_rule {N host P A R E J Ret a b}
    (h₁ : StateTripleBelow N host P a A E J Ret) (h₂ : StateTripleBelow N host A b R E J Ret) :
    StateTripleBelow N host P (.seq a b) R E J Ret := by
  intro ρ m s n ρ' h' e hv hp hr hn hN
  cases hr with
  | seq hfirst hsecond =>
    obtain ⟨t, ha, hh, hk, hvt, hve, ht⟩ := h₁ _ _ _ _ _ _ _ hv hp hfirst (by omega) (by omega)
    rw [← hh] at hsecond
    obtain ⟨u, hau, hhu, hku, hvu, hveu, hu⟩ := h₂ _ _ _ _ _ _ _ hvt ht hsecond (by omega) (by omega)
    refine ⟨u, ha.trans hau, hhu, by omega, hvu, hveu, ?_⟩
    cases e <;> exact hu
  | seq_exit hfirst hne =>
    obtain ⟨t, ha, hh, hk, hvt, hve, ht⟩ := h₁ _ _ _ _ _ _ _ hv hp hfirst hn hN
    refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
    cases e with
    | normal => exact (hne rfl).elim
    | thrown _ => exact ht
    | «break» => exact ht
    | returned _ => exact ht

theorem if_rule {N host P Q E J Ret yes no} {test : Argument}
    (hy : TripleBelow N host (fun ρ m s => P ρ m s ∧ tagHolds .truthy (test.eval ρ) = true) yes Q E J Ret)
    (hn : TripleBelow N host (fun ρ m s => P ρ m s ∧ tagHolds .truthy (test.eval ρ) = false) no Q E J Ret) :
    TripleBelow N host P (.choice test yes no) Q E J Ret := by
  intro ρ m s n ρ' h' e hv hp hr hk hN
  cases hr with
  | yes hb hrun => exact hy _ _ _ _ _ _ _ hv ⟨hp, hb⟩ hrun hk hN
  | no hb hrun => exact hn _ _ _ _ _ _ _ hv ⟨hp, hb⟩ hrun hk hN

theorem if_effects {N host P yes no Φ Φe} {test : Argument}
    (hy : EffectsBelow N host (fun ρ m s => P ρ m s ∧ tagHolds .truthy (test.eval ρ) = true) yes Φ Φe)
    (hn : EffectsBelow N host (fun ρ m s => P ρ m s ∧ tagHolds .truthy (test.eval ρ) = false) no Φ Φe) :
    EffectsBelow N host P (.choice test yes no) Φ Φe := by
  intro ρ m s n ρ' h' e hv hp hr hk hN
  cases hr with
  | yes hb hrun => exact hy _ _ _ _ _ _ _ hv ⟨hp, hb⟩ hrun hk hN
  | no hb hrun => exact hn _ _ _ _ _ _ _ hv ⟨hp, hb⟩ hrun hk hN

theorem try_rule {N host P Q R E J Ret body handler x}
    (hb : StateTripleBelow N host P body Q R J Ret)
    (hd : StateTripleBelow N host R handler Q E J Ret)
    (hscope : ∀ ρ v m s, R ρ m s → R (bindName ρ x v) m s) :
    StateTripleBelow N host P (.handle body x handler) Q E J Ret := by
  intro ρ m s n ρ' h' e hv hp hr hn hN
  cases hr with
  | handle_catch hbody hhandler =>
    obtain ⟨t, ha, hh, hk, hvt, hve, ht⟩ := hb _ _ _ _ _ _ _ hv hp hbody (by omega) (by omega)
    rw [← hh] at hhandler
    obtain ⟨u, hau, hhu, hku, hvu, hveu, hu⟩ := hd _ _ _ _ _ _ _ (hvt.bindName hve)
      (hscope _ _ _ _ ht) hhandler (by omega) (by omega)
    refine ⟨u, ha.trans hau, hhu, by omega, hvu, hveu, ?_⟩
    cases e <;> exact hu
  | handle_exit hbody hne =>
    obtain ⟨t, ha, hh, hk, hvt, hve, ht⟩ := hb _ _ _ _ _ _ _ hv hp hbody hn hN
    refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
    cases e with
    | normal => exact ht
    | «break» => exact ht
    | returned _ => exact ht
    | thrown v => exact (hne v rfl).elim

private theorem state_exit_carry {I E J : Assertion} {Ret : Val → Assertion} {e : Exit}
    {ρ ρ₀ ρ₁ : Env} {m : Nat} {s t u : IndexedHeap}
    (hp : ExitPost (Now I) (Now E) (Now J) (fun v => Now (Ret v)) e ρ₀ ρ₁ m t u) :
    ExitPost (Now I) (Now E) (Now J) (fun v => Now (Ret v)) e ρ ρ₁ m s u := by
  cases e <;> exact hp

private theorem loop_invariant_run {N : Nat} {host : NativeCode} {b : Command}
    {I E : Assertion} {Ret : Val → Assertion} (hb : StateTripleBelow N host I b I E I Ret)
    {cmd ρ h n ρ' h' e} (hr : Executes host cmd ρ h n ρ' h' e) :
    cmd = .loop b → ∀ m (s : IndexedHeap), s.h = h → ValidContext ρ m s → I ρ m s → n < s.n → n < N →
      ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧ ValidContext ρ' m t ∧ ExitValid e t ∧
        ExitPost (Now I) (Now E) (Now I) (fun v => Now (Ret v)) e ρ ρ' m s t := by
  induction hr with
  | loop_next hfirst _ _ ih =>
    intro he m s hh hv hp hn hN
    cases he
    rw [← hh] at hfirst
    obtain ⟨t, ha, ht, hk, hvt, hve, hI⟩ := hb _ _ _ _ _ _ _ hv hp hfirst (by omega) (by omega)
    obtain ⟨u, hau, hhu, hku, hvu, hveu, hu⟩ := ih rfl m t ht hvt hI (by omega) (by omega)
    refine ⟨u, ha.trans hau, hhu, by omega, hvu, hveu, ?_⟩
    exact state_exit_carry hu
  | loop_break hfirst _ =>
    intro he m s hh hv hp hn hN
    cases he
    rw [← hh] at hfirst
    obtain ⟨t, ha, ht, hk, hvt, hve, hI⟩ := hb _ _ _ _ _ _ .break hv hp hfirst hn hN
    exact ⟨t, ha, ht, hk, hvt, trivial, hI⟩
  | loop_return hfirst _ =>
    intro he m s hh hv hp hn hN
    cases he
    rw [← hh] at hfirst
    exact hb _ _ _ _ _ _ _ hv hp hfirst hn hN
  | loop_throw hfirst _ =>
    intro he m s hh hv hp hn hN
    cases he
    rw [← hh] at hfirst
    exact hb _ _ _ _ _ _ _ hv hp hfirst hn hN
  | step _ | seq _ _ _ _ | seq_exit _ _ _ | yes _ _ _ | no _ _ _
    | handle_catch _ _ _ _ | handle_exit _ _ _ | return_ _ | throw_ _ | break_ =>
    intro he; cases he

theorem loop_invariant {N host b I E Ret}
    (hb : StateTripleBelow N host I b I E I Ret) : StateTripleBelow N host I (.loop b) I E I Ret := by
  intro ρ m s n ρ' h' e hv hp hr hn hN
  exact loop_invariant_run hb hr rfl m s rfl hv hp hn hN

end Bounded
end Verification.Paper.TolerantFrames
