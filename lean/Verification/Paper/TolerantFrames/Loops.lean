import Verification.Paper.TolerantFrames.Scopes

/-! # Loop rules

The existing mechanism extended here is finite command execution, with break
obligations in the body's triple. A loop's invariant is proved by induction on
its execution derivation, not assumed as a supplied prefix summary. Returning
and throwing propagate their own obligations. Prefix Reliance remains a
separate theorem about every primitive/callback prefix, not a consequence of an
endpoint triple.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations
open Verification.TolerantFrames

private theorem state_exit_carry {I E J : Assertion} {Ret : Val → Assertion} {e : Exit}
    {ρ ρ₀ ρ₁ : Env} {m : Nat} {s t u : IndexedHeap}
    (hp : ExitPost (Now I) (Now E) (Now J) (fun v => Now (Ret v)) e ρ₀ ρ₁ m t u) :
    ExitPost (Now I) (Now E) (Now J) (fun v => Now (Ret v)) e ρ ρ₁ m s u := by
  cases e <;> exact hp

private theorem loop_invariant_run {host : NativeCode} {b : Command} {I E : Assertion} {Ret : Val → Assertion}
    (hb : StateTriple host I b I E I Ret)
    {cmd ρ h n ρ' h' e} (hr : Executes host cmd ρ h n ρ' h' e) :
    cmd = .loop b → ∀ m (s : IndexedHeap), s.h = h → ValidContext ρ m s → I ρ m s → n < s.n →
      ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧ ValidContext ρ' m t ∧ ExitValid e t ∧
        ExitPost (Now I) (Now E) (Now I) (fun v => Now (Ret v)) e ρ ρ' m s t := by
  induction hr with
  | loop_next hfirst _ _ ih =>
    intro he m s hh hv hp hn
    cases he
    rw [← hh] at hfirst
    obtain ⟨t, ha, ht, hk, hvt, hve, hI⟩ := hb _ _ _ _ _ _ _ hv hp hfirst (by omega)
    obtain ⟨u, hau, hhu, hku, hvu, hveu, hu⟩ := ih rfl m t ht hvt hI (by omega)
    refine ⟨u, ha.trans hau, hhu, by omega, hvu, hveu, ?_⟩
    exact state_exit_carry hu
  | loop_break hfirst _ =>
    intro he m s hh hv hp hn
    cases he
    rw [← hh] at hfirst
    obtain ⟨t, ha, ht, hk, hvt, hve, hI⟩ := hb _ _ _ _ _ _ .break hv hp hfirst hn
    exact ⟨t, ha, ht, hk, hvt, trivial, hI⟩
  | loop_return hfirst _ =>
    intro he m s hh hv hp hn
    cases he
    rw [← hh] at hfirst
    exact hb _ _ _ _ _ _ _ hv hp hfirst hn
  | loop_throw hfirst _ =>
    intro he m s hh hv hp hn
    cases he
    rw [← hh] at hfirst
    exact hb _ _ _ _ _ _ _ hv hp hfirst hn
  | step _ | seq _ _ _ _ | seq_exit _ _ _ | yes _ _ _ | no _ _ _
    | handle_catch _ _ _ _ | handle_exit _ _ _ | return_ _ | throw_ _ | break_ =>
    intro he; cases he

/-- The general invariant rule, including actual break, return and throw. -/
theorem loop_invariant {host : NativeCode} {b : Command} {I E : Assertion} {Ret : Val → Assertion}
    (hb : StateTriple host I b I E I Ret) : StateTriple host I (.loop b) I E I Ret := by
  intro ρ m s n ρ' h' e hv hp hr hn
  exact loop_invariant_run hb hr rfl m s rfl hv hp hn

/-- Loop of §6. The break obligation is I ∧ box R, as the displayed rule's
explanation requires. R and Φ cannot mention loop-carried or freshly bound
names, expressed by the scope premise and derivable by `scope_stable_of_avoids`.
The effect and rigidity premises are semantic, not finite certificates. -/
theorem loop_rule {host : NativeCode} {b : Command} {I E R : Assertion} {Ret : Val → Assertion}
    {Φ Φe : Footprint}
    (hb : StateTriple host (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) b I E
      (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) Ret)
    (he : Effects host (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) b Φ Φe)
    (hs : ScopeStable host b (Box Φ R)) (hΦ : RigidOn Φ) :
    StateTriple host (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) (.loop b)
      (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) E
      (fun ρ m s => I ρ m s ∧ Box Φ R ρ m s) Ret := by
  apply loop_invariant
  intro ρ m s n ρ' h' e hv hp hr hn
  obtain ⟨t, ha, hh, hk, hvt, hve, hq⟩ := hb _ _ _ _ _ _ _ hv hp hr hn
  have hφ := he _ _ _ _ _ _ _ hv hp hr hn
  refine ⟨t, ha, hh, hk, hvt, hve, ?_⟩
  cases e with
  | normal => exact ⟨hq, (hs _ _ _ _ _ _ hr m t).mp
      (box_idem_on hΦ ρ m s hv hp.2 t ⟨ha, hh ▸ hφ⟩)⟩
  | «break» => exact hq
  | returned _ => exact hq
  | thrown _ => exact hq

end Verification.Paper.TolerantFrames
