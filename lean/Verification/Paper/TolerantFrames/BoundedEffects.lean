import Verification.Paper.TolerantFrames.BoundedFrameRules
import Verification.Paper.TolerantFrames.FormulaScopes

/-! # Common rigid effects for bounded body proofs

A sufficient composition mechanism, not the full general Seq-Eff rule. Both
exits use one rigid footprint. Component triples supply admissible worlds,
component effects supply regional posts, and scope restores the original
valuation before transitivity. No world existence is inferred from raw effects.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations TolerantFrames

private theorem uniform_effect {N host P c Φ} (effects : EffectsBelow N host P c Φ Φ)
    {ρ m s n ρ' h' e} (valid : ValidContext ρ m s) (pre : P ρ m s)
    (run : Executes host c ρ s.h n ρ' h' e) (budget : n < s.n) (limited : n < N) :
    Footprints.Post Φ ρ s.h h' := by
  have effect := effects _ _ _ _ _ _ _ valid pre run budget limited
  cases e <;> exact effect

namespace Bounded

theorem seq_rigid_effects {N host P A Q E J Ret a b Γ Φ}
    (first : StateTripleBelow N host P a A E J Ret)
    (second : StateTripleBelow N host A b Q E J Ret)
    (firstEffect : EffectsBelow N host P a Φ Φ) (secondEffect : EffectsBelow N host A b Φ Φ)
    (names : EffectNames Γ Φ) (avoids : ∀ x, Γ x → a.Avoids x) (rigid : RigidOn Φ) :
    EffectsBelow N host P (.seq a b) Φ Φ := by
  intro ρ m s n ρ' h' e valid pre run budget limited
  have effect : Footprints.Post Φ ρ s.h h' := by
    cases run with
    | seq hfirst hsecond =>
      have ef := uniform_effect firstEffect valid pre hfirst (by omega) (by omega)
      obtain ⟨t, reachable, ht, kt, vt, _, middle⟩ := first _ _ _ _ _ _ _ valid pre hfirst (by omega) (by omega)
      rw [← ht] at hsecond
      have es := uniform_effect secondEffect vt middle hsecond (by omega) (by omega)
      obtain ⟨u, au, hu, _, _, _, _⟩ := second _ _ _ _ _ _ _ vt middle hsecond (by omega) (by omega)
      have agree := fun x hx => hfirst.preserves_name (avoids x hx)
      have es' := (post_scope agree names t.h _).mp es
      have action := rigid _ m s t u valid.heap ⟨reachable, ht ▸ ef⟩ ⟨au, hu ▸ es'⟩
      exact hu ▸ action.2
    | seq_exit hfirst _ => exact uniform_effect firstEffect valid pre hfirst budget limited
  cases e <;> exact effect

theorem try_rigid_effects {N host P Q R E J Ret body handler caught Γ Φ}
    (first : StateTripleBelow N host P body Q R J Ret)
    (second : StateTripleBelow N host R handler Q E J Ret)
    (firstEffect : EffectsBelow N host P body Φ Φ) (secondEffect : EffectsBelow N host R handler Φ Φ)
    (handlerPre : ∀ ρ v m s, R ρ m s → R (bindName ρ caught v) m s)
    (names : EffectNames Γ Φ) (avoids : ∀ x, Γ x → body.Avoids x) (fresh : ¬ Γ caught)
    (rigid : RigidOn Φ) : EffectsBelow N host P (.handle body caught handler) Φ Φ := by
  intro ρ m s n ρ' h' e valid pre run budget limited
  have effect : Footprints.Post Φ ρ s.h h' := by
    cases run with
    | handle_catch hbody hhandler =>
      rename_i n₁ ρ₁ h₁ n₂ v
      have ef := uniform_effect firstEffect valid pre hbody (by omega) (by omega)
      obtain ⟨t, reachable, ht, kt, vt, exit, middle⟩ := first _ _ _ _ _ _ _ valid pre hbody (by omega) (by omega)
      rw [← ht] at hhandler
      have vc := vt.bindName (x := caught) exit
      have pc := handlerPre ρ₁ v m t middle
      have es := uniform_effect secondEffect vc pc hhandler (by omega) (by omega)
      obtain ⟨u, au, hu, _, _, _, _⟩ := second _ _ _ _ _ _ _ vc pc hhandler (by omega) (by omega)
      have agree : ∀ x, Γ x → bindName ρ₁ caught v x = ρ x := by
        intro x hx
        have different : x ≠ caught := fun h => fresh (h ▸ hx)
        simp only [bindName, if_neg different]
        exact hbody.preserves_name (avoids x hx)
      have es' := (post_scope agree names t.h _).mp es
      have action := rigid _ m s t u valid.heap ⟨reachable, ht ▸ ef⟩ ⟨au, hu ▸ es'⟩
      exact hu ▸ action.2
    | handle_exit hbody _ => exact uniform_effect firstEffect valid pre hbody budget limited
  cases e <;> exact effect

private theorem loop_rigid_run {N host b I E Ret Γ Φ}
    (body : StateTripleBelow N host I b I E I Ret) (effect : EffectsBelow N host I b Φ Φ)
    (names : EffectNames Γ Φ) (avoids : ∀ x, Γ x → b.Avoids x) (rigid : RigidOn Φ)
    {cmd ρ h n ρ' h' e} (run : Executes host cmd ρ h n ρ' h' e) :
    cmd = .loop b → ∀ m (s : IndexedHeap), s.h = h → ValidContext ρ m s → I ρ m s → n < s.n → n < N →
      ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧
        Footprints.Post Φ ρ s.h h' := by
  induction run with
  | loop_next hfirst _ _ ih =>
    intro same m s heap valid pre budget limited
    cases same
    rw [← heap] at hfirst
    have ef := uniform_effect effect valid pre hfirst (by omega) (by omega)
    obtain ⟨t, reachable, ht, kt, vt, _, middle⟩ := body _ _ _ _ _ _ _ valid pre hfirst (by omega) (by omega)
    obtain ⟨u, au, hu, ku, es⟩ := ih rfl m t ht vt middle (by omega) (by omega)
    have agree := fun x hx => hfirst.preserves_name (avoids x hx)
    have es' := (post_scope agree names t.h _).mp es
    have action := rigid _ m s t u valid.heap ⟨reachable, ht ▸ ef⟩ ⟨au, hu ▸ es'⟩
    exact ⟨u, reachable.trans au, hu, by omega, hu ▸ action.2⟩
  | loop_break hfirst _ | loop_return hfirst _ | loop_throw hfirst _ =>
    intro same m s heap valid pre budget limited
    cases same
    rw [← heap] at hfirst
    have ef := uniform_effect effect valid pre hfirst budget limited
    obtain ⟨t, reachable, ht, kt, _, _, _⟩ := body _ _ _ _ _ _ _ valid pre hfirst budget limited
    exact ⟨t, reachable, ht, kt, ef⟩
  | step _ | seq _ _ _ _ | seq_exit _ _ _ | yes _ _ _ | no _ _ _
    | handle_catch _ _ _ _ | handle_exit _ _ _ | return_ _ | throw_ _ | break_ =>
    intro same; cases same

theorem loop_rigid_effects {N host b I E Ret Γ Φ}
    (body : StateTripleBelow N host I b I E I Ret) (effect : EffectsBelow N host I b Φ Φ)
    (names : EffectNames Γ Φ) (avoids : ∀ x, Γ x → b.Avoids x) (rigid : RigidOn Φ) :
    EffectsBelow N host I (.loop b) Φ Φ := by
  intro ρ m s n ρ' h' e valid pre run budget limited
  obtain ⟨_, _, _, _, post⟩ := loop_rigid_run body effect names avoids rigid run rfl m s rfl valid pre budget limited
  cases e <;> exact post

end Bounded
end Verification.Paper.TolerantFrames
