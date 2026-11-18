import Verification.Paper.TolerantFrames.PrimitiveRenaming
import Verification.Paper.TolerantFrames.PostconditionProgramRenaming
import Verification.Paper.TolerantFrames.Scopes

/-! # Call at names in scope

The total-map result-fiber condition of primitive transport is discharged by
finite lexical freshness. All input aliases are allowed, and the displayed
callee name is fixed. Capture-avoiding first-order postcondition renaming is
connected to actual normal/exceptional call execution and both regional effects.
Rest/spread operational preparation and freshness-mark rebasing are separate.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations TolerantFrames

/-- Semantic precondition instantiation cannot depend on unused input names. -/
theorem RenamePre.extension_independent {inputs : List Nat} {σ τ : Nat → Nat} {P : Assertion}
    (hp : DependsOn P (fun x => x ∈ inputs)) (hm : ∀ x ∈ inputs, σ x = τ x) :
    RenamePre σ P = RenamePre τ P := by
  funext ρ m s
  exact propext (hp _ _ m s (fun x hx => congrArg ρ (hm x hx)))

/-- The fresh-name premise is lexical: formal result outside the input scope,
and actual result absent from all actual input images. -/
theorem finite_call_rule {host P Q Qe J Ret Φ Φe f y z} (inputs parameters : List Nat) (actual : Nat → Nat)
    (hy : y ∉ inputs) (hf : f ∈ inputs) (hcallee : actual f = f)
    (hargs : ∀ p ∈ parameters, p ∈ inputs) (hfresh : ∀ x ∈ inputs, actual x ≠ z)
    (ht : Triple host P (.step (.bind y (.call f (parameters.map Argument.variable)))) Q Qe J Ret)
    (he : Effects host P (.step (.bind y (.call f (parameters.map Argument.variable)))) Φ Φe) :
    let σ := extendCallRenaming inputs actual y z
    Triple host (RenamePre σ P) (.step (.bind z (.call f (parameters.map fun x => Argument.variable (actual x)))))
      (RenamePost σ Q) (RenamePost σ Qe) (RenamePost σ J) (fun v => RenamePost σ (Ret v)) ∧
    Effects host (RenamePre σ P) (.step (.bind z (.call f (parameters.map fun x => Argument.variable (actual x)))))
      (Footprint.rename σ Φ) (Footprint.rename σ Φe) := by
  let σ := extendCallRenaming inputs actual y z
  have hresult : σ y = z := extendCallRenaming_result inputs actual y z
  have hfun : σ f = f := extendCallRenaming_callee hy hf hcallee
  have hparams : parameters.map (fun x => Argument.variable (σ x)) =
      parameters.map (fun x => Argument.variable (actual x)) := by
    apply List.map_congr_left
    intro x hx
    exact congrArg Argument.variable (extendCallRenaming_inputs (actual := actual) (z := z) hy (hargs x hx))
  simpa only [hresult, hfun, hparams] using
    (call_rule (σ := σ) parameters (extendCallRenaming_fresh hfresh) ht he)

/-- Exactly the same result for actual assertion/postcondition syntax.
No simultaneous substitution into an old term is assumed: the complete
capture-avoiding renaming theorem supplies both phases and all binders. -/
theorem finite_call_syntax_rule {host f y z J Ret Φ Φe} (inputs parameters : List Nat) (actual : Nat → Nat)
    (hy : y ∉ inputs) (hf : f ∈ inputs) (hcallee : actual f = f)
    (hargs : ∀ p ∈ parameters, p ∈ inputs) (hfresh : ∀ x ∈ inputs, actual x ≠ z)
    (P : Formula) (Q Qe : TwoState.Post) (η : TwoState.LogicalEnv)
    (ht : Triple host P.meaning (.step (.bind y (.call f (parameters.map Argument.variable))))
      (Q.meaning η) (Qe.meaning η) J Ret)
    (he : Effects host P.meaning (.step (.bind y (.call f (parameters.map Argument.variable)))) Φ Φe) :
    let σ := extendCallRenaming inputs actual y z
    Triple host (P.rename σ).meaning (.step (.bind z (.call f (parameters.map fun x => Argument.variable (actual x)))))
      ((Q.rename (TwoState.programMap σ id id)).meaning η)
      ((Qe.rename (TwoState.programMap σ id id)).meaning η)
      (RenamePost σ J) (fun v => RenamePost σ (Ret v)) ∧
    Effects host (P.rename σ).meaning (.step (.bind z (.call f (parameters.map fun x => Argument.variable (actual x)))))
      (Footprint.rename σ Φ) (Footprint.rename σ Φe) := by
  let σ := extendCallRenaming inputs actual y z
  have hr := finite_call_rule inputs parameters actual hy hf hcallee hargs hfresh ht he
  have hp : Entails (P.rename σ).meaning (RenamePre σ P.meaning) := by
    intro ρ m s hP
    exact (P.holds_rename σ ρ m s).mp hP
  constructor
  · rw [Q.program_rename_meaning, Qe.program_rename_meaning]
    exact triple_consequence hr.1 hp (fun _ _ _ _ _ _ h => h)
  · intro ρ m s n ρ' h' e hv hP hrun hn
    exact hr.2 _ _ _ _ _ _ _ hv (hp _ _ _ hP) hrun hn

/-- Any two extensions agreeing on the actual inputs and fresh result give
identical postcondition syntax, including old and effects inside boxes. -/
theorem TwoState.Post.call_extension_independent {inputs : List Nat} {σ τ : Nat → Nat} {y : Nat}
    (hinputs : ∀ x ∈ inputs, σ x = τ x) (hresult : σ y = τ y)
    {Q : TwoState.Post} (hQ : Q.Scoped (fun x => x ∈ inputs) (fun x => x = y ∨ x ∈ inputs) 0 0) :
    Q.rename (TwoState.programMap σ id id) = Q.rename (TwoState.programMap τ id id) :=
  Q.rename_program_agree hinputs (fun x hx => hx.elim (fun h => h ▸ hresult) (hinputs x)) id id hQ

end Verification.Paper.TolerantFrames
