import Verification.Paper.TolerantFrames.CallRules
import Verification.Paper.TolerantFrames.FormulaScopes
import Verification.Paper.TolerantFrames.PostconditionRenamingAdmission
import Verification.Paper.TolerantFrames.PostconditionScopeWeakening

/-! # Scoped and admitted finite Call instantiation

This assembles lexical freshness, both specification phases, both outer effects
and declaration pullback with actual call execution. Declarations are supplied
by the surrounding type system, not inferred from one heap reading. No native
contract or function-body summary is introduced here.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations TolerantFrames

theorem region_rename_agree_roots {σ τ : Nat → Nat} {r : Region}
    (hm : ∀ x ∈ Parity.regionRoots r, σ x = τ x) : r.rename σ = r.rename τ := by
  induction r with
  | field x _ | fields x | cells x | path x _ _ | pathFields x _ | pathCells x _ | spine x _ =>
    simp only [Region.rename, hm x (by simp [Parity.regionRoots])]
  | cls _ | all => rfl
  | inCls _ _ ih => simp only [Region.rename, ih hm]

theorem effect_rename_extension {inputs : List Nat} {σ τ : Nat → Nat} {Φ : Footprint}
    (hm : ∀ x ∈ inputs, σ x = τ x) (hΦ : EffectNames (fun x => x ∈ inputs) Φ) :
    Footprint.rename σ Φ = Footprint.rename τ Φ := by
  apply List.map_congr_left
  intro e he
  rw [region_rename_agree_roots (fun x hx => hm x (hΦ e he x hx))]

theorem Formula.rename_meaning (σ : Nat → Nat) (P : Formula) :
    (P.rename σ).meaning = RenamePre σ P.meaning := by
  funext ρ m s
  exact propext (P.holds_rename σ ρ m s)

/-- Source specifications use only the finite lexical input scope and fresh
normal result. All declaration assumptions are stated as actual pullbacks. -/
structure CallStatic (inputs : List Nat) (y : Nat) (σ : Nat → Nat) (P : Formula) (Q Qe : TwoState.Post)
    (Φ Φe : Footprint) (preTypes entryTypes resultTypes : DeclaredPaths) : Prop where
  preScope : P.Scoped (fun x => x ∈ inputs)
  normalScope : Q.Scoped (fun x => x ∈ inputs) (fun x => x = y ∨ x ∈ inputs) 0 0
  exceptionalScope : Qe.Scoped (fun x => x ∈ inputs) (fun x => x ∈ inputs) 0 0
  normalEffectsScope : EffectNames (fun x => x ∈ inputs) Φ
  exceptionalEffectsScope : EffectNames (fun x => x ∈ inputs) Φe
  preAdmission : P.WellFormed (preTypes.pullback σ)
  normalAdmission : Q.WellFormed (entryTypes.pullback (TwoState.programMap σ id id).encoded)
    (resultTypes.pullback (TwoState.programMap σ id id).encoded)
  exceptionalAdmission : Qe.WellFormed (entryTypes.pullback (TwoState.programMap σ id id).encoded)
    (entryTypes.pullback (TwoState.programMap σ id id).encoded)
  normalEffectsAdmission : EffectWellFormed (preTypes.pullback σ) Φ
  exceptionalEffectsAdmission : EffectWellFormed (preTypes.pullback σ) Φe

structure CallInstanceAdmitted (Γ Δ : Nat → Prop) (P : Formula) (Q Qe : TwoState.Post) (Φ Φe : Footprint)
    (preTypes entryTypes resultTypes : DeclaredPaths) : Prop where
  preScope : P.Scoped Γ
  preAdmission : P.WellFormed preTypes
  normal : Q.Admitted Γ Δ entryTypes resultTypes
  exceptional : Qe.Admitted Γ Γ entryTypes entryTypes
  normalEffectsScope : EffectNames Γ Φ
  exceptionalEffectsScope : EffectNames Γ Φe
  normalEffectsAdmission : EffectWellFormed preTypes Φ
  exceptionalEffectsAdmission : EffectWellFormed preTypes Φe

/-- Static admission follows from the finite scopes and declaration pullbacks;
no all-name injectivity or hidden caller-scope premise is needed. -/
theorem call_instance_admitted {inputs : List Nat} {actual : Nat → Nat} {y z : Nat} {Γ : Nat → Prop}
    {P Q Qe Φ Φe preTypes entryTypes resultTypes}
    (hy : y ∉ inputs) (ha : ∀ x ∈ inputs, Γ (actual x))
    (hs : CallStatic inputs y (extendCallRenaming inputs actual y z) P Q Qe Φ Φe preTypes entryTypes resultTypes) :
    let σ := extendCallRenaming inputs actual y z
    CallInstanceAdmitted Γ (fun x => x = z ∨ Γ x) (P.rename σ)
      (Q.rename (TwoState.programMap σ id id)) (Qe.rename (TwoState.programMap σ id id))
      (Footprint.rename σ Φ) (Footprint.rename σ Φe) preTypes entryTypes resultTypes := by
  let σ := extendCallRenaming inputs actual y z
  have hin : ∀ x, x ∈ inputs → Γ (σ x) := by
    intro x hx
    simpa only [σ, extendCallRenaming_inputs hy hx] using ha x hx
  have hout : ∀ x, x = y ∨ x ∈ inputs → σ x = z ∨ Γ (σ x) := by
    intro x hx
    rcases hx with rfl | hx
    · exact .inl (extendCallRenaming_result inputs actual x z)
    · exact .inr (hin x hx)
  exact ⟨Formula.Scoped.rename hin hs.preScope, Formula.WellFormed.rename hs.preAdmission,
    ⟨TwoState.Post.Scoped.rename_program (hs.normalScope.weaken hin hout), TwoState.Post.WellFormed.rename_program hs.normalAdmission⟩,
    ⟨TwoState.Post.Scoped.rename_program (hs.exceptionalScope.weaken hin hin), TwoState.Post.WellFormed.rename_program hs.exceptionalAdmission⟩,
    effectNames_rename hin hs.normalEffectsScope, effectNames_rename hin hs.exceptionalEffectsScope,
    EffectWellFormed.rename hs.normalEffectsAdmission, EffectWellFormed.rename hs.exceptionalEffectsAdmission⟩

/-- Complete finite variable-actual Call instantiation, assembled with both
phase-specific postconditions, both effects, scopes and declared admission.
Rest/spread preparation, mark rebasing and Fun are not inferred by this rule. -/
theorem admitted_call_rule {host f y z J Ret Φ Φe Γ preTypes entryTypes resultTypes}
    (inputs parameters : List Nat) (actual : Nat → Nat)
    (hy : y ∉ inputs) (hf : f ∈ inputs) (hcallee : actual f = f)
    (hargs : ∀ p ∈ parameters, p ∈ inputs) (hfresh : ¬ Γ z)
    (ha : ∀ x ∈ inputs, Γ (actual x)) (P : Formula) (Q Qe : TwoState.Post) (η : TwoState.LogicalEnv)
    (hs : CallStatic inputs y (extendCallRenaming inputs actual y z) P Q Qe Φ Φe preTypes entryTypes resultTypes)
    (ht : Triple host P.meaning (.step (.bind y (.call f (parameters.map Argument.variable))))
      (Q.meaning η) (Qe.meaning η) J Ret)
    (he : Effects host P.meaning (.step (.bind y (.call f (parameters.map Argument.variable)))) Φ Φe) :
    let σ := extendCallRenaming inputs actual y z
    (Triple host (P.rename σ).meaning (.step (.bind z (.call f (parameters.map fun x => Argument.variable (actual x)))))
      ((Q.rename (TwoState.programMap σ id id)).meaning η) ((Qe.rename (TwoState.programMap σ id id)).meaning η)
      (RenamePost σ J) (fun v => RenamePost σ (Ret v)) ∧
    Effects host (P.rename σ).meaning (.step (.bind z (.call f (parameters.map fun x => Argument.variable (actual x)))))
      (Footprint.rename σ Φ) (Footprint.rename σ Φe)) ∧
    CallInstanceAdmitted Γ (fun x => x = z ∨ Γ x) (P.rename σ)
      (Q.rename (TwoState.programMap σ id id)) (Qe.rename (TwoState.programMap σ id id))
      (Footprint.rename σ Φ) (Footprint.rename σ Φe) preTypes entryTypes resultTypes ∧
    Command.WellScoped Γ (.step (.bind z (.call f (parameters.map fun x => Argument.variable (actual x)))))
      (fun x => x = z ∨ Γ x) := by
  have himages : ∀ x ∈ inputs, actual x ≠ z := by
    intro x hx heq
    apply hfresh
    exact heq ▸ ha x hx
  refine ⟨finite_call_syntax_rule inputs parameters actual hy hf hcallee hargs himages P Q Qe η ht he,
    call_instance_admitted hy ha hs, ?_⟩
  apply Command.WellScoped.bind hfresh ?_ (by trivial)
  refine ⟨?_, ?_⟩
  · simpa only [hcallee] using ha f hf
  · intro a hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    exact ha x (hargs x hx)

/-- Every part of the instantiated specification is independent of unused
map images, including the two outer regional effects. -/
theorem CallStatic.extension_independent {inputs y σ τ P Q Qe Φ Φe preTypes entryTypes resultTypes}
    (hs : CallStatic inputs y σ P Q Qe Φ Φe preTypes entryTypes resultTypes)
    (hm : ∀ x ∈ inputs, σ x = τ x) (hy : σ y = τ y) :
    (P.rename σ).meaning = (P.rename τ).meaning ∧
    Q.rename (TwoState.programMap σ id id) = Q.rename (TwoState.programMap τ id id) ∧
    Qe.rename (TwoState.programMap σ id id) = Qe.rename (TwoState.programMap τ id id) ∧
    Footprint.rename σ Φ = Footprint.rename τ Φ ∧ Footprint.rename σ Φe = Footprint.rename τ Φe := by
  refine ⟨?_, Q.call_extension_independent hm hy hs.normalScope,
    Qe.rename_program_agree hm hm id id hs.exceptionalScope,
    effect_rename_extension hm hs.normalEffectsScope, effect_rename_extension hm hs.exceptionalEffectsScope⟩
  rw [P.rename_meaning, P.rename_meaning]
  exact RenamePre.extension_independent hs.preScope.dependsOn hm

end Verification.Paper.TolerantFrames
