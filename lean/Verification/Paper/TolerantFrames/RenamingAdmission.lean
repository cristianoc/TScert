import Verification.Paper.TolerantFrames.Admission
import Verification.Paper.TolerantFrames.Renaming

/-! # Declared-type admission under renaming

Renaming does not infer collection/object types from equality at one heap.
The source declarations are the pullback of the actual declarations. Lifting
through an existential commutes with that pullback, so the bound logical value
is not accidentally assigned a free program variable's declared type.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints
open Verification.Parity (Path)

/-- Formal paths have the declared classification of their actual paths. -/
def DeclaredPaths.pullback (σ : Nat → Nat) (types : DeclaredPaths) : DeclaredPaths where
  collection p := types.collection (renamePath σ p)
  object p := types.object (renamePath σ p)
  field p f := types.field (renamePath σ p) f

theorem DeclaredPaths.pullback_underValue (σ : Nat → Nat) (types : DeclaredPaths) :
    types.underValue.pullback (liftRenaming σ) = (types.pullback σ).underValue := by
  unfold DeclaredPaths.pullback DeclaredPaths.underValue
  congr 1
  · funext p; cases p with | mk x fs => cases x <;> simp [renamePath, liftRenaming]
  · funext p; cases p with | mk x fs => cases x <;> simp [renamePath, liftRenaming]
  · funext p f; cases p with | mk x fs => cases x <;> simp [renamePath, liftRenaming]

theorem RegionWellFormed.rename {types : DeclaredPaths} {σ : Nat → Nat} {r : Region}
    (hr : RegionWellFormed (types.pullback σ) r) : RegionWellFormed types (r.rename σ) := by
  cases hr with
  | values => exact .values
  | spines => exact .spines
  | views => exact .views
  | spine h => exact .spine h
  | cells h => exact .cells h
  | fields h => exact .fields h
  | field ho hf => exact .field ho hf

theorem EffectWellFormed.rename {types : DeclaredPaths} {σ : Nat → Nat} {Φ : Footprint}
    (he : EffectWellFormed (types.pullback σ) Φ) : EffectWellFormed types (Footprint.rename σ Φ) := by
  intro e hm
  obtain ⟨⟨r, δ⟩, hr, rfl⟩ := List.mem_map.mp hm
  exact (he (r, δ) hr).rename

theorem Formula.WellFormed.rename {types : DeclaredPaths} {σ : Nat → Nat} {F : Formula}
    (hF : F.WellFormed (types.pullback σ)) : (F.rename σ).WellFormed types := by
  induction F generalizing types σ with
  | truth | falsity | atom _ | separated _ _ | apart _ _ => trivial
  | and F G ihF ihG | or F G ihF ihG => exact ⟨ihF hF.1, ihG hF.2⟩
  | existsValue F ih =>
    apply ih
    rw [DeclaredPaths.pullback_underValue]
    exact hF
  | fresh r => exact RegionWellFormed.rename hF
  | box Φ F ih => exact ⟨EffectWellFormed.rename hF.1, ih hF.2⟩

end Verification.Paper.TolerantFrames
