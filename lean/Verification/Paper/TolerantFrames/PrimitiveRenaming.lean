import Verification.Paper.TolerantFrames.Renaming
import Verification.Paper.TolerantFrames.Commands
import Verification.Paper.TolerantFrames.PostconditionRenaming
import Verification.Semantics.FootprintStability

/-! # Actual primitive execution under argument renaming

The existing mechanisms are primitive execution, fresh binding and shared
footprint renaming. Actual arguments may alias. The only injectivity condition
is at a fresh result name. Output context validity is proved for the whole
actual environment, not inferred from its pullback at formal names.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations TolerantFrames

def Argument.rename (σ : Nat → Nat) : Argument → Argument
  | .variable x => .variable (σ x)
  | .literal v => .literal v

theorem Argument.eval_rename (σ : Nat → Nat) (ρ : Env) (a : Argument) :
    (a.rename σ).eval ρ = a.eval (fun x => ρ (σ x)) := by cases a <;> rfl

def Operation.rename (σ : Nat → Nat) : Operation → Operation
  | .value a => .value (a.rename σ)
  | .binary op a b => .binary op (a.rename σ) (b.rename σ)
  | .not a => .not (a.rename σ)
  | .and a b => .and (a.rename σ) (b.rename σ)
  | .or a b => .or (a.rename σ) (b.rename σ)
  | .fieldRead x f => .fieldRead (σ x) f
  | .fieldWrite x f v => .fieldWrite (σ x) f (v.rename σ)
  | .elementRead x i => .elementRead (σ x) (i.rename σ)
  | .elementWrite x i v => .elementWrite (σ x) (i.rename σ) (v.rename σ)
  | .arrayLength x => .arrayLength (σ x)
  | .viewRead x i => .viewRead (σ x) (i.rename σ)
  | .viewWrite x i v => .viewWrite (σ x) (i.rename σ) (v.rename σ)
  | .viewLength x => .viewLength (σ x)
  | .stringRead x i => .stringRead (σ x) (i.rename σ)
  | .stringLength x => .stringLength (σ x)
  | .objectLiteral fs => .objectLiteral (fs.map fun p => (p.1, p.2.rename σ))
  | .arrayLiteral es => .arrayLiteral (es.map (Argument.rename σ))
  | .methodCall x f args => .methodCall (σ x) f (args.map (Argument.rename σ))
  | .call f args => .call (σ f) (args.map (Argument.rename σ))
  | .construct f args => .construct (σ f) (args.map (Argument.rename σ))

/-- All primitive forms execute the identical shared term after pullback. -/
theorem Operation.code_rename (σ : Nat → Nat) (host : NativeCode) (ρ : Env) (op : Operation) :
    (op.rename σ).code host ρ = op.code host (fun x => ρ (σ x)) := by
  cases op <;> simp only [Operation.rename, Operation.code, Argument.eval_rename,
    List.map_map, Function.comp_def]

def Primitive.rename (σ : Nat → Nat) : Primitive → Primitive
  | .bind x op => .bind (σ x) (op.rename σ)
  | .perform op => .perform (op.rename σ)

/-- A fresh result has no colliding formal name. Actual arguments may alias. -/
def Primitive.FreshRenaming (σ : Nat → Nat) : Primitive → Prop
  | .bind y _ => ∀ x, σ x = σ y ↔ x = y
  | .perform _ => True

theorem bindName_pullback {σ : Nat → Nat} {y : Nat} (hf : ∀ x, σ x = σ y ↔ x = y)
    (ρ : Env) (v : Val) :
    (fun x => bindName ρ (σ y) v (σ x)) = bindName (fun x => ρ (σ x)) y v := by
  funext x
  simp only [bindName, hf x]

/-- Formal and actual executions have the same steps, heap and exit. -/
theorem PrimitiveRun.pullback {host p σ ρ h n ρ' h' e}
    (hf : p.FreshRenaming σ) (hr : PrimitiveRun host (p.rename σ) ρ h n ρ' h' e) :
    PrimitiveRun host p (fun x => ρ (σ x)) h n (fun x => ρ' (σ x)) h' e := by
  cases p with
  | bind y op =>
    cases hr with
    | normal hs hv =>
      simp only [Primitive.rename, Primitive.operation, Operation.code_rename] at hs
      simp only [Primitive.rename, Primitive.bindResult, bindName_pullback hf]
      exact .normal hs hv
    | thrown hs hv =>
      apply PrimitiveRun.thrown (v := _) _ hv
      simpa only [Primitive.rename, Primitive.operation, Operation.code_rename] using hs
  | perform op =>
    cases hr with
    | normal hs hv =>
      apply PrimitiveRun.normal _ hv
      simpa only [Primitive.rename, Primitive.operation, Operation.code_rename] using hs
    | thrown hs hv =>
      apply PrimitiveRun.thrown (v := _) _ hv
      simpa only [Primitive.rename, Primitive.operation, Operation.code_rename] using hs

/-- Pullback validity alone says nothing about unmapped actual slots. Recover
those from the input context and the result from the formal output context. -/
theorem PrimitiveRun.actual_context {host} {p : Primitive} {σ : Nat → Nat} {ρ h n ρ' h' e m s t}
    (hr : PrimitiveRun host (p.rename σ) ρ h n ρ' h' e)
    (hv : ValidContext ρ m s) (ha : Admissible s t)
    (ht : ValidContext (fun x => ρ' (σ x)) m t) : ValidContext ρ' m t := by
  cases p with
  | bind y op =>
    cases hr with
    | normal _ hsource =>
      apply (hv.admissible ha).bindName
      have href := ht.1 y
      simp only [Primitive.rename, Primitive.bindResult, bindName, ↓reduceIte] at href
      exact ⟨hsource, href⟩
    | thrown _ _ => exact hv.admissible ha
  | perform op => cases hr <;> exact hv.admissible ha

def RenamePre (σ : Nat → Nat) (P : Assertion) : Assertion := fun ρ m s => P (fun x => ρ (σ x)) m s

def RenamePost (σ : Nat → Nat) (Q : Postcondition) : Postcondition :=
  fun ρ ρ' m s t => Q (fun x => ρ (σ x)) (fun x => ρ' (σ x)) m s t

/-- General primitive triple transport at actual execution, for both exits. -/
theorem primitive_triple_rename {host p σ P Q Qe J Ret}
    (hf : p.FreshRenaming σ) (ht : Triple host P (.step p) Q Qe J Ret) :
    Triple host (RenamePre σ P) (.step (p.rename σ)) (RenamePost σ Q) (RenamePost σ Qe)
      (RenamePost σ J) (fun v => RenamePost σ (Ret v)) := by
  intro ρ m s n ρ' h' e hv hp hr hn
  cases hr with
  | step hr =>
    have hpull := PrimitiveRun.pullback hf hr
    obtain ⟨t, ha, hh, hk, hvt, hve, hq⟩ := ht _ _ _ _ _ _ _ (hv.rename σ) hp (.step hpull) hn
    refine ⟨t, ha, hh, hk, hr.actual_context hv ha hvt, hve, ?_⟩
    cases e <;> exact hq

/-- Normal and exceptional effects rename at the same actual invocation. -/
theorem primitive_effects_rename {host p σ P Φ Φe}
    (hf : p.FreshRenaming σ) (he : Effects host P (.step p) Φ Φe) :
    Effects host (RenamePre σ P) (.step (p.rename σ)) (Footprint.rename σ Φ) (Footprint.rename σ Φe) := by
  intro ρ m s n ρ' h' e hv hp hr hn
  cases hr with
  | step hr =>
    have hpull := PrimitiveRun.pullback hf hr
    have hpost := he _ _ _ _ _ _ _ (hv.rename σ) hp (.step hpull) hn
    have hrename := Footprints.Post.rename (σ := σ) (ρ := ρ) (fun _ => rfl) hpost
    cases e <;> exact hrename

/-- Call of the paper at variable actual arguments, with unrestricted
argument aliasing and a fresh result. This uses an actual formal call triple
and effect, not an assumed renamed-call summary. -/
theorem call_rule {host σ P Q Qe J Ret Φ Φe f y} (parameters : List Nat)
    (hf : ∀ x, σ x = σ y ↔ x = y)
    (ht : Triple host P (.step (.bind y (.call f (parameters.map Argument.variable)))) Q Qe J Ret)
    (he : Effects host P (.step (.bind y (.call f (parameters.map Argument.variable)))) Φ Φe) :
    Triple host (RenamePre σ P) (.step (.bind (σ y) (.call (σ f) (parameters.map fun x => Argument.variable (σ x)))))
      (RenamePost σ Q) (RenamePost σ Qe) (RenamePost σ J) (fun v => RenamePost σ (Ret v)) ∧
    Effects host (RenamePre σ P) (.step (.bind (σ y) (.call (σ f) (parameters.map fun x => Argument.variable (σ x)))))
      (Footprint.rename σ Φ) (Footprint.rename σ Φe) := by
  constructor
  · simpa only [Primitive.rename, Operation.rename, List.map_map, Function.comp_def, Argument.rename] using
      primitive_triple_rename (σ := σ) (p := .bind y (.call f (parameters.map Argument.variable))) hf ht
  · simpa only [Primitive.rename, Operation.rename, List.map_map, Function.comp_def, Argument.rename] using
      primitive_effects_rename (σ := σ) (p := .bind y (.call f (parameters.map Argument.variable))) hf he

/-- Extend the finite scope's actual-name assignment. Unused names avoid the
fresh result; no injectivity of actual arguments is required. -/
def extendCallRenaming (inputs : List Nat) (actual : Nat → Nat) (formalResult actualResult : Nat) : Nat → Nat :=
  fun x => if x = formalResult then actualResult else if x ∈ inputs then actual x else actualResult + 1

theorem extendCallRenaming_result (inputs : List Nat) (actual : Nat → Nat) (y z : Nat) :
    extendCallRenaming inputs actual y z y = z := by simp [extendCallRenaming]

theorem extendCallRenaming_inputs {inputs : List Nat} {actual : Nat → Nat} {y z x : Nat}
    (hy : y ∉ inputs) (hx : x ∈ inputs) : extendCallRenaming inputs actual y z x = actual x := by
  have hxy : x ≠ y := by intro he; exact hy (he ▸ hx)
  simp [extendCallRenaming, hxy, hx]

theorem extendCallRenaming_fresh {inputs : List Nat} {actual : Nat → Nat} {y z : Nat}
    (ha : ∀ x ∈ inputs, actual x ≠ z) :
    ∀ x, extendCallRenaming inputs actual y z x = extendCallRenaming inputs actual y z y ↔ x = y := by
  intro x
  by_cases hxy : x = y
  · simp [extendCallRenaming, hxy]
  · by_cases hx : x ∈ inputs
    · simp [extendCallRenaming, hxy, hx, ha x hx]
    · simp [extendCallRenaming, hxy, hx]

theorem extendCallRenaming_callee {inputs : List Nat} {actual : Nat → Nat} {y z f : Nat}
    (hy : y ∉ inputs) (hf : f ∈ inputs) (hfixed : actual f = f) :
    extendCallRenaming inputs actual y z f = f := (extendCallRenaming_inputs hy hf).trans hfixed

/-- The semantic transport is the actual capture-avoiding first-order
program renaming, leaving logical binders and their valuations fixed. -/
theorem TwoState.Post.program_rename_meaning (σ : Nat → Nat) (η : TwoState.LogicalEnv) (Q : TwoState.Post) :
    (Q.rename ⟨σ, id, id⟩).meaning η = RenamePost σ (Q.meaning η) := by
  funext ρ ρ' m s t
  apply propext
  exact Q.holds_rename ⟨σ, id, id⟩ ⟨⟨ρ, s⟩, ⟨ρ', t⟩, m⟩ η

end Verification.Paper.TolerantFrames
