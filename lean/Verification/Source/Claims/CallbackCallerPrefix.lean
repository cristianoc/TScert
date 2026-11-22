import Verification.Source.Claims.CallbackTypicalReturn
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open ControlFlow GraphCode ProgramTyping PositiveGraphs PositiveRules ProgramCertificates CallbackEffectInference
open HeapObservations LabelStore

def shadowEnv (Γ : List (Option (Ty ι))) (ρ : Env) : Env :=
  fun i => if Γ[i]?.join.isSome then ρ i else .undef

private theorem shadow_typed {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {Γ ρ n W U}
    (ok : PartialEnv G Γ ρ n W) (unknown : PromiseCalls.admitsUndef G U = true) :
    EnvOk G (Γ.map (·.getD U)) (shadowEnv Γ ρ) n W := by
  refine ⟨fun i => ?_,?_⟩
  · unfold shadowEnv
    split <;> first | exact ok.1 i | trivial
  · intro i A hit
    simp only [List.getElem?_map,Option.map_eq_some_iff] at hit
    obtain ⟨t,found,rfl⟩ := hit
    cases t with
    | none => simpa [shadowEnv,found] using PromiseCalls.admitsUndef_sound unknown n W
    | some A => simpa [shadowEnv,found] using ok.2 i A (by simp [found])

mutual
def prefixReads (visible : Nat → Bool) (depth : Nat) : Tm → Bool
  | .var i => i < depth || visible (i-depth)
  | .letE a b => prefixReads visible depth a && prefixReads visible (depth+1) b
  | .arrLit args | .makeAt .absent _ args => prefixReadsAll visible depth args
  | .makeAt (.graph _ _ _ _ caps _ _ _) _ args => prefixReadsAll visible depth caps && prefixReadsAll visible depth args
  | .nul | .undef | .num _ | .str _ | .tru | .fls => true
  | _ => false
def prefixReadsAll (visible : Nat → Bool) (depth : Nat) : List Tm → Bool
  | [] => true
  | a :: rest => prefixReads visible depth a && prefixReadsAll visible depth rest
end

mutual
theorem prefixReads_eq {visible : Nat → Bool} {ρ σ : Env} (agree : ∀ i, visible i = true → ρ i = σ i) (d : Nat) (t : Tm)
    (ok : prefixReads visible d t = true) : instantiate d ρ t = instantiate d σ t := by
  cases t <;> try rfl
  all_goals try (simp [prefixReads] at ok; done)
  case var i =>
    simp only [prefixReads,Bool.or_eq_true,decide_eq_true_eq] at ok
    by_cases h : i < d
    · simp [instantiate,h]
    · simp [instantiate,h,agree _ (ok.resolve_left h)]
  case letE a b =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp ok
    simp [instantiate,prefixReads_eq agree _ a ha,prefixReads_eq agree _ b hb]
  case arrLit args => simp only [instantiate,prefixReadsAll_eq agree _ args ok]
  case makeAt code names args =>
    cases code <;> try contradiction
    case absent => simp only [instantiate,prefixReadsAll_eq agree _ args ok]
    case graph ar E K start caps kind rest comp =>
      obtain ⟨hc,ha⟩ := Bool.and_eq_true_iff.mp ok
      simp only [instantiate,prefixReadsAll_eq agree _ caps hc,prefixReadsAll_eq agree _ args ha]
termination_by sizeOf t
theorem prefixReadsAll_eq {visible : Nat → Bool} {ρ σ : Env} (agree : ∀ i, visible i = true → ρ i = σ i) (d : Nat) (ts : List Tm)
    (ok : prefixReadsAll visible d ts = true) : instantiateArgs d ρ ts = instantiateArgs d σ ts := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    obtain ⟨ht,hr⟩ := Bool.and_eq_true_iff.mp ok
    simp only [instantiateArgs,prefixReads_eq agree d t ht,prefixReadsAll_eq agree d ts hr]
termination_by sizeOf ts
end

/-- The prefix reads a checked expression at the retained ordinary slots.
The optional slots carrying the opaque marked function receive an unused
undefined value in the auxiliary ordinary sequent. -/
structure PrefixExpression {ι : Type} [DecidableEq ι] (G : NormalGraph ι)
    (I : PositiveCertificates.InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (Γ : List (Option (Ty ι))) (term : Tm) (A : Ty ι) where
  filler : Ty ι
  fillerOk : PromiseCalls.admitsUndef G filler = true
  independent : prefixReads (fun (i : Nat) => Γ[i]?.join.isSome) 0 term = true
  evidence : Evidence ι
  same : claim evidence = ⟨Γ.map (·.getD filler),term,A⟩
  checked : checkTreeUsing G I evidence codes [] = true

theorem PrefixExpression.safe {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {I codes Γ term A}
    (p : PrefixExpression G I codes Γ term A) (codeTable : CodesSound G codes)
    {ρ n W h} (typed : PartialEnv G Γ ρ n W) (world : WorldAdm W) (heap : HeapOk n W h)
    (refs : RefsOk W (instantiate 0 ρ term)) :
    Safe (excOf G) (meaning G A) n W h (instantiate 0 ρ term) := by
  have deriv := checkTreeUsing_sound p.evidence p.checked codeTable
  rw [p.same] at deriv
  have same : instantiate 0 ρ term = instantiate 0 (shadowEnv Γ ρ) term :=
    prefixReads_eq (fun i available => by simp [shadowEnv,available]) 0 term p.independent
  rw [same] at refs ⊢
  exact deriv.sound _ _ _ _ (shadow_typed typed p.fillerOk) world heap refs

end Verification.SourceClaimJson.CallbackInterfaceCheck
