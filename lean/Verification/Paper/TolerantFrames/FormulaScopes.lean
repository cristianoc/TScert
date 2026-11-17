import Verification.Paper.TolerantFrames.Scopes
import Verification.Paper.TolerantFrames.Admission
import Verification.Paper.TolerantFrames.Renaming

/-! # Lexical scope of the complete one-state assertion language

This extends command scope and semantic dependence to every assertion term,
body, region and modality. A logical binder adds slot zero and shifts outer
slots. Lexical scope does not disappear merely because an assertion is a
tautology. Scope implies semantic dependence and survives free-name renaming.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations TolerantFrames
open Verification.Parity (Path)

def RegionNames (Γ : Scope) (r : Region) : Prop := ∀ x ∈ Parity.regionRoots r, Γ x
def EffectNames (Γ : Scope) (Φ : Footprint) : Prop := ∀ e ∈ Φ, RegionNames Γ e.1

def Scope.underValue (Γ : Scope) : Scope | 0 => True | x + 1 => Γ x

def BaseValue.Scoped (Γ : Scope) : BaseValue → Prop | .variable x => Γ x | .literal _ => True
def Value.Scoped (Γ : Scope) : Value → Prop | .base v | .converted _ v => v.Scoped Γ

mutual
def Term.Scoped (Γ : Scope) : Term → Prop
  | .literal _ => True
  | .path _ p | .lengthPath p => Γ p.root
  | .element _ p e _ _ | .lengthElement p e _ => Γ p.root ∧ e.Scoped Γ

def Expression.Scoped (Γ : Scope) : Expression → Prop
  | .constant _ => True
  | .scale _ t => t.Scoped Γ
  | .add e f => e.Scoped Γ ∧ f.Scoped Γ
end

def BodyTerm.Scoped (Γ : Scope) : BodyTerm → Prop | .free t => t.Scoped Γ | _ => True
def BodyExpression.Scoped (Γ : Scope) : BodyExpression → Prop
  | .constant _ => True | .scale _ t => t.Scoped Γ | .add e f => e.Scoped Γ ∧ f.Scoped Γ

def Clause.Scoped (Γ : Scope) : Clause → Prop
  | .le e f => e.Scoped Γ ∧ f.Scoped Γ | .or c d => c.Scoped Γ ∧ d.Scoped Γ

def Body.Scoped (Γ : Scope) : Body → Prop | .clause c => c.Scoped Γ | .and b c => b.Scoped Γ ∧ c.Scoped Γ

def Atom.Scoped (Γ : Scope) : Atom → Prop
  | .le e f => e.Scoped Γ ∧ f.Scoped Γ
  | .equal p v | .optionalEqual p _ v => Γ p.root ∧ v.Scoped Γ
  | .contents p _ => Γ p.root
  | .dense x e => Γ x ∧ e.Scoped Γ
  | .element p e v => Γ p.root ∧ e.Scoped Γ ∧ v.Scoped Γ
  | .every p e b => Γ p.root ∧ e.Scoped Γ ∧ b.Scoped Γ

def Formula.Scoped (Γ : Scope) : Formula → Prop
  | .truth | .falsity => True
  | .atom a => a.Scoped Γ
  | .and F G | .or F G => F.Scoped Γ ∧ G.Scoped Γ
  | .existsValue F => F.Scoped Γ.underValue
  | .separated p q => Γ p.root ∧ Γ q.root
  | .apart x y => Γ x ∧ Γ y
  | .fresh r => RegionNames Γ r
  | .box Φ F => EffectNames Γ Φ ∧ F.Scoped Γ

theorem BaseValue.eval_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {v : BaseValue} (hv : v.Scoped Γ) : v.eval ρ = v.eval ρ' := by
  cases v with | «variable» x => exact ha x hv | literal _ => rfl

theorem Value.eval_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {v : Value} (hv : v.Scoped Γ) : v.eval ρ = v.eval ρ' := by
  cases v <;> simp only [Value.eval, BaseValue.eval_scope ha hv]

mutual
theorem Term.eval_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {t : Term} (ht : t.Scoped Γ) (h : Heap) : t.eval ρ h = t.eval ρ' h := by
  cases t with
  | literal _ => rfl
  | path _ p | lengthPath p => simp only [Term.eval, Parity.Path.read, ha _ ht]
  | element _ p e _ _ | lengthElement p e _ => simp only [Term.eval, Parity.Path.read, ha _ ht.1, Expression.eval_scope ha ht.2]

theorem Expression.eval_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {e : Expression} (he : e.Scoped Γ) (h : Heap) : e.eval ρ h = e.eval ρ' h := by
  cases e with
  | constant _ => rfl
  | scale _ _ => simp only [Expression.eval, Term.eval_scope ha he]
  | add _ _ => simp only [Expression.eval, Expression.eval_scope ha he.1, Expression.eval_scope ha he.2]
end

theorem BodyTerm.eval_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {t : BodyTerm} (ht : t.Scoped Γ) (h : Heap) (z : Val) (i : Int) : t.eval ρ h z i = t.eval ρ' h z i := by
  cases t with | free _ => exact Term.eval_scope ha ht h | _ => rfl

theorem BodyExpression.eval_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {e : BodyExpression} (he : e.Scoped Γ) (h : Heap) (z : Val) (i : Int) : e.eval ρ h z i = e.eval ρ' h z i := by
  induction e with
  | constant _ => rfl
  | scale _ _ => simp only [BodyExpression.eval, BodyTerm.eval_scope ha he]
  | add _ _ ih₁ ih₂ => simp only [BodyExpression.eval, ih₁ he.1, ih₂ he.2]

theorem Clause.holds_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {c : Clause} (hc : c.Scoped Γ) (h : Heap) (z : Val) (i : Int) : c.Holds ρ h z i ↔ c.Holds ρ' h z i := by
  induction c with
  | le _ _ => simp only [Clause.Holds, BodyExpression.eval_scope ha hc.1, BodyExpression.eval_scope ha hc.2]
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ hc.1) (ih₂ hc.2)

theorem Body.holds_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {b : Body} (hb : b.Scoped Γ) (h : Heap) (z : Val) (i : Int) : b.Holds ρ h z i ↔ b.Holds ρ' h z i := by
  induction b with
  | clause _ => exact Clause.holds_scope ha hb h z i
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ hb.1) (ih₂ hb.2)

theorem Atom.holds_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {a : Atom} (hA : a.Scoped Γ) (h : Heap) : a.Holds ρ h ↔ a.Holds ρ' h := by
  cases a with
  | le _ _ => simp only [Atom.Holds, Expression.eval_scope ha hA.1, Expression.eval_scope ha hA.2]
  | equal p _ | optionalEqual p _ _ => simp only [Atom.Holds, optionalRead, Parity.Path.read, ha _ hA.1, Value.eval_scope ha hA.2]
  | contents p _ => simp only [Atom.Holds, Parity.Path.read, ha _ hA]
  | dense x _ => simp only [Atom.Holds, ha _ hA.1, Expression.eval_scope ha hA.2]
  | element p _ _ => simp only [Atom.Holds, Parity.Path.read, ha _ hA.1, Expression.eval_scope ha hA.2.1, Value.eval_scope ha hA.2.2]
  | every p _ _ => simp only [Atom.Holds, Every, Parity.Path.read, ha _ hA.1, Expression.eval_scope ha hA.2.1, Body.holds_scope ha hA.2.2]

theorem region_mem_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {r : Region} (hr : RegionNames Γ r) (h : Heap) (l : Nat) : r.mem ρ h l = r.mem ρ' h l := by
  induction r with
  | field x _ | fields x | cells x | path x _ _ | pathFields x _ | pathCells x _ | spine x _ =>
    simp only [Region.mem, ha x (hr x (by simp [Parity.regionRoots]))]
  | cls _ | all => rfl
  | inCls _ _ ih => simp only [Region.mem, ih hr]

theorem action_scope {Γ ρ ρ'} (ha : ∀ x, Γ x → ρ x = ρ' x) {Φ : Footprint} (hΦ : EffectNames Γ Φ) (s t : IndexedHeap) : Action Φ ρ s t ↔ Action Φ ρ' s t := by
  have allowed : ∀ l v v', Allowed Φ ρ s.h l v v' ↔ Allowed Φ ρ' s.h l v v' := by
    intro l v v'
    simp only [Allowed]
    apply or_congr Iff.rfl
    exact exists_congr fun e => and_congr_right fun he => and_congr (by rw [region_mem_scope ha (hΦ e he)]) Iff.rfl
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun l => forall_congr' fun v =>
    imp_congr_right fun _ => exists_congr fun v' => and_congr Iff.rfl (allowed l v v')))

theorem Formula.Scoped.dependsOn {Γ F} (hF : Formula.Scoped Γ F) : DependsOn F.meaning Γ := by
  intro ρ ρ' m s ha
  induction F generalizing Γ ρ ρ' s with
  | truth | falsity => rfl
  | atom _ => exact Atom.holds_scope ha hF s.h
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ hF.1 ρ ρ' s ha) (ih₂ hF.2 ρ ρ' s ha)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ hF.1 ρ ρ' s ha) (ih₂ hF.2 ρ ρ' s ha)
  | existsValue _ ih =>
    simp only [Formula.meaning, Formula.Holds]
    exact exists_congr fun v => and_congr_right fun _ => and_congr_right fun _ =>
      ih hF (push v ρ) (push v ρ') s (fun x hx => by cases x with | zero => rfl | succ x => exact ha x hx)
  | separated p q => simp only [Formula.meaning, Formula.Holds, ha _ hF.1, ha _ hF.2]
  | apart x y => simp only [Formula.meaning, Formula.Holds, Parity.Apart, Parity.Path.read, ha _ hF.1, ha _ hF.2]
  | fresh _ => simp only [Formula.meaning, Formula.Holds, Fresh, region_mem_scope ha hF]
  | box Φ F ih =>
    simp only [Formula.meaning, Formula.Holds]
    exact forall_congr' fun t => imp_congr (action_scope ha hF.1 s t) (ih hF.2 ρ ρ' t ha)

theorem regionRoots_rename (σ : Nat → Nat) (r : Region) :
    Parity.regionRoots (r.rename σ) = (Parity.regionRoots r).map σ := by
  induction r <;> simp only [Region.rename, Parity.regionRoots, List.map_cons, List.map_nil, *]

theorem RegionNames.rename {Γ Δ σ r} (hm : ∀ x, Γ x → Δ (σ x)) (h : RegionNames Γ r) : RegionNames Δ (r.rename σ) := by
  intro x hx
  rw [regionRoots_rename] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact hm y (h y hy)

theorem effectNames_rename {Γ Δ : Scope} {σ : Nat → Nat} {Φ : Footprint}
    (hm : ∀ x, Γ x → Δ (σ x)) (hΦ : EffectNames Γ Φ) : EffectNames Δ (Footprint.rename σ Φ) := by
  intro e he
  obtain ⟨original, hm', rfl⟩ := List.mem_map.mp he
  exact RegionNames.rename hm (hΦ original hm')

theorem BaseValue.Scoped.rename {Γ Δ σ v} (hm : ∀ x, Γ x → Δ (σ x)) (h : BaseValue.Scoped Γ v) : (v.rename σ).Scoped Δ := by
  cases v with | «variable» x => exact hm x h | literal _ => trivial

theorem Value.Scoped.rename {Γ Δ σ v} (hm : ∀ x, Γ x → Δ (σ x)) (h : Value.Scoped Γ v) : (v.rename σ).Scoped Δ := by
  cases v <;> exact BaseValue.Scoped.rename hm h

mutual
theorem Term.Scoped.rename {Γ Δ σ t} (hm : ∀ x, Γ x → Δ (σ x)) (h : Term.Scoped Γ t) : (t.rename σ).Scoped Δ := by
  cases t with
  | literal _ => trivial
  | path _ p | lengthPath p => exact hm _ h
  | element _ p e _ _ | lengthElement p e _ => exact ⟨hm _ h.1, Expression.Scoped.rename hm h.2⟩

theorem Expression.Scoped.rename {Γ Δ σ e} (hm : ∀ x, Γ x → Δ (σ x)) (h : Expression.Scoped Γ e) : (e.rename σ).Scoped Δ := by
  cases e with
  | constant _ => trivial
  | scale _ _ => exact Term.Scoped.rename hm h
  | add _ _ => exact ⟨Expression.Scoped.rename hm h.1, Expression.Scoped.rename hm h.2⟩
end

theorem BodyTerm.Scoped.rename {Γ Δ σ t} (hm : ∀ x, Γ x → Δ (σ x)) (h : BodyTerm.Scoped Γ t) : (t.rename σ).Scoped Δ := by
  cases t with | free _ => exact Term.Scoped.rename hm h | _ => trivial

theorem BodyExpression.Scoped.rename {Γ Δ σ e} (hm : ∀ x, Γ x → Δ (σ x)) (h : BodyExpression.Scoped Γ e) : (e.rename σ).Scoped Δ := by
  induction e with
  | constant _ => trivial
  | scale _ _ => exact BodyTerm.Scoped.rename hm h
  | add _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Clause.Scoped.rename {Γ Δ σ c} (hm : ∀ x, Γ x → Δ (σ x)) (h : Clause.Scoped Γ c) : (c.rename σ).Scoped Δ := by
  induction c with
  | le _ _ => exact ⟨BodyExpression.Scoped.rename hm h.1, BodyExpression.Scoped.rename hm h.2⟩
  | or _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Body.Scoped.rename {Γ Δ σ b} (hm : ∀ x, Γ x → Δ (σ x)) (h : Body.Scoped Γ b) : (b.rename σ).Scoped Δ := by
  induction b with
  | clause _ => exact Clause.Scoped.rename hm h
  | and _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem Atom.Scoped.rename {Γ Δ σ a} (hm : ∀ x, Γ x → Δ (σ x)) (h : Atom.Scoped Γ a) : (a.rename σ).Scoped Δ := by
  cases a with
  | le _ _ => exact ⟨Expression.Scoped.rename hm h.1, Expression.Scoped.rename hm h.2⟩
  | equal _ _ | optionalEqual _ _ _ => exact ⟨hm _ h.1, Value.Scoped.rename hm h.2⟩
  | contents _ _ => exact hm _ h
  | dense _ _ => exact ⟨hm _ h.1, Expression.Scoped.rename hm h.2⟩
  | element _ _ _ => exact ⟨hm _ h.1, Expression.Scoped.rename hm h.2.1, Value.Scoped.rename hm h.2.2⟩
  | every _ _ _ => exact ⟨hm _ h.1, Expression.Scoped.rename hm h.2.1, Body.Scoped.rename hm h.2.2⟩

theorem Formula.Scoped.rename {Γ Δ σ F} (hm : ∀ x, Γ x → Δ (σ x)) (h : Formula.Scoped Γ F) : (F.rename σ).Scoped Δ := by
  induction F generalizing Γ Δ σ with
  | truth | falsity => trivial
  | atom _ => exact Atom.Scoped.rename hm h
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ => exact ⟨ih₁ hm h.1, ih₂ hm h.2⟩
  | existsValue _ ih =>
    apply ih (fun x hx => ?_) h
    cases x with | zero => trivial | succ x => exact hm x hx
  | separated _ _ | apart _ _ => exact ⟨hm _ h.1, hm _ h.2⟩
  | fresh _ => exact RegionNames.rename hm h
  | box _ _ ih => exact ⟨effectNames_rename hm h.1, ih hm h.2⟩

/-- Frame's noncapture premise follows from the actual lexical judgments. -/
theorem Formula.Scoped.scope_stable {host Γ Δ c F} (hF : Formula.Scoped Γ F)
    (hc : Command.WellScoped Γ c Δ) : ScopeStable host c F.meaning :=
  scope_stable_of_avoids hF.dependsOn hc.avoids_inputs

end Verification.Paper.TolerantFrames
