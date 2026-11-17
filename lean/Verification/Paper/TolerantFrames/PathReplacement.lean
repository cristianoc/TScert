import Verification.Paper.TolerantFrames.Renaming

/-! # Equality-preserving replacement of selected paths

Definition 23 permits replacing an occurring path by an equal path. This is a
structural relation on grammar-admissible input/output, not an operation that
silently drops fields when a variable-only position is encountered. Prefixes
can be replaced while their entire suffix is retained. Region admission is a
separate declared-type obligation, not a consequence of runtime equality.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames
open Verification.Parity (Path)

inductive PathReplacement (p q : Path) : Path → Path → Prop where
  | same (r) : PathReplacement p q r r
  | suffix (fs) : PathReplacement p q ⟨p.root, p.fields ++ fs⟩ ⟨q.root, q.fields ++ fs⟩

mutual
inductive TermReplacement (p q : Path) : Term → Term → Prop where
  | same (t) : TermReplacement p q t t
  | path {k a b} : PathReplacement p q a b → TermReplacement p q (.path k a) (.path k b)
  | lengthPath {a b} : PathReplacement p q a b → TermReplacement p q (.lengthPath a) (.lengthPath b)
  | element {k a b i j fs valid} : PathReplacement p q a b → ExpressionReplacement p q i j →
      TermReplacement p q (.element k a i fs valid) (.element k b j fs valid)
  | lengthElement {a b i j fs} : PathReplacement p q a b → ExpressionReplacement p q i j →
      TermReplacement p q (.lengthElement a i fs) (.lengthElement b j fs)
inductive ExpressionReplacement (p q : Path) : Expression → Expression → Prop where
  | same (e) : ExpressionReplacement p q e e
  | scale {c t u} : TermReplacement p q t u → ExpressionReplacement p q (.scale c t) (.scale c u)
  | add {a b c d} : ExpressionReplacement p q a b → ExpressionReplacement p q c d →
      ExpressionReplacement p q (.add a c) (.add b d)
end

inductive BodyTermReplacement (p q : Path) : BodyTerm → BodyTerm → Prop where
  | same (t) : BodyTermReplacement p q t t
  | free {t u} : TermReplacement p q t u → BodyTermReplacement p q (.free t) (.free u)

inductive BodyExpressionReplacement (p q : Path) : BodyExpression → BodyExpression → Prop where
  | same (e) : BodyExpressionReplacement p q e e
  | scale {c t u} : BodyTermReplacement p q t u → BodyExpressionReplacement p q (.scale c t) (.scale c u)
  | add {a b c d} : BodyExpressionReplacement p q a b → BodyExpressionReplacement p q c d →
      BodyExpressionReplacement p q (.add a c) (.add b d)

inductive ClauseReplacement (p q : Path) : Clause → Clause → Prop where
  | same (c) : ClauseReplacement p q c c
  | le {a b c d} : BodyExpressionReplacement p q a b → BodyExpressionReplacement p q c d →
      ClauseReplacement p q (.le a c) (.le b d)
  | or {a b c d} : ClauseReplacement p q a b → ClauseReplacement p q c d →
      ClauseReplacement p q (.or a c) (.or b d)

inductive BodyReplacement (p q : Path) : Body → Body → Prop where
  | same (b) : BodyReplacement p q b b
  | clause {a b} : ClauseReplacement p q a b → BodyReplacement p q (.clause a) (.clause b)
  | and {a b c d} : BodyReplacement p q a b → BodyReplacement p q c d →
      BodyReplacement p q (.and a c) (.and b d)

inductive BaseValueReplacement (p q : Path) : BaseValue → BaseValue → Prop where
  | same (v) : BaseValueReplacement p q v v
  | variable {x y} : PathReplacement p q ⟨x, []⟩ ⟨y, []⟩ →
      BaseValueReplacement p q (.variable x) (.variable y)

inductive ValueReplacement (p q : Path) : Value → Value → Prop where
  | base {v w} : BaseValueReplacement p q v w → ValueReplacement p q (.base v) (.base w)
  | converted {f v w} : BaseValueReplacement p q v w → ValueReplacement p q (.converted f v) (.converted f w)

inductive AtomReplacement (p q : Path) : Atom → Atom → Prop where
  | same (a) : AtomReplacement p q a a
  | le {a b c d} : ExpressionReplacement p q a b → ExpressionReplacement p q c d → AtomReplacement p q (.le a c) (.le b d)
  | equal {a b v w} : PathReplacement p q a b → ValueReplacement p q v w → AtomReplacement p q (.equal a v) (.equal b w)
  | optionalEqual {a b f v w} : PathReplacement p q a b → ValueReplacement p q v w →
      AtomReplacement p q (.optionalEqual a f v) (.optionalEqual b f w)
  | dense {x y a b} : PathReplacement p q ⟨x, []⟩ ⟨y, []⟩ → ExpressionReplacement p q a b →
      AtomReplacement p q (.dense x a) (.dense y b)
  | contents {a b V} : PathReplacement p q a b → AtomReplacement p q (.contents a V) (.contents b V)
  | element {a b i j v w} : PathReplacement p q a b → ExpressionReplacement p q i j → ValueReplacement p q v w →
      AtomReplacement p q (.element a i v) (.element b j w)
  | every {a b i j c d} : PathReplacement p q a b → ExpressionReplacement p q i j → BodyReplacement p q c d →
      AtomReplacement p q (.every a i c) (.every b j d)

inductive RegionReplacement (p q : Path) : Region → Region → Prop where
  | same (r) : RegionReplacement p q r r
  | field {x y k} : PathReplacement p q ⟨x, []⟩ ⟨y, []⟩ → RegionReplacement p q (.field x k) (.field y k)
  | fields {x y} : PathReplacement p q ⟨x, []⟩ ⟨y, []⟩ → RegionReplacement p q (.fields x) (.fields y)
  | cells {x y} : PathReplacement p q ⟨x, []⟩ ⟨y, []⟩ → RegionReplacement p q (.cells x) (.cells y)
  | path {a b k} : PathReplacement p q a b → RegionReplacement p q (.path a.root a.fields k) (.path b.root b.fields k)
  | pathFields {a b} : PathReplacement p q a b → RegionReplacement p q (.pathFields a.root a.fields) (.pathFields b.root b.fields)
  | pathCells {a b} : PathReplacement p q a b → RegionReplacement p q (.pathCells a.root a.fields) (.pathCells b.root b.fields)
  | spine {a b} : PathReplacement p q a b → RegionReplacement p q (.spine a.root a.fields) (.spine b.root b.fields)
  | inCls {a b c} : RegionReplacement p q a b → RegionReplacement p q (.inCls a c) (.inCls b c)

inductive EffectReplacement (p q : Path) : Footprint → Footprint → Prop where
  | nil : EffectReplacement p q [] []
  | cons {e f Φ Ψ} : (RegionReplacement p q e.1 f.1 ∧ e.2 = f.2) → EffectReplacement p q Φ Ψ →
      EffectReplacement p q (e :: Φ) (f :: Ψ)

/-- Prefix replacement preserves successful and failed readings alike. The
public paper rule supplies equality of defined values. -/
theorem PathReplacement.read_eq {p q a b : Path} (hr : PathReplacement p q a b)
    {ρ : Env} {h : Heap} (he : p.read ρ h = q.read ρ h) : a.read ρ h = b.read ρ h := by
  cases hr with
  | same => rfl
  | suffix fs => simpa only [Path.read, readPath_append] using congrArg (fun v => v.bind (fun u => readPath h u fs)) he

mutual
theorem TermReplacement.eval_eq {p q t u} (hr : TermReplacement p q t u)
    {ρ h} (he : p.read ρ h = q.read ρ h) : t.eval ρ h = u.eval ρ h := by
  cases hr with
  | same => rfl
  | path hp | lengthPath hp => simp only [Term.eval, hp.read_eq he]
  | element hp hi | lengthElement hp hi => simp only [Term.eval, hp.read_eq he, hi.eval_eq he]

theorem ExpressionReplacement.eval_eq {p q a b} (hr : ExpressionReplacement p q a b)
    {ρ h} (he : p.read ρ h = q.read ρ h) : a.eval ρ h = b.eval ρ h := by
  cases hr with
  | same => rfl
  | scale ht => simp only [Expression.eval, ht.eval_eq he]
  | add h₁ h₂ => simp only [Expression.eval, h₁.eval_eq he, h₂.eval_eq he]
end

theorem BodyTermReplacement.eval_eq {p q a b} (hr : BodyTermReplacement p q a b)
    {ρ h z i} (he : p.read ρ h = q.read ρ h) : a.eval ρ h z i = b.eval ρ h z i := by
  cases hr with
  | same => rfl
  | free ht => exact ht.eval_eq he

theorem BodyExpressionReplacement.eval_eq {p q a b} (hr : BodyExpressionReplacement p q a b)
    {ρ h z i} (he : p.read ρ h = q.read ρ h) : a.eval ρ h z i = b.eval ρ h z i := by
  induction hr with
  | same => rfl
  | scale ht => simp only [BodyExpression.eval, ht.eval_eq he]
  | add _ _ ih₁ ih₂ => simp only [BodyExpression.eval, ih₁, ih₂]

theorem ClauseReplacement.holds_iff {p q a b} (hr : ClauseReplacement p q a b)
    {ρ h z i} (he : p.read ρ h = q.read ρ h) : a.Holds ρ h z i ↔ b.Holds ρ h z i := by
  induction hr with
  | same => rfl
  | le h₁ h₂ => simp only [Clause.Holds, h₁.eval_eq he, h₂.eval_eq he]
  | or _ _ ih₁ ih₂ => exact or_congr ih₁ ih₂

theorem BodyReplacement.holds_iff {p q a b} (hr : BodyReplacement p q a b)
    {ρ h z i} (he : p.read ρ h = q.read ρ h) : a.Holds ρ h z i ↔ b.Holds ρ h z i := by
  induction hr with
  | same => rfl
  | clause hc => exact hc.holds_iff he
  | and _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem BaseValueReplacement.eval_eq {p q a b} (hr : BaseValueReplacement p q a b)
    {ρ h} (he : p.read ρ h = q.read ρ h) : a.eval ρ = b.eval ρ := by
  cases hr with
  | same => rfl
  | «variable» hp => exact Option.some.inj (hp.read_eq he)

theorem ValueReplacement.eval_eq {p q a b} (hr : ValueReplacement p q a b)
    {ρ h} (he : p.read ρ h = q.read ρ h) : a.eval ρ = b.eval ρ := by
  cases hr with
  | base hv => simp only [Value.eval, hv.eval_eq he]
  | converted hv => simp only [Value.eval, hv.eval_eq he]

theorem AtomReplacement.holds_iff {p q a b} (hr : AtomReplacement p q a b)
    {ρ h} (he : p.read ρ h = q.read ρ h) : a.Holds ρ h ↔ b.Holds ρ h := by
  cases hr with
  | same => rfl
  | le h₁ h₂ => simp only [Atom.Holds, h₁.eval_eq he, h₂.eval_eq he]
  | equal hp hv => simp only [Atom.Holds, hp.read_eq he, hv.eval_eq he]
  | optionalEqual hp hv => simp only [Atom.Holds, optionalRead, hp.read_eq he, hv.eval_eq he]
  | dense hp hb =>
    have hx := Option.some.inj (hp.read_eq he)
    simp only [Atom.Holds, hb.eval_eq he, hx]
  | contents hp => simp only [Atom.Holds, hp.read_eq he]
  | element hp hi hv => simp only [Atom.Holds, hp.read_eq he, hi.eval_eq he, hv.eval_eq he]
  | every hp hi hb => simp only [Atom.Holds, Every, hp.read_eq he, hi.eval_eq he, hb.holds_iff he]

theorem RegionReplacement.mem_eq {p q a b} (hr : RegionReplacement p q a b)
    {ρ h} (he : p.read ρ h = q.read ρ h) (l : Nat) : a.mem ρ h l = b.mem ρ h l := by
  induction hr with
  | same => rfl
  | field hp | fields hp | cells hp =>
    have hx := Option.some.inj (hp.read_eq he)
    simp only [Region.mem, hx]
  | path hp | pathFields hp | pathCells hp | spine hp =>
    have hx := hp.read_eq he
    simp only [Path.read] at hx
    simp only [Region.mem, hx]
  | inCls _ ih => simp only [Region.mem, ih]

private theorem effect_cover {p q Φ Ψ} (hr : EffectReplacement p q Φ Ψ) {ρ h}
    (he : p.read ρ h = q.read ρ h) :
    (∀ e ∈ Φ, ∃ f ∈ Ψ, (∀ l, e.1.mem ρ h l = f.1.mem ρ h l) ∧ e.2 = f.2) ∧
    (∀ f ∈ Ψ, ∃ e ∈ Φ, (∀ l, f.1.mem ρ h l = e.1.mem ρ h l) ∧ f.2 = e.2) := by
  induction hr with
  | nil =>
    constructor <;> intro _ hm <;> cases hm
  | @cons e f Φ Ψ hrel _ ih =>
    constructor
    · intro a hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨f, List.mem_cons_self, hrel.1.mem_eq he, hrel.2⟩
      · obtain ⟨b, hb, hr, hd⟩ := ih.1 a hm
        exact ⟨b, List.mem_cons_of_mem _ hb, hr, hd⟩
    · intro b hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨e, List.mem_cons_self, fun l => (hrel.1.mem_eq he l).symm, hrel.2.symm⟩
      · obtain ⟨a, ha, hr, hd⟩ := ih.2 b hm
        exact ⟨a, List.mem_cons_of_mem _ ha, hr, hd⟩

private theorem action_of_cover {Φ Ψ : Footprint} {ρ s t}
    (hc : ∀ e ∈ Φ, ∃ f ∈ Ψ, (∀ l, e.1.mem ρ s.h l = f.1.mem ρ s.h l) ∧ e.2 = f.2)
    (ha : Action Φ ρ s t) : Action Ψ ρ s t := by
  refine ⟨ha.1, ha.2.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', hal⟩ := ha.2.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases hal with hh | ⟨e, he, hm, hd⟩
  · exact .inl hh
  · obtain ⟨f, hf, hmem, hδ⟩ := hc e he
    exact .inr ⟨f, hf, (hmem l) ▸ hm, hδ ▸ hd⟩

/-- Rewriting an effect preserves its entire regional action, not just a
class approximation or one permitted change. -/
theorem EffectReplacement.action_iff {p q Φ Ψ} (hr : EffectReplacement p q Φ Ψ) {ρ s t}
    (he : p.read ρ s.h = q.read ρ s.h) : Action Φ ρ s t ↔ Action Ψ ρ s t :=
  ⟨action_of_cover (effect_cover hr he).1, action_of_cover (effect_cover hr he).2⟩

end Verification.Paper.TolerantFrames
