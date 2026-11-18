import Verification.Paper.TolerantFrames.EverySupports
import Verification.Paper.TolerantFrames.Arithmetic

/-! # Inequality support from explicit reading monotonicity

Structural witnesses establish the term changes induced by a finite raw
support. A separate semantic reading-monotonicity criterion preserves the
inequality. It quantifies over all admissible conditioned transitions without
mentioning Supported, so it does not assume the desired support theorem.
Integer-model monotonicity is only a sufficient route to this criterion.
Neither route claims necessary/maximal growth-annotation selection.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames
open Verification.Parity (Path)

abbrev PathGrowth := Path → Bool

/-- Growth is eligible only at a plain array-length reading. -/
def Term.growth (g : PathGrowth) : Term → Bool
  | .path .length p => g p
  | _ => false

inductive TermToleranceSupport (omitted : OmittedFields) : Term → Footprint → Bool → Prop where
  | exact {t S} : TermExactSupport omitted t S → TermToleranceSupport omitted t S false
  | lengthGrow (p : Path) : TermToleranceSupport omitted (.path .length p)
      (pathTermReads omitted .length .grow p) true

inductive ExpressionGrowthSupport (omitted : OmittedFields) (g : PathGrowth) : Expression → Footprint → Prop where
  | constant (n : Int) : ExpressionGrowthSupport omitted g (.constant n) []
  | scale {t S} (c : Int) : TermToleranceSupport omitted t S (t.growth g) →
      ExpressionGrowthSupport omitted g (.scale c t) S
  | add {e f S T} : ExpressionGrowthSupport omitted g e S → ExpressionGrowthSupport omitted g f T →
      ExpressionGrowthSupport omitted g (.add e f) (S ++ T)

/-- Only successful old readings impose a relation; definedness cannot be
inferred for an unrelated term or dropped at coefficient zero. -/
def ReadingChange (g : PathGrowth) (ρ : Env) (h h' : Heap) (t : Term) : Prop :=
  ∀ n, t.eval ρ h = some n → ∃ n', t.eval ρ h' = some n' ∧
    (if t.growth g then n ≤ n' else n' = n)

/-- A semantic criterion independently of any footprint. Bounds, aliasing
and worlds are retained by quantifying actual valid admissible transitions.
This is sufficient; equivalence to every supporting annotation is not claimed. -/
def SemanticReadingMonotone (C : ConditionOn IndexedHeap) (g : PathGrowth) (e f : Expression) : Prop :=
  ∀ ρ m s t, HeapContext ρ m s → Admissible s t → C ρ m s t →
    (∀ u ∈ e.mentioned ++ f.mentioned, ReadingChange g ρ s.h t.h u) →
    (Atom.le e f).Holds ρ s.h → (Atom.le e f).Holds ρ t.h

/-- A purely arithmetic sufficient criterion over a specified model domain.
Unbounded integer models are the special case D=true, not the definition of
semantic eligibility for array growth. -/
def IntegerDomainMonotone (D : (Term → Int) → Prop) (g : PathGrowth) (e f : Expression) : Prop :=
  ∀ ν ν', D ν → D ν' →
    (∀ u ∈ e.mentioned ++ f.mentioned,
      if u.growth g then u.integerModel ν ≤ u.integerModel ν' else u.integerModel ν' = u.integerModel ν) →
    e.integerModel ν ≤ f.integerModel ν → e.integerModel ν' ≤ f.integerModel ν'

private theorem support_left {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported S ρ h h' := fun e he => hs e (List.mem_append_left _ he)
private theorem support_right {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported T ρ h h' := fun e he => hs e (List.mem_append_right _ he)

mutual
/-- Index subterms of element terms retain their own exact supports. -/
theorem TermExactSupport.mentioned_kept {omitted t S} (ht : TermExactSupport omitted t S) {ρ m s v}
    (hc : OmissionCondition omitted ρ m s v) (hs : Supported S ρ s.h v.h) :
    ∀ u ∈ t.mentioned, ∀ n, u.eval ρ s.h = some n → u.eval ρ v.h = some n := by
  cases ht with
  | literal _ | path _ _ =>
    intro u hu n he
    simp only [Term.mentioned, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst u
    exact TermExactSupport.sound (by constructor) hc hs he
  | element hi =>
    intro u hu n he
    simp only [Term.mentioned, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact TermExactSupport.sound (.element hi) hc hs he
    · exact ExpressionExactSupport.mentioned_kept hi hc (support_right hs) u hu n he

theorem ExpressionExactSupport.mentioned_kept {omitted e S} (he : ExpressionExactSupport omitted e S) {ρ m s v}
    (hc : OmissionCondition omitted ρ m s v) (hs : Supported S ρ s.h v.h) :
    ∀ u ∈ e.mentioned, ∀ n, u.eval ρ s.h = some n → u.eval ρ v.h = some n := by
  cases he with
  | constant _ => intro u hu; cases hu
  | scale _ ht => exact ht.mentioned_kept hc hs
  | add he hf =>
    intro u hu
    exact (List.mem_append.mp hu).elim
      (fun hu => he.mentioned_kept hc (support_left hs) u hu)
      (fun hu => hf.mentioned_kept hc (support_right hs) u hu)
end

theorem TermToleranceSupport.mentioned_sound {omitted t S b} (ht : TermToleranceSupport omitted t S b)
    (g : PathGrowth) (hb : b = t.growth g) {ρ m s v}
    (hc : OmissionCondition omitted ρ m s v) (hs : Supported S ρ s.h v.h) :
    ∀ u ∈ t.mentioned, ReadingChange g ρ s.h v.h u := by
  cases ht with
  | exact ht =>
    intro u hu n he
    refine ⟨n, ht.mentioned_kept hc hs u hu n he, ?_⟩
    split <;> first | exact Int.le_refl _ | rfl
  | lengthGrow p =>
    intro u hu n he
    simp only [Term.mentioned, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst u
    obtain ⟨n', hn', hle, _⟩ := path_term_supported hc (.inr rfl) hs he
    refine ⟨n', hn', ?_⟩
    simpa only [← hb, ↓reduceIte] using hle

theorem ExpressionGrowthSupport.mentioned_sound {omitted g e S} (he : ExpressionGrowthSupport omitted g e S)
    {ρ m s v} (hc : OmissionCondition omitted ρ m s v) (hs : Supported S ρ s.h v.h) :
    ∀ u ∈ e.mentioned, ReadingChange g ρ s.h v.h u := by
  induction he with
  | constant _ => intro u hu; cases hu
  | scale _ ht => exact ht.mentioned_sound g rfl hc hs
  | add he hf ihe ihf =>
    intro u hu
    exact (List.mem_append.mp hu).elim
      (fun hu => ihe (support_left hs) u hu)
      (fun hu => ihf (support_right hs) u hu)

/-- The finite structural support and semantic criterion are independent
premises. This is not an arbitrary entailment constructor or search claim. -/
theorem inequality_support {omitted g e f S T}
    (he : ExpressionGrowthSupport omitted g e S) (hf : ExpressionGrowthSupport omitted g f T)
    (hm : SemanticReadingMonotone (OmissionCondition omitted) g e f) :
    Supports (OmissionCondition omitted) (Formula.atom (.le e f)).meaning (S ++ T) := by
  intro ρ m s t ha ⟨hv, hc⟩ hF hs
  apply hm ρ m s t hv ha hc
  · intro u hu
    exact (List.mem_append.mp hu).elim
      (fun hu => he.mentioned_sound hc (support_left hs) u hu)
      (fun hu => hf.mentioned_sound hc (support_right hs) u hu)
  · exact hF

/-- Arithmetic domains discharge semantic reading monotonicity when actual
successful readings are proved in D. No range/correlation fact is inferred. -/
theorem semanticMonotone_of_integerDomain {C : ConditionOn IndexedHeap} {D g e f}
    (hm : IntegerDomainMonotone D g e f)
    (hD : ∀ ρ m s, HeapContext ρ m s →
      (∀ u ∈ e.mentioned ++ f.mentioned, (u.eval ρ s.h).isSome = true) →
      D (fun u => (u.eval ρ s.h).getD 0)) : SemanticReadingMonotone C g e f := by
  intro ρ m s t hv ha _hc hchange hF
  obtain ⟨a, b, ha0, hb0, hab⟩ := hF
  have hdefined : ∀ u ∈ e.mentioned ++ f.mentioned, (u.eval ρ s.h).isSome = true := by
    intro u hu
    exact (List.mem_append.mp hu).elim
      (fun hu => Expression.mentioned_defined ha0 u hu)
      (fun hu => Expression.mentioned_defined hb0 u hu)
  have hread : ∀ u ∈ e.mentioned ++ f.mentioned,
      ∃ n n', u.eval ρ s.h = some n ∧ u.eval ρ t.h = some n' ∧
        (if u.growth g then n ≤ n' else n' = n) := by
    intro u hu
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hdefined u hu)
    obtain ⟨n', hn', hrel⟩ := hchange u hu n hn
    exact ⟨n, n', hn, hn', hrel⟩
  have hdefined' : ∀ u ∈ e.mentioned ++ f.mentioned, (u.eval ρ t.h).isSome = true := by
    intro u hu
    obtain ⟨_, n', _, hn', _⟩ := hread u hu
    rw [hn']; rfl
  obtain ⟨a', ha'⟩ := Expression.eval_of_defined (fun u hu => hdefined' u (List.mem_append_left _ hu))
  obtain ⟨b', hb'⟩ := Expression.eval_of_defined (fun u hu => hdefined' u (List.mem_append_right _ hu))
  refine ⟨a', b', ha', hb', ?_⟩
  have hle := hm (fun u => (u.eval ρ s.h).getD 0) (fun u => (u.eval ρ t.h).getD 0)
    (hD ρ m s hv hdefined) (hD ρ m t (hv.admissible ha) hdefined')
    (fun u hu => by
      obtain ⟨n, n', hn, hn', hrel⟩ := hread u hu
      simpa only [Term.integerModel_eval hn, Term.integerModel_eval hn'] using hrel)
    (by simpa only [Expression.integerModel_eval ha0, Expression.integerModel_eval hb0] using hab)
  simpa only [Expression.integerModel_eval ha', Expression.integerModel_eval hb'] using hle

end Verification.Paper.TolerantFrames
