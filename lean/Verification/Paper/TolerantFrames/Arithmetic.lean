import Verification.Paper.TolerantFrames.Assertions

/-! # General integer consequences with explicit definedness

This extends the partial general expressions. Integer implication is a semantic
proof premise about a finite list of inequalities, not an automatic search
procedure. A term of the goal must occur in a premise (nested index terms
included) or be a literal. Zero coefficients never erase such an occurrence.
The literal/term equality bridge is separate: see `Obstructions` for -0.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames

mutual
/-- The term itself and recursively mentioned terms of an element index.
Path prefixes and object-valued intermediate elements are not numeric terms. -/
def Term.mentioned (t : Term) : List Term :=
  t :: match t with
    | .element _ _ e _ _ | .lengthElement _ e _ => e.mentioned
    | _ => []

def Expression.mentioned : Expression → List Term
  | .constant _ => []
  | .scale _ t => t.mentioned
  | .add e f => e.mentioned ++ f.mentioned
end

/-- Integer literals have their specified value in every arithmetic model. -/
def Term.integerModel (ν : Term → Int) : Term → Int
  | .literal n => n.val
  | t => ν t

def Expression.integerModel (ν : Term → Int) : Expression → Int
  | .constant n => n
  | .scale c t => c * t.integerModel ν
  | .add e f => e.integerModel ν + f.integerModel ν

abbrev Inequality := Expression × Expression

/-- The ordinary integer entailment in Definition 23. Every repeated term
has one valuation; literals are fixed, and other terms are independent. -/
def IntegerConsequence (hypotheses : List Inequality) (goal : Inequality) : Prop :=
  ∀ ν : Term → Int,
    (∀ p ∈ hypotheses, p.1.integerModel ν ≤ p.2.integerModel ν) →
    goal.1.integerModel ν ≤ goal.2.integerModel ν

def Term.IsLiteral : Term → Prop
  | .literal _ => True
  | _ => False

/-- Exactly the paper's syntactic source of goal-term definedness. -/
def GoalTermsDefined (hypotheses : List Inequality) (goal : Inequality) : Prop :=
  ∀ t ∈ goal.1.mentioned ++ goal.2.mentioned,
    t.IsLiteral ∨ ∃ p ∈ hypotheses, t ∈ p.1.mentioned ++ p.2.mentioned

mutual
theorem Term.mentioned_defined {ρ : Env} {h : Heap} : ∀ {t : Term} {n : Int},
    t.eval ρ h = some n → ∀ u ∈ t.mentioned, (u.eval ρ h).isSome = true
  | .literal _, _, he, _, hm | .path _ _, _, he, _, hm | .lengthPath _, _, he, _, hm => by
    simp only [Term.mentioned, List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm; rw [he]; rfl
  | .element _ _ _ _ _, _, he, u, hm | .lengthElement _ _ _, _, he, u, hm => by
    simp only [Term.mentioned, List.mem_cons] at hm
    rcases hm with rfl | hm
    · rw [he]; rfl
    · simp only [Term.eval, bind, Option.bind_eq_some_iff] at he
      obtain ⟨_, _, i, hi, _⟩ := he
      exact Expression.mentioned_defined hi u hm

theorem Expression.mentioned_defined {ρ : Env} {h : Heap} : ∀ {e : Expression} {n : Int},
    e.eval ρ h = some n → ∀ u ∈ e.mentioned, (u.eval ρ h).isSome = true
  | .constant _, _, _, _, hm => by cases hm
  | .scale _ _, _, he, u, hm => by
    simp only [Expression.eval, Option.map_eq_some_iff] at he
    obtain ⟨_, ht, _⟩ := he
    exact Term.mentioned_defined ht u hm
  | .add _ _, _, he, u, hm => by
    simp only [Expression.eval, bind, pure, Option.bind_eq_some_iff] at he
    obtain ⟨_, he, _, hf, _⟩ := he
    exact (List.mem_append.mp hm).elim
      (fun hm => Expression.mentioned_defined he u hm)
      (fun hm => Expression.mentioned_defined hf u hm)
end

/-- The actual partial readings supply an integer model wherever defined. -/
theorem Term.integerModel_eval {ρ : Env} {h : Heap} {t : Term} {n : Int}
    (he : t.eval ρ h = some n) : t.integerModel (fun t => (t.eval ρ h).getD 0) = n := by
  cases t with
  | literal v => exact Option.some.inj he
  | path _ _ | element _ _ _ _ _ | lengthPath _ | lengthElement _ _ _ => simp only [Term.integerModel, he, Option.getD_some]

theorem Expression.integerModel_eval {ρ : Env} {h : Heap} {e : Expression} {n : Int}
    (he : e.eval ρ h = some n) : e.integerModel (fun t => (t.eval ρ h).getD 0) = n := by
  cases e with
  | constant c => exact Option.some.inj he
  | scale c t =>
    simp only [Expression.eval, Option.map_eq_some_iff] at he
    obtain ⟨a, ha, he⟩ := he
    rw [Expression.integerModel, Term.integerModel_eval ha]
    exact he
  | add e f =>
    simp only [Expression.eval, bind, pure, Option.bind_eq_some_iff] at he
    obtain ⟨a, ha, b, hb, he⟩ := he
    rw [Expression.integerModel, Expression.integerModel_eval ha, Expression.integerModel_eval hb]
    exact Option.some.inj he

/-- No undefined term can be hidden by integer algebra. -/
theorem Expression.eval_of_defined {ρ : Env} {h : Heap} {e : Expression}
    (hd : ∀ t ∈ e.mentioned, (t.eval ρ h).isSome = true) : ∃ n, e.eval ρ h = some n := by
  cases e with
  | constant n => exact ⟨n, rfl⟩
  | scale c t =>
    have ht := hd t (by cases t <;> simp [Expression.mentioned, Term.mentioned])
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ht
    exact ⟨c * n, by simp [Expression.eval, hn]⟩
  | add e f =>
    obtain ⟨a, ha⟩ := Expression.eval_of_defined (e := e) (fun t ht => hd t (List.mem_append_left _ ht))
    obtain ⟨b, hb⟩ := Expression.eval_of_defined (e := f) (fun t ht => hd t (List.mem_append_right _ ht))
    exact ⟨a + b, by simp [Expression.eval, ha, hb]⟩

/-- The full current-state linear consequence schema, including exact
conclusion definedness. Mixed old/current terms are a separate syntax layer. -/
theorem integer_consequence {hypotheses : List Inequality} {goal : Inequality}
    (hc : IntegerConsequence hypotheses goal) (hd : GoalTermsDefined hypotheses goal)
    {ρ : Env} {h : Heap} (hh : ∀ p ∈ hypotheses, (Atom.le p.1 p.2).Holds ρ h) :
    (Atom.le goal.1 goal.2).Holds ρ h := by
  have hdefs : ∀ t ∈ goal.1.mentioned ++ goal.2.mentioned, (t.eval ρ h).isSome = true := by
    intro t ht
    rcases hd t ht with hl | ⟨p, hp, ht⟩
    · cases t <;> try cases hl
      rfl
    · obtain ⟨a, b, ha, hb, _⟩ := hh p hp
      exact (List.mem_append.mp ht).elim
        (fun ht => Expression.mentioned_defined ha t ht)
        (fun ht => Expression.mentioned_defined hb t ht)
  obtain ⟨a, ha⟩ := Expression.eval_of_defined (fun t ht => hdefs t (List.mem_append_left _ ht))
  obtain ⟨b, hb⟩ := Expression.eval_of_defined (fun t ht => hdefs t (List.mem_append_right _ ht))
  refine ⟨a, b, ha, hb, ?_⟩
  have hm := hc (fun t => (t.eval ρ h).getD 0) (fun p hp => by
    obtain ⟨a, b, ha, hb, hab⟩ := hh p hp
    rwa [Expression.integerModel_eval ha, Expression.integerModel_eval hb])
  rwa [Expression.integerModel_eval ha, Expression.integerModel_eval hb] at hm

/-- The three exact ranges of defined length readings. -/
theorem defined_length_range {h : Heap} {v : Val} {k : Reading} {n : Int}
    (hk : k = .length ∨ k = .view ∨ k = .strLength) (he : kindValue h k v = some n) :
    0 ≤ n ∧ n ≤ (if k = .length then maxArrayLength else 2 ^ 53 - 1) := by
  rcases hk with rfl | rfl | rfl
  · obtain ⟨_, es, _, _, rfl, hm⟩ := lengthOf_spine he
    simp only [↓reduceIte]
    exact ⟨by omega, by exact_mod_cast hm⟩
  · simpa using viewLengthOf_range he
  · simpa using strLengthOf_range he

/-- The explicitly requested kind of an auxiliary sorted path/element reader. -/
def Term.ReadsKind (k : Reading) : Term → Prop
  | .path k' _ | .element k' _ _ _ _ => k' = k
  | .literal _ | .lengthPath _ | .lengthElement _ _ _ => False

/-- Defined length readings, including projected elements, have these bounds. -/
theorem Term.eval_length_range {ρ : Env} {h : Heap} {t : Term} {k : Reading} {n : Int}
    (hr : t.ReadsKind k) (hk : k = .length ∨ k = .view ∨ k = .strLength)
    (he : t.eval ρ h = some n) :
    0 ≤ n ∧ n ≤ (if k = .length then maxArrayLength else 2 ^ 53 - 1) := by
  cases t with
  | literal _ | lengthPath _ | lengthElement _ _ _ => exact hr.elim
  | path k' p =>
    cases hr
    simp only [Term.eval, Option.bind_eq_some_iff] at he
    obtain ⟨v, _, he⟩ := he
    exact defined_length_range hk he
  | element k' p e fs valid =>
    cases hr
    simp only [Term.eval, bind, Option.bind_eq_some_iff] at he
    obtain ⟨_, _, _, _, _, _, v, _, he⟩ := he
    exact defined_length_range hk he

/-- Reflexive inequality is exactly partial definedness. -/
def TermDefined (t : Term) : Formula :=
  .atom (.le (.scale 1 t) (.scale 1 t))

def LengthBounds (k : Reading) (t : Term) : Formula :=
  .and (.atom (.le (.constant 0) (.scale 1 t)))
    (.atom (.le (.scale 1 t) (.constant (if k = .length then maxArrayLength else 2 ^ 53 - 1))))

theorem TermDefined.holds_iff {ρ m s t} :
    (TermDefined t).Holds ρ m s ↔ ∃ n, t.eval ρ s.h = some n := by
  cases he : t.eval ρ s.h <;> simp [TermDefined, Formula.Holds, Atom.Holds, Expression.eval, he]

theorem length_bounds {ρ m s t k} (hr : t.ReadsKind k)
    (hk : k = .length ∨ k = .view ∨ k = .strLength)
    (hd : (TermDefined t).Holds ρ m s) : (LengthBounds k t).Holds ρ m s := by
  obtain ⟨n, hn⟩ := TermDefined.holds_iff.mp hd
  have hrange := Term.eval_length_range hr hk hn
  by_cases hkl : k = .length <;>
    simpa [LengthBounds, Formula.Holds, Atom.Holds, Expression.eval, hn, hkl] using hrange

/-- Canonical length syntax, distinct from the auxiliary sorted readers. -/
def Term.IsLength : Term → Prop
  | .lengthPath _ | .lengthElement _ _ _ => True
  | _ => False

/-- The unified operator has the paper's common range, including empty suffixes. -/
theorem Term.eval_canonical_length_range {ρ : Env} {h : Heap} {t : Term} {n : Int}
    (ht : t.IsLength) (he : t.eval ρ h = some n) : 0 ≤ n ∧ n ≤ 2 ^ 53 - 1 := by
  cases t with
  | lengthPath p =>
    simp only [Term.eval, Option.bind_eq_some_iff] at he
    obtain ⟨v, _, he⟩ := he
    exact lengthReading_range he
  | lengthElement p i fs =>
    simp only [Term.eval, bind, Option.bind_eq_some_iff] at he
    obtain ⟨_, _, _, _, _, _, v, _, he⟩ := he
    exact lengthReading_range he
  | _ => cases ht

def CanonicalLengthBounds (t : Term) : Formula :=
  .and (.atom (.le (.constant 0) (.scale 1 t)))
    (.atom (.le (.scale 1 t) (.constant (2 ^ 53 - 1))))

theorem canonical_length_bounds {ρ m s t} (ht : t.IsLength)
    (hd : (TermDefined t).Holds ρ m s) : (CanonicalLengthBounds t).Holds ρ m s := by
  obtain ⟨n, hn⟩ := TermDefined.holds_iff.mp hd
  have hr := Term.eval_canonical_length_range ht hn
  simpa [CanonicalLengthBounds, Formula.Holds, Atom.Holds, Expression.eval, hn] using hr

end Verification.Paper.TolerantFrames
