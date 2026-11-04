import Init.Data.List.Lex
import Init.Data.String.Lemmas

/-! Canonical lists: a list strictly increasing in a strict total order is
determined by its members, so sorting and removing duplicates gives a set
one representation (heap-knowledge draft, §2.5). -/
namespace Verification.CanonicalLists

/-- A strict total order. -/
class StrictTotal (α : Type) [LT α] [DecidableLT α] : Prop where
  irrefl : ∀ a : α, ¬ a < a
  trans : ∀ {a b c : α}, a < b → b < c → a < c
  total : ∀ {a b : α}, a ≠ b → a < b ∨ b < a

variable {α : Type} [LT α] [DecidableLT α] [StrictTotal α] [DecidableEq α]


/-- The order as a Boolean test: not above. -/
def notAbove (a b : α) : Bool := !decide (b < a)

/-- A sorted list without its adjacent repeats. -/
def dedupSorted : List α → List α
  | a :: b :: l => if a = b then dedupSorted (b :: l) else a :: dedupSorted (b :: l)
  | l => l

/-- The members of a list, strictly increasing: sorted, adjacent repeats
removed. -/
def canon (l : List α) : List α := dedupSorted (l.mergeSort notAbove)

omit [LT α] [DecidableLT α] [StrictTotal α] in
theorem mem_dedupSorted : ∀ (l : List α) (x : α), x ∈ dedupSorted l ↔ x ∈ l
  | [], _ => by simp [dedupSorted]
  | [_], _ => by simp [dedupSorted]
  | a :: b :: l, x => by
    have ih := mem_dedupSorted (b :: l) x
    simp only [dedupSorted]
    split
    · rename_i e; subst e; rw [ih]; simp
    · rw [List.mem_cons, ih, List.mem_cons (l := b :: l)]

omit [DecidableEq α] in
theorem notAbove_lt {a b : α} (h : notAbove a b = true) (hne : a ≠ b) : a < b := by
  simp only [notAbove, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact (StrictTotal.total hne).resolve_right h

omit [DecidableEq α] in
theorem notAbove_antisymm {a b : α} (h₁ : notAbove a b = true) (h₂ : notAbove b a = true) : a = b :=
  Classical.byContradiction fun hne => by
    have := notAbove_lt h₁ hne
    simp only [notAbove, Bool.not_eq_true', decide_eq_false_iff_not] at h₂
    exact h₂ this

theorem dedupSorted_spec : ∀ (l : List α), l.Pairwise (fun a b => notAbove a b = true) →
    (dedupSorted l).Pairwise (· < ·) ∧ ∀ x, x ∈ dedupSorted l ↔ x ∈ l
  | [], _ => by simp [dedupSorted]
  | [a], _ => by simp [dedupSorted]
  | a :: b :: l, h => by
    obtain ⟨ih₁, ih₂⟩ := dedupSorted_spec (b :: l) (List.pairwise_cons.mp h).2
    have ha := (List.pairwise_cons.mp h).1
    have hb := (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).1
    simp only [dedupSorted]
    split
    · rename_i e
      subst e
      refine ⟨ih₁, fun x => ?_⟩
      rw [ih₂]; simp
    · rename_i hne
      refine ⟨List.Pairwise.cons (fun y hy => ?_) ih₁, fun x => ?_⟩
      · have hy := (ih₂ y).mp hy
        have hle : notAbove a y = true := ha y hy
        refine notAbove_lt hle fun e => ?_
        subst e
        rcases List.mem_cons.mp hy with e | hy
        · exact hne e
        · exact hne (notAbove_antisymm (ha b (List.mem_cons_self ..)) (hb a hy))
      · simp only [List.mem_cons, ih₂]

omit [DecidableEq α] in
theorem notAbove_trans (a b c : α) (h₁ : notAbove a b = true) (h₂ : notAbove b c = true) :
    notAbove a c = true := by
  by_cases hab : a = b
  · subst hab; exact h₂
  by_cases hbc : b = c
  · subst hbc; exact h₁
  have := StrictTotal.trans (notAbove_lt h₁ hab) (notAbove_lt h₂ hbc)
  simp only [notAbove, Bool.not_eq_true', decide_eq_false_iff_not]
  exact fun hca => StrictTotal.irrefl a (StrictTotal.trans this hca)

omit [DecidableEq α] in
theorem notAbove_total (a b : α) : (notAbove a b || notAbove b a) = true := by
  by_cases hab : a = b
  · subst hab; simp [notAbove, StrictTotal.irrefl]
  · rcases StrictTotal.total hab with h | h
    · simp only [notAbove, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact Or.inl fun h' => StrictTotal.irrefl a (StrictTotal.trans h h')
    · simp only [notAbove, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact Or.inr fun h' => StrictTotal.irrefl a (StrictTotal.trans h' h)

omit [StrictTotal α] in
theorem mem_canon {a : α} {l : List α} : a ∈ canon l ↔ a ∈ l := by
  rw [canon, mem_dedupSorted, (List.mergeSort_perm l notAbove).mem_iff]


theorem pairwise_canon (l : List α) : (canon l).Pairwise (· < ·) :=
  (dedupSorted_spec _ (List.pairwise_mergeSort notAbove_trans notAbove_total l)).1

omit [DecidableEq α] in
/-- Two strictly increasing lists with the same members are equal. -/
theorem eq_of_pairwise {l₁ l₂ : List α} (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b _ => exact absurd ((h b).mpr (List.mem_cons_self ..)) (by simp)
  | cons a l₁ ih =>
    cases l₂ with
    | nil => exact absurd ((h a).mp (List.mem_cons_self ..)) (by simp)
    | cons b l₂ =>
      obtain ⟨ha, t₁⟩ := List.pairwise_cons.mp h₁
      obtain ⟨hb, t₂⟩ := List.pairwise_cons.mp h₂
      have hab : a = b := by
        rcases List.mem_cons.mp ((h a).mp (List.mem_cons_self ..)) with e | e
        · exact e
        · rcases List.mem_cons.mp ((h b).mpr (List.mem_cons_self ..)) with e' | e'
          · exact e'.symm
          · exact absurd (StrictTotal.trans (hb a e) (ha b e')) (StrictTotal.irrefl b)
      subst hab
      have not₁ : a ∉ l₁ := fun m => StrictTotal.irrefl a (ha a m)
      have not₂ : a ∉ l₂ := fun m => StrictTotal.irrefl a (hb a m)
      congr 1
      refine ih t₁ t₂ fun c => ⟨fun hc => ?_, fun hc => ?_⟩
      · rcases List.mem_cons.mp ((h c).mp (List.mem_cons_of_mem _ hc)) with e | e
        · subst e; exact absurd hc not₁
        · exact e
      · rcases List.mem_cons.mp ((h c).mpr (List.mem_cons_of_mem _ hc)) with e | e
        · subst e; exact absurd hc not₂
        · exact e

/-- Lists with the same members have one canonical list. -/
theorem canon_eq {l₁ l₂ : List α} (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : canon l₁ = canon l₂ :=
  eq_of_pairwise (pairwise_canon l₁) (pairwise_canon l₂) fun a => by rw [mem_canon, mem_canon, h]

theorem canon_canon (l : List α) : canon (canon l) = canon l :=
  canon_eq fun _ => mem_canon

/-- A strictly increasing list is its canonical list. -/
theorem canon_of_pairwise {l : List α} (h : l.Pairwise (· < ·)) : canon l = l :=
  eq_of_pairwise (pairwise_canon l) h fun _ => mem_canon

instance : StrictTotal Nat := ⟨Nat.lt_irrefl, Nat.lt_trans, Nat.lt_or_gt_of_ne⟩
instance : StrictTotal Int := ⟨Int.lt_irrefl, Int.lt_trans, Int.lt_or_gt_of_ne⟩

instance : StrictTotal UInt64 where
  irrefl a := by simp
  trans := by simp only [UInt64.lt_iff_toNat_lt]; omega
  total {a b} h := by
    simp only [UInt64.lt_iff_toNat_lt]
    have : a.toNat ≠ b.toNat := fun e => h (UInt64.toNat_inj.mp e)
    omega

instance : StrictTotal String where
  irrefl := String.lt_irrefl
  trans := String.lt_trans
  total {a b} h := by
    rcases String.le_total a b with hab | hba
    · exact Or.inl (String.not_le.mp fun hba => h (String.le_antisymm hab hba))
    · exact Or.inr (String.not_le.mp fun hab => h (String.le_antisymm hab hba))

/-- Lexicographic order on lists is a strict total order. -/
theorem lex_total {β : Type} [LT β] [DecidableLT β] [StrictTotal β] [DecidableEq β] :
    ∀ {l₁ l₂ : List β}, l₁ ≠ l₂ → l₁ < l₂ ∨ l₂ < l₁
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => Or.inl List.Lex.nil
  | _ :: _, [], _ => Or.inr List.Lex.nil
  | a :: l₁, b :: l₂, h => by
    by_cases hab : a = b
    · subst hab
      have : l₁ ≠ l₂ := fun e => h (e ▸ rfl)
      rcases lex_total this with h' | h'
      · exact Or.inl (List.Lex.cons h')
      · exact Or.inr (List.Lex.cons h')
    · rcases StrictTotal.total hab with h' | h'
      · exact Or.inl (List.Lex.rel h')
      · exact Or.inr (List.Lex.rel h')

instance {β : Type} [LT β] [DecidableLT β] [StrictTotal β] [DecidableEq β] : StrictTotal (List β) where
  irrefl l := by
    have : Std.Irrefl (α := β) (· < ·) := ⟨StrictTotal.irrefl⟩
    exact List.lt_irrefl l
  trans h₁ h₂ := by
    have : Trans (α := β) (· < ·) (· < ·) (· < ·) := ⟨StrictTotal.trans⟩
    exact List.lt_trans h₁ h₂
  total := lex_total

end Verification.CanonicalLists
