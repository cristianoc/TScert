import Verification.Source.PrimitiveBoundary

/-! # Checking primitive attachments against graph rows -/
namespace Verification.PrimitiveBoundary
open CallEffects PositiveGraphs PositiveNormalization PositiveRules ProgramTyping

@[nospecialize] def Atom.clause (a : Atom) : Clause (Ty ι) :=
  match a with
  | .number => .num
  | .bigint => .bigint
  | .boolean => .bool
  | .string => .str

@[nospecialize] def atomCheck [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (a : Atom) : Bool :=
  decide (expand G A = [a.clause])

theorem atomCheck_sound [DecidableEq ι] {G : NormalGraph ι} {A : Ty ι} {a : Atom}
    (h : atomCheck G A a = true) : meaning G A = a.meaning := by
  have hr : expand G A = [a.clause] := of_decide_eq_true h
  funext n W v
  apply propext
  rw [represents_sem hr]
  cases a <;> cases hb : G.builtins <;>
    simp [Atom.clause, Atom.meaning, rowSem, semWithArgs, builtinInvariant, hb,
      Clause.carriesInvariant]

@[nospecialize] def argumentsCheck [DecidableEq ι] (G : NormalGraph ι) :
    List (Ty ι) → List Atom → Bool
  | [], [] => true
  | A :: As, a :: atoms => atomCheck G A a && argumentsCheck G As atoms
  | _, _ => false

theorem argumentsCheck_sound [DecidableEq ι] {G : NormalGraph ι} :
    ∀ {As : List (Ty ι)} {atoms : List Atom}, argumentsCheck G As atoms = true →
      As.map (meaning G) = atoms.map Atom.meaning := by
  intro As
  induction As with
  | nil => intro atoms; cases atoms <;> simp [argumentsCheck]
  | cons A As ih =>
    intro atoms
    cases atoms with
    | nil => simp [argumentsCheck]
    | cons a atoms =>
      intro h
      simp only [argumentsCheck, Bool.and_eq_true] at h
      simp [atomCheck_sound h.1, ih h.2]

/-- A row attachment is checked at its actual label. The receiver's `source`
interpretation includes exactly this graph's exception invariant. -/
@[nospecialize] def attachmentCheck [DecidableEq ι] (G : NormalGraph ι) (F : Ty ι)
    (s : Signature) : Bool :=
  match expand G F with
  | [.arrs [p] []] => decide (expand G p.receiver = [.source]) &&
      argumentsCheck G p.arguments s.parameters && atomCheck G p.result s.result &&
      decide (p.effect = s.effect)
  | _ => false

theorem attachmentCheck_sound [DecidableEq ι] {G : NormalGraph ι} {F : Ty ι} {s : Signature}
    (h : attachmentCheck G F s = true) : Attachment G F s := by
  unfold attachmentCheck at h
  split at h
  · rename_i p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have receiver : meaning G p.receiver = excOf G := by
      funext n W v
      exact propext (represents_sem h.1.1.1 n W v)
    refine ⟨⟨p, hp, ?_⟩⟩
    cases p
    simp only [Arrow.map, Contract.map, Signature.contract]
    simp_all [argumentsCheck_sound h.1.1.2, atomCheck_sound h.1.2]
  · cases h

/-- An attachment needs an actual arrow clause in a row of its type.
Top-level request acceptance alone need not intern such a row. -/
theorem Attachment.arrow_row {G : NormalGraph ι} {F : Ty ι} {s : Signature}
    (h : Attachment G F s) :
    ∃ i ∈ F, ∃ p : Arrow (Ty ι), .arrs [p] [] ∈ G i := by
  obtain ⟨p, hp, _⟩ := h.row
  have member : .arrs [p] [] ∈ expand G F := by rw [hp]; simp
  rw [expand_of_plain (Represents.plain hp)] at member
  obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp member
  exact ⟨i, hi, p, hr⟩

theorem no_attachment_without_arrow_rows {G : NormalGraph ι} {F : Ty ι} {s : Signature}
    (noArrows : ∀ i ∈ F, ∀ p : Arrow (Ty ι), .arrs [p] [] ∉ G i) :
    ¬ Attachment G F s := by
  intro h
  obtain ⟨i, hi, p, hp⟩ := h.arrow_row
  exact noArrows i hi p hp

/-- With no array built-ins the exception invariant is independent of all
labels and assignments. This suffices for two closed primitive graphs. -/
theorem exceptions_eq_of_no_builtins {ι κ : Type} {G : NormalGraph ι} {H : NormalGraph κ}
    (g : G.builtins = none) (h : H.builtins = none) : excOf G = excOf H := by
  funext n W v
  simp [excOf, builtinExc, builtinInvariant, g, h, Clause.carriesInvariant]

end Verification.PrimitiveBoundary
