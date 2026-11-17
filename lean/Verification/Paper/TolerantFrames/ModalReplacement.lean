import Verification.Paper.TolerantFrames.PathReplacement

/-! # Path replacement across binders and modalities

The structural relation includes unchanged subformulas, including entire boxes.
Local replacement therefore requires no rigidity of unrelated paths or boxes.
Rewriting a box transports its effect as well as its body and requires future
equality of the two selected paths. The paper's current equality plus rigidity
of both paths supplies that equality at every admissible future state.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames
open Verification.Parity (Path)

inductive FormulaReplacement (modal : Bool) : Path → Path → Formula → Formula → Prop where
  | same {p q} (F) : FormulaReplacement modal p q F F
  | atom {p q a b} : AtomReplacement p q a b → FormulaReplacement modal p q (.atom a) (.atom b)
  | and {p q A B C D} : FormulaReplacement modal p q A B → FormulaReplacement modal p q C D →
      FormulaReplacement modal p q (.and A C) (.and B D)
  | or {p q A B C D} : FormulaReplacement modal p q A B → FormulaReplacement modal p q C D →
      FormulaReplacement modal p q (.or A C) (.or B D)
  | existsValue {p q F G} : FormulaReplacement modal (renamePath Nat.succ p) (renamePath Nat.succ q) F G →
      FormulaReplacement modal p q (.existsValue F) (.existsValue G)
  | separated {p q a b c d} : PathReplacement p q a b → PathReplacement p q c d →
      FormulaReplacement modal p q (.separated a c) (.separated b d)
  | apart {p q x y z w} : PathReplacement p q ⟨x, []⟩ ⟨y, []⟩ → PathReplacement p q ⟨z, []⟩ ⟨w, []⟩ →
      FormulaReplacement modal p q (.apart x z) (.apart y w)
  | fresh {p q r t} : RegionReplacement p q r t → FormulaReplacement modal p q (.fresh r) (.fresh t)
  | box {p q Φ Ψ F G} : modal = true → EffectReplacement p q Φ Ψ → FormulaReplacement modal p q F G →
      FormulaReplacement modal p q (.box Φ F) (.box Ψ G)

/-- A bound witness cannot capture either free replacement path. -/
theorem read_shift (p : Path) (v : Val) (ρ : Env) (h : Heap) :
    (renamePath Nat.succ p).read (push v ρ) h = p.read ρ h := rfl

/-- Soundness simultaneously covers local and modal replacement. Only a
rewritten box consumes the future-equality premise. -/
theorem FormulaReplacement.holds_iff {modal p q F G} (hr : FormulaReplacement modal p q F G)
    {ρ : Env} {m : Nat} {s : IndexedHeap} (he : p.read ρ s.h = q.read ρ s.h)
    (hf : modal = true → ∀ t, Admissible s t → p.read ρ t.h = q.read ρ t.h) :
    F.Holds ρ m s ↔ G.Holds ρ m s := by
  induction hr generalizing ρ s with
  | same => rfl
  | atom ha => exact ha.holds_iff he
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ he hf) (ih₂ he hf)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ he hf) (ih₂ he hf)
  | existsValue _ ih =>
    apply exists_congr
    intro v
    apply and_congr Iff.rfl
    apply and_congr Iff.rfl
    exact ih (by simpa only [read_shift] using he)
      (fun hm t ha => by simpa only [read_shift] using hf hm t ha)
  | separated h₁ h₂ =>
    have hp := h₁.read_eq he
    have hq := h₂.read_eq he
    simp only [Path.read] at hp hq
    simp only [Formula.Holds, PathSpinesApart, hp, hq]
  | apart h₁ h₂ =>
    have hx := Option.some.inj (h₁.read_eq he)
    have hy := Option.some.inj (h₂.read_eq he)
    simp only [Formula.Holds, Verification.Parity.Apart, Path.read, readPath, hx, hy]
  | fresh ht => simp only [Formula.Holds, Fresh, ht.mem_eq he]
  | box hm hΦ _ ih =>
    have ht := hf hm
    constructor
    · intro hG t ha
      exact (ih (ht t ha.1) (fun _ u hau => ht u (ha.1.trans hau))).mp
        (hG t ((hΦ.action_iff he).mpr ha))
    · intro hG t ha
      exact (ih (ht t ha.1) (fun _ u hau => ht u (ha.1.trans hau))).mpr
        (hG t ((hΦ.action_iff he).mp ha))

/-- Outside changed modalities, current equality suffices for every term,
quantified body, optional reading, connective, separation and fresh region. -/
theorem FormulaReplacement.local {p q F G} (hr : FormulaReplacement false p q F G)
    {ρ : Env} {m : Nat} {s : IndexedHeap} (he : p.read ρ s.h = q.read ρ s.h) :
    F.Holds ρ m s ↔ G.Holds ρ m s := hr.holds_iff he (fun hm => by cases hm)

/-- The paper's equal-path premise, in the actual assertion grammar. -/
def PathEquality (p q : Path) : Formula :=
  .existsValue (.and (.atom (.equal (renamePath Nat.succ p) (.base (.variable 0))))
    (.atom (.equal (renamePath Nat.succ q) (.base (.variable 0)))))

theorem PathEquality.read_eq {p q ρ m s} (he : (PathEquality p q).Holds ρ m s) : p.read ρ s.h = q.read ρ s.h := by
  obtain ⟨v, _, _, ⟨u, hu, hv⟩, ⟨w, hw, hwv⟩⟩ := he
  have hv' : v = u := Option.some.inj hv
  have hw' : v = w := Option.some.inj hwv
  rw [read_shift] at hu hw
  exact hu.trans ((congrArg some (hv'.symm.trans hw')).trans hw.symm)

/-- A rigid path reads one valid source value in every admissible future. -/
def RigidPath (p : Path) : Assertion := fun ρ _ s =>
  ∃ v, isSourceVal v = true ∧ RefsOk s.W v ∧ ∀ t, Admissible s t → p.read ρ t.h = some v

theorem future_equal_of_rigid {p q : Path} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hp : RigidPath p ρ m s) (hq : RigidPath q ρ m s) (he : p.read ρ s.h = q.read ρ s.h) :
    ∀ t, Admissible s t → p.read ρ t.h = q.read ρ t.h := by
  obtain ⟨v, _, _, hp⟩ := hp
  obtain ⟨w, _, _, hq⟩ := hq
  have hvw := Option.some.inj ((hp s (Admissible.refl s)).symm.trans (he.trans (hq s (Admissible.refl s))))
  subst w
  exact fun t ha => (hp t ha).trans (hq t ha).symm

/-- Definition 23's modal path replacement, without imposing rigidity on
unrelated paths, scalar terms, or unchanged boxes. -/
theorem FormulaReplacement.rigid {p q F G} (hr : FormulaReplacement true p q F G)
    {ρ : Env} {m : Nat} {s : IndexedHeap} (hp : RigidPath p ρ m s) (hq : RigidPath q ρ m s)
    (he : (PathEquality p q).Holds ρ m s) : F.Holds ρ m s ↔ G.Holds ρ m s :=
  hr.holds_iff (PathEquality.read_eq he) (fun _ => future_equal_of_rigid hp hq (PathEquality.read_eq he))

/-- Rigidity as an assertion of the paper's own grammar. -/
def RigidFormula (p : Path) : Formula :=
  .existsValue (.box Closed.top.fp (.atom (.equal (renamePath Nat.succ p) (.base (.variable 0)))))

theorem RigidFormula.holds_iff {p : Path} {ρ : Env} {m : Nat} {s : IndexedHeap} :
    (RigidFormula p).Holds ρ m s ↔ RigidPath p ρ m s := by
  constructor
  · rintro ⟨v, hval, href, hbox⟩
    refine ⟨v, hval, href, fun t ha => ?_⟩
    obtain ⟨u, hread, hvu⟩ := hbox t (action_top ha)
    have hv : v = u := Option.some.inj hvu
    subst u
    simpa only [read_shift] using hread
  · rintro ⟨v, hval, href, hp⟩
    refine ⟨v, hval, href, fun t ha => ⟨v, ?_, rfl⟩⟩
    simpa only [read_shift] using hp t ha.1

end Verification.Paper.TolerantFrames
