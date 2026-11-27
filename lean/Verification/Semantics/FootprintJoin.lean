import Verification.Semantics.ExitComposition

/-! # The join of footprints

The entry-wise maximum of a frame with an entry (`Footprint.insertMax`), the
join of two frames (`Footprint.join`, an upper bound in the order `⊑`), and
covering (`Footprint.Covers`: each entry of one frame has an entry of its
region in the other with at least its change), which is inclusion at any
class evidence (`Footprint.Covers.le`); the join covers both frames
(`Footprint.covers_join`). -/
namespace Verification.CallEffects
open Verification Footprints

/-- **Entry-wise maximum**: an entry added to a frame raises the change of
the first entry of its region to their maximum, or is appended where no
entry has its region. -/
def Footprint.insertMax : Footprint → Region × Change → Footprint
  | [], e => [e]
  | f :: Φ, e => if f.1 = e.1 then (f.1, f.2.max e.2) :: Φ else f :: Footprint.insertMax Φ e

/-- **The join of two frames** (the note, §3, "Order, top, rigidity": an
upper bound in `⊑`): the second's entries inserted into the first by
entry-wise maximum. -/
def Footprint.join (Φ Ψ : Footprint) : Footprint := Ψ.foldl Footprint.insertMax Φ

/-- Each entry of `Φ` has an entry of its region in `Ψ` with at least its
change. -/
def Footprint.Covers (Φ Ψ : Footprint) : Prop := ∀ e ∈ Φ, ∃ f ∈ Ψ, f.1 = e.1 ∧ e.2.le f.2 = true

private theorem change_le_trans {a b c : Change} (h₁ : a.le b = true) (h₂ : b.le c = true) : a.le c = true := by
  simp only [Change.le, decide_eq_true_eq] at *
  omega

theorem Footprint.Covers.trans {Φ Ψ Θ : Footprint} (h₁ : Footprint.Covers Φ Ψ) (h₂ : Footprint.Covers Ψ Θ) :
    Footprint.Covers Φ Θ := by
  intro e he
  obtain ⟨f, hf, hfe, hle⟩ := h₁ e he
  obtain ⟨g, hg, hgf, hle'⟩ := h₂ f hf
  exact ⟨g, hg, hgf.trans hfe, change_le_trans hle hle'⟩

/-- Covering is inclusion, at any class evidence. -/
theorem Footprint.Covers.le {Φ Ψ : Footprint} (h : Footprint.Covers Φ Ψ) (cl : ClassEvidence) :
    Footprint.le cl Φ Ψ = true := by
  refine List.all_eq_true.mpr fun e he => ?_
  obtain ⟨f, hf, hfe, hle⟩ := h e he
  exact Bool.or_eq_true_iff.mpr (.inr (List.any_eq_true.mpr ⟨f, hf, by rw [hfe]; simp [hle, Region.sub_refl]⟩))

theorem Footprint.covers_insertMax (Φ : Footprint) (e : Region × Change) :
    Footprint.Covers Φ (Footprint.insertMax Φ e) ∧
      ∃ f ∈ Footprint.insertMax Φ e, f.1 = e.1 ∧ e.2.le f.2 = true := by
  induction Φ with
  | nil => exact ⟨(fun _ h => by cases h), ⟨e, List.mem_singleton_self _, rfl, Change.le_refl _⟩⟩
  | cons g Φ ih =>
    simp only [Footprint.insertMax]
    split
    · rename_i hg
      refine ⟨fun e' he' => ?_, ⟨_, List.mem_cons_self .., hg, Change.le_max_right _ _⟩⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨_, List.mem_cons_self .., rfl, Change.le_max_left _ _⟩
      · exact ⟨e', List.mem_cons_of_mem _ he', rfl, Change.le_refl _⟩
    · obtain ⟨hc, f, hf, hfe, hle⟩ := ih
      refine ⟨fun e' he' => ?_, ⟨f, List.mem_cons_of_mem _ hf, hfe, hle⟩⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨e', List.mem_cons_self .., rfl, Change.le_refl _⟩
      · obtain ⟨f', hf', h1, h2⟩ := hc e' he'
        exact ⟨f', List.mem_cons_of_mem _ hf', h1, h2⟩

/-- **The join covers both frames.** -/
theorem Footprint.covers_join (Φ Ψ : Footprint) :
    Footprint.Covers Φ (Footprint.join Φ Ψ) ∧ Footprint.Covers Ψ (Footprint.join Φ Ψ) := by
  induction Ψ generalizing Φ with
  | nil => exact ⟨fun e he => ⟨e, he, rfl, Change.le_refl _⟩, fun _ h => by cases h⟩
  | cons e Ψ ih =>
    obtain ⟨h₁, f, hf, hfe, hle⟩ := Footprint.covers_insertMax Φ e
    obtain ⟨i₁, i₂⟩ := ih (Footprint.insertMax Φ e)
    simp only [Footprint.join, List.foldl_cons] at i₁ i₂ ⊢
    refine ⟨h₁.trans i₁, fun e' he' => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · obtain ⟨g, hg, hgf, hle'⟩ := i₁ f hf
      exact ⟨g, hg, hgf.trans hfe, change_le_trans hle hle'⟩
    · exact i₂ e' he'

end Verification.CallEffects
