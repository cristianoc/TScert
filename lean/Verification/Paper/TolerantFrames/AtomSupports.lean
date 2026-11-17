import Verification.Paper.TolerantFrames.ElementSupports

/-! # Element and density supports

The paper keeps every index/bound reading exactly. A density's receiver is a
variable, so only its ordinary array spine needs grow. Element facts retain the
selected receiver, spine and cells, including undefined values at holes.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames
open Verification.Parity (Path)

private theorem support_left {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported S ρ h h' := fun e he => hs e (List.mem_append_left _ he)
private theorem support_right {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported T ρ h h' := fun e he => hs e (List.mem_append_right _ he)

/-- The complete element-atom row, ordinary and view readings alike. -/
theorem element_atom_support {omitted : OmittedFields} {index : Expression} {S : Footprint}
    (hi : ExpressionExactSupport omitted index S) (z : Path) (w : Value) :
    Supports (OmissionCondition omitted) (Formula.atom (.element z index w)).meaning
      (reads omitted .grow z ++ collectionReads z ++ S) := by
  intro ρ m s t _ ⟨_, hc⟩ hF hs
  obtain ⟨v, i, u, hp, hindex, he, hw⟩ := hF
  obtain ⟨_, hcol⟩ := elementValue_collection he
  have hp' := reads_sound hc (support_left (support_left hs)) (collection_receiver_kept hcol) hp
  exact ⟨v, i, u, hp', hi.sound hc (support_right hs) hindex,
    elementValue_supported hp (support_right (support_left hs)) he, hw⟩

/-- Dense-prefix tolerance preserves every fixed mathematical density bound,
including vacuous negative bounds. No bound≤length premise is inserted. -/
theorem density_of_densePrefixes {es es' : List (Option Nat)} {n : Int}
    (hg : ∀ k, DensePrefix k es → DensePrefix k es')
    (hd : ∀ i : Nat, (i : Int) < n → ∃ l, es[i]? = some (some l)) :
    ∀ i : Nat, (i : Int) < n → ∃ l, es'[i]? = some (some l) := by
  intro i hi
  obtain ⟨old, hold⟩ := hd i hi
  have hlt : i < es.length := (List.getElem?_eq_some_iff.mp hold).1
  have hp : DensePrefix (i + 1) es := by
    refine ⟨by omega, fun j hj hh => ?_⟩
    obtain ⟨l, hl⟩ := hd j (by omega)
    rw [hl] at hh
    cases hh
  have hp' := hg (i + 1) hp
  have hi' : i < es'.length := by have := hp'.1; omega
  have hcell := List.getElem?_eq_getElem hi'
  cases ho : es'[i] with
  | none => exact (hp'.2 i (by omega) (by simpa only [ho] using hcell)).elim
  | some l => exact ⟨l, by simpa only [ho] using hcell⟩

/-- Exactly spine_grow(x) plus the support keeping the bound's value. -/
theorem density_support {omitted : OmittedFields} {bound : Expression} {S : Footprint}
    (hb : ExpressionExactSupport omitted bound S) (x : Nat) :
    Supports (OmissionCondition omitted) (Formula.atom (.dense x bound)).meaning
      ([(.spine x [], .grow)] ++ S) := by
  intro ρ m s t _ ⟨_, hc⟩ hF hs
  obtain ⟨st, es, n, hst, hes, hn, hd⟩ := hF
  have hselected : elementsOf (ρ x) = some st := by
    cases hv : ρ x <;> simp_all [spineOf, fieldsOf, elementsOf]
  have hm : (Region.spine x []).mem ρ s.h st = true := by
    simp [Region.mem, readPath, hselected]
  obtain ⟨v', hv', hg⟩ := support_left hs _ (List.mem_singleton_self _) st (.arr es) hm hes
  have hn' := hb.sound hc (support_right hs) hn
  rcases hg with rfl | ⟨es0, es', heq, rfl, hdp, _, _⟩ | hscalar | ⟨_, _, _, hbad, _⟩
  · exact ⟨st, es, n, hst, hv', hn', hd⟩
  · cases heq
    exact ⟨st, es', n, hst, hv', hn', density_of_densePrefixes hdp hd⟩
  · exact (by cases hscalar.2.1)
  · cases hbad

end Verification.Paper.TolerantFrames
