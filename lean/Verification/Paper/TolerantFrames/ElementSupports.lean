import Verification.Paper.TolerantFrames.PathTermSupports

/-! # Exact collection readings at the paper's kept support

The notation z[*]:keep expands to both the selected spine and its cells. It
preserves successful partial element readings, including array holes and views.
No element presence, density or ordinary-array restriction is inferred here;
the table's Every-array restriction belongs to its structural body judgment.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames
open Verification.Parity (Path)

/-- The paper's z[*]:keep abbreviation includes spine and element cells. -/
def collectionReads (z : Path) : Footprint :=
  [(.spine z.root z.fields, .keep), (.pathCells z.root z.fields, .keep)]

/-- A successful collection read is of an object, which grow keeps. -/
theorem collection_receiver_kept {h : Heap} {v : Val} {es : List (Option Nat)}
    (he : collectionEntries h v = some es) : Keeps .grow v := by
  cases v with
  | objAt _ _ _ => exact keeps_obj (by decide) rfl
  | _ => simp [collectionEntries, elementsOf] at he

/-- The selected spine is kept, whether an ordinary spine or a view spine. -/
theorem collectionEntries_supported {ρ : Env} {s t : IndexedHeap} {z : Path} {v : Val} {es : List (Option Nat)}
    (hp : z.read ρ s.h = some v)
    (hs : Supported (collectionReads z) ρ s.h t.h)
    (he : collectionEntries s.h v = some es) : collectionEntries t.h v = some es := by
  simp only [collectionEntries, Option.bind_eq_some_iff] at he ⊢
  obtain ⟨st, hst, u, hu, he⟩ := he
  have hm : (Region.spine z.root z.fields).mem ρ s.h st = true := by
    change (match z.read ρ s.h with | some a => elementsOf a == some st | none => false) = true
    simp [hp, hst]
  obtain ⟨u', hu', hh⟩ := hs (.spine z.root z.fields, .keep) (by simp [collectionReads]) st u hm hu
  have hue : u' = u := hh
  subst u'
  exact ⟨st, hst, u, hu', he⟩

/-- A kept cell region preserves a successful old element reading. A hole is
an undefined source value, with no cell requirement added. -/
theorem elementValue_supported {ρ : Env} {s t : IndexedHeap} {z : Path} {v u : Val} {i : Int}
    (hp : z.read ρ s.h = some v)
    (hs : Supported (collectionReads z) ρ s.h t.h)
    (he : elementValue s.h v i = some u) : elementValue t.h v i = some u := by
  by_cases hi : i < 0
  · simp [elementValue, hi] at he
  · simp only [elementValue, hi, ↓reduceIte, bind, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨es, hes, he⟩ := he
    refine ⟨es, collectionEntries_supported hp hs hes, ?_⟩
    split at he
    · cases he
    · exact he
    · rename_i l hl
      have hm : (Region.pathCells z.root z.fields).mem ρ s.h l = true := by
        simp only [Region.mem]
        change (match z.read ρ s.h with | some a => (spineCells s.h a).contains (some l) | none => false) = true
        rw [hp]
        apply List.contains_iff_mem.mpr
        simp only [collectionEntries, Option.bind_eq_some_iff] at hes
        obtain ⟨st, hst, w, hw, hentries⟩ := hes
        apply elementsOf_entries_sub hst
        simp only [entriesAt, hw, hentries, Option.bind_some, Option.getD_some]
        exact List.mem_of_getElem? hl
      obtain ⟨u', hu', hh⟩ := hs (.pathCells z.root z.fields, .keep) (by simp [collectionReads]) l u hm he
      have hue : u' = u := hh
      exact hue ▸ hu'

/-- A successful element reading entails an actual collection listing. -/
theorem elementValue_collection {h : Heap} {v u : Val} {i : Int}
    (he : elementValue h v i = some u) : ∃ es, collectionEntries h v = some es := by
  by_cases hi : i < 0
  · simp [elementValue, hi] at he
  · simp only [elementValue, hi, ↓reduceIte, bind, Option.bind_eq_some_iff] at he
    obtain ⟨es, hes, _⟩ := he
    exact ⟨es, hes⟩

mutual
/-- Exact term supports defined structurally at the paper table's fragment.
Projected element terms receive no constructor here. Arbitrary supported
expression indices, including shifts, are permitted. Bound body-element
restrictions belong to a separate body judgment; all_support covers the full
modality-free syntax. -/
inductive TermExactSupport (omitted : OmittedFields) : Term → Footprint → Prop where
  | literal (n : IntegerLiteral) : TermExactSupport omitted (.literal n) []
  | path (kind : Reading) (p : Path) : TermExactSupport omitted (.path kind p) (pathTermReads omitted kind .keep p)
  | element {z : Path} {index : Expression} {S : Footprint} : ExpressionExactSupport omitted index S →
      TermExactSupport omitted (.element .value z index [] (.inl rfl))
        (reads omitted .grow z ++ collectionReads z ++ S)

inductive ExpressionExactSupport (omitted : OmittedFields) : Expression → Footprint → Prop where
  | constant (n : Int) : ExpressionExactSupport omitted (.constant n) []
  | scale {t S} (c : Int) : TermExactSupport omitted t S → ExpressionExactSupport omitted (.scale c t) S
  | add {e f S T} : ExpressionExactSupport omitted e S → ExpressionExactSupport omitted f T →
      ExpressionExactSupport omitted (.add e f) (S ++ T)
end

private theorem support_left {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported S ρ h h' := fun e he => hs e (List.mem_append_left _ he)
private theorem support_right {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported T ρ h h' := fun e he => hs e (List.mem_append_right _ he)

mutual
/-- Every exact term support preserves its successful partial integer reading. -/
theorem TermExactSupport.sound {omitted t S} (ht : TermExactSupport omitted t S) {ρ m s u}
    (hc : OmissionCondition omitted ρ m s u) (hs : Supported S ρ s.h u.h) {n : Int}
    (he : t.eval ρ s.h = some n) : t.eval ρ u.h = some n := by
  cases ht with
  | literal _ => exact he
  | path k p =>
    obtain ⟨n', hn', _, heq⟩ := path_term_supported hc (.inl rfl) hs he
    simpa only [heq (.inl rfl)] using hn'
  | element hi =>
    simp only [Term.eval, bind, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨v, hp, i, hi', w, hw, v', hv', hn⟩ := he
    obtain ⟨_, hes⟩ := elementValue_collection hw
    have hp' := reads_sound hc (support_left (support_left hs)) (collection_receiver_kept hes) hp
    exact ⟨v, hp', i, ExpressionExactSupport.sound hi hc (support_right hs) hi', w,
      elementValue_supported hp (support_right (support_left hs)) hw, v', hv', hn⟩

/-- Zero coefficients retain the support of their mentioned term. -/
theorem ExpressionExactSupport.sound {omitted e S} (he : ExpressionExactSupport omitted e S) {ρ m s u}
    (hc : OmissionCondition omitted ρ m s u) (hs : Supported S ρ s.h u.h) {n : Int}
    (hv : e.eval ρ s.h = some n) : e.eval ρ u.h = some n := by
  cases he with
  | constant _ => exact hv
  | scale c ht =>
    simp only [Expression.eval, Option.map_eq_some_iff] at hv ⊢
    obtain ⟨a, ha, hv⟩ := hv
    exact ⟨a, TermExactSupport.sound ht hc hs ha, hv⟩
  | add he hf =>
    simp only [Expression.eval, bind, pure, Option.bind_eq_some_iff] at hv ⊢
    obtain ⟨a, ha, b, hb, hv⟩ := hv
    exact ⟨a, ExpressionExactSupport.sound he hc (support_left hs) ha,
      b, ExpressionExactSupport.sound hf hc (support_right hs) hb, hv⟩
end

end Verification.Paper.TolerantFrames
