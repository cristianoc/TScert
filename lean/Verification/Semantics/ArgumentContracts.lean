import Verification.Semantics.Safety

/-! Same-level contracts on argument lists. Grouping evaluated arguments adds
no operational step; the call or constructor supplies the recursive guard. -/
namespace Verification.ArgumentContracts

/-- A contract on an actual list; grouping values spends no execution step. -/
abbrev Family := ArgFam

/-- The same tuple shape as a store, interpreted on values at this level. -/
def Fits (T : TupleF) : Family := fun n W vs =>
  TupleFits (fun A v => A n W v) T vs

theorem fits_adm {T : TupleF}
    (hT : ∀ i A, positionFam T i = some A → Adm A) : Adm (Fits T) :=
  Adm.of_transfer (fun h j hj U hx =>
    h.map (fun i A hA _v hv => (hT i A hA).transfer hv j hj U hx))

/-- Exact tuples and fixed parameters have identical membership, for arbitrary
families: objects, callbacks and recursive types need no stability premise.
Readonly positions admit the same lists: a list holds values, not locations. -/
theorem fits_exact {r : Bool} {d : ArrayPresence} (As : List Fam) (n W vs) :
    Fits ⟨As, [], none, r, d⟩ n W vs ↔ ArgsT As n W vs := by
  constructor
  · rintro ⟨hl, hb, hp⟩
    dsimp at hl hb
    have hlen : As.length = vs.length := by have := hb rfl; omega
    apply ArgsT_of_getElem? hlen
    intro i A v hA hv
    exact hp i v A hv (by simp [positionFam, hA])
  · intro ha
    have hl := ArgsT_length ha
    refine ⟨by simp [hl], by simp [hl], ?_⟩
    intro i v A hv hA
    have hi : i < As.length := by
      obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hv
      omega
    have he : As[i]? = some A := by
      simpa [positionFam, List.getElem?_eq_getElem hi] using hA
    exact ArgsT_getElem? ha he hv

/-- An element rest admits exactly the lists of its element's values at this
level. -/
theorem fits_elem {E : Fam} {r : Bool} {d : ArrayPresence} {n W vs} :
    Fits ⟨[], [], some E, r, d⟩ n W vs ↔ ∀ v ∈ vs, E n W v := by
  constructor
  · rintro ⟨-, -, hp⟩ v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    exact hp i _ E (List.getElem?_eq_getElem hi) (by simp [positionFam])
  · intro h
    refine ⟨by simp, by simp, fun i v A hv hA => ?_⟩
    simp only [positionFam, List.getElem?_nil, List.length_nil, Nat.sub_zero,
      Nat.add_zero, Nat.zero_le, if_true, Option.some.injEq] at hA
    cases hA
    exact h v (List.mem_of_getElem? hv)

/-- Within a contract's bounds every index has a position. -/
theorem positionFam_isSome {T : TupleF} {i : Nat}
    (h : i < T.required.length + T.optional.length ∨ T.rest.isSome = true) :
    (positionFam T i).isSome = true := by
  unfold positionFam
  cases hr : T.required[i]? with
  | some A => rfl
  | none =>
    cases ho : T.optional[i - T.required.length]? with
    | some A => rfl
    | none =>
      rw [List.getElem?_eq_none_iff] at hr ho
      simp only
      rcases h with h | h
      · omega
      · rw [if_pos (by omega)]; exact h

/-- A tuple's element bound constrains the same-level argument values. -/
theorem fits_bound {T : TupleF} {E : Fam}
    (hb : ∀ i A, positionFam T i = some A → FamLe A E) {n W vs}
    (h : Fits T n W vs) : ∀ v ∈ vs, E n W v := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hs : (positionFam T i).isSome = true := by
    apply positionFam_isSome
    cases hr : T.rest with
    | none => have := h.2.1 hr; left; omega
    | some _ => right; rfl
  obtain ⟨A, hA⟩ := Option.isSome_iff_exists.mp hs
  exact hb i A hA n W _ (h.2.2 i _ A (List.getElem?_eq_getElem hi) hA)

abbrev Admissible := @Adm (List Val)

/-- One operational call promise for every argument-list presentation. -/
def callable (Ξ : Fam) (P : Family) (Rc R : Fam) : Fam := fun n W v =>
  Invocable v ∧ Promise Ξ P Rc R n W v

/-- Elimination uses the existing operational step and establishes `Safe`. -/
theorem call_safe {P : Family} {Rc R : Fam} (hP : Admissible P) (hRc : Adm Rc)
    {n W heap f r vs} (hf : callable Ξ P Rc R n W f) (hr : Rc n W r)
    (hrv : isVal r = true) (hv : CallArguments.Values vs) (ha : P n W vs)
    (hw : WorldAdm W) (hh : HeapOk n W heap) : Safe Ξ R n W heap (.invoke f r vs) := by
  cases n with
  | zero => trivial
  | succ n =>
    let U := trunc n (Nat.le_succ n) W
    obtain ⟨body, hi, hs⟩ := hf.2 n (Nat.lt_succ_self n) U (WExt_refl _)
      (WorldAdm_trunc _ hw) heap (HeapOk_trunc n W heap hh) r hrv (hRc.down n W r hr)
      vs hv (hP.transfer ha n (Nat.le_succ n) U (WExt_refl _))
    exact .inr ⟨U, heap, body, WExt_refl _, WorldAdm_trunc _ hw, hi.step heap,
      HeapOk_trunc n W heap hh, hs⟩

#print axioms fits_adm
#print axioms fits_exact
#print axioms fits_elem
#print axioms call_safe
end Verification.ArgumentContracts
