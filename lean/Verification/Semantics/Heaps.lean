import Verification.Types.Types
/-!
# Heaps and their invariant

The world says what a location is for; the heap says what it holds. `HeapOk`
relates them: every declared location holds a value meeting its contract, at
every level below the current one, with the world truncated to that level.

Membership never inspects the heap, only the world. That is the point of the
whole construction: a write cannot disturb any claim, so preservation reduces to
a local check at the location written -- and allocation preserves the invariant
provided the world's contracts are admissible, which is a property of the
contracts and not of any one type constructor.
-/
namespace Verification

def HeapOk (n : Nat) (W : WorldT n) (h : Heap) : Prop :=
  h.length = (toList W).length ∧
    ∀ l c, lookup W l = some c →
      ∃ v, h[l]? = some v ∧ ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v

/-- At positive remaining level, a heap satisfying a stable location's
contract holds its single value. -/
theorem HeapOk.stable_value {n : Nat} {W : WorldT n} {h : Heap}
    {l : Nat} {c : Ctr n} {v : Val} (hh : HeapOk n W h)
    (hn : 0 < n) (hl : lookup W l = some c) (hc : CtrStable c v) :
    h[l]? = some v := by
  obtain ⟨u, hu, hm⟩ := hh.2 l c hl
  have he := hc 0 hn (trunc 0 (Nat.zero_le n) W) u (hm 0 hn)
  simpa [he] using hu

/-- Heap satisfaction survives dropping a level, with the world truncated. -/
theorem HeapOk_trunc (n : Nat) (W : WorldT (n + 1)) (h : Heap)
    (hok : HeapOk (n + 1) W h) : HeapOk n (trunc n (Nat.le_succ n) W) h := by
  obtain ⟨hlen, hall⟩ := hok
  refine ⟨by simpa [trunc, lookup] using hlen, ?_⟩
  intro l c hl
  simp only [lookup, trunc, toList_ofList, List.getElem?_map] at hl
  rcases hd : (toList W)[l]? with _ | d
  · rw [hd] at hl; simp at hl
  · rw [hd] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    obtain ⟨v, hv, hmem⟩ := hall l d (by simpa [lookup] using hd)
    refine ⟨v, hv, ?_⟩
    intro j hj
    rw [trunc_trunc]
    exact hmem j (by omega)

/-- A write meeting the contract preserves satisfaction, including when the
location is aliased: no other location's obligation mentions the heap. -/
theorem write_sound (n : Nat) (W : WorldT n) (h : Heap) (l : Nat) (c : Ctr n) (v : Val)
    (hok : HeapOk n W h) (hl : lookup W l = some c)
    (hv : ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v) :
    HeapOk n W (h.set l v) := by
  obtain ⟨hlen, hall⟩ := hok
  refine ⟨by simpa using hlen, ?_⟩
  intro k d hk
  by_cases hkl : k = l
  · subst hkl
    rw [hl] at hk; cases hk
    refine ⟨v, ?_, hv⟩
    have hlt : k < h.length := by
      have := (List.getElem?_eq_some_iff.mp hl).1
      simp only [lookup] at hl
      omega
    simp [hlt]
  · obtain ⟨w, hw, hmem⟩ := hall k d hk
    exact ⟨w, by rwa [List.getElem?_set_ne (fun hc => hkl hc.symm)], hmem⟩

/-- **Allocation preserves satisfaction — and this is where admissibility is
needed.** Every existing location's obligation is stated against a contract that
must survive the world growing, which is a property of the contracts, not of any
one type constructor. -/
theorem heap_alloc (n : Nat) (W : WorldT n) (h : Heap) (c : Ctr n) (v : Val)
    (hok : HeapOk n W h) (hadm : WorldAdm W)
    (hv : ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) (appendW W c)) v) :
    HeapOk n (appendW W c) (h ++ [v]) := by
  obtain ⟨hlen, hall⟩ := hok
  refine ⟨by simp [appendW, hlen], ?_⟩
  intro l d hl
  have hl' : (toList W ++ [c])[l]? = some d := by simpa [lookup, appendW] using hl
  by_cases hlt : l < (toList W).length
  · rw [List.getElem?_append_left hlt] at hl'
    have hlW : lookup W l = some d := by simpa [lookup] using hl'
    obtain ⟨w, hw, hmem⟩ := hall l d hlW
    refine ⟨w, by rw [List.getElem?_append_left (by omega)]; exact hw, ?_⟩
    intro j hj
    exact (hadm l d hlW).1 j hj _ _
      (WExt_trunc (Nat.le_of_lt hj) (WExt_appendW W c)) w (hmem j hj)
  · have hb : l < (toList W).length + 1 := by
      have := (List.getElem?_eq_some_iff.mp hl').1; simpa using this
    have hll : l = (toList W).length := by omega
    subst hll
    rw [List.getElem?_append_right (Nat.le_refl _)] at hl'
    simp at hl'
    subst hl'
    refine ⟨v, ?_, hv⟩
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]

/-- **Allocating a whole object.** One object takes one fresh location per
named field, so the world grows by that many contracts at once. Each is the
single allocation above, so admissibility is needed for exactly the same
reason and nothing new is assumed. -/
theorem heap_allocs : ∀ (n : Nat) (cs : List (Ctr n)) (W : WorldT n) (h : Heap) (vs : List Val),
    HeapOk n W h → WorldAdm W → (∀ c ∈ cs, CtrAdm c) → cs.length = vs.length →
    (∀ p ∈ cs.zip vs, ∀ (j : Nat) (hj : j < n),
      p.1 j hj (trunc j (Nat.le_of_lt hj) W) p.2) →
    HeapOk n (appendWs W cs) (h ++ vs) := by
  intro n cs
  induction cs with
  | nil =>
    intro W h vs hok _ _ hlen _
    have hv : vs = [] := by cases vs <;> simp_all
    subst hv
    simpa using hok
  | cons c cs ih =>
    intro W h vs hok hadm hc hlen hv
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have hcadm := hc c (by simp)
      have hxt : ∀ (j : Nat) (hj : j < n),
          WExt (trunc j (Nat.le_of_lt hj) W) (trunc j (Nat.le_of_lt hj) (appendW W c)) :=
        fun j hj => WExt_trunc (Nat.le_of_lt hj) (WExt_appendW W c)
      have hstep : HeapOk n (appendW W c) (h ++ [v]) := by
        refine heap_alloc n W h c v hok hadm ?_
        intro j hj
        exact hcadm.1 j hj _ _ (hxt j hj) v (hv (c, v) (by simp) j hj)
      have hrest := ih (appendW W c) (h ++ [v]) vs hstep
        (WorldAdm_append hadm hcadm) (fun d hd => hc d (by simp [hd]))
        (by simpa using hlen) ?_
      · rw [appendWs_cons]
        simpa [List.append_assoc] using hrest
      · rintro ⟨d, w⟩ hp j hj
        have hd : d ∈ cs := (List.of_mem_zip hp).1
        exact (hc d (by simp [hd])).1 j hj _ _ (hxt j hj) w
          (hv (d, w) (List.mem_cons_of_mem _ hp) j hj)

end Verification
