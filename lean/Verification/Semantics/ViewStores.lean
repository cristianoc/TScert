import Verification.Semantics.KindsAllocation
import Verification.Semantics.ViewConversion

/-! # The contract of a view store

A typed array's view store lists one element cell per index (`Cat`,
`StoreForm.view`). Its cells hold numbers of the store's format, and its
contract admits every replacement a write through any typed array may make:
every view store of its format and length whose cells are such cells
(`viewStoreCtr`, `Worlds.lean`; the note *Tolerant frames*, (W2): "the
contract of a view store admits every such store"). Every admissible world
gives each view store this canonical contract (`WorldAdm.view`); an
allocation of a typed array choosing it keeps an admissible world
(`WorldAdm.typedArray`), and on a well-formed heap of an admissible world
every cell a view store lists holds a number of its format, at level 2 or
more (`HeapOk.view_cell_stored`). The host's total conversion of a written
number into that range is `ViewFormat.conv` (`ViewFormat.conv_stored`). -/
namespace Verification

theorem viewStoreCtr_adm (k : Nat) (f : ViewFormat) (N : Nat) : CtrAdm (viewStoreCtr k f N) := by
  refine ⟨fun j _ U U' hx v hv => ?_, fun _ _ _ v hv => ?_⟩
  · obtain ⟨cs, rfl, hn, hc⟩ := hv
    exact ⟨cs, rfl, hn, fun c hc' => (hc c hc').mono hx⟩
  · obtain ⟨cs, rfl, -, -⟩ := hv; rfl

/-- **The canonical contract admits every replacement**: every view store
of the format and length whose cells are cells of the format, the old
vector, a reordering, or one of fresh cells alike. -/
theorem viewStoreCtr_admits {k j : Nat} (hj : j < k) (U : WorldT j) {f : ViewFormat} {cs : List Nat}
    (hcs : ∀ c ∈ cs, ViewCell U f c) : viewStoreCtr k f cs.length j hj U (.viewStore f cs) :=
  ⟨cs, rfl, rfl, hcs⟩

/-- The contract of a cell of format `f`. -/
def viewCellCtr (k : Nat) (f : ViewFormat) : Ctr k := fun _ _ _ u => f.Stored u

theorem viewCellCtr_adm (k : Nat) (f : ViewFormat) : CtrAdm (viewCellCtr k f) :=
  ⟨fun _ _ _ _ _ _ h => h, fun _ _ _ _ h => h.isVal⟩

/-- **A typed array's allocation keeps a view world** where its view store
gets the canonical contract and its own fields no view-store role: the
note's (W2) for an allocated typed array. -/
theorem ViewWorld.typedArray {k : Nat} {W : WorldT k} (hW : ViewWorld W) (f : ViewFormat) (N : Nat)
    (rs : List Role) (ccs : List (Ctr k)) (hrs : ∀ r ∈ rs, ∀ f N, r ≠ .store (.view f N)) :
    ViewWorld (Verification.appendWs (Verification.appendWs W [(.store (.view f N), viewStoreCtr k f N)])
      (Kinds.objectEntries rs ccs)) := by
  refine ViewWorld.appendWs (ViewWorld.appendWs hW ?_) ?_
  · intro e he f' N' hef j hj U v
    simp only [List.mem_singleton] at he
    subst he
    simp only [Role.store.injEq, StoreForm.view.injEq] at hef
    obtain ⟨rfl, rfl⟩ := hef
    exact Iff.rfl
  · intro e he f' N' hef
    have hmem : e.1 ∈ rs ++ [Role.identity] := by
      have := List.of_mem_zip he
      exact this.1
    rcases List.mem_append.mp hmem with h | h
    · exact absurd hef (hrs _ h f' N')
    · simp only [List.mem_singleton] at h; rw [h] at hef; cases hef

/-- **The cells of a view store hold numbers of its format** on a
well-formed heap of an admissible world, at level 2 or more: the store meets its
canonical contract, which makes each listed cell one whose contract admits
exactly those numbers, and the cell meets its contract. -/
theorem HeapOk.view_cell_stored {n : Nat} {W : WorldT (n + 2)} {h : Heap} (hok : HeapOk (n + 2) W h)
    (hW : WorldAdm W) {s : Nat} {f : ViewFormat} {cs : List Nat} (hs : h[s]? = some (.viewStore f cs))
    {c : Nat} (hc : c ∈ cs) {u : Val} (hu : h[c]? = some u) : f.Stored u := by
  have hlen : s < (entries W).length := by
    have := (List.getElem?_eq_some_iff.mp hs).1
    have h1 := hok.1.1; simp only [toList_length] at h1; omega
  obtain ⟨r, hr⟩ := roleAt_some hlen
  obtain ⟨u₀, hu₀, hcat, -⟩ := hok.2 s r hr
  rw [hs] at hu₀; cases hu₀
  cases r with
  | store sf =>
    cases sf with
    | array => obtain ⟨_, he⟩ := hcat; cases he
    | view f' N =>
      obtain ⟨cs', he, -⟩ := hcat
      cases he
      obtain ⟨d, hd, hiff⟩ := hW.view s f N hr
      obtain ⟨v, hv, hall⟩ := hok.1.2 s d hd
      rw [hs] at hv; cases hv
      obtain ⟨cs'', he, -, hcells⟩ := (hiff (n + 1) (by omega) _ _).mp (hall (n + 1) (by omega))
      cases he
      obtain ⟨-, d', hd', hiff'⟩ := hcells c hc
      obtain ⟨e, he, rfl⟩ := lookup_trunc_inv (Nat.le_of_lt (by omega)) W c d' hd'
      obtain ⟨v', hv', hall'⟩ := hok.1.2 c e he
      rw [hu] at hv'; cases hv'
      exact (hiff' n (by omega) _ u).mp (hall' n (by omega))
  | field | cell | elem | identity => simp [Cat, isSourceVal] at hcat

/-- **A typed array's allocation keeps an admissible world** where its view
store gets the canonical contract and its own fields admissible contracts of
no view-store role: the note's (W2) for an allocated typed array, as a
native constructor's, `subarray`'s or `Buffer`'s contract must allocate it. -/
theorem WorldAdm.typedArray {k : Nat} {W : WorldT k} (hW : WorldAdm W) (f : ViewFormat) (N : Nat)
    (rs : List Role) (ccs : List (Ctr k)) (hrs : ∀ r ∈ rs, ∀ f N, r ≠ .store (.view f N))
    (hccs : ∀ c ∈ ccs, CtrAdm c) :
    WorldAdm (Verification.appendWs (Verification.appendWs W [(.store (.view f N), viewStoreCtr k f N)])
      (Kinds.objectEntries rs ccs)) := by
  have h₁ : WorldAdm (Verification.appendWs W [(.store (.view f N), viewStoreCtr k f N)]) :=
    WorldAdm_appendWs hW (fun e he => by simp only [List.mem_singleton] at he; subst he; exact viewStoreCtr_adm k f N)
      (fun e he f' N' hef => by
        simp only [List.mem_singleton] at he; subst he
        simp only [Role.store.injEq, StoreForm.view.injEq] at hef
        obtain ⟨rfl, rfl⟩ := hef
        exact fun _ _ _ _ => Iff.rfl)
  refine ⟨(WorldAdm_appendWs h₁ (fun e he => ?_) (fun e he f' N' hef => ?_)).ctr, hW.view.typedArray f N rs ccs hrs⟩
  · have hmem : e.2 ∈ ccs ++ [Kinds.idCtr] := (List.of_mem_zip he).2
    rcases List.mem_append.mp hmem with h | h
    · exact hccs _ h
    · simp only [List.mem_singleton] at h; rw [h]; exact Kinds.idCtr_adm
  · have hmem : e.1 ∈ rs ++ [Role.identity] := (List.of_mem_zip he).1
    rcases List.mem_append.mp hmem with h | h
    · exact absurd hef (hrs _ h f' N')
    · simp only [List.mem_singleton] at h; rw [h] at hef; cases hef

end Verification
