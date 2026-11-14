import Verification.Semantics.KindsAllocation
import Verification.Semantics.SafeIntegers

/-! # The contract of a view store

A typed array's view store lists one element cell per index (`Cat`,
`StoreForm.view`). Its cells hold numbers of the store's format, and its
contract admits every replacement a write through any typed array may make:
every view store of its format and length whose cells are such cells (the
note *Tolerant frames*, (W2): "the contract of a view store admits every
such store"). A world whose every view-store location has this canonical
contract is a **view world** (`ViewWorld`); truncation and extension keep it
(`ViewWorld.trunc`, `ViewWorld.appendWs`), an allocation of a typed array
choosing the canonical contract keeps it (`ViewWorld.typedArray`), and on a
well-formed heap of a view world every cell a view store lists holds a
number of its format (`HeapOk.view_cell_stored`).

The format's stored range here is a predicate on a cell's contents: an
integer in the format's range for `uint8`, `uint16` and `int32`, any number
for `float64`. The host's total conversion of a written number into that
range is the primitive write's, which the operational rules state. -/
namespace Verification

/-- The integers an integer format stores: `0` to `2^8 - 1`, `0` to
`2^16 - 1`, `-2^31` to `2^31 - 1`; `float64` stores every number. -/
def ViewFormat.range : ViewFormat → Option (Int × Int)
  | .uint8 => some (0, 255)
  | .uint16 => some (0, 65535)
  | .int32 => some (-2147483648, 2147483647)
  | .float64 => none

/-- **The values a format stores**: a number, an integer in the format's
range where it has one. -/
def ViewFormat.Stored (f : ViewFormat) (v : Val) : Prop :=
  ∃ b, v = .num b ∧ ∀ lo hi, f.range = some (lo, hi) → ∃ i, SafeIntegers.SafeInt b i ∧ lo ≤ i ∧ i ≤ hi

theorem ViewFormat.Stored.isVal {f : ViewFormat} {v : Val} (h : f.Stored v) : isVal v = true := by
  obtain ⟨b, rfl, -⟩ := h; rfl

/-- A cell of a view store of format `f` in `U`: an element cell whose
contract admits exactly the values `f` stores, at every level it inspects. -/
def ViewCell {j : Nat} (U : WorldT j) (f : ViewFormat) (c : Nat) : Prop :=
  roleAt U c = some .elem ∧
    ∃ d, lookup U c = some d ∧ ∀ i (hi : i < j) (U' : WorldT i) u, d i hi U' u ↔ f.Stored u

theorem ViewCell.mono {j : Nat} {U U' : WorldT j} (hx : WExt U U') {f : ViewFormat} {c : Nat}
    (h : ViewCell U f c) : ViewCell U' f c := by
  obtain ⟨hr, d, hd, hiff⟩ := h
  exact ⟨WExt_roleAt hx hr, d, WExt_lookup hx hd, hiff⟩

theorem ViewCell.trunc {k j : Nat} (hj : j ≤ k) {W : WorldT k} {f : ViewFormat} {c : Nat}
    (h : ViewCell W f c) : ViewCell (Verification.trunc j hj W) f c := by
  obtain ⟨hr, d, hd, hiff⟩ := h
  exact ⟨by simpa using hr, _, lookup_trunc hj W c d hd, fun i hi U' u => hiff i _ U' u⟩

/-- **The canonical contract of a view store** of format `f` and length `N`:
every view store of that format and length whose cells are cells of the
format. -/
def viewStoreCtr (k : Nat) (f : ViewFormat) (N : Nat) : Ctr k :=
  fun _ _ U v => ∃ cs, v = .viewStore f cs ∧ cs.length = N ∧ ∀ c ∈ cs, ViewCell U f c

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

/-- **A view world**: every view-store location has the canonical contract
of its format and length, at every level it inspects. -/
def ViewWorld {k : Nat} (W : WorldT k) : Prop :=
  ∀ l f N, roleAt W l = some (.store (.view f N)) →
    ∃ c, lookup W l = some c ∧ ∀ j (hj : j < k) U v, c j hj U v ↔ viewStoreCtr k f N j hj U v

theorem ViewWorld.trunc {k j : Nat} (hj : j ≤ k) {W : WorldT k} (hW : ViewWorld W) :
    ViewWorld (Verification.trunc j hj W) := by
  intro l f N hr
  obtain ⟨c, hc, hiff⟩ := hW l f N (by simpa using hr)
  exact ⟨_, lookup_trunc hj W l c hc, fun i hi U v => hiff i _ U v⟩

/-- **Extension keeps a view world** where each appended view-store entry
has the canonical contract. -/
theorem ViewWorld.appendWs {k : Nat} {W : WorldT k} {es : List (Role × Ctr k)} (hW : ViewWorld W)
    (hes : ∀ e ∈ es, ∀ f N, e.1 = .store (.view f N) →
      ∀ j (hj : j < k) U v, e.2 j hj U v ↔ viewStoreCtr k f N j hj U v) :
    ViewWorld (Verification.appendWs W es) := by
  intro l f N hr
  by_cases hl : l < (entries W).length
  · rw [roleAt_appendWs_lt W es hl] at hr
    obtain ⟨c, hc, hiff⟩ := hW l f N hr
    exact ⟨c, by rw [lookup_appendWs_lt W es hl]; exact hc, hiff⟩
  · have hge : (entries W).length ≤ l := by omega
    rw [roleAt_appendWs_ge W es hge] at hr
    obtain ⟨i, rfl⟩ : ∃ i, l = (entries W).length + i := ⟨l - (entries W).length, by omega⟩
    simp only [Nat.add_sub_cancel_left, List.getElem?_map, Option.map_eq_some_iff] at hr
    obtain ⟨e, he, hef⟩ := hr
    refine ⟨e.2, ?_, hes e (List.mem_of_getElem? he) f N hef⟩
    rw [lookup_appendWs_ge]; simp [he]

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
well-formed heap of a view world, at level 2 or more: the store meets its
canonical contract, which makes each listed cell one whose contract admits
exactly those numbers, and the cell meets its contract. -/
theorem HeapOk.view_cell_stored {n : Nat} {W : WorldT (n + 2)} {h : Heap} (hok : HeapOk (n + 2) W h)
    (hW : ViewWorld W) {s : Nat} {f : ViewFormat} {cs : List Nat} (hs : h[s]? = some (.viewStore f cs))
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
      obtain ⟨d, hd, hiff⟩ := hW s f N hr
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

end Verification
