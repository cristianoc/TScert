import Verification.Semantics.TolerantFrames

/-! # Tolerant frames: allocated cells and separation

A store lists only cells of its world, each of the element role, so every
state's roots list allocated cells (`rootCells_holds`). A root's **allocated cells**
(`RootCells`: every cell its store lists is below the heap's length,
`HeapKnowledge.ElementsBelow`) follow, at every state an admissible transition
reaches, from a fact of the world: its store location's contract lists only
cells of its world (`StoreCells`, `CellsCtr`), as every tuple contract does
(`listT_cells`). That fact is established by a lookup and kept by every
admissible transition (`storeCells_invariant`), so no step need preserve the
cells themselves.

With allocated cells, two separations hold: a store allocated past a mark is
apart from an old store whose cells lie below it (`alloc_apart`), and two
apart arrays stay apart when one's store grows and the other's is kept
(`apart_grow_keep`, the third atom). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.HeapKnowledge (ElementsBelow ElementsAbove RegionOf RegionsApart InRegion)

/-! ## Allocated cells from contracts -/

/-- A contract every store of which lists only cells of its world. -/
def CellsCtr {k : Nat} (c : Ctr k) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j) (ls : List (Option Nat)), c j hj U (.arr ls) →
    ElementsBelow (toList U).length ls

/-- **A tuple contract lists cells of its world**: each position is
required, optional or rest, and each states a lookup of its cell. -/
theorem listT_cells {T : TupleF} {k : Nat} {W : WorldT k} {ls : List (Option Nat)}
    (h : listT T k W (.arr ls)) : ElementsBelow (toList W).length ls := by
  obtain ⟨ls', he, -, -, -, -, hreq, hopt, hrest⟩ := h
  cases he
  intro l hm
  obtain ⟨i, hi, hil⟩ := List.getElem_of_mem hm
  have hget : ls[i]? = some (some l) := by rw [List.getElem?_eq_getElem hi, hil]
  have found : ∃ c, lookup W l = some c := by
    by_cases h1 : i < T.required.length
    · obtain ⟨A, hA⟩ : ∃ A, T.required[i]? = some A := ⟨_, List.getElem?_eq_getElem h1⟩
      obtain ⟨l', c, hl', hw, -⟩ := hreq i A hA
      rw [hget] at hl'; cases hl'
      exact ⟨c, hw⟩
    · by_cases h2 : i < T.required.length + T.optional.length
      · have hi' : i - T.required.length < T.optional.length := by omega
        obtain ⟨A, hA⟩ : ∃ A, T.optional[i - T.required.length]? = some A := ⟨_, List.getElem?_eq_getElem hi'⟩
        have hget' : ls[T.required.length + (i - T.required.length)]? = some (some l) := by
          rw [show T.required.length + (i - T.required.length) = i by omega]; exact hget
        obtain ⟨c, hw, -⟩ := hopt _ A l hA hget'
        exact ⟨c, hw⟩
      · obtain ⟨-, c, -, hw, -⟩ := hrest i l (by omega) hget
        exact ⟨c, hw⟩
  obtain ⟨c, hc⟩ := found
  exact (List.getElem?_eq_some_iff.mp hc).1

/-- A contract whose stores meet a tuple contract lists cells of its world. -/
theorem cellsCtr_of_listT {k : Nat} {c : Ctr k}
    (hc : ∀ j hj U u, c j hj U u → ∃ T, listT T j U u) : CellsCtr c :=
  fun j hj U ls hu => by obtain ⟨T, hT⟩ := hc j hj U _ hu; exact listT_cells hT

/-- Restricting a contract to a lower budget keeps the property. -/
theorem CellsCtr.restrict {k j : Nat} {c : Ctr k} (hc : CellsCtr c) (hle : j ≤ k) :
    CellsCtr (fun i hi w => c i (Nat.lt_of_lt_of_le hi hle) w) :=
  fun i _ U ls hu => hc i _ U ls hu

/-- `cells(x)`, a fact of the world: `x`'s store location has a contract
listing only cells of its world. -/
def StoreCells (x : Nat) : Assertion := fun ρ _ s =>
  ∃ st c, storeOf (ρ x) = some st ∧ lookup s.W st = some c ∧ CellsCtr c

/-- `x`'s store lists only allocated cells: the review's relevant-root
`ElementsBelow`. -/
def RootCells (x : Nat) : Assertion := fun ρ _ s =>
  ∀ st ls, storeOf (ρ x) = some st → s.h[st]? = some (.arr ls) → ElementsBelow s.h.length ls

/-- **The store-cells fact is invariant**: a contract persists, restricted,
along every admissible transition. -/
theorem storeCells_invariant (x : Nat) : Invariant (StoreCells x) := by
  intro ρ m s s' ha ⟨st, c, hst, hl, hc⟩
  obtain ⟨hle, hl'⟩ := ha.lookup_ext hl
  exact ⟨st, _, hst, hl', hc.restrict hle⟩

/-- **The store-cells fact gives allocated cells** at the state, at its
positive budget: the heap meets the contract one level down. -/
theorem rootCells_of_storeCells {x : Nat} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hs : StoreCells x ρ m s) : RootCells x ρ m s := by
  obtain ⟨st, c, hst, hl, hc⟩ := hs
  intro st' ls hst' hv
  rw [hst] at hst'; cases hst'
  obtain ⟨v, hv', hall⟩ := s.ok.1.2 st c hl
  rw [hv] at hv'; cases hv'
  have h0 := hc 0 s.pos _ ls (hall 0 s.pos)
  simpa [toList_length, s.ok.1.1] using h0

/-- **Allocated cells hold after every action**, from the store-cells fact. -/
theorem rootCells_box {Φ : Footprint} {x : Nat} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hs : StoreCells x ρ m s) : Box Φ (RootCells x) ρ m s :=
  fun s' ha => rootCells_of_storeCells (storeCells_invariant x ρ m s s' ha.1 hs)

/-- Establishment: a store location whose contract's stores meet a tuple
contract. -/
theorem storeCells_of_listT {x : Nat} {ρ : Env} {m : Nat} {s : IndexedHeap} {st : Nat} {c : Ctr s.n}
    (hst : storeOf (ρ x) = some st) (hl : lookup s.W st = some c)
    (hc : ∀ j hj U u, c j hj U u → ∃ T, listT T j U u) : StoreCells x ρ m s :=
  ⟨st, c, hst, hl, cellsCtr_of_listT hc⟩

/-! ## Allocated cells hold at every state -/

/-- **Every state's roots list allocated cells**: a store the heap holds has
valid references, so each cell it lists has the element role, a location of
the world and so of the heap. -/
theorem rootCells_holds (x : Nat) (ρ : Env) (m : Nat) (s : IndexedHeap) : RootCells x ρ m s := by
  intro st ls _ hv l hl
  have hrole := RefsOk_arr_iff.mp (s.ok.refs_at hv) l hl
  have hlt : l < (roles s.W).length := (List.getElem?_eq_some_iff.mp hrole).1
  rw [s.ok.1.1, toList_length]
  simpa [roles] using hlt

/-- **`RootCells` is invariant**: it holds at every state. -/
theorem rootCells_invariant (x : Nat) : Invariant (RootCells x) :=
  fun ρ m _ s' _ _ => rootCells_holds x ρ m s'

/-! ## Allocation separation -/

/-- **A store allocated past a mark is apart from an old one**: `x`'s store
location and cells at or past `b`, `y`'s store location and cells below
`b`. -/
theorem alloc_apart {h : Heap} {u w : Val} {sx sy b : Nat} {xs ys : List (Option Nat)}
    (hx : storeOf u = some sx) (hxv : h[sx]? = some (.arr xs)) (hbx : b ≤ sx) (hax : ElementsAbove b xs)
    (hy : storeOf w = some sy) (hyv : h[sy]? = some (.arr ys)) (hby : sy < b) (hay : ElementsBelow b ys) :
    RegionsApart h u w := by
  refine ⟨some sx, xs, some sy, ys, .inr ⟨sx, rfl, hx, hxv⟩, .inr ⟨sy, rfl, hy, hyv⟩, ?_⟩
  intro l hl l' hl' he
  subst he
  have hge : b ≤ l := by
    rcases hl with hl | hl
    · cases hl; exact hbx
    · exact hax l hl
  have hlt : l < b := by
    rcases hl' with hl' | hl'
    · cases hl'; exact hby
    · exact hay l hl'
  omega

/-! ## The third atom: one array grows, the other is kept -/

/-- `x`'s store may grow and every location holding a value may change; every
other store is kept. -/
def growOne (x : Nat) : Footprint := [(.cls .value, .any), (.field x arrayStoreKey, .grow)]

/-- `apart(x, y)`: the regions of `x` and `y` share no location. -/
def ApartAt (x y : Nat) : Assertion := fun ρ _ s => RegionsApart s.h (ρ x) (ρ y)

/-- A store location not `x`'s is kept by an action of `growOne x`. -/
theorem growOne_keeps_store {x : Nat} {ρ : Env} {h h' : Heap} {st : Nat} {ls : List (Option Nat)}
    (hp : Post (growOne x) ρ h h') (hst : h[st]? = some (.arr ls))
    (hne : (fieldsOf (ρ x)).lookup arrayStoreKey ≠ some st) : h'[st]? = some (.arr ls) := by
  obtain ⟨v', hv', ha⟩ := hp.2 st _ hst
  rcases ha with rfl | ⟨e, he, hm, -⟩
  · exact hv'
  · simp only [growOne, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · simp [Region.mem, hst, Cls.has, isArr] at hm
    · simp [Region.mem] at hm; exact absurd hm hne

/-- **(Apart, one-sided)** `apart(x, y) ∧ cells(y) ⊢ □_{growOne x} apart(x, y)`,
for `y` an array object: `x`'s store gains only cells at or past the heap's
end, beyond every cell `y`'s kept store lists and beyond `y`'s store
location. -/
theorem apart_grow_keep {x y : Nat} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hys : (storeOf (ρ y)).isSome = true) (hap : ApartAt x y ρ m s) (hc : RootCells y ρ m s) :
    Box (growOne x) (ApartAt x y) ρ m s := by
  intro s' ha
  obtain ⟨sa, xs, sb, ys, hx, hy, hab⟩ := hap
  have hp := ha.2
  obtain ⟨sty, hsty⟩ := Option.isSome_iff_exists.mp hys
  have hyr : sb = some sty ∧ s.h[sty]? = some (.arr ys) := by
    rcases hy with ⟨rfl, hv⟩ | ⟨st, rfl, hst, hv⟩
    · rw [hv] at hsty; simp [storeOf, fieldsOf] at hsty
    · rw [hsty] at hst; cases hst; exact ⟨rfl, hv⟩
  obtain ⟨rfl, hyv⟩ := hyr
  have hylt : sty < s.h.length := (List.getElem?_eq_some_iff.mp hyv).1
  have hycells := hc sty ys hsty hyv
  -- `x`'s region at `s'`: the old one, or its store grown by cells past the heap's end.
  have xNew : ∃ xs', RegionOf s'.h (ρ x) sa xs' ∧
      ∀ l, InRegion sa xs' l → InRegion sa xs l ∨ s.h.length ≤ l := by
    rcases hx with ⟨rfl, hv⟩ | ⟨st, rfl, hst, hv⟩
    · exact ⟨xs, .inl ⟨rfl, hv⟩, fun l hl => .inl hl⟩
    · obtain ⟨v', hv', hal⟩ := hp.2 st _ hv
      have grown : ∃ xs', v' = .arr xs' ∧ ∀ l, some l ∈ xs' → some l ∈ xs ∨ s.h.length ≤ l := by
        rcases hal with rfl | ⟨e, he, hm, hch⟩
        · exact ⟨xs, rfl, fun l hl => .inl hl⟩
        · simp only [growOne, List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl
          · simp [Region.mem, hv, Cls.has, isArr] at hm
          · simp only [Change.Holds] at hch
            rcases hch with rfl | ⟨ls, ls', he1, he2, -, hnew, -⟩ | hsc
            · exact ⟨xs, rfl, fun l hl => .inl hl⟩
            · cases he1; exact ⟨ls', he2, hnew⟩
            · exact absurd hsc.2.1 (by simp [isArr])
      obtain ⟨xs', rfl, hnew⟩ := grown
      refine ⟨xs', .inr ⟨st, rfl, hst, hv'⟩, fun l hl => ?_⟩
      rcases hl with hl | hl
      · exact .inl (.inl hl)
      · rcases hnew l hl with h1 | h1
        · exact .inl (.inr h1)
        · exact .inr h1
  obtain ⟨xs', hx', hxnew⟩ := xNew
  -- `y`'s store location is not `x`'s, so it is kept.
  have hne : (fieldsOf (ρ x)).lookup arrayStoreKey ≠ some sty := by
    intro he
    have hsa : InRegion sa xs sty := by
      rcases hx with ⟨rfl, hv⟩ | ⟨st, rfl, hst, -⟩
      · rw [hv] at he; simp [fieldsOf] at he
      · have : st = sty := Option.some.inj (hst.symm.trans he)
        exact .inl (by rw [this])
    exact hab sty hsa sty (.inl rfl) rfl
  have hy' : RegionOf s'.h (ρ y) (some sty) ys := .inr ⟨sty, rfl, hsty, growOne_keeps_store hp hyv hne⟩
  refine ⟨sa, xs', some sty, ys, hx', hy', fun l hl l' hl' he => ?_⟩
  subst he
  rcases hxnew l hl with hold | hge
  · exact hab l hold l hl' rfl
  · have : l < s.h.length := by
      rcases hl' with hl' | hl'
      · cases hl'; exact hylt
      · exact hycells l hl'
    omega

end Verification.TolerantFrames
