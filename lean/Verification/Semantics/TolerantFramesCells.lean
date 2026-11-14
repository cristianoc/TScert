import Verification.Semantics.TolerantFrames

/-! # Tolerant frames: allocated cells and separation

A well-formed heap's stores list only element cells, locations of the heap
(`HeapOk.store_cells`), so a root's **allocated cells** (`RootCells`: every
cell its store lists is below the heap's length,
`HeapKnowledge.ElementsBelow`) hold at every state (`rootCells_holds`) and
after every action (`rootCells_box`). Roles, valid references and view-length
metadata are kept by every admissible transition, so a typed array's length
read through valid references is immutable (`viewLengthOf_kept`).

With allocated cells, two separations hold: a store allocated past a mark is
apart from an old store whose cells lie below it (`alloc_apart`), and two
apart arrays stay apart when one's store grows and the other's is kept
(`apart_grow_keep`, the third atom). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.HeapKnowledge (ElementsBelow ElementsAbove RegionOf RegionsApart InRegion)

/-- `x`'s store lists only allocated cells: the review's relevant-root
`ElementsBelow`. -/
def RootCells (x : Nat) : Assertion := fun ρ _ s =>
  ∀ st ls, storeOf (ρ x) = some st → s.h[st]? = some (.arr ls) → ElementsBelow s.h.length ls

/-! ## Structural consequences of a well-formed heap -/

/-- A store a well-formed heap holds lists locations of the heap, at every
budget. -/
theorem _root_.Verification.HeapOk.elementsBelow {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h)
    {s : Nat} {ls : List (Option Nat)} (hs : h[s]? = some (Tm.arr ls)) : ElementsBelow h.length ls :=
  fun _ hl => (hok.store_cells hs hl).2

/-- A valid object's `[[viewLength]]` location is a view-length metadata
location. -/
theorem _root_.Verification.RefsOk.lengthMeta {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)}
    {c : CallCode} {o m : Nat} (h : RefsOk W (.objAt fs c o)) (hm : fs.lookup viewLengthKey = some m) :
    ∃ N, LengthMeta W m N := by
  have hf : RefOk W (.fields fs) := h _ (by
    rw [Kinds.refs_objAt]; exact List.mem_append_left _ (by simp [objRefs]))
  exact hf.1 m (Kinds.lookup_mem hm)

/-- At positive budget a view-length metadata location holds its length. -/
theorem _root_.Verification.HeapOk.lengthMeta_value {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h)
    (hn : 0 < n) {m N : Nat} (hm : LengthMeta W m N) : h[m]? = some (.num (bitsOfNat N)) :=
  let ⟨_, _, hl, hs⟩ := hm; hok.stable_value hn hl hs

/-- **Roles are fixed**: every location keeps its role along an admissible
transition. -/
theorem Admissible.roleAt {s s' : IndexedHeap} (ha : Admissible s s') {l : Nat} {r : Role}
    (hl : Verification.roleAt s.W l = some r) : Verification.roleAt s'.W l = some r := by
  obtain ⟨hle, hx⟩ := ha
  exact WExt_roleAt hx (by simpa using hl)

/-- **Valid references stay valid**, by truncation and extension. -/
theorem Admissible.refsOk {s s' : IndexedHeap} (ha : Admissible s s') {t : Tm} (ht : RefsOk s.W t) :
    RefsOk s'.W t := by
  obtain ⟨hle, hx⟩ := ha
  exact RefsOk_mono hx (RefsOk_trunc hle ht)

/-- A view-length metadata location stays one, of the same length. -/
theorem Admissible.lengthMeta {s s' : IndexedHeap} (ha : Admissible s s') {m N : Nat}
    (hm : LengthMeta s.W m N) : LengthMeta s'.W m N := by
  obtain ⟨hle, hx⟩ := ha
  exact (hm.trunc hle).mono hx

/-- A listed cell stays an element cell after every admissible transition. -/
theorem Admissible.elem_kept {s s' : IndexedHeap} (ha : Admissible s s') {st : Nat}
    {ls : List (Option Nat)} (hs : s.h[st]? = some (.arr ls)) {l : Nat} (hl : some l ∈ ls) :
    Verification.roleAt s'.W l = some .elem := ha.roleAt (s.ok.store_cells hs hl).1

/-- **An environment's roots are valid**: every reference of every value it
holds has the role its position demands. A graph state's environment is
(`ControlFlow.StateRefs`). -/
def RootsOk {k : Nat} (W : WorldT k) (ρ : Env) : Prop := ∀ x, RefsOk W (ρ x)

/-- **Admissibility keeps the roots valid.** -/
theorem RootsOk.admissible {s s' : IndexedHeap} (ha : Admissible s s') {ρ : Env}
    (h : RootsOk s.W ρ) : RootsOk s'.W ρ := fun x => ha.refsOk (h x)

/-! ## (View): a typed array's length is immutable -/

/-- **The typed-array length a value of valid references reads is kept by
every admissible transition.** An object owning `[[viewLength]]` reads a
view-length metadata location, whose contract admits one value; every other
value reads none. -/
theorem viewLengthOf_kept {s s' : IndexedHeap} {v : Val} (hv : RefsOk s.W v) (ha : Admissible s s') :
    HeapKnowledge.viewLengthOf s'.h v = HeapKnowledge.viewLengthOf s.h v := by
  cases v
  case objAt fs cd o =>
    cases hl : fs.lookup viewLengthKey with
    | none => simp [HeapKnowledge.viewLengthOf, hl]
    | some m =>
      obtain ⟨N, hN⟩ := hv.lengthMeta hl
      simp [HeapKnowledge.viewLengthOf, hl, s.ok.lengthMeta_value s.pos hN,
        s'.ok.lengthMeta_value s'.pos (ha.lengthMeta hN)]
  all_goals rfl

/-- **(View)**: what a valid root's typed-array length reads is invariant. -/
theorem viewLength_invariant (w : Nat) (n : Option Int) :
    Invariant (fun ρ _ s => RefsOk s.W (ρ w) ∧ HeapKnowledge.viewLengthOf s.h (ρ w) = n) := by
  intro ρ m s s' ha ⟨hr, h⟩
  exact ⟨ha.refsOk hr, by rw [viewLengthOf_kept hr ha]; exact h⟩

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

/-- **Allocated cells hold after every action.** -/
theorem rootCells_box {Φ : Footprint} (x : Nat) (ρ : Env) (m : Nat) (s : IndexedHeap) :
    Box Φ (RootCells x) ρ m s := fun s' _ => rootCells_holds x ρ m s'

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

/-- **A store allocated past a well-formed heap is apart from an old one**:
`h` is the entry heap, meeting a world at any budget, `h'` a later heap;
`u`'s store location and its cells are at or past `h`'s end, `w`'s store is a
store of `h` that `h'` keeps, whose cells are below `h`'s end because `h` is
well-formed. -/
theorem alloc_apart_wellformed {n : Nat} {W : WorldT n} {h h' : Heap} (hok : HeapOk n W h) {u w : Val}
    {sx sy : Nat} {xs ys : List (Option Nat)}
    (hx : storeOf u = some sx) (hxv : h'[sx]? = some (.arr xs)) (hbx : h.length ≤ sx)
    (hax : ElementsAbove h.length xs)
    (hy : storeOf w = some sy) (hyv : h[sy]? = some (.arr ys)) (hkeep : h'[sy]? = some (.arr ys)) :
    RegionsApart h' u w :=
  alloc_apart hx hxv hbx hax hy hkeep (List.getElem?_eq_some_iff.mp hyv).1 (hok.elementsBelow hyv)

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
