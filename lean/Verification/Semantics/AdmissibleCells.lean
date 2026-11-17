import Verification.Semantics.IndexedStates

/-! # Tolerant frames: allocated cells and separation

A well-formed heap's spines list only element cells, locations of the heap
(`HeapOk.spine_cells`), so a root's **allocated cells** (`RootCells`: every
cell its spine lists is below the heap's length,
`HeapKnowledge.ElementsBelow`) hold at every state (`rootCells_holds`) and
after every action (`rootCells_box`). Roles and valid references are kept by
every admissible transition, and so is the category of every old location's
contents (`Admissible.contentsCategory`); a typed array's length is its
descriptor's, so what it reads is immutable (`viewLength_invariant`).

With allocated cells, two separations hold: a spine allocated past a mark is
apart from an old spine whose cells lie below it (`alloc_apart`), and two
apart arrays stay apart when one's spine grows and the other's is kept
(`apart_grow_keep`, the third atom). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.HeapKnowledge (ElementsBelow ElementsAbove RegionOf RegionsApart InRegion)

/-- `x`'s spine lists only allocated cells: the review's relevant-root
`ElementsBelow`. -/
def RootCells (x : Nat) : Assertion := fun ρ _ s =>
  ∀ st ls, spineOf (ρ x) = some st → s.h[st]? = some (.arr ls) → ElementsBelow s.h.length ls

/-! ## Structural consequences of a well-formed heap -/

/-- A spine a well-formed heap holds lists locations of the heap, at every
budget. -/
theorem _root_.Verification.HeapOk.elementsBelow {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h)
    {s : Nat} {ls : List (Option Nat)} (hs : h[s]? = some (Tm.arr ls)) : ElementsBelow h.length ls :=
  fun _ hl => (hok.spine_cells hs hl).2

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

/-- **Contents keep their category** (parity-interfaces I1): an old
location's contents after an admissible transition are of the category its
contents had before, an array's spine, a view spine or a value, since its
role is kept and a well-formed heap's contents are of their role's category
(`Shaped.category`). -/
theorem Admissible.contentsCategory {s s' : IndexedHeap} (ha : Admissible s s') {l : Nat} {u u' : Val}
    (hu : s.h[l]? = some u) (hu' : s'.h[l]? = some u') :
    Verification.contentsCategory u' = Verification.contentsCategory u := by
  have hlen : s.h.length = (entries s.W).length := by simpa using s.ok.1.1
  have hl : l < (entries s.W).length := by have := (List.getElem?_eq_some_iff.mp hu).1; omega
  obtain ⟨r, hr⟩ := roleAt_some hl
  rw [s'.ok.2.category (ha.roleAt hr) hu', s.ok.2.category hr hu]

/-- **Class regions transport across an admissible transition**: an old
location is in the class region of a selector after it exactly when it was
before, whatever the transition changed, `any` included: its contents keep
their category (`Admissible.contentsCategory`). -/
theorem Admissible.cls_mem {s s' : IndexedHeap} (ha : Admissible s s') {l : Nat} (hl : l < s.h.length)
    (ρ : Env) (c : Footprints.Selector) :
    (Footprints.Region.cls c).mem ρ s'.h l = (Footprints.Region.cls c).mem ρ s.h l := by
  obtain ⟨u, hu⟩ : ∃ u, s.h[l]? = some u := ⟨_, List.getElem?_eq_getElem hl⟩
  have hl' : l < s'.h.length := Nat.lt_of_lt_of_le hl ha.length_le
  obtain ⟨u', hu'⟩ : ∃ u, s'.h[l]? = some u := ⟨_, List.getElem?_eq_getElem hl'⟩
  simp only [Footprints.Region.mem, hu, hu', Footprints.Selector.selects, ha.contentsCategory hu hu']

/-- A listed cell stays an element cell after every admissible transition. -/
theorem Admissible.elem_kept {s s' : IndexedHeap} (ha : Admissible s s') {st : Nat}
    {ls : List (Option Nat)} (hs : s.h[st]? = some (.arr ls)) {l : Nat} (hl : some l ∈ ls) :
    Verification.roleAt s'.W l = some .elem := ha.roleAt (s.ok.spine_cells hs hl).1

/-- **Admissibility keeps the roots valid.** -/
theorem _root_.Verification.RootsOk.admissible {s s' : IndexedHeap} (ha : Admissible s s') {ρ : Env}
    (h : RootsOk s.W ρ) : RootsOk s'.W ρ := fun x => ha.refsOk (h x)

/-! ## (View): a typed array's length is immutable -/

/-- **(View)**: a typed array's length is its descriptor's, part of the
value, so what a root's typed-array length reads is invariant. -/
theorem viewLength_invariant (w : Nat) (n : Option Int) :
    Invariant (fun ρ _ _ => HeapKnowledge.viewLengthOf (ρ w) = n) := fun _ _ _ _ _ h => h

/-! ## Allocated cells hold at every state -/

/-- **Every state's roots list allocated cells**: a spine the heap holds has
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

/-- **Two spines on either side of a mark are apart**: `x`'s spine
location and cells at or past `b`, `y`'s spine location and cells below
`b`, both bounds stated. `alloc_apart` derives the second from a
well-formed heap. -/
theorem apart_of_mark {h : Heap} {u w : Val} {sx sy b : Nat} {xs ys : List (Option Nat)}
    (hx : spineOf u = some sx) (hxv : h[sx]? = some (.arr xs)) (hbx : b ≤ sx) (hax : ElementsAbove b xs)
    (hy : spineOf w = some sy) (hyv : h[sy]? = some (.arr ys)) (hby : sy < b) (hay : ElementsBelow b ys) :
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

/-- **A spine allocated past a well-formed heap is apart from an old one**:
`h` is the entry heap, meeting a world at any budget, `h'` a later heap;
`u`'s spine location and its cells are at or past `h`'s end, `w`'s spine is a
spine of `h` that `h'` keeps, whose cells are below `h`'s end because `h` is
well-formed. -/
theorem alloc_apart {n : Nat} {W : WorldT n} {h h' : Heap} (hok : HeapOk n W h) {u w : Val}
    {sx sy : Nat} {xs ys : List (Option Nat)}
    (hx : spineOf u = some sx) (hxv : h'[sx]? = some (.arr xs)) (hbx : h.length ≤ sx)
    (hax : ElementsAbove h.length xs)
    (hy : spineOf w = some sy) (hyv : h[sy]? = some (.arr ys)) (hkeep : h'[sy]? = some (.arr ys)) :
    RegionsApart h' u w :=
  apart_of_mark hx hxv hbx hax hy hkeep (List.getElem?_eq_some_iff.mp hyv).1 (hok.elementsBelow hyv)

/-! ## The third atom: one array grows, the other is kept -/

/-- `x`'s spine may grow and every location holding a value may change; every
other spine is kept. -/
def growOne (x : Nat) : Footprint := [(.cls .values, .any), (.field x arraySpineKey, .grow)]

/-- `apart(x, y)`: the regions of `x` and `y` share no location. -/
def ApartAt (x y : Nat) : Assertion := fun ρ _ s => RegionsApart s.h (ρ x) (ρ y)

end Verification.TolerantFrames
