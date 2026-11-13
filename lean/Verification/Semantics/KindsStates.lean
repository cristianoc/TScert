import Verification.Semantics.KindsWrites
import Verification.Semantics.TolerantFramesCells
/-!
# Well-formed states over an environment, in the kinded world

A **state** is a budget, a kinded world at that budget and a heap meeting it
(`Kinds.HeapOk`: the world's contracts below the budget, and each location's
role's shape at every budget). A **state over an environment** `ρ` is a state
whose world gives every reference of every value of `ρ` the role its position
demands (`RootsOk`). An **admissible transition** drops the budget and
extends the truncated world; it keeps every role, every valid reference and
every view-length metadata location, so the state it reaches is a state over
the same environment (`State.next`), and over an environment extended by a
value valid there (`RootsOk.set`).

Three statements of the note *Tolerant frames* hold of these states with no
premise beyond the state:

- **(View)**: the typed-array length a value of valid references reads
  (`HeapKnowledge.viewLengthOf`) is the same after every admissible
  transition (`viewLengthOf_kept`, `viewLength_invariant`);
- **allocated cells**: every cell a store of the heap lists is an element
  cell of the world and a location of the heap, at every budget, zero
  included (`HeapOk.store_cells`), so at every state (`storeCells`,
  `rootCells`) and after every action (`rootCells_box`);
- **allocation separation**: a store allocated past a well-formed heap is
  apart from every store of that heap the later heap keeps (`alloc_apart`).
-/
namespace Verification.Kinds
open Verification Footprints
open Verification.HeapKnowledge (ElementsBelow ElementsAbove RegionsApart viewLengthOf)

/-! ## Structural consequences of heap satisfaction, at every budget -/

theorem HeapOk.elementsBelow {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) {s : Nat}
    {ls : List (Option Nat)} (hs : h[s]? = some (Tm.arr ls)) : ElementsBelow h.length ls :=
  fun _ hl => (hok.store_cells hs hl).2

/-- The dangling store is excluded at budget zero, where the heap meets no
contract: the exclusion is structural. -/
example (W : WorldT 0) : ¬ HeapOk 0 W [.arr [some 5], .nul, .nul] := dangling_excluded W

/-- A valid object's `[[viewLength]]` location is a view-length metadata
location. -/
theorem RefsOk.lengthMeta {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {c : CallCode}
    {o m : Nat} (h : RefsOk W (.objAt fs c o)) (hm : fs.lookup viewLengthKey = some m) :
    ∃ N, LengthMeta W m N := by
  have hf : RefOk W (.fields fs) := h _ (by
    rw [refs_objAt]; exact List.mem_append_left _ (by simp [objRefs]))
  exact hf.1 m (lookup_mem hm)

/-- At positive budget a view-length metadata location holds its length. -/
theorem HeapOk.lengthMeta_value {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h)
    (hn : 0 < n) {m N : Nat} (hm : LengthMeta W m N) : h[m]? = some (.num (bitsOfNat N)) :=
  let ⟨_, _, hl, hs⟩ := hm; hok.stable_value hn hl hs

/-! ## States and admissible transitions -/

/-- A state: budget `n`, positive, a kinded world at `n` whose contracts
survive allocation, and a heap meeting the world in both parts. -/
structure IndexedHeap where
  n : Nat
  W : WorldT n
  h : Heap
  pos : 0 < n
  adm : WorldAdm W
  ok : HeapOk n W h

/-- `s'` is reachable from `s` by what safe code may do: its budget is at
most `s`'s, and its world extends `s`'s world truncated to its budget. -/
def Admissible (s s' : IndexedHeap) : Prop :=
  ∃ hle : s'.n ≤ s.n, WExt (trunc s'.n hle s.W) s'.W

namespace Admissible

theorem refl (s : IndexedHeap) : Admissible s s :=
  ⟨Nat.le_refl _, by rw [trunc_id]; exact WExt_refl _⟩

theorem trans {s₁ s₂ s₃ : IndexedHeap} (h₁ : Admissible s₁ s₂) (h₂ : Admissible s₂ s₃) :
    Admissible s₁ s₃ := by
  obtain ⟨hle₁, hx₁⟩ := h₁
  obtain ⟨hle₂, hx₂⟩ := h₂
  refine ⟨Nat.le_trans hle₂ hle₁, ?_⟩
  simpa only [trunc_trunc] using WExt_trans (WExt_trunc hle₂ hx₁) hx₂

/-- The heap grows. -/
theorem length_le {s s' : IndexedHeap} (ha : Admissible s s') : s.h.length ≤ s'.h.length := by
  obtain ⟨hle, tail, ht⟩ := ha
  have h1 : s.h.length = (entries s.W).length := by simpa using s.ok.1.1
  have h2 : s'.h.length = (entries s'.W).length := by simpa using s'.ok.1.1
  rw [h1, h2, ht]
  simp

/-- **Roles are fixed**: every location keeps its role. -/
theorem roleAt {s s' : IndexedHeap} (ha : Admissible s s') {l : Nat} {r : Role}
    (hl : roleAt s.W l = some r) : Kinds.roleAt s'.W l = some r := by
  obtain ⟨hle, hx⟩ := ha
  exact WExt_roleAt hx (by simpa using hl)

/-- **Valid references stay valid**, by truncation and extension. -/
theorem refsOk {s s' : IndexedHeap} (ha : Admissible s s') {t : Tm} (ht : RefsOk s.W t) :
    RefsOk s'.W t := by
  obtain ⟨hle, hx⟩ := ha
  exact RefsOk_mono hx (RefsOk_trunc hle ht)

/-- A view-length metadata location stays one, of the same length. -/
theorem lengthMeta {s s' : IndexedHeap} (ha : Admissible s s') {m N : Nat}
    (hm : LengthMeta s.W m N) : LengthMeta s'.W m N := by
  obtain ⟨hle, hx⟩ := ha
  exact (hm.trunc hle).mono hx

/-- A location whose contract admits one value holds it after every
admissible transition. -/
theorem stable_value {s s' : IndexedHeap} (ha : Admissible s s') {l : Nat} {c : Ctr s.n} {v : Val}
    (hl : lookup s.W l = some c) (hc : CtrStable c v) : s'.h[l]? = some v := by
  obtain ⟨hle, hx⟩ := ha
  exact s'.ok.stable_value s'.pos (WExt_lookup hx (lookup_trunc hle s.W l c hl)) (hc.restrict hle)

end Admissible

/-! ## The environment inside the well-formed state -/

/-- **Structural validity of an environment's roots**: every reference of
every value the environment holds has the role its position demands. -/
def RootsOk {k : Nat} (W : WorldT k) (ρ : Env) : Prop := ∀ x, RefsOk W (ρ x)

/-- **Admissibility keeps the roots valid**: old roots by truncation and
extension. -/
theorem RootsOk.admissible {s s' : IndexedHeap} (ha : Admissible s s') {ρ : Env}
    (h : RootsOk s.W ρ) : RootsOk s'.W ρ := fun x => ha.refsOk (h x)

/-- Extending the environment by a value valid in the world keeps every
existing binding valid. -/
theorem RootsOk.set {k : Nat} {W : WorldT k} {ρ : Env} (h : RootsOk W ρ) (y : Nat) {v : Tm}
    (hv : RefsOk W v) : RootsOk W (fun x => if x = y then v else ρ x) := fun x => by
  by_cases hx : x = y
  · simpa [hx] using hv
  · simpa [hx] using h x

/-- **A well-formed state over the environment `ρ`**: a state whose world
validates `ρ`'s roots. -/
structure State (ρ : Env) extends IndexedHeap where
  roots : RootsOk W ρ

/-- **Admissibility keeps well-formedness**: the state an admissible
transition reaches is a state over the same environment. -/
def State.next {ρ : Env} (s : State ρ) (s' : IndexedHeap) (ha : Admissible s.toIndexedHeap s') :
    State ρ :=
  ⟨s', RootsOk.admissible ha s.roots⟩

@[simp] theorem State.next_h {ρ : Env} (s : State ρ) (s' : IndexedHeap)
    (ha : Admissible s.toIndexedHeap s') : (s.next s' ha).h = s'.h := rfl

/-- An assertion, read at a name valuation, an entry mark and a state over
that valuation. -/
abbrev Assertion := (ρ : Env) → Nat → State ρ → Prop

/-- An action of the footprint `Φ` at `ρ`: an admissible transition whose
heaps meet `Φ`'s postcondition. -/
def Action (Φ : Footprint) (ρ : Env) (s s' : IndexedHeap) : Prop :=
  Admissible s s' ∧ Post Φ ρ s.h s'.h

/-- `Box Φ F`: `F` holds after every action of `Φ`. -/
def Box (Φ : Footprint) (F : Assertion) : Assertion :=
  fun ρ m s => ∀ s' (ha : Action Φ ρ s.toIndexedHeap s'), F ρ m (s.next s' ha.1)

/-- An assertion is invariant when every admissible transition keeps it. -/
def Invariant (g : Assertion) : Prop :=
  ∀ ρ m (s : State ρ) s' (ha : Admissible s.toIndexedHeap s'), g ρ m s → g ρ m (s.next s' ha)

/-- An invariant assertion holds after every action of every footprint. -/
theorem Invariant.box {g : Assertion} (hg : Invariant g) {Φ : Footprint} {ρ : Env} {m : Nat}
    {s : State ρ} (h : g ρ m s) : Box Φ g ρ m s := fun s' ha => hg ρ m s s' ha.1 h

/-! ## (View): a typed array's length is immutable -/

/-- **The typed-array length a value of valid references reads is kept by
every admissible transition.** The value is any: an object owning
`[[viewLength]]` reads a view-length metadata location, whose contract admits
one value, and every other value reads none. -/
theorem viewLengthOf_kept {s s' : IndexedHeap} {v : Val} (hv : RefsOk s.W v) (ha : Admissible s s') :
    viewLengthOf s'.h v = viewLengthOf s.h v := by
  cases v
  case objAt fs cd o =>
    cases hl : fs.lookup viewLengthKey with
    | none => simp [viewLengthOf, hl]
    | some m =>
      obtain ⟨N, hN⟩ := hv.lengthMeta hl
      simp [viewLengthOf, hl, s.ok.lengthMeta_value s.pos hN,
        s'.ok.lengthMeta_value s'.pos (ha.lengthMeta hN)]
  all_goals rfl

/-- **(View)**: what a root's typed-array length reads is invariant. -/
theorem viewLength_invariant (w : Nat) (n : Option Int) :
    Invariant (fun ρ _ s => viewLengthOf s.h (ρ w) = n) := by
  intro ρ m s s' ha h
  simpa [viewLengthOf_kept (s.roots w) ha] using h

/-! ## Allocated cells -/

/-- Every store of the heap lists element cells of the world, locations of
the heap. -/
def StoreCells : Assertion := fun _ _ s =>
  ∀ (st : Nat) (ls : List (Option Nat)), s.h[st]? = some (Tm.arr ls) → ∀ l, some l ∈ ls →
    roleAt s.W l = some .elem ∧ l < s.h.length

/-- **Every state has allocated cells.** -/
theorem storeCells (ρ : Env) (m : Nat) (s : State ρ) : StoreCells ρ m s :=
  fun _ _ hs _ hl => s.ok.store_cells hs hl

/-- **Admissibility keeps allocated cells**: the state reached is a state. -/
theorem storeCells_invariant : Invariant StoreCells :=
  fun ρ m s s' ha _ => storeCells ρ m (s.next s' ha)

/-- A listed cell stays an element cell after every admissible transition. -/
theorem Admissible.elem_kept {s s' : IndexedHeap} (ha : Admissible s s') {st : Nat}
    {ls : List (Option Nat)} (hs : s.h[st]? = some (.arr ls)) {l : Nat} (hl : some l ∈ ls) :
    Kinds.roleAt s'.W l = some .elem := ha.roleAt (s.ok.store_cells hs hl).1

/-- `x`'s store lists only allocated cells: `RootCells` of
`Semantics/TolerantFramesCells.lean`. -/
def RootCells (x : Nat) : Assertion := fun ρ _ s =>
  ∀ (st : Nat) (ls : List (Option Nat)), storeOf (ρ x) = some st → s.h[st]? = some (Tm.arr ls) →
    ElementsBelow s.h.length ls

/-- **A root's cells are allocated at every state.** -/
theorem rootCells (x : Nat) (ρ : Env) (m : Nat) (s : State ρ) : RootCells x ρ m s :=
  fun _ _ _ hv => s.ok.elementsBelow hv

theorem rootCells_invariant (x : Nat) : Invariant (RootCells x) :=
  fun ρ m s s' ha _ => rootCells x ρ m (s.next s' ha)

/-- **Allocated cells hold after every action.** -/
theorem rootCells_box {Φ : Footprint} (x : Nat) (ρ : Env) (m : Nat) (s : State ρ) :
    Box Φ (RootCells x) ρ m s := (rootCells_invariant x).box (rootCells x ρ m s)

/-! ## Allocation separation -/

/-- **A store allocated past a well-formed heap is apart from an old one.**
`h` is the entry heap, meeting a world at any budget; `h'` a later heap.
`u`'s store location and its cells are at or past `h`'s end, `w`'s store is a
store of `h` that `h'` keeps. The old store's cells are below `h`'s end
because `h` is well-formed. -/
theorem alloc_apart {n : Nat} {W : WorldT n} {h h' : Heap} (hok : HeapOk n W h) {u w : Val}
    {sx sy : Nat} {xs ys : List (Option Nat)}
    (hx : storeOf u = some sx) (hxv : h'[sx]? = some (.arr xs)) (hbx : h.length ≤ sx)
    (hax : ElementsAbove h.length xs)
    (hy : storeOf w = some sy) (hyv : h[sy]? = some (.arr ys)) (hkeep : h'[sy]? = some (.arr ys)) :
    RegionsApart h' u w :=
  TolerantFrames.alloc_apart hx hxv hbx hax hy hkeep (List.getElem?_eq_some_iff.mp hyv).1
    (hok.elementsBelow hyv)

end Verification.Kinds
