import Verification.Semantics.RegionBounds
import Verification.Semantics.AdmissibleCells

/-! # Heap-based logical value validity

Logical witnesses do not consult a world. Identity references must be allocated;
slots and elements have the shapes their readings require, and a view descriptor
selects a view spine of its format and length. Null contents do not establish an
identity role. World-role validity implies this domain; its converse is not
claimed. Program environments and command exits retain `RefsOk` separately.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames

/-- The heap-only, role-erased requirements on a logical reference. -/
def HeapRefOk (h : Heap) : Ref → Prop
  | .ident l => l < h.length
  | .slot k l => if k = arraySpineKey then ∃ es, h[l]? = some (.arr es)
      else ∃ u, h[l]? = some u ∧ isSourceVal u = true
  | .elem l => ∃ u, h[l]? = some u ∧ isSourceVal u = true
  | .view l f n plain => plain = true ∧ ∃ cs, h[l]? = some (.viewSpine f cs) ∧ cs.length = n

/-- Heap validity includes every syntactic reference, including captures. -/
def HeapRefs (h : Heap) (v : Val) : Prop := ∀ r ∈ refs v, HeapRefOk h r

def refLocation : Ref → Nat
  | .ident l | .slot _ l | .elem l | .view l _ _ _ => l

theorem HeapRefOk.allocated {h r} (hr : HeapRefOk h r) : refLocation r < h.length := by
  cases r with
  | ident l => exact hr
  | slot k l =>
    simp only [HeapRefOk] at hr
    split at hr
    · obtain ⟨es, he⟩ := hr; exact (List.getElem?_eq_some_iff.mp he).1
    · obtain ⟨u, he, _⟩ := hr; exact (List.getElem?_eq_some_iff.mp he).1
  | elem l => obtain ⟨u, he, _⟩ := hr; exact (List.getElem?_eq_some_iff.mp he).1
  | view l f n p => obtain ⟨_, cs, he, _⟩ := hr; exact (List.getElem?_eq_some_iff.mp he).1

theorem role_allocated {s : IndexedHeap} {l r} (hr : roleAt s.W l = some r) : l < s.h.length := by
  have hh : s.h.length = (entries s.W).length := by simpa using s.ok.1.1
  rw [hh]; exact roleAt_lt hr

theorem heapRefOk_of_world {s : IndexedHeap} {r : Ref} (hr : RefOk s.W r) : HeapRefOk s.h r := by
  cases r with
  | ident l => exact role_allocated hr
  | elem l =>
    obtain ⟨u, hu, hc, _⟩ := s.ok.2 l .elem hr
    exact ⟨u, hu, hc⟩
  | view l f n plain =>
    obtain ⟨u, hu, ⟨cs, rfl, hn⟩, _⟩ := s.ok.2 l _ hr.2
    exact ⟨hr.1, cs, hu, hn⟩
  | slot k l =>
    simp only [RefOk] at hr
    cases he : roleAt s.W l with
    | none => simp [he, SlotRole] at hr
    | some r =>
      obtain ⟨u, hu, hc, _⟩ := s.ok.2 l r he
      rw [he] at hr
      cases r with
      | field | cell =>
        have hk : k ≠ arraySpineKey := hr
        simpa [HeapRefOk, hk] using (show ∃ u, s.h[l]? = some u ∧ isSourceVal u = true from ⟨u, hu, hc⟩)
      | spine f =>
        cases f with
        | array =>
          have hk : k = arraySpineKey := hr
          obtain ⟨es, rfl⟩ := hc
          simpa [HeapRefOk, hk] using (Exists.intro es hu)
        | view => simp [SlotRole] at hr
      | _ => simp [SlotRole] at hr

theorem HeapRefs.of_world {s : IndexedHeap} {v : Val} (hv : RefsOk s.W v) : HeapRefs s.h v :=
  fun r hr => heapRefOk_of_world (hv r hr)

theorem HeapRefs.of_nil {h : Heap} {v : Val} (hv : refs v = []) : HeapRefs h v := by
  intro r hr; rw [hv] at hr; cases hr

/-- A slot descriptor supplies its location bound without a role inference. -/
theorem HeapRefs.slot {h : Heap} {fs c i k l} (hv : HeapRefs h (.objAt fs c i))
    (hl : fs.lookup k = some l) : l < h.length :=
  HeapRefOk.allocated (hv _ (slot_mem_refs (lookup_mem_pair hl)))

/-- A successful read preserves heap validity; nonempty paths obtain their
references from actual heap contents and W3, rather than from the logical root. -/
theorem readPath_heapRefs {s : IndexedHeap} : ∀ {v u : Val} (p : List String),
    HeapRefs s.h v → readPath s.h v p = some u → HeapRefs s.h u
  | v, u, [], hv, he => by cases he; exact hv
  | v, u, f :: p, hv, he => by
    cases v with
    | objAt fs c i =>
      simp only [readPath] at he
      split at he
      · split at he
        · rename_i w hw
          exact readPath_heapRefs p (HeapRefs.of_world (s.ok.refs_at hw)) he
        · cases he
      · cases he
    | _ => cases he

private theorem source_admissible {s t : IndexedHeap} (ha : Admissible s t) {l : Nat} {u : Val}
    (hu : s.h[l]? = some u) (hs : isSourceVal u = true) :
    ∃ v, t.h[l]? = some v ∧ isSourceVal v = true := by
  obtain ⟨r, hr⟩ := roleAt_some (W := s.W) (l := l) (by
    have := (List.getElem?_eq_some_iff.mp hu).1
    have hh : s.h.length = (entries s.W).length := by simpa using s.ok.1.1
    omega)
  obtain ⟨v, hv, hc, _⟩ := t.ok.2 l r (ha.roleAt hr)
  obtain ⟨u', hu', hc', _⟩ := s.ok.2 l r hr
  rw [hu] at hu'; cases hu'
  refine ⟨v, hv, ?_⟩
  cases r with
  | field | cell | elem => exact hc
  | identity => cases hc; rfl
  | spine f =>
    cases f with
    | array => obtain ⟨es, rfl⟩ := hc'; cases hs
    | view => obtain ⟨cs, rfl, _⟩ := hc'; cases hs

private theorem array_admissible {s t : IndexedHeap} (ha : Admissible s t) {l : Nat} {es : List (Option Nat)}
    (hu : s.h[l]? = some (.arr es)) : ∃ es', t.h[l]? = some (.arr es') := by
  have hl : l < s.h.length := (List.getElem?_eq_some_iff.mp hu).1
  obtain ⟨r, hr⟩ := roleAt_some (W := s.W) (l := l) (by
    have hh : s.h.length = (entries s.W).length := by simpa using s.ok.1.1
    omega)
  have hc := s.ok.2.category hr hu
  have hr' : r = .spine .array := by
    cases r <;> simp_all [contentsCategory, Role.category]
    rename_i f; cases f <;> simp_all
  subst r
  obtain ⟨u, hv, ⟨es', rfl⟩, _⟩ := t.ok.2 l _ (ha.roleAt hr)
  exact ⟨es', hv⟩

private theorem view_admissible {s t : IndexedHeap} (ha : Admissible s t) {l : Nat} {f : ViewFormat} {cs : List Nat}
    (hu : s.h[l]? = some (.viewSpine f cs)) :
    ∃ cs', t.h[l]? = some (.viewSpine f cs') ∧ cs'.length = cs.length := by
  have hl : l < s.h.length := (List.getElem?_eq_some_iff.mp hu).1
  obtain ⟨r, hr⟩ := roleAt_some (W := s.W) (l := l) (by
    have hh : s.h.length = (entries s.W).length := by simpa using s.ok.1.1
    omega)
  obtain ⟨u, hv, hc, _⟩ := s.ok.2 l r hr
  rw [hu] at hv; cases hv
  have hr' : r = .spine (.view f cs.length) := by
    cases r with
    | spine sf => cases sf with
      | array => obtain ⟨es, he⟩ := hc; cases he
      | view f' n => obtain ⟨cs', he, hn⟩ := hc; cases he; simp_all
    | _ => cases hc
  subst r
  obtain ⟨u, hv, ⟨cs', rfl, hn⟩, _⟩ := t.ok.2 l _ (ha.roleAt hr)
  exact ⟨cs', hv, hn⟩

theorem HeapRefOk.admissible {s t : IndexedHeap} (ha : Admissible s t) {r}
    (hr : HeapRefOk s.h r) : HeapRefOk t.h r := by
  cases r with
  | ident l => exact Nat.lt_of_lt_of_le hr ha.length_le
  | elem l => obtain ⟨u, hu, hs⟩ := hr; exact source_admissible ha hu hs
  | slot k l =>
    simp only [HeapRefOk] at hr ⊢
    by_cases hk : k = arraySpineKey
    · simp only [if_pos hk] at hr ⊢
      obtain ⟨es, he⟩ := hr; exact array_admissible ha he
    · simp only [if_neg hk] at hr ⊢
      obtain ⟨u, hu, hs⟩ := hr; exact source_admissible ha hu hs
  | view l f n p =>
    obtain ⟨hp, cs, he, hn⟩ := hr
    obtain ⟨cs', he', hn'⟩ := view_admissible ha he
    exact ⟨hp, cs', he', hn'.trans hn⟩

theorem HeapRefs.admissible {s t : IndexedHeap} (ha : Admissible s t) {v}
    (hv : HeapRefs s.h v) : HeapRefs t.h v := fun r hr => HeapRefOk.admissible ha (hv r hr)

/-- Logical environments allow heap-valid witnesses without program role typing.
Command `ValidContext` remains a separate, stronger notion. -/
def HeapContext (ρ : Env) (m : Nat) (s : IndexedHeap) : Prop :=
  (∀ x, HeapRefs s.h (ρ x)) ∧ (∀ x, isSourceVal (ρ x) = true) ∧ m ≤ s.h.length

theorem HeapContext.admissible {ρ m s t} (hv : HeapContext ρ m s) (ha : Admissible s t) :
    HeapContext ρ m t := ⟨fun x => HeapRefs.admissible ha (hv.1 x), hv.2.1, Nat.le_trans hv.2.2 ha.length_le⟩

theorem HeapContext.push {ρ m s} (hv : HeapContext ρ m s) {v}
    (hs : isSourceVal v = true) (hr : HeapRefs s.h v) : HeapContext (push v ρ) m s := by
  refine ⟨?_, ?_, hv.2.2⟩
  · intro x; cases x with | zero => exact hr | succ x => exact hv.1 x
  · intro x; cases x with | zero => exact hs | succ x => exact hv.2.1 x

end Verification.Paper.TolerantFrames
