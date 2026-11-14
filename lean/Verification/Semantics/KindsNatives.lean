import Verification.Semantics.KindsWrites
import Verification.Semantics.FootprintNatives
import Verification.Semantics.CallEffects
/-!
# Natives, copies and administrative steps preserve kinds

The array natives are modelled as steps on a store's list of element
locations (`Footprints.Arr`); each keeps the store's cells among the original
ones and fresh ones (`Arr.Within`), and a native's element-storage phase
preserves kinds when its world extension makes the fresh cells element cells
and the contents it writes are source values (`native_shaped`); a whole
native, callbacks included, has the obligation of every call contract
(`CallEffects.NativeContract`). A copy (`Tm.merge`) reads only values the heap holds; the
administrative steps (substitution, a run's entry, its environment maps, its
handlers, reads, comparisons) refer to no location the term or the heap did
not. A contract stated as a relation between heaps can meet that obligation
only if every transition it admits from a structurally well-formed heap
reaches one (`RespectsKinds`); the typed-array element write's coarse change
admits one that does not (`elementWrite_not_respects`), and the call
contracts state beside it the kinded view write (`ViewWrite`,
`CallEffects.Effect.viewPost`), from the call's entry world.
-/
namespace Verification.Kinds

/-! ## Array natives -/

section natives
open Footprints

/-- A native's store lists element cells where the original store does and
the native's world extension makes every fresh cell it lists one. -/
theorem Arr.Within.refs {k : Nat} {W : WorldT k} {b : Nat} {orig : List (Option Nat)} {a : Arr}
    (hw : a.Within b orig) (ho : RefsOk W (.arr orig))
    (hfresh : ∀ l, b ≤ l → some l ∈ a.ls → roleAt W l = some .elem) : RefsOk W (.arr a.ls) :=
  RefsOk_arr_iff.mpr fun l hl => (hw.2 l hl).elim (RefsOk_arr_iff.mp ho l) (fun hb => hfresh l hb hl)

private theorem foldl_within' {b orig} {f : Arr → Nat → Arr}
    (hf : ∀ a k, a.Within b orig → (f a k).Within b orig) :
    ∀ (xs : List Nat) (a : Arr), a.Within b orig → (xs.foldl f a).Within b orig
  | [], _, h => h
  | x :: xs, a, h => foldl_within' hf xs (f a x) (hf a x h)

theorem Arr.pop_within {b} {a : Arr} (h : b ≤ a.next) : a.pop.Within b a.ls := by
  unfold Arr.pop
  split
  · exact (Arr.Within.refl h).setLength _
  · exact ((Arr.Within.refl h).delete _).setLength _

theorem Arr.shift_within {b} {a : Arr} (h : b ≤ a.next) : a.shift.Within b a.ls := by
  unfold Arr.shift
  split
  · exact (Arr.Within.refl h).setLength _
  · refine (Arr.Within.delete ?_ _).setLength _
    refine foldl_within' (fun s j hs => ?_) _ _ (Arr.Within.refl h)
    split
    · exact hs.set _
    · exact hs.delete _

theorem Arr.reverse_within {b} {a : Arr} (h : b ≤ a.next) : a.reverse.Within b a.ls := by
  unfold Arr.reverse
  refine foldl_within' (fun s lower hs => ?_) _ _ (Arr.Within.refl h)
  dsimp only
  split
  · exact (hs.set _).set _
  · exact (hs.set _).delete _
  · exact (hs.delete _).set _
  · exact hs

/-- **Every array native keeps its store's cells among the original and
fresh ones**: `Set`, `Delete`, a length change, `push`, `pop`, `shift`,
`unshift`, `reverse` and `sort`'s writeback. -/
theorem Arr.natives_within {b} {a : Arr} (h : b ≤ a.next) (k n c len : Nat) :
    (a.set k).Within b a.ls ∧ (a.delete k).Within b a.ls ∧ (a.setLength n).Within b a.ls ∧
      a.push.Within b a.ls ∧ a.pop.Within b a.ls ∧ a.shift.Within b a.ls ∧
      a.unshift.Within b a.ls ∧ a.reverse.Within b a.ls ∧ (a.writeback c len).Within b a.ls :=
  ⟨(Arr.Within.refl h).set k, (Arr.Within.refl h).delete k, (Arr.Within.refl h).setLength n,
    Arr.push_within h, Arr.pop_within h, Arr.shift_within h, Arr.unshift_within h,
    Arr.reverse_within h, Arr.writeback_within c len (Arr.Within.refl h)⟩

/-- **An array native's element-storage phase preserves kinds.** From a
well-formed heap `h`, the phase of a native that rewrites the array store at
`s` reaches `h'`: the store holds the native's result `a.ls`, every other old
location keeps its contents or is an element cell now holding a source
value, and every fresh location holds a source value. The world extension
makes the fresh locations element cells.

The premises are stated here: the store's change, the element contents and
the fresh locations' contents. `array_native_post` bounds which locations
change and gives none of them. -/
theorem native_shaped {k : Nat} {W : WorldT k} {h h' : Heap} {s : Nat} {orig : List (Option Nat)}
    {a : Arr} (cs : List (Ctr k)) (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hs : roleAt W s = some (.store .array)) (hso : h[s]? = some (.arr orig))
    (hw : a.Within h.length orig)
    (hlen' : h'.length = h.length + cs.length) (hs' : h'[s]? = some (.arr a.ls))
    (hcells : ∀ l, some l ∈ a.ls → l < h'.length)
    (hold : ∀ l, l < h.length → l ≠ s → h'[l]? = h[l]? ∨
      (roleAt W l = some .elem ∧ ∃ v, h'[l]? = some v ∧ isSourceVal v = true ∧
        RefsOk (appendWs W (cs.map fun c => (Role.elem, c))) v))
    (hfresh : ∀ l, h.length ≤ l → l < h'.length → ∃ v, h'[l]? = some v ∧ isSourceVal v = true ∧
        RefsOk (appendWs W (cs.map fun c => (Role.elem, c))) v) :
    Shaped (appendWs W (cs.map fun c => (Role.elem, c))) h' := by
  let W' := appendWs W (cs.map fun c => (Role.elem, c))
  have hxt : WExt W W' := WExt_appendWs W _
  have hroleNew : ∀ l, h.length ≤ l → l < h'.length → roleAt W' l = some .elem := by
    intro l h1 h2
    obtain ⟨i, rfl⟩ : ∃ i, l = (entries W).length + i := ⟨l - (entries W).length, by omega⟩
    rw [roleAt_appendWs']
    simp only [List.map_map, Function.comp_def, List.map_const', List.getElem?_replicate]
    rw [if_pos (by omega)]
  intro l r hr
  by_cases hl : l < h.length
  · have hrW : roleAt W l = some r := by
      rw [roleAt_appendWs_lt W _ (by omega)] at hr; exact hr
    by_cases hls : l = s
    · subst hls
      rw [hs] at hrW; cases hrW
      obtain ⟨u, hu, -, ho⟩ := hsh l _ hs
      rw [hso] at hu; cases hu
      refine ⟨_, hs', ⟨_, rfl⟩, Arr.Within.refs hw (RefsOk_mono hxt ho) fun m hm hm' => ?_⟩
      exact hroleNew m hm (hcells m hm')
    · rcases hold l hl hls with he | ⟨he, v, hv, hsrc, hvr⟩
      · obtain ⟨u, hu, hsu⟩ := hsh l r hrW
        exact ⟨u, by rw [he]; exact hu, Shape_mono hxt hsu⟩
      · rw [he] at hrW; cases hrW
        exact ⟨v, hv, hsrc, hvr⟩
  · have hlt : l < h'.length := by
      have := roleAt_lt hr; simp at this; omega
    rw [hroleNew l (by omega) hlt] at hr; cases hr
    obtain ⟨v, hv, hsrc, hvr⟩ := hfresh l (by omega) hlt
    exact ⟨v, hv, hsrc, hvr⟩

end natives

/-! ## Contracts no step states -/

/-- **A heap relation respects kinds**: every transition it admits from a
heap meeting a world's structural part reaches a heap meeting the structural
part of an extension of that world. A contract stated as a relation between
heaps meets the native-contract condition only if it has this property. -/
def RespectsKinds (R : Heap → Heap → Prop) : Prop :=
  ∀ (k : Nat) (W : WorldT k) (h h' : Heap), h.length = (entries W).length → Shaped W h → R h h' →
    ∃ W' : WorldT k, WExt W W' ∧ h'.length = (entries W').length ∧ Shaped W' h'

/-- **The typed-array element write's coarse change does not respect
kinds** (`ElementWrite.changes`: every location holding no store, object or
number may change, and every store keeps its length). A field holding a
string may come to hold a store; the kinded view write the call's
postcondition states beside it keeps every location whose role is no view
store (`ViewWrite.keep`). -/
theorem elementWrite_not_respects :
    ¬ RespectsKinds (CallEffects.ElementWrite.stores.changes.Holds) := by
  intro H
  let W : WorldT 0 := ofEntries [(.field, fun _ hj _ _ => absurd hj (Nat.not_lt_zero _))]
  have hW : roleAt W 0 = some .field := by simp [W, roleAt, roles]
  have hsh : Shaped W [.str "a"] := by
    intro l r hr
    have hl : l = 0 := by have := roleAt_lt hr; simp [W] at this; omega
    subst hl
    rw [hW] at hr; cases hr
    exact ⟨_, rfl, rfl, fun _ h => by simp [refs] at h⟩
  have hc : CallEffects.ElementWrite.stores.changes.Holds [.str "a"] [.arr []] := by
    refine ⟨fun l v hv halt => ?_, fun _ l ls hl => ?_, fun hg => ?_⟩
    · have : l = 0 := by have := (List.getElem?_eq_some_iff.mp hv).1; simp at this; omega
      subst this; simp at hv; subst hv
      simp [HeapKnowledge.Changes.alters] at halt
    · have : l = 0 := by have := (List.getElem?_eq_some_iff.mp hl).1; simp at this; omega
      subst this; simp at hl
    · simp [CallEffects.ElementWrite.changes] at hg
  obtain ⟨W', hx, -, hsh'⟩ := H 0 W _ _ (by simp [W]) hsh hc
  obtain ⟨u, hu, hcat, -⟩ := hsh' 0 .field (WExt_roleAt hx hW)
  simp at hu; subst hu
  simp [Cat, isSourceVal] at hcat

end Verification.Kinds
