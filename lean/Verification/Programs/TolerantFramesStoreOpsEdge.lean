import Verification.Programs.TolerantFramesStoreOpsDrop
import Verification.Programs.TolerantFramesStore

/-! # Tolerant frames: the edge operations keep the store well-formed

`applyDelta`'s three loops only add (`Store.add`) and remove
(`Store.remove`) facts, so the delta keeps a store well-formed
(`applyDelta_wf`); an edge's store (`SinglePass.edgeStoreOf`: a handler's
heap-free facts, an observation's or a promotion's delta, or the output
store) and its transfer (`SinglePass.edgeTransfer`, the store without the
names it drops) are then well-formed wherever the output store and the
entry store are (`edgeStoreOf_wf`, `edgeTransfer_wf`). -/
namespace Verification.TolerantFrames
open Verification SinglePass PositiveGraphs

theorem deltaAdd_wf {s : Store} (w : StoreWF s) (pairs : List (Atom × Atom)) (out : HeapKnowledge.Knowledge)
    (shift : Bool) (back : Nat → Option Nat) : StoreWF (deltaAdd s pairs out shift back).1 := by
  unfold deltaAdd
  simp only [Id.run]
  refine forIn_inv_bind (R := fun (r : Store × List HeapKnowledge.IndexAtom) => StoreWF r.1)
    (SinglePass.atomsOf out) (s, []) _ (fun r => StoreWF r.1) _ w ?_ (fun _ h => h)
  intro o _ r hr
  repeat' split
  all_goals first | exact add_wf hr _ | exact hr

theorem deltaRestate_wf {s : Store} (w : StoreWF s) (added : List HeapKnowledge.IndexAtom) :
    StoreWF (deltaRestate s added) := by
  unfold deltaRestate
  simp only [Id.run]
  refine forIn_inv_bind (R := StoreWF) added s _ StoreWF _ w ?_ (fun _ h => h)
  intro x _ t ht
  show StoreWF (forIn (m := Id) x.fact.slots t _)
  refine forIn_inv _ _ _ StoreWF ht ?_
  intro v _ u hu
  split
  · show StoreWF (forIn (m := Id) _ u _)
    exact forIn_inv _ _ _ StoreWF hu fun y _ w' hw => add_wf hw _
  · exact hu

/-- **The delta keeps the store well-formed.** -/
theorem applyDelta_wf {s : Store} (w : StoreWF s) (pairs : List (Atom × Atom)) (out : HeapKnowledge.Knowledge)
    (shift : Bool) (back : Nat → Option Nat) : StoreWF (SinglePass.applyDelta s pairs out shift back) := by
  rw [applyDelta_eq]
  exact deltaRestate_wf (deltaAdd_wf (deltaRemove_wf w pairs out shift).1 pairs out shift back) _

variable {ι : Type}

/-- **An edge's store is well-formed** where the entry store and the output
store are. -/
theorem edgeStoreOf_wf {G : NormalGraph ι} {Γ : List (ProgramTyping.Ty ι)} {entryStore store : Store}
    (we : StoreWF entryStore) (ws : StoreWF store) (names pushedNames : List Nat) (width : Nat)
    (pushed isHandler : Bool) (observed : Option BranchRefinement.Observation) (promote : Option Bool) :
    StoreWF (edgeStoreOf G Γ entryStore store names pushedNames width pushed isHandler observed promote) := by
  unfold edgeStoreOf
  split
  · exact (dropHeap_cover we _).1
  · split
    · exact applyDelta_wf ws _ _ _ _
    · exact applyDelta_wf ws _ _ _ _
    · exact ws

/-- **An edge's transfer keeps the store well-formed**: the target's store is
the edge's store without the dropped names (`drop_wf`). -/
theorem edgeTransfer_wf [DecidableEq ι] [Hashable ι] {names : List Nat} {m : PointClaims.Mapping} {pushed isHandler outFresh : Bool}
    {entry : State} {result : Nat} {edgeStore : Store} (ws : StoreWF edgeStore)
    (implies : List (PromiseCalls.Implication ι)) :
    StoreWF (edgeTransfer names m pushed isHandler outFresh entry result edgeStore implies).1.store :=
  drop_wf ws _

/-- **An edge's transfer has the mapping's width** where `mapNames` gives
the target one name per mapped slot (`MapNamesLength`, a premise:
`orderedSuffix` is a `while` loop); the identity mapping keeps the source's
names. -/
def MapNamesLength : Prop :=
  ∀ (names slots : List Nat), (∀ j ∈ slots, j < names.length) → (mapNames names (some slots)).length = slots.length

theorem edgeTransfer_names [DecidableEq ι] [Hashable ι] {names : List Nat} {m : PointClaims.Mapping} {pushed isHandler outFresh : Bool}
    {entry : State} {result : Nat} {edgeStore : Store} (implies : List (PromiseCalls.Implication ι)) :
    (edgeTransfer names m pushed isHandler outFresh entry result edgeStore implies).1.names = mapNames names m :=
  rfl

theorem mapNames_none (names : List Nat) : mapNames names none = names := rfl

/-- **The target's width**: with `MapNamesLength`, an edge whose mapping
reads only source slots gives the target as many names as the mapping has
slots; the identity mapping as many as the source. -/
theorem edgeTransfer_width [DecidableEq ι] [Hashable ι] (hlen : MapNamesLength) {names : List Nat} {m : PointClaims.Mapping}
    {pushed isHandler outFresh : Bool} {entry : State} {result : Nat} {edgeStore : Store}
    (implies : List (PromiseCalls.Implication ι)) {w : Nat}
    (hw : match m with | none => names.length = w | some slots => slots.length = w ∧ ∀ j ∈ slots, j < names.length) :
    (edgeTransfer names m pushed isHandler outFresh entry result edgeStore implies).1.names.length = w := by
  rw [edgeTransfer_names]
  cases m with
  | none => exact hw
  | some slots => rw [hlen names slots hw.2]; exact hw.1

end Verification.TolerantFrames
