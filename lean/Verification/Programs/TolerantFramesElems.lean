import Verification.Programs.TolerantFramesWrites

/-! # Tolerant frames: element facts under an effect

`Atom.keptBy` decides the named facts a closed effect keeps by atom: heap-free
facts and the index facts its change keeps. This module adds the element
facts:

- a quantified element fact (`IndexFact.every`: every element below a stop
  meets a body) is kept by a change keeping stores and numbers
  (`IndexFact.everyKept`), among the closed effects the initialisation
  write's `{values: init, stores: keep}` (`every_keptBy_init`);
- an elements atom (`.elem`: every present element of a store meets a
  predicate, `CallEffects.ElemsAt`) is kept by `{values: keep, stores: keep}`;
- a dense prefix (`DenseAt`) is kept by `{values: any, stores: grow}`
  (`dense`, in `TolerantFrames`).

`Atom.keptByElems` is `Atom.keptBy` with the first two; `atom_keptByElems`
and `named_keptByElems_box` are `atom_kept` and `named_kept_box` for it. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom)

/-- The initialisation write's closed effect: values from absent to present,
stores kept (`ExpressionEffects.initWriteWithin`). -/
def initEffect : Footprints.Closed := ⟨.init, .keep⟩

/-- A named fact every action of `c` keeps: `Atom.keptBy`'s, a quantified
element fact `c`'s change keeps (`IndexFact.everyKept`), or an elements atom
under an effect keeping every old location. -/
def _root_.Verification.SinglePass.Atom.keptByElems (c : Footprints.Closed) : Atom → Bool
  | .index x => x.fact.envOnly || x.fact.keptBy (HeapKnowledge.Changes.ofClosed c) (fun _ _ => false) ||
      x.fact.everyKept (HeapKnowledge.Changes.ofClosed c) (fun _ _ => false)
  | .elem _ => c.value == .keep && c.store == .keep
  | a => a.heapFree

/-- `Atom.keptBy` decides less. -/
theorem keptBy_keptByElems {c : Footprints.Closed} {a : Atom} (hk : a.keptBy c = true) : a.keptByElems c = true := by
  cases a <;> simp_all [Atom.keptBy, Atom.keptByElems, Atom.heapFree]

/-- **An element fact kept by atom survives an action of its effect.** -/
theorem atom_keptByElems {c : Footprints.Closed} {a : Atom} (hk : a.keptByElems c = true) {η ρ : Env}
    {s s' : IndexedHeap} (hact : Action c.fp ρ s s') (ha : AtomHolds a η s.h) : AtomHolds a η s'.h := by
  have hc : c.Holds s.h s'.h := Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp hact.2)
  cases a with
  | index x =>
    simp only [Atom.keptByElems, Bool.or_eq_true] at hk
    rcases hk with (he | hk) | hk
    · exact atomHolds_heapFree (a := .index x) he ha s'.h
    · exact atom_kept (a := .index x) (by simp [Atom.keptBy, hk]) hact ha
    · intro x' hx hcnd
      simp only [List.mem_singleton] at hx
      subst hx
      exact HeapKnowledge.IndexFact.everyKept_sound (HeapKnowledge.Changes.ofClosed_holds hc)
        (fun _ _ _ _ _ _ _ hf => by simp at hf) hk (ha x' (List.mem_singleton_self _) hcnd)
  | elem e =>
    simp only [Atom.keptByElems, Bool.and_eq_true, beq_iff_eq] at hk
    obtain ⟨hv, hs⟩ := hk
    have he : c = Footprints.Closed.empty := by
      cases c; simp only at hv hs; subst hv; subst hs; rfl
    subst he
    obtain ⟨vs, hvs⟩ := Footprints.Closed.holds_empty.mp hc
    rw [← hvs]
    exact atomHolds_extend vs ha
  | _ => exact atomHolds_heapFree (by simpa only [Atom.keptByElems] using hk) ha s'.h

/-- **(Keep by atom), element facts included**: `Named S η ⊢ □_c Named S η`
for `S` kept by `c` (`Atom.keptByElems`). -/
theorem named_keptByElems_box {c : Footprints.Closed} {S : List Atom} (hk : ∀ a ∈ S, a.keptByElems c = true)
    {η ρ : Env} {m : Nat} {s : IndexedHeap} (hS : Named S η ρ m s) : Box c.fp (Named S η) ρ m s :=
  fun _ ha a hm => atom_keptByElems (hk a hm) ha (hS a hm)

/-- An elements atom is kept by `{values: keep, stores: keep}`. -/
theorem elem_keptByElems_empty (e : HeapKnowledge.ElemAtom) :
    (Atom.elem e).keptByElems Footprints.Closed.empty = true := rfl

/-- A quantified element fact over a slot's store, its stop a slot's value,
its body reading the elements: kept by the initialisation write's effect,
which keeps stores and numbers. -/
theorem every_keptBy_init (x y : Nat) (body : List (HeapKnowledge.LinearClause HeapKnowledge.Bound))
    (hb : body.all (fun F => F.vars.all fun b => match b with
        | .free t => t.keptBy (HeapKnowledge.Changes.ofClosed initEffect) (fun _ _ => false)
        | .project _ _ => false
        | _ => true) = true) :
    (Atom.index ⟨.every x [] (.value y) body, none, false⟩).keptByElems initEffect = true := by
  simp only [Atom.keptByElems, Bool.or_eq_true]
  right
  simp only [HeapKnowledge.IndexFact.everyKept, Bool.and_eq_true]
  exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hb⟩

end Verification.TolerantFrames
