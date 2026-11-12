import Verification.Programs.TolerantFramesMergeGraph

/-! # Tolerant frames: entering a loop head

A loop head other than the start (`SinglePass.headEntry … false …`) enters
with fresh names `fresh + i` at its slots, but where its given inputs or its
promised input name a start name, and its store is its given facts renamed
from slots to those names. Its given facts are an obligation on every edge
into it: the edge establishes them at the head's environment
(`EdgeEstablishes`, the interface with the edge check). This module proves
that where an edge establishes them, the head's state holds
(`headEntry_holds`), at the valuation `headVal`: a start name its entry
value, a fresh name the value of its slot. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping PositiveGraphs

section Head
variable {ι : Type}

/-- **What an edge into a loop head establishes** at the head's
environment `ρ'` and the state `s`, its entry values `ρ0`: the head's given
facts `g` hold at its slots; its given implications hold; a slot `j` a given
input `(j, q)` names holds the entry value of `q`; a slot the promised input
names holds the entry value of the start name the promised input is. -/
structure EdgeEstablishes (G : NormalGraph ι) (g : HeapKnowledge.Knowledge)
    (implies : List (PromiseCalls.Implication ι)) (startNames : List Nat) (argName : Option Nat)
    (argSlots : List Nat) (inputSlots : List (Nat × Nat)) (ρ0 ρ' : Env) (s : IndexedHeap) : Prop where
  facts : HeapKnowledge.Holds g ρ' s.h
  implies : PromiseCalls.ImpliesOk G implies ρ' s.n s.W
  inputs : ∀ j q x, (j, q) ∈ inputSlots → startNames[q]? = some x → ρ' j = ρ0 q
  arg : ∀ j a q, j ∈ argSlots → argName = some a → startNames[q]? = some a → ρ' j = ρ0 q

/-- The head's valuation: a start name its entry value, any other name
`fresh + i` the value of slot `i`. -/
noncomputable def headVal (startNames : List Nat) (ρ0 ρ' : Env) (fresh : Nat) : Env := fun y =>
  open Classical in if h : ∃ q, startNames[q]? = some y then ρ0 (Classical.choose h) else ρ' (y - fresh)

theorem headVal_start {startNames : List Nat} {ρ0 ρ' : Env} {fresh q y : Nat} (hnd : startNames.Nodup)
    (hq : startNames[q]? = some y) : headVal startNames ρ0 ρ' fresh y = ρ0 q := by
  have hex : ∃ q, startNames[q]? = some y := ⟨q, hq⟩
  simp only [headVal, dif_pos hex]
  have hc := Classical.choose_spec hex
  have h1 := (List.getElem?_eq_some_iff.mp hc)
  have h2 := (List.getElem?_eq_some_iff.mp hq)
  congr 1
  exact (List.getElem_inj hnd).mp (h1.2.trans h2.2.symm)

theorem headVal_fresh {startNames : List Nat} {ρ0 ρ' : Env} {fresh i : Nat} (hlt : ∀ x ∈ startNames, x < fresh) :
    headVal startNames ρ0 ρ' fresh (i + fresh) = ρ' i := by
  have hne : ¬∃ q : Nat, startNames[q]? = some (i + fresh) := by
    rintro ⟨q, hq⟩
    have := hlt _ (List.mem_of_getElem? hq); omega
  simp only [headVal, dif_neg hne]; congr 1; omega

/-- **The head's slots hold their names' values** under `headVal`, where
the edge establishes the given inputs and the promised input. -/
theorem headEntry_slots {G : NormalGraph ι} {g : HeapKnowledge.Knowledge} {width fresh : Nat}
    {startNames : List Nat} {argName : Option Nat} {argSlots : List Nat} {inputSlots : List (Nat × Nat)}
    {implies : List (PromiseCalls.Implication ι)} {ρ0 ρ' : Env} {s : IndexedHeap}
    (hnd : startNames.Nodup) (hlt : ∀ x ∈ startNames, x < fresh)
    (harg : ∀ a, argName = some a → ∃ q : Nat, startNames[q]? = some a)
    (he : EdgeEstablishes G g implies startNames argName argSlots inputSlots ρ0 ρ' s) :
    SlotsNamed (SinglePass.headEntry g false width fresh startNames argName argSlots inputSlots implies).1.names
      ρ' (headVal startNames ρ0 ρ' fresh) := by
  intro i x hx
  simp only [SinglePass.headEntry, Bool.false_eq_true, if_false, List.getElem?_map] at hx
  by_cases hi : i < width
  · rw [List.getElem?_range hi] at hx
    simp only [Option.map_some, Option.some.injEq] at hx
    split at hx
    · rename_i x' heq
      obtain ⟨⟨j, q⟩, hf, hq⟩ := Option.bind_eq_some_iff.mp heq
      have hj : j = i := by simpa using List.find?_some hf
      subst hj hx
      rw [he.inputs j q x' (List.mem_of_find?_eq_some hf) hq, headVal_start hnd hq]
    · split at hx
      · rename_i _ _ a
        split at hx
        · rename_i hc
          subst hx
          obtain ⟨q, hq⟩ := harg a rfl
          rw [he.arg i a q (List.contains_iff_mem.mp hc) rfl hq, headVal_start hnd hq]
        · subst hx; rw [headVal_fresh hlt]
      · subst hx; rw [headVal_fresh hlt]
  · rw [List.getElem?_eq_none (by simpa using hi)] at hx
    simp at hx

/-- **(Head) A loop head's state holds where an edge establishes its given
facts**: at a loop head other than the start, with distinct start names
below the counter and the promised input a start name, where the edge
establishes the head's given facts, implications, inputs and promised input
at the head's environment `ρ'`, the head's state with its implications holds
at `ρ'`, each start name holding its entry value; its store is well-formed. -/
theorem headEntry_holds {G : NormalGraph ι} {g : HeapKnowledge.Knowledge} {width fresh : Nat}
    {startNames : List Nat} {argName : Option Nat} {argSlots : List Nat} {inputSlots : List (Nat × Nat)}
    {implies : List (PromiseCalls.Implication ι)} {ρ0 ρ' : Env} {m : Nat} {s : IndexedHeap}
    (hnd : startNames.Nodup) (hlt : ∀ x ∈ startNames, x < fresh)
    (harg : ∀ a, argName = some a → ∃ q : Nat, startNames[q]? = some a)
    (he : EdgeEstablishes G g implies startNames argName argSlots inputSlots ρ0 ρ' s) :
    StateHolds G (SinglePass.headEntry g false width fresh startNames argName argSlots inputSlots implies).1
      (SinglePass.headEntry g false width fresh startNames argName argSlots inputSlots implies).2.1
      startNames ρ0 ρ' m s ∧
    StoreWF (SinglePass.headEntry g false width fresh startNames argName argSlots inputSlots implies).1.store := by
  have hsl := headEntry_slots (width := width) hnd hlt harg he
  have hst := headStore_ok
    (f := fun i => (SinglePass.headEntry g false width fresh startNames argName argSlots inputSlots implies).1.names[i]?)
    he.facts (fun i x hx => (hsl i x hx).symm)
  refine ⟨⟨headVal startNames ρ0 ρ' fresh, hsl, hst.1, ?_, ⟨fun x hx => ?_, fun q x hq => headVal_start hnd hq⟩⟩,
    hst.2⟩
  · intro x hx htest
    obtain ⟨y, hy, hyx⟩ := List.mem_filterMap.mp hx
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hyx
    obtain ⟨a, ha, b, hb, rfl⟩ := hyx
    rw [← hsl _ _ hb]
    exact he.implies y hy (by rw [hsl _ _ ha]; exact htest)
  · simp [SinglePass.headEntry] at hx

/-- **The heads a walk enters with their head entries are entered**
(`HeadsEntered`), where every edge state into a head holding establishes the
head's given facts at the head's environment (`EdgeEstablishes`) and no head
is the start. -/
theorem headsEntered_of {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {ρ0 : Env}
    {given : Nat → Bool} {m : Nat} (gk : Nat → HeapKnowledge.Knowledge) (width fresh : Nat → Nat)
    (argName : Option Nat) (argSlots : Nat → List Nat) (inputSlots : Nat → List (Nat × Nat))
    (gimp : Nat → List (PromiseCalls.Implication ι))
    (hnd : startNames.Nodup) (hlt : ∀ t, given t = true → ∀ x ∈ startNames, x < fresh t)
    (harg : ∀ a, argName = some a → ∃ q : Nat, startNames[q]? = some a)
    (hentry : ∀ t, given t = true → w.entry t =
      (SinglePass.headEntry (gk t) false (width t) (fresh t) startNames argName (argSlots t) (inputSlots t) (gimp t)).1 ∧
      w.implies t =
      (SinglePass.headEntry (gk t) false (width t) (fresh t) startNames argName (argSlots t) (inputSlots t) (gimp t)).2.1)
    (hedges : ∀ t ρ (s : IndexedHeap), given t = true → edgePre G w startNames ρ0 t ρ m s →
      EdgeEstablishes G (gk t) (gimp t) startNames argName (argSlots t) (inputSlots t) ρ0 ρ s) :
    HeadsEntered G w startNames ρ0 given m := by
  intro t ρ s hg he
  obtain ⟨h1, h2⟩ := hentry t hg
  rw [h1, h2]
  exact (headEntry_holds hnd (hlt t hg) harg (hedges t ρ s hg he)).1

end Head

end Verification.TolerantFrames
