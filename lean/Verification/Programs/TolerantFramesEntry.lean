import Verification.Programs.TolerantFramesStore

/-! # Tolerant frames: the unit's entry

The pass checks a unit's entry before its walk (`SinglePass.entryRefusal`):
the start's context is the request's inputs, its given state states no
implication, names a slot after the promised input or an input's entry value
only at that input's own slot, and the request's entry facts entail its
written and supplied facts (`ControlFlow.entryKnows`). The start's state is
then the head entry of its given invariant (`SinglePass.headEntry`), the
written facts with the request's entry facts and the supplied facts
(`startGiven`). This module proves that, from the request's input contracts
and entry facts, that state holds (`StateHolds`) at the start environment,
each slot named by itself. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

section Entry
variable {ι : Type} [DecidableEq ι]
open ProgramTyping PositiveGraphs

/-- The start's given invariant as `SinglePass.run` builds it: the written
assertion with the request's entry index facts and separation, then the
supplied facts. -/
def startGiven (written : Option HeapKnowledge.Knowledge) (entryIndices : List HeapKnowledge.IndexAtom)
    (entrySeparation : HeapSeparation.Separation) (supplied : List HeapKnowledge.IndexAtom) : HeapKnowledge.Knowledge :=
  let w := written.getD {}
  let w : HeapKnowledge.Knowledge :=
    { w with indices := w.indices ++ entryIndices, separation := HeapSeparation.union w.separation entrySeparation }
  { w with indices := w.indices ++ supplied }

/-! ## What an accepted entry check states -/

/-- An accepted entry preserves the start's written separation. -/
theorem entryRefusal_startKept {G : NormalGraph ι} {inputs : List (Ty ι)}
    {claims : List (CertificateProducer.PointClaim ι)} {start : Nat}
    {goal : ControlFlow.Goal ι} {written : Option HeapKnowledge.Knowledge} {supplied}
    {givenImplies : List (PromiseCalls.Implication ι)} {givenArgs givenInputs entryIndices entrySeparation}
    (h : SinglePass.entryRefusal G inputs claims start goal written supplied givenImplies givenArgs givenInputs
      entryIndices entrySeparation = none) :
    SinglePass.startSeparationKept written entrySeparation = true := by
  unfold SinglePass.entryRefusal at h
  repeat' (first | split at h | extract_lets at h)
  all_goals simp_all

/-- **An accepted entry check** gives the start's claim at the inputs, no
given implication, the promised input's slot at each slot its given state
names after it, each input's entry value at its own slot, and the entry
facts' entailment of the written and supplied facts. -/
theorem entryRefusal_ok {G : NormalGraph ι} {inputs : List (Ty ι)} {claims : List (CertificateProducer.PointClaim ι)} {start : Nat}
    {goal : ControlFlow.Goal ι} {written : Option HeapKnowledge.Knowledge} {supplied : List HeapKnowledge.IndexAtom}
    {givenImplies : List (PromiseCalls.Implication ι)} {givenArgs : List Nat} {givenInputs : List (Nat × Nat)}
    {entryIndices : List HeapKnowledge.IndexAtom} {entrySeparation : HeapSeparation.Separation}
    (h : SinglePass.entryRefusal G inputs claims start goal written supplied givenImplies givenArgs givenInputs
      entryIndices entrySeparation = none) :
    (∃ c, claims[start]? = some c ∧ c.context = inputs) ∧ (∀ sl, goal.slot = some sl → sl < inputs.length) ∧
      givenImplies = [] ∧ (∀ i ∈ givenArgs, goal.slot = some i) ∧ (∀ p ∈ givenInputs, p.1 = p.2) ∧
      ControlFlow.entryKnows G inputs entrySeparation entryIndices
        { written.getD {} with indices := (written.getD {}).indices ++ supplied } = true := by
  unfold SinglePass.entryRefusal at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · cases h
    rename_i h1
    split at h
    · cases h
    rename_i h2
    split at h
    · cases h
    rename_i h3
    split at h
    · cases h
    rename_i h4
    split at h
    · cases h
    rename_i h5
    split at h
    · cases h
    dsimp only at h
    split at h
    · cases h
    rename_i h6
    simp only [Bool.not_eq_true', Bool.not_eq_false] at h1 h2 h3 h4 h5 h6
    refine ⟨⟨c, hc, beq_iff_eq.mp h1⟩, fun sl hsl => ?_, List.isEmpty_iff.mp h3, fun i hi => ?_, fun p hp => ?_, h6⟩
    · rw [hsl] at h2; simpa using h2
    · have := List.all_eq_true.mp h4 i hi; exact (beq_iff_eq.mp this).symm
    · have := List.all_eq_true.mp h5 p hp; exact beq_iff_eq.mp this

theorem union_holds {S T : HeapSeparation.Separation} {ρ : Env} (hS : HeapSeparation.Holds S ρ)
    (hT : HeapSeparation.Holds T ρ) : HeapSeparation.Holds (HeapSeparation.union S T) ρ := by
  unfold HeapSeparation.union
  split
  · exact hT
  · split
    · exact hS
    · split
      · rename_i hd
        apply HeapSeparation.norm_holds
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hS a ha
        · exact (beq_iff_eq.mp hd) ▸ hT a (List.mem_filter.mp ha).1
      · exact hT

/-- **The start's given invariant holds** at the start environment where the
entry check accepted it: its written and supplied facts by the entry facts'
entailment, the entry facts and separation as the request states them. -/
theorem startGiven_holds {G : NormalGraph ι} {inputs : List (Ty ι)} {written : Option HeapKnowledge.Knowledge}
    {supplied entryIndices : List HeapKnowledge.IndexAtom} {entrySeparation : HeapSeparation.Separation}
    (hk : ControlFlow.entryKnows G inputs entrySeparation entryIndices
      { written.getD {} with indices := (written.getD {}).indices ++ supplied } = true)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} (he : EnvOk G inputs ρ n W)
    (hs : HeapSeparation.Holds entrySeparation ρ) (hi : HeapKnowledge.IndexHolds ⟨ρ, h⟩ entryIndices ρ h) :
    HeapKnowledge.Holds (startGiven written entryIndices entrySeparation supplied) ⟨ρ, h⟩ ρ h := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ControlFlow.entryKnows_sound hk he hs hi
  refine ⟨h1, h2, h3, union_holds h4 hs, h5, fun a ha => ?_⟩
  simp only [startGiven, List.append_assoc, List.mem_append] at ha
  rcases ha with ha | ha | ha
  · exact h6 a (List.mem_append_left _ ha)
  · exact hi a ha
  · exact h6 a (List.mem_append_right _ ha)

/-! ## The start's state -/

omit [DecidableEq ι] in
/-- **At the start, `headEntry` names each slot by itself**: with the start's
names `0, …, w - 1`, a slot named after the promised input is that input's
slot and a slot named after an input's entry value is that input's. -/
theorem headEntry_start_names {g : HeapKnowledge.Knowledge} {w fresh : Nat} {goal : ControlFlow.Goal ι}
    {argSlots : List Nat} {inputSlots : List (Nat × Nat)} {implies : List (PromiseCalls.Implication ι)}
    (hargs : ∀ i ∈ argSlots, goal.slot = some i) (hinputs : ∀ p ∈ inputSlots, p.1 = p.2) :
    (SinglePass.headEntry g true w fresh (List.range w) (goal.slot.bind ((List.range w)[·]?)) argSlots inputSlots
      implies).1.names = List.range w := by
  simp only [SinglePass.headEntry, if_true]
  have hbase : (List.range w).headD 0 = 0 := by cases w <;> simp [List.range_succ_eq_map]
  rw [hbase]
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  simp only [List.length_map, List.length_range] at hi
  simp only [List.getElem_map, List.getElem_range]
  split
  · rename_i x hx
    obtain ⟨⟨i', q⟩, hf, hq⟩ := Option.bind_eq_some_iff.mp hx
    have hfi := List.find?_some hf
    simp only [beq_iff_eq] at hfi
    have hiq := hinputs _ (List.mem_of_find?_eq_some hf)
    simp only at hiq hfi
    subst hfi; subst hiq
    rw [List.getElem?_range hi] at hq
    exact (Option.some.inj hq).symm
  · split
    · rename_i a ha
      split
      · rename_i hc
        have hs := hargs i (List.contains_iff_mem.mp hc)
        rw [hs] at ha
        simp only [Option.bind_some, List.getElem?_range hi, Option.some.injEq] at ha
        exact ha.symm
      · rfl
    · rfl

theorem storeOk_empty {η : Env} {h : Heap} : StoreOk ε {} η h := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact absurd (mem_keysOf.mp hx) (Std.HashSet.not_mem_empty)
  · obtain ⟨n, hn⟩ := mem_valsOf.mp hx
    simp at hn

theorem storeWF_empty : StoreWF {} :=
  ⟨fun _ h => absurd h Std.HashSet.not_mem_empty, fun _ _ h => by simp at h, fun _ _ h => by simp at h,
    fun _ => by simp⟩

/-- **A head's store holds** where its given invariant holds at the slots
and the renaming sends each slot to a name holding its value; it is
well-formed. -/
theorem headStore_ok {g : HeapKnowledge.Knowledge} {f : Nat → Option Nat} {ρ η : Env} {h : Heap}
    (hg : HeapKnowledge.Holds g ε ρ h) (hf : ∀ i x, f i = some x → η x = ρ i) :
    StoreOk ε ((SinglePass.atomsOf g).foldl (fun s a => match a.rename f with | some b => s.add b | none => s) {}) η h ∧
      StoreWF ((SinglePass.atomsOf g).foldl (fun s a => match a.rename f with | some b => s.add b | none => s) {}) := by
  refine foldl_inv (fun s => StoreOk ε s η h ∧ StoreWF s) _ _ _ ⟨storeOk_empty, storeWF_empty⟩ ?_
  intro a ha s ⟨hs, ws⟩
  split
  · rename_i b hb
    exact ⟨add_ok hs (atomHolds_rename (fun i x hx => hf i x hx) hb (atomsOf_holds hg a ha)), add_wf ws b⟩
  · exact ⟨hs, ws⟩

/-- **(Entry) The start's state holds where the entry check accepted it.**
From the request's input contracts (`EnvOk` at its inputs), its entry
separation and index facts, the start's state, the head entry of the start's
given invariant over the start's names `0, …, |inputs| - 1`, holds at the
start environment `ρ`, each start name holding its entry value `ρ q`; its
store is well-formed and each slot named by itself. -/
theorem entry_stateHolds {G : NormalGraph ι} {inputs : List (Ty ι)} {claims : List (CertificateProducer.PointClaim ι)} {start : Nat}
    {goal : ControlFlow.Goal ι} {written : Option HeapKnowledge.Knowledge} {supplied : List HeapKnowledge.IndexAtom}
    {givenImplies : List (PromiseCalls.Implication ι)} {givenArgs : List Nat} {givenInputs : List (Nat × Nat)}
    {entryIndices : List HeapKnowledge.IndexAtom} {entrySeparation : HeapSeparation.Separation}
    (hacc : SinglePass.entryRefusal G inputs claims start goal written supplied givenImplies givenArgs givenInputs
      entryIndices entrySeparation = none)
    {ρ : Env} {m : Nat} {s : IndexedHeap} (he : EnvOk G inputs ρ s.n s.W)
    (hs : HeapSeparation.Holds entrySeparation ρ) (hi : HeapKnowledge.IndexHolds ⟨ρ, s.h⟩ entryIndices ρ s.h) (fresh : Nat) :
    StateHolds G (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true inputs.length
        fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs givenInputs
        givenImplies).1
      (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true inputs.length
        fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs givenInputs
        givenImplies).2.1
      (List.range inputs.length) ⟨ρ, s.h⟩ ρ m s ∧
    StoreWF (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true inputs.length
        fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs givenInputs
        givenImplies).1.store ∧
    (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true inputs.length
        fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs givenInputs
        givenImplies).1.names = List.range inputs.length := by
  obtain ⟨-, -, himp, hargs, hinputs, hk⟩ := entryRefusal_ok hacc
  have hnames := headEntry_start_names (g := startGiven written entryIndices entrySeparation supplied)
    (w := inputs.length) (fresh := fresh) (implies := givenImplies) hargs hinputs
  have hstore : (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true
    inputs.length fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs
    givenInputs givenImplies).1.store = (SinglePass.atomsOf (startGiven written entryIndices entrySeparation
      supplied)).foldl (fun s a => match a.rename (fun i => (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true
    inputs.length fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs
    givenInputs givenImplies).1.names[i]?) with
        | some b => s.add b | none => s) {} := rfl
  have himpl : (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true
    inputs.length fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs
    givenInputs givenImplies).2.1 = [] := by subst himp; rfl
  have hfr : (SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true
    inputs.length fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs
    givenInputs givenImplies).1.fresh = [] := rfl
  generalize SinglePass.headEntry (startGiven written entryIndices entrySeparation supplied) true inputs.length
    fresh (List.range inputs.length) (goal.slot.bind ((List.range inputs.length)[·]?)) givenArgs givenInputs
    givenImplies = E at hnames hstore himpl hfr ⊢
  have hg := startGiven_holds hk he hs hi
  have hf : ∀ i x, (List.range inputs.length)[i]? = some x → ρ x = ρ i := by
    intro i x hx
    by_cases hi : i < inputs.length
    · rw [List.getElem?_range hi] at hx; cases hx; rfl
    · rw [List.getElem?_eq_none (by simp; omega)] at hx; cases hx
  have hf' : ∀ i x, (fun i => E.1.names[i]?) i = some x → ρ x = ρ i := by
    intro i x hx; rw [hnames] at hx; exact hf i x hx
  obtain ⟨hok, hwf⟩ := headStore_ok hg hf'
  rw [← hstore] at hok hwf
  refine ⟨⟨ρ, fun i x hx => (hf i x (hnames ▸ hx)).symm, fun a ha => hok a ha, ?_, ?_,
    fun q x hx => hf q x hx⟩, hwf, hnames⟩
  · rw [himpl]; intro x hx; cases hx
  · rw [hfr]; intro x hx; cases hx

end Entry

end Verification.TolerantFrames
