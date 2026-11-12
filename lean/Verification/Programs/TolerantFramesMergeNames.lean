import Verification.Programs.TolerantFramesStoreOpsDrop

/-! # Tolerant frames: a merge's names and valuation

The merge's first loop (`mergeSlots`) gives each slot a name: the
predecessors' common name where they agree, else the fresh name of the
vector of their names there, drawn from the counter the first time the
vector is met, each predecessor renaming its name at that slot to it. On the
path through predecessor `p`, whose state holds at a valuation `η`, the
merge's names denote under `mergeVal`: a name below the counter its value
under `η`, a fresh name the value of the first slot it names. This module
proves the loop's invariant (`mergeSlots_inv`) and that under `mergeVal`
each slot holds its merged name's value (`mergeVal_slots`), `η` is kept
below the counter, and a fresh name `φ` that `p` renames its name `x` to
denotes `η x` (`mergeVal_rename`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

/-- The predecessors' names at slot `j`, as the merge reads them. -/
def nsv (preds : List State) (j : Nat) : List Nat := (preds.map (·.names.toArray)).map (·.getD j 0)

/-- **The merge's first loop's invariant** after `k` slots: the counter
grew from `fresh0`; each slot keeps the predecessors' common name or holds
a fresh name, the one its names' vector has; the vectors' fresh names are
fresh and distinct; each predecessor's renaming sends a name only to fresh
names of slots where the predecessor holds that name. -/
structure SlotsInv (preds : List State) (fresh0 k fresh : Nat) (names : Array Nat)
    (renames : List (Std.HashMap Nat (List Nat))) (phis : Std.HashMap (List Nat) Nat) : Prop where
  ge : fresh0 ≤ fresh
  size : names.size = k
  slot : ∀ j (hj : j < names.size), (∀ q ∈ preds, q.names.toArray.getD j 0 = names[j]) ∨
    (fresh0 ≤ names[j] ∧ names[j] < fresh ∧ phis[nsv preds j]? = some names[j])
  phi : ∀ (v : List Nat) (φ : Nat), phis[v]? = some φ → fresh0 ≤ φ ∧ φ < fresh
  inj : ∀ (v v' : List Nat) (φ : Nat), phis[v]? = some φ → phis[v']? = some φ → v = v'
  len : renames.length = preds.length
  ren : ∀ p (hp : p < renames.length) (x φ : Nat), φ ∈ (renames[p]).getD x [] →
    ∃ j, ∃ hj : j < names.size, names[j] = φ ∧ fresh0 ≤ φ ∧ preds[p]?.map (·.names.toArray.getD j 0) = some x
  ne : ∀ p (hp : p < renames.length) (x : Nat) (φs : List Nat), (renames[p])[x]? = some φs → φs ≠ []

theorem nsv_get {preds : List State} {j p : Nat} {x : Nat} (h : (nsv preds j)[p]? = some x) :
    preds[p]?.map (·.names.toArray.getD j 0) = some x := by
  simp only [nsv, List.map_map, List.getElem?_map] at h
  simpa using h

theorem nsv_length (preds : List State) (j : Nat) : (nsv preds j).length = preds.length := by simp [nsv]

theorem slotsInv_zero (preds : List State) (width fresh0 : Nat) :
    SlotsInv preds fresh0 0 fresh0 (Array.mkEmpty width) ((preds.map (·.names.toArray)).map fun _ => {}) {} where
  ge := Nat.le_refl _
  size := rfl
  slot := fun j hj => by simp at hj
  phi := fun v φ h => by simp at h
  inj := fun v v' φ h => by simp at h
  len := by simp
  ren := fun p hp x φ h => by simp at h
  ne := fun p hp x φs h => by simp at h

theorem push_lt {names : Array Nat} {y j : Nat} (hj : j < names.size) :
    (names.push y)[j]'(by simp; omega) = names[j] := Array.getElem_push_lt hj

theorem push_eq {names : Array Nat} {y : Nat} : (names.push y)[names.size]'(by simp) = y := Array.getElem_push_eq

/-- One slot of the merge's first loop keeps the invariant. -/
theorem slotsInv_step {preds : List State} {fresh0 k fresh : Nat} {names : Array Nat}
    {renames : List (Std.HashMap Nat (List Nat))} {phis : Std.HashMap (List Nat) Nat}
    (I : SlotsInv preds fresh0 k fresh names renames phis) :
    let ns := nsv preds k
    let n0 := ns.headD 0
    (ns.all (· == n0) = true → SlotsInv preds fresh0 (k + 1) fresh (names.push n0) renames phis) ∧
    (∀ φ, ns.all (· == n0) = false → phis.get? ns = some φ → SlotsInv preds fresh0 (k + 1) fresh (names.push φ) renames phis) ∧
    (ns.all (· == n0) = false → phis.get? ns = none →
      SlotsInv preds fresh0 (k + 1) (fresh + 1) (names.push fresh)
        ((renames.zip ns).map fun (m, x) => m.insert x (fresh :: m.getD x [])) (phis.insert ns fresh)) := by
  intro ns n0
  have hsz := I.size
  refine ⟨fun hall => ?_, fun φ _ hφ => ?_, fun _ hnone => ?_⟩
  · refine { I with size := by simp [hsz], slot := ?_, ren := ?_ }
    · intro j hj
      simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [push_lt hj]; exact I.slot j hj
      · rw [push_eq]
        left
        intro q hq
        have : (nsv preds names.size).all (· == n0) = true := hsz ▸ hall
        have hmem : q.names.toArray.getD names.size 0 ∈ nsv preds names.size := by
          simp only [nsv, List.map_map, List.mem_map]; exact ⟨q, hq, rfl⟩
        have := List.all_eq_true.mp this _ hmem
        simp only [beq_iff_eq] at this
        rw [this]
    · intro p hp x φ' hm
      obtain ⟨j, hj, h1, h2, h3⟩ := I.ren p hp x φ' hm
      exact ⟨j, by simp; omega, by rw [push_lt hj]; exact h1, h2, h3⟩
  · have hφ' : phis[ns]? = some φ := by rw [← Std.HashMap.get?_eq_getElem?]; exact hφ
    refine { I with size := by simp [hsz], slot := ?_, ren := ?_ }
    · intro j hj
      simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [push_lt hj]; exact I.slot j hj
      · rw [push_eq]
        obtain ⟨h1, h2⟩ := I.phi _ _ hφ'
        exact .inr ⟨h1, h2, hsz ▸ hφ'⟩
    · intro p hp x φ' hm
      obtain ⟨j, hj, h1, h2, h3⟩ := I.ren p hp x φ' hm
      exact ⟨j, by simp; omega, by rw [push_lt hj]; exact h1, h2, h3⟩
  · have hnone' : phis[ns]? = none := by rw [← Std.HashMap.get?_eq_getElem?]; exact hnone
    have hlen : ((renames.zip ns).map fun (m, x) => m.insert x (fresh :: m.getD x [])).length = renames.length := by
      simp [I.len, ns, nsv_length]
    refine ⟨by have := I.ge; omega, by simp [hsz], ?_, ?_, ?_, by rw [hlen, I.len], ?_, ?_⟩
    · intro j hj
      simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [push_lt hj]
        rcases I.slot j hj with h | ⟨h1, h2, h3⟩
        · exact .inl h
        · refine .inr ⟨h1, by omega, ?_⟩
          rw [Std.HashMap.getElem?_insert]
          split
          · rename_i he; simp only [beq_iff_eq] at he; rw [he] at hnone'; rw [hnone'] at h3; cases h3
          · exact h3
      · rw [push_eq]
        refine .inr ⟨I.ge, by omega, ?_⟩
        rw [Std.HashMap.getElem?_insert]; simp [hsz, ns]
    · intro v φ hv
      rw [Std.HashMap.getElem?_insert] at hv
      split at hv
      · cases hv; exact ⟨I.ge, by omega⟩
      · have := I.phi v φ hv; omega
    · intro v v' φ hv hv'
      rw [Std.HashMap.getElem?_insert] at hv hv'
      split at hv <;> split at hv'
      · rename_i h1 h2; simp only [beq_iff_eq] at h1 h2; rw [← h1, ← h2]
      · cases hv; have := (I.phi _ _ hv').2; omega
      · cases hv'; have := (I.phi _ _ hv).2; omega
      · exact I.inj v v' φ hv hv'
    · intro p hp x φ hm
      rw [hlen] at hp
      have hpn : p < ns.length := by rw [nsv_length, ← I.len]; exact hp
      simp only [List.getElem_map, List.getElem_zip] at hm
      rw [Std.HashMap.getD_insert] at hm
      split at hm
      · rename_i he
        simp only [beq_iff_eq] at he
        rcases List.mem_cons.mp hm with rfl | hm
        · refine ⟨names.size, by simp, push_eq, I.ge, ?_⟩
          have : (nsv preds k)[p]? = some x := by rw [List.getElem?_eq_getElem hpn, he]
          rw [← hsz] at this; exact nsv_get this
        · obtain ⟨j, hj, h1, h2, h3⟩ := I.ren p hp x φ (by rw [← he]; exact hm)
          exact ⟨j, by simp; omega, by rw [push_lt hj]; exact h1, h2, h3⟩
      · obtain ⟨j, hj, h1, h2, h3⟩ := I.ren p hp x φ hm
        exact ⟨j, by simp; omega, by rw [push_lt hj]; exact h1, h2, h3⟩
    · intro p hp x φs hm
      rw [hlen] at hp
      simp only [List.getElem_map, List.getElem_zip] at hm
      rw [Std.HashMap.getElem?_insert] at hm
      split at hm
      · cases hm; simp
      · exact I.ne p hp x φs hm

/-- **The merge's first loop keeps its invariant** over every slot. -/
theorem mergeSlots_inv (preds : List State) (width fresh0 : Nat) :
    SlotsInv preds fresh0 width (mergeSlots preds width fresh0).1 (mergeSlots preds width fresh0).2.1
      (mergeSlots preds width fresh0).2.2.1 (mergeSlots preds width fresh0).2.2.2 := by
  unfold mergeSlots
  simp only [Id.run]
  refine forIn_idx_bind (List.range width) _ _
    (fun k (b : (Nat × Array Nat × List (Std.HashMap Nat (List Nat)) × Std.HashMap (List Nat) Nat)) => SlotsInv preds fresh0 k b.1 b.2.1 b.2.2.1 b.2.2.2)
    (fun (b : (Nat × Array Nat × List (Std.HashMap Nat (List Nat)) × Std.HashMap (List Nat) Nat)) => SlotsInv preds fresh0 width b.1 b.2.1 b.2.2.1 b.2.2.2) _
    (fun (r : (Nat × Array Nat × List (Std.HashMap Nat (List Nat)) × Std.HashMap (List Nat) Nat)) => SlotsInv preds fresh0 width r.1 r.2.1 r.2.2.1 r.2.2.2)
    (slotsInv_zero preds width fresh0) ?_ ?_ (fun b hb => by simpa using hb) (fun b hb => hb)
  · intro k i b b' hk I hf
    have hi : i = k := by
      rw [List.getElem?_range (by have := (List.getElem?_eq_some_iff.mp hk).1; simpa using this)] at hk
      exact (Option.some.inj hk).symm
    subst hi
    obtain ⟨h1, h2, h3⟩ := slotsInv_step I
    split at hf
    · rename_i hall; cases hf; exact h1 hall
    · rename_i hall
      have hall' : ((nsv preds i).all fun x => x == (nsv preds i).headD 0) = false :=
        Bool.eq_false_iff.mpr hall
      split at hf
      · rename_i φ hφ; cases hf; exact h2 φ hall' hφ
      · rename_i hφ; cases hf; exact h3 hall' hφ
  · intro k i b b' _ _ hf
    split at hf
    · cases hf
    · split at hf <;> cases hf

/-! ## The merge's valuation on one path -/

/-- **The merge's valuation on the path through a predecessor** valued by
`η`, at slot environment `ρ`: a name below the counter `fresh0` denotes its
value under `η`, a name at or past it the value of a slot it names. -/
noncomputable def mergeVal (ρ η : Env) (names : List Nat) (fresh0 : Nat) : Env := fun y =>
  if y < fresh0 then η y else
  open Classical in if h : ∃ i, names[i]? = some y then ρ (Classical.choose h) else η y

theorem mergeVal_below {ρ η : Env} {names : List Nat} {fresh0 y : Nat} (hy : y < fresh0) :
    mergeVal ρ η names fresh0 y = η y := by simp [mergeVal, hy]

section Path
variable {preds : List State} {width fresh0 p : Nat} {ρ η : Env}

/-- A slot of the merge holds, on the path through `p`, `p`'s name's value. -/
theorem slot_pred (hp : p < preds.length) (hlen : ∀ q ∈ preds, q.names.length = width)
    (hS : SlotsNamed preds[p].names ρ η) {j : Nat} (hj : j < width) :
    ρ j = η (preds[p].names.toArray.getD j 0) := by
  have hl := hlen _ (List.getElem_mem hp)
  apply hS
  simp [Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem (hl ▸ hj)]

theorem pred_below (hp : p < preds.length) (hlen : ∀ q ∈ preds, q.names.length = width)
    (hbel : ∀ q ∈ preds, ∀ x ∈ q.names, x < fresh0) {j : Nat} (hj : j < width) :
    preds[p].names.toArray.getD j 0 < fresh0 := by
  have hl := hlen _ (List.getElem_mem hp)
  apply hbel _ (List.getElem_mem hp)
  simp [Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem (hl ▸ hj)]

/-- **Two slots of the merge with one name hold one value** on the path
through `p`. -/
theorem slots_same (hp : p < preds.length) (hlen : ∀ q ∈ preds, q.names.length = width)
    (hbel : ∀ q ∈ preds, ∀ x ∈ q.names, x < fresh0) (hS : SlotsNamed preds[p].names ρ η)
    {j j' : Nat} (hj : j < (mergeSlots preds width fresh0).2.1.size) (hj' : j' < (mergeSlots preds width fresh0).2.1.size)
    (he : (mergeSlots preds width fresh0).2.1[j] = (mergeSlots preds width fresh0).2.1[j']) : ρ j = ρ j' := by
  have I := mergeSlots_inv preds width fresh0
  have hw : (mergeSlots preds width fresh0).2.1.size = width := I.size
  have hpm := List.getElem_mem hp
  rw [slot_pred hp hlen hS (hw ▸ hj), slot_pred hp hlen hS (hw ▸ hj')]
  have hb := pred_below hp hlen hbel (hw ▸ hj)
  have hb' := pred_below hp hlen hbel (hw ▸ hj')
  rcases I.slot j hj with h1 | ⟨h1, -, h3⟩ <;> rcases I.slot j' hj' with h1' | ⟨h1', -, h3'⟩
  · rw [h1 _ hpm, h1' _ hpm, he]
  · have := h1 _ hpm; omega
  · have := h1' _ hpm; omega
  · rw [he] at h3
    have hv := I.inj _ _ _ h3 h3'
    have e1 : (nsv preds j)[p]? = some (preds[p].names.toArray.getD j 0) := by
      simp only [nsv, List.map_map, List.getElem?_map, List.getElem?_eq_getElem hp]; rfl
    have e2 : (nsv preds j')[p]? = some (preds[p].names.toArray.getD j' 0) := by
      simp only [nsv, List.map_map, List.getElem?_map, List.getElem?_eq_getElem hp]; rfl
    rw [hv, e2] at e1
    rw [Option.some.inj e1]

/-- **Each slot of the merge holds its merged name's value** under
`mergeVal` on the path through `p`. -/
theorem mergeVal_slots (hp : p < preds.length) (hlen : ∀ q ∈ preds, q.names.length = width)
    (hbel : ∀ q ∈ preds, ∀ x ∈ q.names, x < fresh0) (hS : SlotsNamed preds[p].names ρ η) :
    SlotsNamed (mergeSlots preds width fresh0).2.1.toList ρ
      (mergeVal ρ η (mergeSlots preds width fresh0).2.1.toList fresh0) := by
  have I := mergeSlots_inv preds width fresh0
  have hw : (mergeSlots preds width fresh0).2.1.size = width := I.size
  have hpm := List.getElem_mem hp
  intro i y hy
  have hi : i < (mergeSlots preds width fresh0).2.1.size := by
    have := (List.getElem?_eq_some_iff.mp hy).1; simpa using this
  have hyi : (mergeSlots preds width fresh0).2.1[i] = y := by
    have := (List.getElem?_eq_some_iff.mp hy).2; simpa using this
  by_cases hy0 : y < fresh0
  · rw [mergeVal_below hy0]
    rcases I.slot i hi with h1 | ⟨h1, -, -⟩
    · rw [slot_pred hp hlen hS (hw ▸ hi), h1 _ hpm, hyi]
    · omega
  · have hex : ∃ i, (mergeSlots preds width fresh0).2.1.toList[i]? = some y := ⟨i, hy⟩
    simp only [mergeVal, hy0, if_false, dif_pos hex]
    have hc := Classical.choose_spec hex
    have hci : Classical.choose hex < (mergeSlots preds width fresh0).2.1.size := by
      have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
    have hcy : (mergeSlots preds width fresh0).2.1[Classical.choose hex] = y := by
      have := (List.getElem?_eq_some_iff.mp hc).2; simpa using this
    exact slots_same hp hlen hbel hS hi hci (by rw [hyi, hcy])

/-- **A fresh name a predecessor renames its name `x` to denotes `x`'s
value** under `mergeVal`. -/
theorem mergeVal_rename (hp : p < preds.length) (hlen : ∀ q ∈ preds, q.names.length = width)
    (hbel : ∀ q ∈ preds, ∀ x ∈ q.names, x < fresh0) (hS : SlotsNamed preds[p].names ρ η)
    (hpr : p < (mergeSlots preds width fresh0).2.2.1.length) {x φ : Nat}
    (hm : φ ∈ ((mergeSlots preds width fresh0).2.2.1[p]).getD x []) :
    mergeVal ρ η (mergeSlots preds width fresh0).2.1.toList fresh0 φ = η x := by
  have I := mergeSlots_inv preds width fresh0
  have hw : (mergeSlots preds width fresh0).2.1.size = width := I.size
  obtain ⟨j, hj, h1, -, h3⟩ := I.ren p hpr x φ hm
  have hx : preds[p].names.toArray.getD j 0 = x := by
    rw [List.getElem?_eq_getElem hp] at h3; exact Option.some.inj h3
  rw [← mergeVal_slots hp hlen hbel hS j φ (by simp [hj, h1]), slot_pred hp hlen hS (hw ▸ hj), hx]

/-- **A name a predecessor renames is below the counter.** -/
theorem rename_key_below (hp : p < preds.length) (hlen : ∀ q ∈ preds, q.names.length = width)
    (hbel : ∀ q ∈ preds, ∀ x ∈ q.names, x < fresh0)
    (hpr : p < (mergeSlots preds width fresh0).2.2.1.length) {x : Nat} {φs : List Nat}
    (hm : ((mergeSlots preds width fresh0).2.2.1[p])[x]? = some φs) : x < fresh0 := by
  have I := mergeSlots_inv preds width fresh0
  have hw : (mergeSlots preds width fresh0).2.1.size = width := I.size
  obtain ⟨φ, hφ⟩ := List.exists_mem_of_ne_nil _ (I.ne p hpr x φs hm)
  have hg : ((mergeSlots preds width fresh0).2.2.1[p]).getD x [] = φs := by
    rw [Std.HashMap.getD_eq_getD_getElem?, hm]; rfl
  obtain ⟨j, hj, -, -, h3⟩ := I.ren p hpr x φ (hg ▸ hφ)
  have hx : preds[p].names.toArray.getD j 0 = x := by
    rw [List.getElem?_eq_getElem hp] at h3; exact Option.some.inj h3
  rw [← hx]; exact pred_below hp hlen hbel (hw ▸ hj)

end Path

end Verification.TolerantFrames
