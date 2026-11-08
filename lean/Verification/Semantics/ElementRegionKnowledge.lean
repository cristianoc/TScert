import Verification.Semantics.ElementRegions

/-! Executable transfer of allocated element-region evidence. -/
namespace Verification.HeapKnowledge.ElementRegions

abbrev Facts := List (View × View)

def View.mapM (f : Nat → Option Nat) (v : View) : Option View :=
  (f v.slot).map fun s => v.map (fun _ => s)

def mapM (f : Nat → Option Nat) (facts : Facts) : Facts :=
  facts.filterMap fun (a, b) => do pure (← a.mapM f, ← b.mapM f)

theorem mapM_holds {f : Nat → Option Nat} {facts : Facts} {ρ ρ' : Env} {h : Heap}
    (hf : ∀ s t, f s = some t → ρ' t = ρ s) (hh : Holds facts ρ h) :
    Holds (mapM f facts) ρ' h := by
  intro fact hm
  obtain ⟨⟨a, b⟩, hab, hm⟩ := List.mem_filterMap.mp hm
  simp only [View.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
  obtain ⟨a', ⟨s, hs, rfl⟩, b', ⟨t, ht, rfl⟩, rfl⟩ := hm
  obtain ⟨sa, xs, sb, ys, ha, hb, hsep⟩ := hh (a, b) hab
  exact ⟨sa, xs, sb, ys, (reads_map (hf _ _ hs)).mpr ha,
    (reads_map (hf _ _ ht)).mpr hb, hsep⟩

/-- A root may be restated on each equal-valued alias. -/
def pull (pre : Nat → List Nat) (facts : Facts) : Facts :=
  facts.flatMap fun (a, b) => (pre a.slot).flatMap fun s =>
    (pre b.slot).map fun t => (a.map (fun _ => s), b.map (fun _ => t))

theorem pull_holds {pre : Nat → List Nat} {facts : Facts} {ρ ρ' : Env} {h : Heap}
    (hf : ∀ s t, t ∈ pre s → ρ' t = ρ s) (hh : Holds facts ρ h) :
    Holds (pull pre facts) ρ' h := by
  intro fact hm
  obtain ⟨⟨a, b⟩, hab, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  obtain ⟨sa, xs, sb, ys, ha, hb, hsep⟩ := hh (a, b) hab
  exact ⟨sa, xs, sb, ys, (reads_map (hf _ _ hs)).mpr ha,
    (reads_map (hf _ _ ht)).mpr hb, hsep⟩

def shift (facts : Facts) : Facts := mapM (fun s => some (s + 1)) facts

theorem shift_holds {facts : Facts} {ρ : Env} {h : Heap} {v : Val}
    (hh : Holds facts ρ h) : Holds (shift facts) (push v ρ) h :=
  mapM_holds (fun s t ht => by cases ht; rfl) hh

/-- A mapping drops a fact if either endpoint has no destination. -/
def drop (facts : Facts) : Facts := mapM (fun s => if s = 0 then none else some (s - 1)) facts

theorem drop_holds {facts : Facts} {ρ : Env} {h : Heap} {v : Val}
    (hh : Holds facts (push v ρ) h) : Holds (drop facts) ρ h := by
  apply mapM_holds _ hh
  intro s t ht
  split at ht
  · cases ht
  · rename_i hn
    cases ht
    obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by omega⟩
    rfl

/-- An edge requires each target pair in the mapped incoming evidence. -/
def check (f : Nat → Option Nat) (source target : Facts) : Bool :=
  target.all (mapM f source).contains

theorem check_sound {f : Nat → Option Nat} {source target : Facts} {ρ ρ' : Env} {h : Heap}
    (hf : ∀ s t, f s = some t → ρ' t = ρ s)
    (hc : check f source target = true) (hh : Holds source ρ h) : Holds target ρ' h := by
  intro fact hm
  exact mapM_holds hf hh fact (List.contains_iff_mem.mp (List.all_eq_true.mp hc fact hm))

theorem holds_extend {facts : Facts} {ρ : Env} {h : Heap} (vs : List Val)
    (hh : Holds facts ρ h) : Holds facts ρ (h ++ vs) :=
  fun fact hm => apart_extend (hh fact hm) vs

/-- A heap change retains a pair only when both endpoint reads remain valid. -/
def keep (valid : View → Bool) (facts : Facts) : Facts :=
  facts.filter fun (a, b) => valid a && valid b

theorem keep_holds {valid : View → Bool} {facts : Facts} {ρ : Env} {h h' : Heap}
    (hf : ∀ v, valid v = true → ∀ s xs, Reads v ρ h s xs → Reads v ρ h' s xs)
    (hh : Holds facts ρ h) : Holds (keep valid facts) ρ h' := by
  intro fact hm
  obtain ⟨hm, hv⟩ := List.mem_filter.mp hm
  simp only [Bool.and_eq_true] at hv
  apply apart_frame (hh fact hm)
  intro v s xs he hr
  rcases he with rfl | rfl
  · exact hf _ hv.1 _ _ hr
  · exact hf _ hv.2 _ _ hr

/-- Reading a named field gives a shorter path rooted at its result. -/
def View.read (i : Nat) (fld : String) (r : Nat) : View → View
  | .array s (f :: p) => if s == i && f == fld then .array r p else .array s (f :: p)
  | v => v

theorem reads_read {v : View} {ρ : Env} {h : Heap} {i r : Nat} {fld : String}
    {fs cd oid l s xs}
    (hi : ρ i = .objAt fs cd oid) (hf : fs.lookup (.str fld) = some l)
    (hv : h[l]? = some (ρ r)) :
    Reads (v.read i fld r) ρ h s xs ↔ Reads v ρ h s xs := by
  cases v with
  | raw _ => rfl
  | array a p =>
    cases p with
    | nil => rfl
    | cons f p =>
      simp only [View.read]
      split
      · rename_i he
        simp only [Bool.and_eq_true, beq_iff_eq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact (reads_field hi hf hv).symm
      · rfl

def read (facts : Facts) (i : Nat) (fld : String) (r : Nat) : Facts :=
  facts ++ facts.map fun (a, b) => (a.read i fld r, b.read i fld r)

theorem read_holds {facts : Facts} {ρ : Env} {h : Heap} {i r : Nat} {fld : String}
    {fs cd oid l}
    (hi : ρ i = .objAt fs cd oid) (hf : fs.lookup (.str fld) = some l)
    (hv : h[l]? = some (ρ r)) (hh : Holds facts ρ h) :
    Holds (read facts i fld r) ρ h := by
  intro fact hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hh fact hm
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hm
    obtain ⟨sa, xs, sb, ys, ha, hb, hsep⟩ := hh (a, b) hab
    exact ⟨sa, xs, sb, ys, (reads_read hi hf hv).mpr ha,
      (reads_read hi hf hv).mpr hb, hsep⟩

end Verification.HeapKnowledge.ElementRegions
