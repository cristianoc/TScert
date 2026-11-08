import Verification.Semantics.CallEffects

/-! Heap-dependent element regions. A raw store value and an object whose
store field reads that value have different regions: only the latter
includes the store location. All locations in a region are allocated. -/
namespace Verification.HeapKnowledge.ElementRegions

/-- A raw store in a slot, or an array reached through named object fields. -/
inductive View where
  | raw (slot : Nat)
  | array (slot : Nat) (path : List String)
  deriving DecidableEq, Repr, Hashable

/-- The allocated locations of a store view, including its store cell
where it is reached through an object. -/
def Reads (v : View) (ρ : Env) (h : Heap) (store : Option Nat)
    (cells : List (Option Nat)) : Prop :=
  (match v with
    | .raw s => store = none ∧ ρ s = .arr cells
    | .array s p => ∃ w st, store = some st ∧ readPath h (ρ s) p = some w ∧
        Footprints.storeOf w = some st ∧ h[st]? = some (.arr cells)) ∧
  ElementsBelow h.length cells

/-- Membership includes a present element cell or the allocated store cell. -/
def Contains (store : Option Nat) (cells : List (Option Nat)) (l : Nat) : Prop :=
  store = some l ∨ some l ∈ cells

/-- Region evidence keeps both the store cells and the element cells apart. -/
def Apart (a b : View) (ρ : Env) (h : Heap) : Prop :=
  ∃ sa xs sb ys, Reads a ρ h sa xs ∧ Reads b ρ h sb ys ∧
    ∀ l, Contains sa xs l → ∀ m, Contains sb ys m → l ≠ m

theorem reads_below {v ρ h s xs} (hr : Reads v ρ h s xs) :
    ∀ l, Contains s xs l → l < h.length := by
  intro l hl
  rcases hl with hl | hl
  · cases v with
    | raw i => rw [hr.1.1] at hl; cases hl
    | array i p =>
      obtain ⟨⟨w, st, hs, _, _, hv⟩, _⟩ := hr
      rw [hs] at hl; cases hl
      exact (List.getElem?_eq_some_iff.mp hv).1
  · exact hr.2 l hl

theorem reads_extend {v ρ h s xs} (hr : Reads v ρ h s xs) (vs : List Val) :
    Reads v ρ (h ++ vs) s xs := by
  refine ⟨?_, fun l hl => ?_⟩
  · cases v with
    | raw i => exact hr.1
    | array i p =>
      obtain ⟨w, st, hs, hp, hst, hx⟩ := hr.1
      exact ⟨w, st, hs, readPath_extend vs hp, hst,
        by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]; exact hx⟩
  · have := hr.2 l hl
    simp only [List.length_append]; omega

theorem apart_symm {a b ρ h} (ha : Apart a b ρ h) : Apart b a ρ h := by
  obtain ⟨sa, xs, sb, ys, hx, hy, hab⟩ := ha
  exact ⟨sb, ys, sa, xs, hy, hx, fun l hl m hm he => hab m hm l hl he.symm⟩

theorem apart_extend {a b ρ h} (ha : Apart a b ρ h) (vs : List Val) :
    Apart a b ρ (h ++ vs) := by
  obtain ⟨sa, xs, sb, ys, hx, hy, hab⟩ := ha
  exact ⟨sa, xs, sb, ys, reads_extend hx vs, reads_extend hy vs, hab⟩

/-- Renaming a region changes only its root slot. -/
def View.map (f : Nat → Nat) : View → View
  | .raw s => .raw (f s)
  | .array s p => .array (f s) p

def View.slot : View → Nat
  | .raw s | .array s _ => s

theorem reads_map {v : View} {f : Nat → Nat} {ρ ρ' : Env} {h s xs}
    (hf : ρ' (f v.slot) = ρ v.slot) :
    Reads (v.map f) ρ' h s xs ↔ Reads v ρ h s xs := by
  cases v <;> simp_all [Reads, View.map, View.slot]

theorem apart_map {a b : View} {f : Nat → Nat} {ρ ρ' : Env} {h}
    (ha : ρ' (f a.slot) = ρ a.slot) (hb : ρ' (f b.slot) = ρ b.slot) :
    Apart (a.map f) (b.map f) ρ' h ↔ Apart a b ρ h := by
  unfold Apart
  simp only [reads_map ha, reads_map hb]

/-- A literal's raw store is apart from an allocated old view. Dangling
store values cannot supply the premise. -/
theorem literal_apart {a : View} {ρ : Env} {h : Heap} {s xs}
    (hr : Reads a ρ h s xs) (vs : List Val) :
    Apart (.raw 0) (a.map (· + 1)) (push (.arr (elemSlots h.length vs.length)) ρ) (h ++ vs) := by
  refine ⟨none, elemSlots h.length vs.length, s, xs, ⟨⟨rfl, rfl⟩, ?_⟩,
    (reads_map (by rfl)).mpr (reads_extend hr vs), ?_⟩
  · intro l hl
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hl
    simp only [List.mem_range] at hi
    simp only [Option.some.injEq] at he
    simp only [List.length_append]
    omega
  · intro l hl m hm
    rcases hl with hl | hl
    · cases hl
    · have hlow := reads_below hr m hm
      have hhigh := elemSlots_above h.length vs.length l hl
      omega

/-- A field read restates an array path at the returned value. -/
theorem reads_field {ρ : Env} {h : Heap} {i r : Nat} {fld : String}
    {p : List String} {fs cd oid l s xs}
    (hi : ρ i = .objAt fs cd oid) (hf : fs.lookup (.str fld) = some l)
    (hv : h[l]? = some (ρ r)) :
    Reads (.array i (fld :: p)) ρ h s xs ↔ Reads (.array r p) ρ h s xs := by
  simp only [Reads, hi, readPath_cons hf hv]

/-- Framing requires both endpoint reads to remain valid. In particular,
an arbitrary replacement of either store supplies no such evidence. -/
theorem apart_frame {a b ρ h h'} (ha : Apart a b ρ h)
    (hf : ∀ v s xs, (v = a ∨ v = b) → Reads v ρ h s xs → Reads v ρ h' s xs) :
    Apart a b ρ h' := by
  obtain ⟨sa, xs, sb, ys, hx, hy, hab⟩ := ha
  exact ⟨sa, xs, sb, ys, hf a sa xs (.inl rfl) hx, hf b sb ys (.inr rfl) hy, hab⟩

/-- Object construction installs a raw store into a fresh store cell. The
new cell is apart from every location of an allocated old view. -/
theorem object_apart {a : View} {ρ : Env} {h : Heap} {sa xs sb ys fs cd oid}
    (hx : Reads (.raw sa) ρ h none xs) (hy : Reads a ρ h sb ys)
    (hapart : ElementsApart xs ys)
    (hstore : ∀ l, some l ∈ xs → sb ≠ some l)
    (hf : fs.lookup arrayStoreKey = some h.length) :
    Apart (.array 0 []) (a.map (· + 1))
      (push (.objAt fs cd oid) ρ) (h ++ [.arr xs]) := by
  refine ⟨some h.length, xs, sb, ys, ?_,
    (reads_map (by rfl)).mpr (reads_extend hy [.arr xs]), ?_⟩
  · refine ⟨⟨.objAt fs cd oid, h.length, rfl, rfl, ?_, ?_⟩, ?_⟩
    · simpa [Footprints.storeOf, Footprints.fieldsOf] using hf
    · simp
    · intro l hl
      have := hx.2 l hl
      simp only [List.length_append, List.length_singleton]; omega
  · intro l hl m hm
    rcases hl with hl | hl
    · cases hl
      have := reads_below hy m hm
      omega
    · rcases hm with hm | hm
      · intro he; exact hstore l hl (by simpa only [he] using hm)
      · exact hapart l hl m hm

/-- Growing a region with freshly allocated cells preserves separation from
an unchanged allocated old region. The updated store's identity is fixed. -/
theorem apart_grow {a b : View} {ρ : Env} {h h' : Heap} {sa xs sb ys xs'}
    (hy : Reads b ρ h sb ys)
    (hx' : Reads a ρ h' sa xs') (hy' : Reads b ρ h' sb ys)
    (ha : ∀ l, Contains sa xs l → ∀ m, Contains sb ys m → l ≠ m)
    (hg : ∀ l, some l ∈ xs' → some l ∈ xs ∨ h.length ≤ l) :
    Apart a b ρ h' := by
  refine ⟨sa, xs', sb, ys, hx', hy', fun l hl m hm => ?_⟩
  rcases hl with hl | hl
  · exact ha l (.inl hl) m hm
  · rcases hg l hl with hold | hfresh
    · exact ha l (.inr hold) m hm
    · have := reads_below hy m hm
      omega

/-- The audited append relation puts every appended cell beyond the input
heap. Together with the unchanged prefix, this supplies the cell premise
of `apart_grow`. -/
theorem appended_cells {r : Tm} {args : List Tm} {h h' : Heap} {s xs ys}
    (ha : CallEffects.ReceiverAppends r args h h')
    (hv : ∀ a ∈ args, isVal a = true)
    (hs : Footprints.storeOf r = some s) (hx : h[s]? = some (.arr xs))
    (hy : h'[s]? = some (.arr ys)) (hp : xs <+: ys) :
    ∀ l, some l ∈ ys → some l ∈ xs ∨ h.length ≤ l := by
  obtain ⟨ys', hy', hlen, hel⟩ := ha hv s xs hs hx
  rw [hy] at hy'; cases hy'
  intro l hl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  by_cases hold : i < xs.length
  · left
    obtain ⟨tail, rfl⟩ := hp
    rw [List.getElem?_append_left hold] at hi
    exact List.mem_of_getElem? hi
  · right
    have hil : i < ys.length := (List.getElem?_eq_some_iff.mp hi).1
    have hj : i - xs.length < args.length := by omega
    obtain ⟨cell, hcell, _, hfresh⟩ := hel (i - xs.length) args[i - xs.length]
      (List.getElem?_eq_getElem hj)
    have heq : xs.length + (i - xs.length) = i := by omega
    rw [heq, hi] at hcell
    cases hcell
    exact hfresh

/-- A join retains only evidence present on each incoming edge. -/
def meet (states : List (List (View × View))) : List (View × View) :=
  match states with
  | [] => []
  | first :: rest => first.filter fun fact => rest.all (·.contains fact)

def Holds (facts : List (View × View)) (ρ : Env) (h : Heap) : Prop :=
  ∀ fact ∈ facts, Apart fact.1 fact.2 ρ h

theorem meet_holds {states : List (List (View × View))} {facts ρ h}
    (hm : facts ∈ states) (hh : Holds facts ρ h) : Holds (meet states) ρ h := by
  intro fact hf
  cases states with
  | nil => cases hm
  | cons first rest =>
    obtain ⟨hfirst, hrest⟩ := List.mem_filter.mp hf
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hh fact hfirst
    · exact hh fact (List.contains_iff_mem.mp (List.all_eq_true.mp hrest facts hm))

end Verification.HeapKnowledge.ElementRegions
