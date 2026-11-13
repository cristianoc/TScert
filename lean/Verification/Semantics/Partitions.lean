import Verification.Semantics.CanonicalLists
import Std.Data.HashMap.Lemmas

/-! Partitions of a finite set of slots, as lists of disjoint classes, and
the merge of two classes (heap-knowledge draft, §3). -/
namespace Verification.Partitions

abbrev Partition := List (List Nat)

/-- The class holding `a`, or `[a]` where no class does. -/
def cls (cs : Partition) (a : Nat) : List Nat := (cs.find? (·.contains a)).getD [a]

/-- First-class lookup, including the first match when classes overlap. -/
def index : Partition → Std.HashMap Nat (List Nat)
  | [] => {}
  | c :: cs => c.foldl (fun m x => m.insert x c) (index cs)

/-- Whether `a` and `b` are in one class. -/
def same (cs : Partition) (a b : Nat) : Bool := (cls cs a).contains b

/-- Merge the classes of `a` and `b`; the partition itself where they are one. -/
def merge (cs : Partition) (a b : Nat) : Partition :=
  if same cs a b then cs
  else (cls cs a ++ cls cs b) :: cs.filter fun k => !k.contains a && !k.contains b

/-- A partition of `S`: disjoint, nonempty classes covering exactly `S`. -/
structure Ok (S : List Nat) (cs : Partition) : Prop where
  cover : ∀ x, x ∈ S ↔ ∃ k ∈ cs, x ∈ k
  disjoint : ∀ k ∈ cs, ∀ k' ∈ cs, ∀ x, x ∈ k → x ∈ k' → k = k'
  nonempty : ∀ k ∈ cs, k ≠ []

theorem cls_of_mem {cs : Partition} {S : List Nat} (h : Ok S cs) {k : List Nat} (hk : k ∈ cs) {a : Nat}
    (ha : a ∈ k) : cls cs a = k := by
  unfold cls
  cases hf : cs.find? (·.contains a) with
  | none =>
    have := List.find?_eq_none.mp hf k hk
    simp [ha] at this
  | some k' =>
    have hk' := List.mem_of_find?_eq_some hf
    have ha' : a ∈ k' := by simpa using List.find?_some hf
    simp only [Option.getD_some]
    exact h.disjoint k' hk' k hk a ha' ha

theorem mem_cls_self {cs : Partition} (a : Nat) : a ∈ cls cs a := by
  unfold cls
  cases hf : cs.find? (·.contains a) with
  | none => simp
  | some k => simpa using List.find?_some hf

theorem cls_not_mem {cs : Partition} {S : List Nat} (h : Ok S cs) {a : Nat} (ha : a ∉ S) :
    cls cs a = [a] := by
  unfold cls
  cases hf : cs.find? (·.contains a) with
  | none => rfl
  | some k =>
    have := List.mem_of_find?_eq_some hf
    have ha' : a ∈ k := by simpa using List.find?_some hf
    exact absurd ((h.cover a).mpr ⟨k, this, ha'⟩) ha

/-- `same` is an equivalence. -/
theorem same_refl (cs : Partition) (a : Nat) : same cs a a = true := by
  simp [same, mem_cls_self]

theorem same_iff {cs : Partition} {S : List Nat} (h : Ok S cs) {a b : Nat} :
    same cs a b = true ↔ cls cs a = cls cs b := by
  simp only [same, List.contains_iff_mem]
  constructor
  · intro hb
    by_cases ha : a ∈ S
    · obtain ⟨k, hk, hak⟩ := (h.cover a).mp ha
      rw [cls_of_mem h hk hak] at hb ⊢
      exact (cls_of_mem h hk hb).symm
    · rw [cls_not_mem h ha] at hb ⊢
      simp at hb; subst hb; exact (cls_not_mem h ha).symm
  · intro e; rw [e]; exact mem_cls_self b

theorem same_symm {cs : Partition} {S : List Nat} (h : Ok S cs) {a b : Nat} (hab : same cs a b = true) :
    same cs b a = true := (same_iff h).mpr ((same_iff h).mp hab).symm

theorem same_trans {cs : Partition} {S : List Nat} (h : Ok S cs) {a b c : Nat} (hab : same cs a b = true)
    (hbc : same cs b c = true) : same cs a c = true :=
  (same_iff h).mpr (((same_iff h).mp hab).trans ((same_iff h).mp hbc))

theorem two_le_length {α : Type} {m : List α} {x y : α} (hx : x ∈ m) (hy : y ∈ m) (hxy : x ≠ y) :
    2 ≤ m.length := by
  match m, hx, hy with
  | [a], hx, hy => simp at hx hy; exact absurd (hx.trans hy.symm) hxy
  | _ :: _ :: _, _, _ => simp

theorem length_filter_two {α : Type} {l : List α} {p : α → Bool} {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hxy : x ≠ y) (px : p x = false) (py : p y = false) : (l.filter p).length + 2 ≤ l.length := by
  have e := List.length_eq_countP_add_countP p (l := l)
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at e
  have := two_le_length (m := l.filter fun a => ¬p a) (List.mem_filter.mpr ⟨hx, by simp [px]⟩)
    (List.mem_filter.mpr ⟨hy, by simp [py]⟩) hxy
  omega

theorem cls_mem_of {cs : Partition} {S : List Nat} (h : Ok S cs) {a : Nat} (ha : a ∈ S) : cls cs a ∈ cs := by
  obtain ⟨k, hk, hak⟩ := (h.cover a).mp ha
  rw [cls_of_mem h hk hak]; exact hk

theorem mem_cls_iff {cs : Partition} {S : List Nat} (h : Ok S cs) {a x : Nat} :
    x ∈ cls cs a ↔ cls cs x = cls cs a := by
  constructor
  · intro hx
    by_cases ha : a ∈ S
    · exact cls_of_mem h (cls_mem_of h ha) hx
    · rw [cls_not_mem h ha] at hx ⊢; simp at hx; subst hx; exact cls_not_mem h ha
  · intro e; rw [← e]; exact mem_cls_self x

section merge
variable {cs : Partition} {S : List Nat} (h : Ok S cs) {a b : Nat} (ha : a ∈ S) (hb : b ∈ S)
include h ha hb

private abbrev rest (cs : Partition) (a b : Nat) := cs.filter fun k => !k.contains a && !k.contains b

theorem merge_ok : Ok S (merge cs a b) := by
  unfold merge
  split
  · exact h
  · have hka := cls_mem_of h ha
    have hkb := cls_mem_of h hb
    -- A class holding `a` or `b` is the class of `a` or of `b`.
    have hrest : ∀ k ∈ cs, k ∉ rest cs a b → k = cls cs a ∨ k = cls cs b := fun k hk hn => by
      by_cases hak : a ∈ k
      · exact Or.inl (cls_of_mem h hk hak).symm
      · by_cases hbk : b ∈ k
        · exact Or.inr (cls_of_mem h hk hbk).symm
        · exact absurd (List.mem_filter.mpr ⟨hk, by simp [hak, hbk]⟩) hn
    refine ⟨fun x => ?_, ?_, ?_⟩
    · constructor
      · intro hx
        obtain ⟨k, hk, hxk⟩ := (h.cover x).mp hx
        by_cases hkr : k ∈ rest cs a b
        · exact ⟨k, List.mem_cons_of_mem _ hkr, hxk⟩
        · rcases hrest k hk hkr with rfl | rfl
          · exact ⟨_, List.mem_cons_self .., List.mem_append_left _ hxk⟩
          · exact ⟨_, List.mem_cons_self .., List.mem_append_right _ hxk⟩
      · rintro ⟨k, hk, hxk⟩
        rcases List.mem_cons.mp hk with rfl | hk
        · rcases List.mem_append.mp hxk with hx | hx
          · exact (h.cover x).mpr ⟨_, hka, hx⟩
          · exact (h.cover x).mpr ⟨_, hkb, hx⟩
        · exact (h.cover x).mpr ⟨k, (List.mem_filter.mp hk).1, hxk⟩
    · -- The merged class meets no remaining class.
      have hnew : ∀ k ∈ rest cs a b, ∀ x, x ∈ cls cs a ++ cls cs b → x ∈ k → False := by
        intro k hk x hx hxk
        obtain ⟨hk, hp⟩ := List.mem_filter.mp hk
        have hp : a ∉ k ∧ b ∉ k := by simpa using hp
        rcases List.mem_append.mp hx with hx | hx
        · exact hp.1 (h.disjoint _ hka k hk x hx hxk ▸ mem_cls_self a)
        · exact hp.2 (h.disjoint _ hkb k hk x hx hxk ▸ mem_cls_self b)
      intro k hk k' hk' x hx hx'
      rcases List.mem_cons.mp hk with rfl | hk <;> rcases List.mem_cons.mp hk' with rfl | hk'
      · rfl
      · exact (hnew _ hk' x hx hx').elim
      · exact (hnew _ hk x hx' hx).elim
      · exact h.disjoint k (List.mem_filter.mp hk).1 k' (List.mem_filter.mp hk').1 x hx hx'
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact List.ne_nil_of_mem (List.mem_append_left _ (mem_cls_self a))
      · exact h.nonempty k (List.mem_filter.mp hk).1

theorem merge_length (hn : same cs a b = false) : (merge cs a b).length < cs.length := by
  unfold merge
  rw [if_neg (by simp [hn])]
  have hne : cls cs a ≠ cls cs b := fun e => by
    simp [same, e, mem_cls_self] at hn
  have := length_filter_two (p := fun k => !k.contains a && !k.contains b) (cls_mem_of h ha) (cls_mem_of h hb) hne
    (by simp [mem_cls_self]) (by simp [mem_cls_self])
  simp only [List.length_cons]
  omega

/-- After a merge, two slots are in one class when they were, or when each
was with `a` or with `b`. -/
theorem same_merge (x y : Nat) : same (merge cs a b) x y = true ↔
    same cs x y = true ∨ ((same cs x a = true ∨ same cs x b = true) ∧ (same cs y a = true ∨ same cs y b = true)) := by
  have hm := merge_ok h ha hb
  have sym := fun {u v : Nat} (e : same cs u v = true) => same_symm h e
  by_cases hab : same cs a b = true
  · simp only [merge, hab, if_true]
    constructor
    · exact Or.inl
    · rintro (e | ⟨hx, hy⟩)
      · exact e
      · have hxa : same cs x a = true := hx.elim id fun e => same_trans h e (sym hab)
        have hya : same cs y a = true := hy.elim id fun e => same_trans h e (sym hab)
        exact same_trans h hxa (sym hya)
  · -- The merged class is the head; other classes are unchanged.
    have hnew : ∀ u, u ∈ cls cs a ++ cls cs b → cls (merge cs a b) u = cls cs a ++ cls cs b := fun u hu =>
      cls_of_mem hm (by simp [merge, hab]) hu
    have hold : ∀ u, u ∉ cls cs a ++ cls cs b → cls (merge cs a b) u = cls cs u := by
      intro u hu
      by_cases hS : u ∈ S
      · have hk := cls_mem_of h hS
        have hna : a ∉ cls cs u := fun m =>
          hu (List.mem_append_left _ ((mem_cls_iff h).mpr ((mem_cls_iff h).mp m).symm))
        have hnb : b ∉ cls cs u := fun m =>
          hu (List.mem_append_right _ ((mem_cls_iff h).mpr ((mem_cls_iff h).mp m).symm))
        apply cls_of_mem hm _ (mem_cls_self u)
        simp only [merge, hab]
        exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hk, by simp [hna, hnb]⟩)
      · rw [cls_not_mem hm hS, cls_not_mem h hS]
    have hxa : ∀ u, u ∈ cls cs a ++ cls cs b ↔ (same cs u a = true ∨ same cs u b = true) := fun u => by
      simp only [List.mem_append, same, List.contains_iff_mem]
      constructor
      · rintro (e | e)
        · exact Or.inl ((mem_cls_iff h).mpr ((mem_cls_iff h).mp e).symm)
        · exact Or.inr ((mem_cls_iff h).mpr ((mem_cls_iff h).mp e).symm)
      · rintro (e | e)
        · exact Or.inl ((mem_cls_iff h).mpr ((mem_cls_iff h).mp e).symm)
        · exact Or.inr ((mem_cls_iff h).mpr ((mem_cls_iff h).mp e).symm)
    show (cls (merge cs a b) x).contains y = true ↔ _
    by_cases hx : x ∈ cls cs a ++ cls cs b
    · rw [hnew x hx, List.contains_iff_mem, hxa y]
      have hx' := (hxa x).mp hx
      constructor
      · intro e; exact Or.inr ⟨hx', e⟩
      · rintro (e | ⟨_, e⟩)
        · rcases hx' with e' | e'
          · exact Or.inl (same_trans h (sym e) e')
          · exact Or.inr (same_trans h (sym e) e')
        · exact e
    · rw [hold x hx]
      have : ¬ (same cs x a = true ∨ same cs x b = true) := fun e => hx ((hxa x).mpr e)
      constructor
      · exact Or.inl
      · rintro (e | ⟨e, _⟩)
        · exact e
        · exact absurd e this

end merge

end Verification.Partitions
