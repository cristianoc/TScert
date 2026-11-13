import Verification.Semantics.Rules
import Verification.Semantics.Tower

/-! A nonempty conjunction of record contracts. Keeping the first operand
explicit prevents the empty conjunction from silently becoming top.

An operand is a finite map from field names to contracts, and each names only
the fields it constrains. Two operands therefore meet only where they name the
same field, which is what makes a conjunction of contracts on disjoint fields
the composed record rather than the empty type. -/
namespace Verification.ReferenceConjunctions

def refsT (A : Fields) (Bs : List Fields) : Fam := fun n W v =>
  recT A n W v ∧ (∀ B ∈ Bs, recT B n W v) ∧ ((A :: Bs).flatten ≠ [] → NoHost v)

theorem adm (A : Fields) (Bs : List Fields) : Adm (refsT A Bs) := by
  constructor
  · intro n W v h
    exact ⟨(recT_adm A).down n W v h.1,
      fun B hb => (recT_adm B).down n W v (h.2.1 B hb), h.2.2⟩
  · intro n W U hx v h
    exact ⟨(recT_adm A).mono n W U hx v h.1,
      fun B hb => (recT_adm B).mono n W U hx v (h.2.1 B hb), h.2.2⟩

/-- A conjunction naming an invariant field admits no host object. -/
theorem noHost {A : Fields} {Bs : List Fields} {n : Nat} {W : WorldT n} {v : Val}
    (h : refsT A Bs n W v) (hne : (A :: Bs).flatten ≠ []) : NoHost v := h.2.2 hne

/-- The families a label map denotes, storage position by position: each
key keeps its role. -/
def famsOf {ι : Type} (X : ι → Fam) (fs : List (Stored ι)) : Fields := mapStored X fs

theorem mem_famsOf {ι : Type} {X : ι → Fam} {fs : List (Stored ι)} {f : PropKey}
    {s : StorageRole} {A : Fam} :
    (f, s, A) ∈ famsOf X fs ↔ ∃ i, (f, s, i) ∈ fs ∧ A = X i := by
  simp only [famsOf, mem_mapStored]
  exact ⟨fun ⟨i, hi, he⟩ => ⟨i, hi, he.symm⟩, fun ⟨i, hi, he⟩ => ⟨i, hi, he.symm⟩⟩

/-- **Interpretation keeps every key's role.** -/
@[simp] theorem storageOf_famsOf {ι : Type} (X : ι → Fam) (fs : List (Stored ι)) :
    storageOf (famsOf X fs) = storageOf fs := storageOf_mapStored X fs

/-- The families a map of read capabilities denotes, key by key. -/
def viewsOf {ι : Type} (X : ι → Fam) (fs : List (PropKey × ι)) : Views :=
  fs.map (fun p => (p.1, X p.2))

theorem mem_viewsOf {ι : Type} {X : ι → Fam} {fs : List (PropKey × ι)} {f : PropKey} {A : Fam} :
    (f, A) ∈ viewsOf X fs ↔ ∃ i, (f, i) ∈ fs ∧ A = X i := by
  simp only [viewsOf, List.mem_map]
  constructor
  · rintro ⟨⟨g, i⟩, hp, he⟩
    cases he
    exact ⟨i, hp, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(f, i), hi, rfl⟩

theorem viewsOf_append {ι : Type} (X : ι → Fam) (a b : List (PropKey × ι)) :
    viewsOf X (a ++ b) = viewsOf X a ++ viewsOf X b := List.map_append ..

/-- Naming an invariant field is a fact about the labels, whatever they
denote. -/
theorem famsOf_flatten_ne {ι : Type} {X : ι → Fam} {a : List (Stored ι)} {bs : List (List (Stored ι))}
    (h : (a :: bs).flatten ≠ []) : (famsOf X a :: bs.map (famsOf X)).flatten ≠ [] := by
  intro he
  apply h
  simp only [List.flatten_cons, List.append_eq_nil_iff, List.flatten_eq_nil_iff, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, famsOf, mapStored, List.map_eq_nil_iff] at he ⊢
  exact he

theorem recT_congr_below {ι : Type} (X Y : ι → Fam) (a : List (Stored ι)) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    recT (famsOf X a) n W v ↔ recT (famsOf Y a) n W v := by
  constructor <;> rintro ⟨flds, oid, rfl, hown, hfs⟩
  · refine ⟨flds, oid, rfl, fun f s T hm => ?_, fun f s T hm => ?_⟩ <;>
      obtain ⟨i, hi, rfl⟩ := mem_famsOf.mp hm
    · exact hown f s (X i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
    · obtain ⟨l, c, hl, hw, hag⟩ := hfs f s (X i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
      exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).trans (h i j hj W' u)⟩
  · refine ⟨flds, oid, rfl, fun f s T hm => ?_, fun f s T hm => ?_⟩ <;>
      obtain ⟨i, hi, rfl⟩ := mem_famsOf.mp hm
    · exact hown f s (Y i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
    · obtain ⟨l, c, hl, hw, hag⟩ := hfs f s (Y i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
      exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).trans (h i j hj W' u).symm⟩

theorem famsOf_append {ι : Type} (X : ι → Fam) (a b : List (Stored ι)) :
    famsOf X (a ++ b) = famsOf X a ++ famsOf X b := List.map_append ..

theorem view_congr_below {ι : Type} (X Y : ι → Fam) (a : List (PropKey × ι)) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    viewT (viewsOf X a) n W v ↔ viewT (viewsOf Y a) n W v := by
  constructor <;> intro hv f T hm <;> obtain ⟨i, hi, rfl⟩ := mem_viewsOf.mp hm
  · obtain ⟨flds, l, c, oid, rfl, hf, hl, hag⟩ := hv f (X i) (mem_viewsOf.mpr ⟨i, hi, rfl⟩)
    exact ⟨flds, l, c, oid, rfl, hf, hl, fun j hj W' u hu => (h i j hj W' u).mp (hag j hj W' u hu)⟩
  · obtain ⟨flds, l, c, oid, rfl, hf, hl, hag⟩ := hv f (Y i) (mem_viewsOf.mpr ⟨i, hi, rfl⟩)
    exact ⟨flds, l, c, oid, rfl, hf, hl, fun j hj W' u hu => (h i j hj W' u).mpr (hag j hj W' u hu)⟩

/-- Read capabilities, an array's `length` included, read their families
below the level. -/
theorem views_congr_below {ι : Type} (X Y : ι → Fam) (a : List (PropKey × ι)) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    viewsT (viewsOf X a) n W v ↔ viewsT (viewsOf Y a) n W v := by
  have side : ∀ (X Y : ι → Fam), (∀ i, Agree (X i) (Y i) n) →
      viewsT (viewsOf X a) n W v → viewsT (viewsOf Y a) n W v := by
    intro X Y h hv f T hm
    obtain ⟨i, hi, rfl⟩ := mem_viewsOf.mp hm
    rcases hv f (X i) (mem_viewsOf.mpr ⟨i, hi, rfl⟩) with hw | ⟨hf, hst, hall⟩
    · left
      intro g U hg
      simp only [List.mem_singleton, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      obtain ⟨flds, l, c, oid, rfl, hf, hl, hag⟩ := hw g (X i) (List.mem_singleton_self _)
      exact ⟨flds, l, c, oid, rfl, hf, hl, fun j hj W' u hu => (h i j hj W' u).mp (hag j hj W' u hu)⟩
    · exact .inr ⟨hf, hst, fun j hj W' m => (h i j hj W' _).mp (hall j hj W' m)⟩
  exact ⟨side X Y h, side Y X fun i j hj W' u => (h i j hj W' u).symm⟩

theorem opt_congr_below {ι : Type} (X Y : ι → Fam) (a : List (OptionalField ι)) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    optT (a.map (·.map X)) n W v ↔ optT (a.map (·.map Y)) n W v := by
  have side : ∀ (X Y : ι → Fam), (∀ i j (hj : j < n) (W' : WorldT j) u, X i j W' u ↔ Y i j W' u) →
      optT (a.map (·.map X)) n W v → optT (a.map (·.map Y)) n W v := by
    rintro X Y h ⟨flds, oid, rfl, hw, hp, hv⟩
    refine ⟨flds, oid, rfl, fun o hm hro l hl => ?_, fun o hm hl => ?_, fun o hm l hl => ?_⟩
    · obtain ⟨p, hpa, rfl⟩ := List.mem_map.mp hm
      exact hw (p.map X) (List.mem_map_of_mem hpa) hro l hl
    · obtain ⟨p, hpa, rfl⟩ := List.mem_map.mp hm
      exact hp (p.map X) (List.mem_map_of_mem hpa) hl
    · obtain ⟨p, hpa, rfl⟩ := List.mem_map.mp hm
      obtain ⟨c, hc, hag⟩ := hv (p.map X) (List.mem_map_of_mem hpa) l hl
      exact ⟨c, hc, fun j hj W' u => (hag j hj W' u).congr (h p.type j hj W' u)⟩
  exact ⟨side X Y fun i j hj W' u => h i j hj W' u,
    side Y X fun i j hj W' u => (h i j hj W' u).symm⟩

theorem congr_below {ι : Type} (X Y : ι → Fam) (a : List (Stored ι))
    (bs : List (List (Stored ι))) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    refsT (famsOf X a) (bs.map (famsOf X)) n W v ↔
      refsT (famsOf Y a) (bs.map (famsOf Y)) n W v := by
  have hne : ∀ Z : ι → Fam, (famsOf Z a :: bs.map (famsOf Z)).flatten = [] ↔ (a :: bs).flatten = [] := by
    intro Z
    simp [famsOf, mapStored, List.flatten_eq_nil_iff]
  simp only [refsT, List.forall_mem_map]
  constructor
  · rintro ⟨ha, hb, hh⟩
    exact ⟨(recT_congr_below X Y a n h W v).mp ha,
      fun b hm => (recT_congr_below X Y b n h W v).mp (hb b hm),
      fun hy => hh fun hx => hy ((hne Y).mpr ((hne X).mp hx))⟩
  · rintro ⟨ha, hb, hh⟩
    exact ⟨(recT_congr_below X Y a n h W v).mpr ha,
      fun b hm => (recT_congr_below X Y b n h W v).mpr (hb b hm),
      fun hx => hh fun hy => hx ((hne X).mpr ((hne Y).mp hy))⟩

/-- One operand naming the fields of two: a value has one own-field map, so
the two operands' fields are fields of that one map, and one operand listing
both says exactly what the two say. -/
theorem recT_append (A C : Fields) (n : Nat) (W : WorldT n) (v : Val) :
    recT (A ++ C) n W v ↔ interT (recT A) (recT C) n W v := by
  constructor
  · rintro ⟨flds, oid, rfl, hown, h⟩
    exact ⟨⟨flds, oid, rfl, fun f s T hm => hown f s T (List.mem_append_left _ hm),
        fun f s T hm => h f s T (List.mem_append_left _ hm)⟩,
      ⟨flds, oid, rfl, fun f s T hm => hown f s T (List.mem_append_right _ hm),
        fun f s T hm => h f s T (List.mem_append_right _ hm)⟩⟩
  · rintro ⟨⟨flds, oid, rfl, hoa, ha⟩, ⟨flds', oid', he, hoc, hc⟩⟩
    cases he
    refine ⟨flds, oid, rfl, fun f s T hm => ?_, fun f s T hm => ?_⟩
    · rcases List.mem_append.mp hm with h | h
      · exact hoa f s T h
      · exact hoc f s T h
    rcases List.mem_append.mp hm with h | h
    · exact ha f s T h
    · exact hc f s T h

/-- The conjunction of two conjunctions, with their first operands joined
into one: the record the meet of two object contracts is, whose named fields
the read rules find in its first operand. -/
theorem flatten (A C : Fields) (Bs Ds : List Fields) (n : Nat) (W : WorldT n) (v : Val) :
    refsT (A ++ C) (Bs ++ Ds) n W v ↔ interT (refsT A Bs) (refsT C Ds) n W v := by
  have hfl : ((A ++ C) :: (Bs ++ Ds)).flatten ≠ [] ↔ (A :: Bs).flatten ≠ [] ∨ (C :: Ds).flatten ≠ [] := by
    simp only [List.flatten_cons, List.flatten_append, ne_eq, List.append_eq_nil_iff]
    constructor
    · intro h
      by_cases h1 : A = [] ∧ Bs.flatten = []
      · exact .inr fun h2 => h ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩
      · exact .inl h1
    · rintro (h | h) ⟨⟨ha, hc⟩, hb, hd⟩
      · exact h ⟨ha, hb⟩
      · exact h ⟨hc, hd⟩
  simp only [refsT, recT_append, interT, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨⟨ha, hc⟩, ⟨hb, hd⟩, hh⟩
    exact ⟨⟨ha, hb, fun hn => hh (hfl.mpr (.inl hn))⟩, hc, hd, fun hn => hh (hfl.mpr (.inr hn))⟩
  · rintro ⟨⟨ha, hb, hh1⟩, hc, hd, hh2⟩
    exact ⟨⟨ha, hc⟩, ⟨hb, hd⟩, fun hn => (hfl.mp hn).elim hh1 hh2⟩

end Verification.ReferenceConjunctions
