import Verification.Semantics.Rules
import Verification.Semantics.Tower

/-! A nonempty conjunction of record contracts. Keeping the first operand
explicit prevents the empty conjunction from silently becoming top.

An operand is a finite map from field names to contracts, and each names only
the fields it constrains. Two operands therefore meet only where they name the
same field, which is what makes a conjunction of contracts on disjoint fields
the composed record rather than the empty type. -/
namespace Verification.ReferenceConjunctions

/-- What one operand says: a contract per named field. -/
abbrev Fields := List (PropKey × Fam)

def refsT (A : Fields) (Bs : List Fields) : Fam := fun n W v =>
  recT A n W v ∧ ∀ B ∈ Bs, recT B n W v

theorem adm (A : Fields) (Bs : List Fields) : Adm (refsT A Bs) := by
  constructor
  · intro n W v h
    exact ⟨(recT_adm A).down n W v h.1,
      fun B hb => (recT_adm B).down n W v (h.2 B hb)⟩
  · intro n W U hx v h
    exact ⟨(recT_adm A).mono n W U hx v h.1,
      fun B hb => (recT_adm B).mono n W U hx v (h.2 B hb)⟩

/-- The families a label map denotes, field by field. -/
def famsOf {ι : Type} (X : ι → Fam) (fs : List (PropKey × ι)) : Fields :=
  fs.map (fun p => (p.1, X p.2))

theorem mem_famsOf {ι : Type} {X : ι → Fam} {fs : List (PropKey × ι)} {f : PropKey} {A : Fam} :
    (f, A) ∈ famsOf X fs ↔ ∃ i, (f, i) ∈ fs ∧ A = X i := by
  simp only [famsOf, List.mem_map]
  constructor
  · rintro ⟨⟨g, i⟩, hp, he⟩
    cases he
    exact ⟨i, hp, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(f, i), hi, rfl⟩

theorem recT_congr_below {ι : Type} (X Y : ι → Fam) (a : List (PropKey × ι)) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    recT (famsOf X a) n W v ↔ recT (famsOf Y a) n W v := by
  constructor <;> rintro ⟨flds, oid, rfl, hfs⟩ <;> refine ⟨flds, oid, rfl, ?_⟩ <;>
      intro f T hm <;> obtain ⟨i, hi, rfl⟩ := mem_famsOf.mp hm
  · obtain ⟨l, c, hl, hw, hag⟩ := hfs f (X i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
    exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).trans (h i j hj W' u)⟩
  · obtain ⟨l, c, hl, hw, hag⟩ := hfs f (Y i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
    exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).trans (h i j hj W' u).symm⟩

theorem famsOf_append {ι : Type} (X : ι → Fam) (a b : List (PropKey × ι)) :
    famsOf X (a ++ b) = famsOf X a ++ famsOf X b := List.map_append ..

theorem view_congr_below {ι : Type} (X Y : ι → Fam) (a : List (PropKey × ι)) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    viewT (famsOf X a) n W v ↔ viewT (famsOf Y a) n W v := by
  constructor <;> intro hv f T hm <;> obtain ⟨i, hi, rfl⟩ := mem_famsOf.mp hm
  · obtain ⟨flds, l, c, oid, rfl, hf, hl, hag⟩ := hv f (X i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
    exact ⟨flds, l, c, oid, rfl, hf, hl, fun j hj W' u hu => (h i j hj W' u).mp (hag j hj W' u hu)⟩
  · obtain ⟨flds, l, c, oid, rfl, hf, hl, hag⟩ := hv f (Y i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
    exact ⟨flds, l, c, oid, rfl, hf, hl, fun j hj W' u hu => (h i j hj W' u).mpr (hag j hj W' u hu)⟩

/-- Read capabilities, an array's `length` included, read their families
below the level. -/
theorem views_congr_below {ι : Type} (X Y : ι → Fam) (a : List (PropKey × ι)) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    viewsT (famsOf X a) n W v ↔ viewsT (famsOf Y a) n W v := by
  have side : ∀ (X Y : ι → Fam), (∀ i, Agree (X i) (Y i) n) →
      viewsT (famsOf X a) n W v → viewsT (famsOf Y a) n W v := by
    intro X Y h hv f T hm
    obtain ⟨i, hi, rfl⟩ := mem_famsOf.mp hm
    rcases hv f (X i) (mem_famsOf.mpr ⟨i, hi, rfl⟩) with hw | ⟨hf, hst, hall⟩
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
    rintro X Y h ⟨flds, oid, rfl, hp, hv⟩
    refine ⟨flds, oid, rfl, fun o hm hl => ?_, fun o hm l hl => ?_⟩
    · obtain ⟨p, hpa, rfl⟩ := List.mem_map.mp hm
      exact hp (p.map X) (List.mem_map_of_mem hpa) hl
    · obtain ⟨p, hpa, rfl⟩ := List.mem_map.mp hm
      obtain ⟨c, hc, hag⟩ := hv (p.map X) (List.mem_map_of_mem hpa) l hl
      exact ⟨c, hc, fun j hj W' u => (hag j hj W' u).congr (h p.type j hj W' u)⟩
  exact ⟨side X Y fun i j hj W' u => h i j hj W' u,
    side Y X fun i j hj W' u => (h i j hj W' u).symm⟩

theorem congr_below {ι : Type} (X Y : ι → Fam) (a : List (PropKey × ι))
    (bs : List (List (PropKey × ι))) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    refsT (famsOf X a) (bs.map (famsOf X)) n W v ↔
      refsT (famsOf Y a) (bs.map (famsOf Y)) n W v := by
  simp only [refsT, List.forall_mem_map]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨(recT_congr_below X Y a n h W v).mp ha,
      fun b hm => (recT_congr_below X Y b n h W v).mp (hb b hm)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨(recT_congr_below X Y a n h W v).mpr ha,
      fun b hm => (recT_congr_below X Y b n h W v).mpr (hb b hm)⟩

/-- One operand naming the fields of two: a value has one own-field map, so
the two operands' fields are fields of that one map, and one operand listing
both says exactly what the two say. -/
theorem recT_append (A C : Fields) (n : Nat) (W : WorldT n) (v : Val) :
    recT (A ++ C) n W v ↔ interT (recT A) (recT C) n W v := by
  constructor
  · rintro ⟨flds, oid, rfl, h⟩
    exact ⟨⟨flds, oid, rfl, fun f T hm => h f T (List.mem_append_left _ hm)⟩,
      ⟨flds, oid, rfl, fun f T hm => h f T (List.mem_append_right _ hm)⟩⟩
  · rintro ⟨⟨flds, oid, rfl, ha⟩, ⟨flds', oid', he, hc⟩⟩
    cases he
    refine ⟨flds, oid, rfl, fun f T hm => ?_⟩
    rcases List.mem_append.mp hm with h | h
    · exact ha f T h
    · exact hc f T h

/-- The conjunction of two conjunctions, with their first operands joined
into one: the record the meet of two object contracts is, whose named fields
the read rules find in its first operand. -/
theorem flatten (A C : Fields) (Bs Ds : List Fields) (n : Nat) (W : WorldT n) (v : Val) :
    refsT (A ++ C) (Bs ++ Ds) n W v ↔ interT (refsT A Bs) (refsT C Ds) n W v := by
  simp only [refsT, recT_append, interT, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨⟨ha, hc⟩, hb, hd⟩; exact ⟨⟨ha, hb⟩, hc, hd⟩
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩; exact ⟨⟨ha, hc⟩, hb, hd⟩

end Verification.ReferenceConjunctions
